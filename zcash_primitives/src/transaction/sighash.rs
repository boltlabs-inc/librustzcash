use blake2_rfc::blake2b::Blake2b;
use byteorder::{LittleEndian, WriteBytesExt};

use super::{
    components::{Amount, Script},
    Transaction, OVERWINTER_VERSION_GROUP_ID, SAPLING_TX_VERSION,
};

const ZCASH_SIGHASH_PERSONALIZATION_PREFIX: &'static [u8; 12] = b"ZcashSigHash";
const ZCASH_PREVOUTS_HASH_PERSONALIZATION: &'static [u8; 16] = b"ZcashPrevoutHash";
const ZCASH_SEQUENCE_HASH_PERSONALIZATION: &'static [u8; 16] = b"ZcashSequencHash";
const ZCASH_OUTPUTS_HASH_PERSONALIZATION: &'static [u8; 16] = b"ZcashOutputsHash";
const ZCASH_JOINSPLITS_HASH_PERSONALIZATION: &'static [u8; 16] = b"ZcashJSplitsHash";

const SIGHASH_NONE: u32 = 2;
const SIGHASH_SINGLE: u32 = 3;
const SIGHASH_MASK: u32 = 0x1f;
const SIGHASH_ANYONECANPAY: u32 = 0x80;

macro_rules! update_u32 {
    ($h:expr, $value:expr, $tmp:expr) => {
        (&mut $tmp[..4]).write_u32::<LittleEndian>($value).unwrap();
        $h.update(&$tmp[..4]);
    };
}

macro_rules! update_hash {
    ($h:expr, $cond:expr, $value:expr) => {
        if $cond {
            $h.update(&$value);
        } else {
            $h.update(&[0; 32]);
        }
    };
}

#[derive(PartialEq)]
enum SigHashVersion {
    Sprout,
    Overwinter,
}

impl SigHashVersion {
    fn from_tx(tx: &Transaction) -> Self {
        if tx.overwintered {
            match tx.version_group_id {
                OVERWINTER_VERSION_GROUP_ID => SigHashVersion::Overwinter,
                _ => unimplemented!(),
            }
        } else {
            SigHashVersion::Sprout
        }
    }
}

fn prevout_hash(tx: &Transaction) -> Vec<u8> {
    let mut data = Vec::with_capacity(tx.vin.len() * 36);
    for t_in in &tx.vin {
        t_in.prevout.write(&mut data).unwrap();
    }
    let mut h = Blake2b::with_params(32, &[], &[], ZCASH_PREVOUTS_HASH_PERSONALIZATION);
    h.update(&data);
    h.finalize().as_ref().to_vec()
}

fn sequence_hash(tx: &Transaction) -> Vec<u8> {
    let mut data = Vec::with_capacity(tx.vin.len() * 4);
    for t_in in &tx.vin {
        (&mut data)
            .write_u32::<LittleEndian>(t_in.sequence)
            .unwrap();
    }
    let mut h = Blake2b::with_params(32, &[], &[], ZCASH_SEQUENCE_HASH_PERSONALIZATION);
    h.update(&data);
    h.finalize().as_ref().to_vec()
}

fn outputs_hash(tx: &Transaction) -> Vec<u8> {
    let mut data = Vec::with_capacity(tx.vout.len() * (4 + 1));
    for t_out in &tx.vout {
        t_out.write(&mut data).unwrap();
    }
    let mut h = Blake2b::with_params(32, &[], &[], ZCASH_OUTPUTS_HASH_PERSONALIZATION);
    h.update(&data);
    h.finalize().as_ref().to_vec()
}

fn joinsplits_hash(tx: &Transaction) -> Vec<u8> {
    let mut data = Vec::with_capacity(
        tx.joinsplits.len() * if tx.version < SAPLING_TX_VERSION {
            1802 // JSDescription with PHGR13 proof
        } else {
            1698 // JSDescription with Groth16 proof
        },
    );
    for js in &tx.joinsplits {
        js.write(&mut data).unwrap();
    }
    data.extend_from_slice(&tx.joinsplit_pubkey);
    let mut h = Blake2b::with_params(32, &[], &[], ZCASH_JOINSPLITS_HASH_PERSONALIZATION);
    h.update(&data);
    h.finalize().as_ref().to_vec()
}

pub fn signature_hash(
    tx: &Transaction,
    consensus_branch_id: u32,
    hash_type: u32,
    transparent_input: Option<(usize, Script, Amount)>,
) -> Vec<u8> {
    let sigversion = SigHashVersion::from_tx(tx);
    match sigversion {
        SigHashVersion::Overwinter => {
            let hash_outputs = if (hash_type & SIGHASH_MASK) != SIGHASH_SINGLE
                && (hash_type & SIGHASH_MASK) != SIGHASH_NONE
            {
                outputs_hash(tx)
            } else if (hash_type & SIGHASH_MASK) == SIGHASH_SINGLE
                && transparent_input.is_some()
                && transparent_input.as_ref().unwrap().0 < tx.vout.len()
            {
                let mut data = vec![];
                tx.vout[transparent_input.as_ref().unwrap().0]
                    .write(&mut data)
                    .unwrap();
                let mut h = Blake2b::with_params(32, &[], &[], ZCASH_OUTPUTS_HASH_PERSONALIZATION);
                h.update(&data);
                h.finalize().as_ref().to_vec()
            } else {
                vec![0; 32]
            };

            let mut personal = [0; 16];
            (&mut personal[..12]).copy_from_slice(ZCASH_SIGHASH_PERSONALIZATION_PREFIX);
            (&mut personal[12..])
                .write_u32::<LittleEndian>(consensus_branch_id)
                .unwrap();

            let mut h = Blake2b::with_params(32, &[], &[], &personal);
            let mut tmp = [0; 8];

            update_u32!(h, tx.header(), tmp);
            update_u32!(h, tx.version_group_id, tmp);
            update_hash!(h, hash_type & SIGHASH_ANYONECANPAY == 0, prevout_hash(tx));
            update_hash!(
                h,
                hash_type & SIGHASH_ANYONECANPAY == 0
                    && (hash_type & SIGHASH_MASK) != SIGHASH_SINGLE
                    && (hash_type & SIGHASH_MASK) != SIGHASH_NONE,
                sequence_hash(tx)
            );
            h.update(&hash_outputs);
            update_hash!(h, !tx.joinsplits.is_empty(), joinsplits_hash(tx));
            update_u32!(h, tx.lock_time, tmp);
            update_u32!(h, tx.expiry_height, tmp);
            update_u32!(h, hash_type, tmp);

            if let Some((n, script_code, amount)) = transparent_input {
                let mut data = vec![];
                tx.vin[n].prevout.write(&mut data).unwrap();
                script_code.write(&mut data).unwrap();
                (&mut data).write_u64::<LittleEndian>(amount.0).unwrap();
                (&mut data)
                    .write_u32::<LittleEndian>(tx.vin[n].sequence)
                    .unwrap();
                h.update(&data);
            }

            h.finalize().as_ref().to_vec()
        }
        SigHashVersion::Sprout => unimplemented!(),
    }
}