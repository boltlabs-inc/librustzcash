//! ZIP 304 protocol for signing arbitrary messages with Sapling payment addresses.

use bellman::{
    gadgets::multipack,
    groth16::{create_random_proof, verify_proof, Parameters, PreparedVerifyingKey, Proof},
};
use ff::Field;
use pairing::bls12_381::{Bls12, Fr};
use rand_os::OsRng;
use zcash_primitives::{
    jubjub::{edwards, fs::Fs, FixedGenerators, JubjubBls12, Unknown},
    keys::ExpandedSpendingKey,
    merkle_tree::{CommitmentTree, IncrementalWitness},
    primitives::{Note, PaymentAddress, ValueCommitment},
    redjubjub::{self, PrivateKey, PublicKey},
    sapling::{spend_sig, Node},
};

use crate::circuit::sapling::Spend;

const ZIP304_PERSONALIZATION_PREFIX: &'static [u8; 12] = b"ZIP304Signed";

fn is_small_order<Order>(p: &edwards::Point<Bls12, Order>, params: &JubjubBls12) -> bool {
    p.double(params).double(params).double(params) == edwards::Point::zero()
}

/// A ZIP 304 signature over an arbitrary message, created with the spending key of a
/// Sapling payment address.
///
/// All signatures for a specific payment address are trivially linkable, as their first
/// 32 bytes will be identical.
///
/// A signature is bound to a specific diversified address of the spending key. Signatures
/// for different diversified addresses of the same spending key are unlinkable.
pub struct Signature {
    nullifier: [u8; 32],
    rk: PublicKey<Bls12>,
    zkproof: Proof<Bls12>,
    spend_auth_sig: redjubjub::Signature,
}

impl Signature {
    pub fn from_bytes(bytes: &[u8; 320], params: &JubjubBls12) -> Option<Self> {
        let mut nullifier = [0; 32];
        nullifier.copy_from_slice(&bytes[0..32]);

        let rk = match PublicKey::<Bls12>::read(&bytes[32..64], params) {
            Ok(p) => p,
            Err(_) => return None,
        };
        if is_small_order(&rk.0, params) {
            return None;
        }

        let zkproof = Proof::read(&bytes[64..256]).unwrap();

        let spend_auth_sig = match redjubjub::Signature::read(&bytes[256..320]) {
            Ok(sig) => sig,
            Err(_) => return None,
        };

        Some(Signature {
            nullifier,
            rk,
            zkproof,
            spend_auth_sig,
        })
    }

    pub fn to_bytes(&self) -> [u8; 320] {
        let mut bytes = [0; 320];
        bytes[0..32].copy_from_slice(&self.nullifier);
        self.rk.write(&mut bytes[32..64]).unwrap();
        self.zkproof.write(&mut bytes[64..256]).unwrap();
        self.spend_auth_sig.write(&mut bytes[256..320]).unwrap();
        bytes
    }
}

/// Signs an arbitrary message for the given [`PaymentAddress`] and [`SLIP 44`] coin type.
///
/// The coin type is used here in its index form, not its hardened form (i.e. 133 for
/// mainnet Zcash).
///
/// [`SLIP 44`]: https://github.com/satoshilabs/slips/blob/master/slip-0044.md
pub fn sign_message(
    expsk: ExpandedSpendingKey<Bls12>,
    payment_address: PaymentAddress<Bls12>,
    coin_type: u32,
    message: &str,
    proving_key: &Parameters<Bls12>,
    params: &JubjubBls12,
) -> Signature {
    // Initialize secure RNG
    let mut rng = OsRng;

    // We sign a fake note with value of 1 zatoshi, setting rcm and rcv to zero
    let value = 1;
    let rcm = Fs::zero();
    let rcv = Fs::zero();

    // Create the fake note
    let note = Note {
        value,
        g_d: payment_address
            .g_d(params)
            .expect("was a valid diversifier before"),
        pk_d: payment_address.pk_d.clone(),
        r: rcm,
    };

    // Create a fake tree containing the fake note, and witness it
    let (anchor, witness) = {
        let mut tree = CommitmentTree::new();
        tree.append(Node::new(note.cm(params).into())).unwrap();
        (
            tree.root(),
            IncrementalWitness::from_tree(&tree).path().unwrap(),
        )
    };

    // Construct the value commitment
    let value_commitment = ValueCommitment::<Bls12> {
        value,
        randomness: rcv,
    };

    // Re-randomize the payment address
    let proof_generation_key = expsk.proof_generation_key(params);
    let alpha = Fs::random(&mut rng);
    let rk = PublicKey::<Bls12>(proof_generation_key.ak.clone().into()).randomize(
        alpha,
        FixedGenerators::SpendingKeyGenerator,
        params,
    );

    // Derive the nullifier for the fake note
    let ivk = proof_generation_key.into_viewing_key(params);
    let nullifier = {
        let mut nf = [0; 32];
        nf.copy_from_slice(&note.nf(&ivk, witness.position, params));
        nf
    };

    // We now have the full witness for our circuit
    let instance = Spend {
        params,
        value_commitment: Some(value_commitment),
        proof_generation_key: Some(proof_generation_key),
        payment_address: Some(payment_address),
        commitment_randomness: Some(rcm),
        ar: Some(alpha),
        auth_path: witness
            .auth_path
            .iter()
            .map(|n| n.map(|(node, b)| (node.into(), b)))
            .collect(),
        anchor: Some(anchor.into()),
    };

    // Create the proof
    let zkproof =
        create_random_proof(instance, proving_key, &mut rng).expect("proving should not fail");

    // Create the signature
    let mut personal = [0; 16];
    personal[..12].copy_from_slice(ZIP304_PERSONALIZATION_PREFIX);
    personal[12..].copy_from_slice(&coin_type.to_le_bytes());
    let mut sighash = [0; 32];
    sighash.copy_from_slice(
        blake2b_simd::Params::new()
            .hash_length(32)
            .personal(&personal)
            .to_state()
            .update(message.as_bytes())
            .finalize()
            .as_ref(),
    );
    let spend_auth_sig = spend_sig(PrivateKey(expsk.ask), alpha, &sighash, &mut rng, params);

    Signature {
        nullifier,
        rk,
        zkproof,
        spend_auth_sig,
    }
}

/// Verifies a [`Signature`] on a message with the given [`PaymentAddress`]  and
/// [`SLIP 44`] coin type.
///
/// The coin type is used here in its index form, not its hardened form (i.e. 133 for
/// mainnet Zcash).
///
/// [`SLIP 44`]: https://github.com/satoshilabs/slips/blob/master/slip-0044.md
pub fn verify_message(
    payment_address: &PaymentAddress<Bls12>,
    coin_type: u32,
    message: &str,
    signature: &Signature,
    verifying_key: &PreparedVerifyingKey<Bls12>,
    params: &JubjubBls12,
) -> Result<(), ()> {
    // We signed a fake note with value of 1 zatoshi, setting rcm and rcv to zero
    let value = 1;
    let rcm = Fs::zero();
    let rcv = Fs::zero();

    // Recreate the fake note
    let note = Note {
        value,
        g_d: payment_address
            .g_d(params)
            .expect("was a valid diversifier before"),
        pk_d: payment_address.pk_d.clone(),
        r: rcm,
    };

    // Recreate the fake tree containing the fake note
    let anchor = {
        let mut tree = CommitmentTree::new();
        tree.append(Node::new(note.cm(params).into())).unwrap();
        tree.root()
    };

    // Reconstruct the value commitment
    let cv: edwards::Point<Bls12, Unknown> = ValueCommitment::<Bls12> {
        value,
        randomness: rcv,
    }
    .cm(params)
    .into();

    // Grab the nullifier as a sequence of bytes
    let nullifier = &signature.nullifier[..];

    // Compute the signature's message for rk/spend_auth_sig
    let mut personal = [0; 16];
    personal[..12].copy_from_slice(ZIP304_PERSONALIZATION_PREFIX);
    personal[12..].copy_from_slice(&coin_type.to_le_bytes());
    let sighash = blake2b_simd::Params::new()
        .hash_length(32)
        .personal(&personal)
        .to_state()
        .update(message.as_bytes())
        .finalize();
    let mut data_to_be_signed = [0u8; 64];
    signature
        .rk
        .0
        .write(&mut data_to_be_signed[0..32])
        .expect("message buffer should be 32 bytes");
    data_to_be_signed[32..64].copy_from_slice(sighash.as_ref());

    // Verify the spend_auth_sig
    if !signature.rk.verify(
        &data_to_be_signed,
        &signature.spend_auth_sig,
        FixedGenerators::SpendingKeyGenerator,
        params,
    ) {
        return Err(());
    }

    // Construct public input for circuit
    let mut public_input = [Fr::zero(); 7];
    {
        let (x, y) = signature.rk.0.into_xy();
        public_input[0] = x;
        public_input[1] = y;
    }
    {
        let (x, y) = cv.into_xy();
        public_input[2] = x;
        public_input[3] = y;
    }
    public_input[4] = anchor.into();

    // Add the nullifier through multiscalar packing
    {
        let nullifier = multipack::bytes_to_bits_le(nullifier);
        let nullifier = multipack::compute_multipacking::<Bls12>(&nullifier);

        assert_eq!(nullifier.len(), 2);

        public_input[5] = nullifier[0];
        public_input[6] = nullifier[1];
    }

    // Verify the proof
    match verify_proof(verifying_key, &signature.zkproof, &public_input[..]) {
        // No error, and proof verification successful
        Ok(true) => Ok(()),

        // Any other case
        _ => Err(()),
    }
}

#[cfg(test)]
mod tests {
    use zcash_primitives::{
        jubjub::JubjubBls12, keys::ExpandedSpendingKey, primitives::Diversifier, JUBJUB,
    };

    use super::{sign_message, verify_message};
    use crate::prover::LocalTxProver;

    #[test]
    fn test_signatures() {
        let local_prover = LocalTxProver::with_default_location().unwrap();
        let spend_params = local_prover.spend_params();
        let spend_vk = local_prover.spend_vk();
        let params: &JubjubBls12 = &JUBJUB;

        let expsk = ExpandedSpendingKey::from_spending_key(&[42; 32][..]);
        let addr = {
            let diversifier = Diversifier([0; 11]);
            expsk
                .proof_generation_key(params)
                .into_viewing_key(params)
                .into_payment_address(diversifier, params)
                .unwrap()
        };

        let msg1 = "Foo bar";
        let msg2 = "Spam eggs";

        let sig1 = sign_message(expsk.clone(), addr.clone(), 1, msg1, spend_params, params);
        let sig2 = sign_message(expsk.clone(), addr.clone(), 1, msg2, spend_params, params);

        // The signatures are bound to the specific message they were created over
        assert!(verify_message(&addr, 1, msg1, &sig1, spend_vk, params).is_ok());
        assert!(verify_message(&addr, 1, msg2, &sig2, spend_vk, params).is_ok());
        assert!(verify_message(&addr, 1, msg1, &sig2, spend_vk, params).is_err());
        assert!(verify_message(&addr, 1, msg2, &sig1, spend_vk, params).is_err());

        // ... and the signatures are unique but trivially linkable by the nullifier
        assert_ne!(&sig1.to_bytes()[..], &sig2.to_bytes()[..]);
        assert_eq!(sig1.nullifier, sig2.nullifier);

        // Generate a signature with a diversified address
        let addr_b = {
            let diversifier = Diversifier([5; 11]);
            expsk
                .proof_generation_key(params)
                .into_viewing_key(params)
                .into_payment_address(diversifier, params)
                .unwrap()
        };
        let sig1_b = sign_message(expsk.clone(), addr_b.clone(), 1, msg1, spend_params, params);

        // The signatures are bound to the specific address they were created with
        assert!(verify_message(&addr_b, 1, msg1, &sig1_b, spend_vk, params).is_ok());
        assert!(verify_message(&addr_b, 1, msg1, &sig1, spend_vk, params).is_err());
        assert!(verify_message(&addr, 1, msg1, &sig1_b, spend_vk, params).is_err());

        // ... and the signatures are unlinkable
        assert_ne!(&sig1.to_bytes()[..], &sig1_b.to_bytes()[..]);
        assert_ne!(sig1.nullifier, sig1_b.nullifier);
    }
}
