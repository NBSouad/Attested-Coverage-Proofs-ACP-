//! Signed-registry absence oracle (the cleanest ACP absence-witness
//! instantiation, where the registry authoritatively defines the namespace).
//!
//! A regulator-operated registry maintains the authoritative set of deployed
//! identifiers, commits it in a Poseidon2 sparse Merkle tree, and signs the root
//! with a post-quantum signature (ML-DSA-65). An **absence witness** for a
//! sampled identifier `a` is the registry's signed root together with a
//! non-membership proof of `a` in the registry tree; it certifies that `a` is
//! genuinely not deployed (assumption A10, reducing to EUF-CMA of the registry
//! signature plus Poseidon2 collision resistance).
//!
//! The registry root and signature are public and shared across all `q` samples
//! in an epoch, so verifying `q` absence witnesses costs **one** signature
//! verification plus `q` Poseidon2 non-membership checks. (Verifying the
//! registry signature *inside* the proof circuit is only required for the
//! blind-ACP variant that hides which samples took the absence branch; that is
//! deferred. Here the public root/signature are checked out of circuit.)

use acp_smt::{verify as smt_verify, CoverageProof, Digest, SparseMerkleTree, DIGEST_ELEMS, F};
use fips204::ml_dsa_65;
use fips204::traits::{Signer, Verifier};
use p3_field::PrimeField64;

/// Domain-separation context for the registry-root signature.
pub const REGISTRY_CTX: &[u8] = b"ACP/signed-registry-root/v1";

/// Serialize a digest to bytes (little-endian canonical field elements).
pub fn digest_to_bytes(d: &Digest) -> [u8; DIGEST_ELEMS * 8] {
    let mut out = [0u8; DIGEST_ELEMS * 8];
    for (i, e) in d.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&e.as_canonical_u64().to_le_bytes());
    }
    out
}

/// A registry-issued absence witness for a single identifier.
#[derive(Clone)]
pub struct AbsenceWitness {
    /// The registry's committed root (the signed message).
    pub root: Digest,
    /// The registry's ML-DSA signature over the root.
    pub sig: [u8; ml_dsa_65::SIG_LEN],
    /// Non-membership proof of the identifier against `root`.
    pub nonmembership: CoverageProof,
}

/// A mock regulator-operated signed registry.
pub struct SignedRegistry {
    depth: usize,
    smt: SparseMerkleTree,
    pk: ml_dsa_65::PublicKey,
    sk: ml_dsa_65::PrivateKey,
    root: Digest,
    sig: [u8; ml_dsa_65::SIG_LEN],
}

impl SignedRegistry {
    /// Build a registry over the authoritative set of deployed identifiers,
    /// committing it in a depth-`depth` SMT and signing the root with ML-DSA-65.
    pub fn build(deployed: &[Vec<u8>], depth: usize) -> Self {
        let entries: Vec<(Vec<u8>, Vec<F>)> =
            deployed.iter().map(|id| (id.clone(), Vec::new())).collect();
        let smt = SparseMerkleTree::build(depth, &entries);
        let root = smt.root();

        let (pk, sk) = ml_dsa_65::try_keygen().expect("ML-DSA keygen");
        let sig = sk
            .try_sign(&digest_to_bytes(&root), REGISTRY_CTX)
            .expect("ML-DSA sign");

        Self { depth, smt, pk, sk, root, sig }
    }

    /// The registry's public key (published).
    pub fn public_key(&self) -> &ml_dsa_65::PublicKey {
        &self.pk
    }

    /// The signed root: `(root, signature)`, published once per epoch.
    pub fn signed_root(&self) -> (Digest, [u8; ml_dsa_65::SIG_LEN]) {
        (self.root, self.sig)
    }

    /// Whether an identifier is registered as deployed.
    pub fn is_deployed(&self, id: &[u8]) -> bool {
        self.smt.contains(id)
    }

    /// Issue an absence witness for `id`, or `None` if `id` is in fact deployed
    /// (in which case no honest absence witness exists).
    pub fn absence_witness(&self, id: &[u8]) -> Option<AbsenceWitness> {
        if self.smt.contains(id) {
            return None;
        }
        match self.smt.prove(id) {
            p @ CoverageProof::Absence { .. } => Some(AbsenceWitness {
                root: self.root,
                sig: self.sig,
                nonmembership: p,
            }),
            _ => None,
        }
    }

    /// Re-sign the current root (for benchmarking signing cost).
    pub fn sign_root(&self) -> [u8; ml_dsa_65::SIG_LEN] {
        self.sk
            .try_sign(&digest_to_bytes(&self.root), REGISTRY_CTX)
            .expect("ML-DSA sign")
    }

    pub fn depth(&self) -> usize {
        self.depth
    }
}

/// Verify an absence witness for `id` under the registry public key.
///
/// Checks (1) the ML-DSA signature on the committed root, and (2) the Poseidon2
/// non-membership proof of `id` against that root. Returns `true` iff both hold.
pub fn verify_absence(
    pk: &ml_dsa_65::PublicKey,
    id: &[u8],
    depth: usize,
    w: &AbsenceWitness,
) -> bool {
    // (1) The registry actually signed this root.
    if !pk.verify(&digest_to_bytes(&w.root), &w.sig, REGISTRY_CTX) {
        return false;
    }
    // (2) `id` is genuinely absent from the signed registry tree.
    matches!(w.nonmembership, CoverageProof::Absence { .. })
        && smt_verify(w.root, depth, id, &w.nonmembership, false)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn deployed_set(n: usize) -> Vec<Vec<u8>> {
        (0..n)
            .map(|i| format!("deployed-{i}.svc.example.gov").into_bytes())
            .collect()
    }

    #[test]
    fn absent_identifier_verifies() {
        let reg = SignedRegistry::build(&deployed_set(500), 48);
        for i in 0..50 {
            let id = format!("not-deployed-{i}.svc.example.gov").into_bytes();
            assert!(!reg.is_deployed(&id));
            let w = reg.absence_witness(&id).expect("witness for absent id");
            assert!(verify_absence(reg.public_key(), &id, reg.depth(), &w), "absence must verify");
        }
    }

    #[test]
    fn deployed_identifier_has_no_witness() {
        let set = deployed_set(500);
        let reg = SignedRegistry::build(&set, 48);
        assert!(reg.is_deployed(&set[3]));
        assert!(reg.absence_witness(&set[3]).is_none());
    }

    #[test]
    fn tampered_signature_rejected() {
        let reg = SignedRegistry::build(&deployed_set(200), 48);
        let id = b"x-not-deployed.svc.example.gov".to_vec();
        let mut w = reg.absence_witness(&id).unwrap();
        w.sig[0] ^= 0x01;
        assert!(!verify_absence(reg.public_key(), &id, reg.depth(), &w));
    }

    #[test]
    fn tampered_root_rejected() {
        let reg = SignedRegistry::build(&deployed_set(200), 48);
        let pk = reg.public_key().clone();
        let id = b"y-not-deployed.svc.example.gov".to_vec();
        let mut w = reg.absence_witness(&id).unwrap();
        // Changing the root breaks the signature binding.
        w.root = acp_smt::empty_leaf();
        assert!(!verify_absence(&pk, &id, reg.depth(), &w));
    }

    #[test]
    fn wrong_key_rejected() {
        let reg = SignedRegistry::build(&deployed_set(200), 48);
        let other = SignedRegistry::build(&deployed_set(10), 48);
        let id = b"z-not-deployed.svc.example.gov".to_vec();
        let w = reg.absence_witness(&id).unwrap();
        // A different registry's key must not validate this witness.
        assert!(!verify_absence(other.public_key(), &id, reg.depth(), &w));
    }
}
