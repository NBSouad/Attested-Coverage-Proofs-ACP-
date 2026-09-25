//! Integrated ACP coverage protocol.
//!
//! Ties together the two evidence sources of the ACP primitive:
//!
//! * the **prover's hiding commitment** `C_Sigma` to its private inventory
//!   (a Poseidon2 sparse Merkle tree, [`acp_smt`]); and
//! * the **externally-attested absence oracle** (a regulator-signed registry,
//!   [`acp_absence`]),
//!
//! mediated by a beacon-derived challenge so the prover cannot adapt its
//! inventory to the sampled identifiers. For each of the `q` sampled
//! identifiers the prover supplies *either* an inclusion proof against
//! `C_Sigma` *or* a registry absence witness; the verifier accepts iff every
//! sample is covered, and learns the per-sample deployment bit vector `b_S`.
//!
//! This module is the protocol logic and is deliberately transparent (no zero
//! knowledge): it is the executable specification against which the in-circuit
//! STARK (which hides the inclusion paths) is measured. It also lets us
//! *empirically* exhibit coverage soundness: a prover that conceals a deployed
//! identifier cannot cover a sample that lands on it, because the registry
//! refuses an absence witness for a deployed identifier.

use acp_absence::{verify_absence, AbsenceWitness, SignedRegistry};
use acp_smt::{verify as smt_verify, AcpHasher, CoverageProof as PathProof, Digest, SparseMerkleTree, F};
use p3_field::PrimeField64;

/// Domain-separation tag for beacon-derived sampling.
pub const SAMPLE_CTX: &[u8] = b"ACP/sample/v1";

/// A public namespace: the ordered list of identifiers the sampler draws from.
pub struct Namespace {
    pub ids: Vec<Vec<u8>>,
}

impl Namespace {
    pub fn len(&self) -> usize {
        self.ids.len()
    }
    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }
}

/// Derive the `q` sampled namespace indices from a public beacon seed.
///
/// Index `j` is `H(SAMPLE_CTX || seed || j) mod |namespace|`, i.e. i.i.d.\
/// uniform draws fixed by the beacon and independent of the commitment.
pub fn sample_indices(seed: &[u8], q: usize, ns_size: usize) -> Vec<usize> {
    assert!(ns_size > 0);
    let h = AcpHasher::new();
    (0..q)
        .map(|j| {
            let mut msg = Vec::with_capacity(SAMPLE_CTX.len() + seed.len() + 8);
            msg.extend_from_slice(SAMPLE_CTX);
            msg.extend_from_slice(seed);
            msg.extend_from_slice(&(j as u64).to_le_bytes());
            (h.id_digest(&msg)[0].as_canonical_u64() % ns_size as u64) as usize
        })
        .collect()
}

/// A per-sample coverage witness: the prover proves inclusion or absence.
pub enum SampleWitness {
    /// The sampled identifier is in the committed inventory `C_Sigma`.
    Inclusion(PathProof),
    /// The sampled identifier is certified absent by the registry.
    Absence(AbsenceWitness),
}

/// The ACP prover: holds the private inventory commitment.
pub struct Prover {
    sigma: SparseMerkleTree,
    depth: usize,
}

impl Prover {
    /// Commit to the disclosed inventory (the identifiers the prover reports as
    /// deployed). Returns the prover and the public commitment `C_Sigma`.
    pub fn commit(disclosed: &[Vec<u8>], depth: usize) -> (Self, Digest) {
        let entries: Vec<(Vec<u8>, Vec<F>)> =
            disclosed.iter().map(|id| (id.clone(), Vec::new())).collect();
        let sigma = SparseMerkleTree::build(depth, &entries);
        let root = sigma.root();
        (Self { sigma, depth }, root)
    }

    /// Produce coverage witnesses for the sampled identifiers.
    ///
    /// For each sample: an inclusion proof if it is in `C_Sigma`; otherwise a
    /// registry absence witness if one exists. If neither is possible (the
    /// identifier is deployed-but-concealed: not in `C_Sigma`, and the registry
    /// will not certify its absence), the prover can only submit a doomed
    /// proof, which the verifier rejects --- this is coverage soundness in
    /// action.
    pub fn cover(&self, registry: &SignedRegistry, samples: &[Vec<u8>]) -> Vec<SampleWitness> {
        samples
            .iter()
            .map(|id| {
                if self.sigma.contains(id) {
                    SampleWitness::Inclusion(self.sigma.prove(id))
                } else if let Some(w) = registry.absence_witness(id) {
                    SampleWitness::Absence(w)
                } else {
                    // Deployed-but-concealed: no honest witness exists.
                    // `sigma.prove(id)` is an Absence-kind path, which fails the
                    // verifier's inclusion check (kind mismatch).
                    SampleWitness::Inclusion(self.sigma.prove(id))
                }
            })
            .collect()
    }

    pub fn depth(&self) -> usize {
        self.depth
    }

    /// Number of disclosed inventory leaves.
    pub fn inventory_size(&self) -> usize {
        self.sigma.len()
    }
}

/// Outcome of verification: acceptance and the leaked deployment-bit vector.
pub struct VerifyResult {
    pub accept: bool,
    /// `b_S[j]` = the prover's claimed deployment bit for sample `j`
    /// (`true` = inclusion branch, `false` = absence branch).
    pub b_s: Vec<bool>,
    /// Index of the first sample whose witness failed, if any.
    pub first_failure: Option<usize>,
}

/// Verify an ACP coverage proof.
///
/// Recomputes the sampled identifiers from the public beacon seed, then checks
/// each sample's witness against the public commitment `c_sigma` (inclusion) or
/// the public signed registry (absence). Accepts iff every sample is covered.
pub fn verify(
    c_sigma: Digest,
    registry: &SignedRegistry,
    depth: usize,
    seed: &[u8],
    ns: &Namespace,
    witnesses: &[SampleWitness],
) -> VerifyResult {
    let q = witnesses.len();
    let idxs = sample_indices(seed, q, ns.len());
    let (reg_root, _) = registry.signed_root();
    let pk = registry.public_key();

    let mut accept = true;
    let mut b_s = Vec::with_capacity(q);
    let mut first_failure = None;

    for (k, w) in witnesses.iter().enumerate() {
        let id = &ns.ids[idxs[k]];
        let ok = match w {
            SampleWitness::Inclusion(p) => {
                b_s.push(true);
                matches!(p, PathProof::Inclusion { .. }) && smt_verify(c_sigma, depth, id, p, true)
            }
            SampleWitness::Absence(aw) => {
                b_s.push(false);
                aw.root == reg_root && verify_absence(pk, id, depth, aw)
            }
        };
        if !ok && first_failure.is_none() {
            first_failure = Some(k);
        }
        accept &= ok;
    }

    VerifyResult { accept, b_s, first_failure }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DEPTH: usize = 48;

    /// Build a namespace of `deployed` deployed identifiers followed by
    /// `undeployed` undeployed ones.
    fn make_world(deployed: usize, undeployed: usize) -> (Vec<Vec<u8>>, Namespace) {
        let dep: Vec<Vec<u8>> = (0..deployed)
            .map(|i| format!("deployed-{i}.svc.example.gov").into_bytes())
            .collect();
        let und: Vec<Vec<u8>> = (0..undeployed)
            .map(|i| format!("undeployed-{i}.svc.example.gov").into_bytes())
            .collect();
        let mut ids = dep.clone();
        ids.extend(und);
        (dep, Namespace { ids })
    }

    #[test]
    fn honest_prover_is_accepted_and_bs_is_correct() {
        let (deployed, ns) = make_world(1000, 1000);
        // Honest: discloses exactly the deployed set; registry commits the same.
        let (prover, c_sigma) = Prover::commit(&deployed, DEPTH);
        let registry = SignedRegistry::build(&deployed, DEPTH);

        let seed = b"epoch-2026-Q2-beacon";
        let q = 100;
        let idxs = sample_indices(seed, q, ns.len());
        let samples: Vec<Vec<u8>> = idxs.iter().map(|&i| ns.ids[i].clone()).collect();

        let wits = prover.cover(&registry, &samples);
        let res = verify(c_sigma, &registry, DEPTH, seed, &ns, &wits);
        assert!(res.accept, "honest prover must be accepted");
        // b_S must match true membership in the deployed set (first 1000 ids).
        for (k, &idx) in idxs.iter().enumerate() {
            let truly_deployed = idx < 1000;
            assert_eq!(res.b_s[k], truly_deployed, "b_S mismatch at sample {k}");
        }
    }

    #[test]
    fn concealing_prover_is_rejected() {
        // Authoritative deployed set of 1000; the registry commits all of it.
        let (deployed, ns) = make_world(1000, 1000);
        let registry = SignedRegistry::build(&deployed, DEPTH);

        // Malicious prover conceals 500 deployed identifiers (omits them from
        // C_Sigma). The registry still attests they are deployed, so no absence
        // witness exists for them.
        let disclosed: Vec<Vec<u8>> = deployed[..500].to_vec();
        let (prover, c_sigma) = Prover::commit(&disclosed, DEPTH);

        let seed = b"epoch-2026-Q2-beacon";
        let q = 100;
        let idxs = sample_indices(seed, q, ns.len());
        let samples: Vec<Vec<u8>> = idxs.iter().map(|&i| ns.ids[i].clone()).collect();

        // Sanity: with 500/2000 = 25% of the namespace concealed and q=100,
        // a sample lands on a concealed identifier except with probability
        // 0.75^100 ~= 3e-13. Confirm at least one concealed id is sampled.
        let concealed_hit = idxs
            .iter()
            .any(|&i| i >= 500 && i < 1000); // deployed-but-not-disclosed
        assert!(concealed_hit, "test seed should sample a concealed id");

        let wits = prover.cover(&registry, &samples);
        let res = verify(c_sigma, &registry, DEPTH, seed, &ns, &wits);
        assert!(!res.accept, "concealing prover must be rejected");
        assert!(res.first_failure.is_some());
    }

    #[test]
    fn commit_before_beacon_cannot_be_evaded() {
        // Even if the prover knows the seed, it cannot cover a concealed id:
        // the absence oracle is the binding constraint, not the challenge.
        let (deployed, _ns) = make_world(200, 200);
        let registry = SignedRegistry::build(&deployed, DEPTH);
        let disclosed: Vec<Vec<u8>> = deployed[..100].to_vec();
        let (prover, c_sigma) = Prover::commit(&disclosed, DEPTH);

        // Directly sample a known concealed identifier.
        let concealed = &deployed[150]; // deployed, not disclosed
        let wits = prover.cover(&registry, std::slice::from_ref(concealed));
        // Construct a one-sample namespace/seed that selects index 0.
        let ns1 = Namespace { ids: vec![concealed.clone()] };
        let res = verify(c_sigma, &registry, DEPTH, b"x", &ns1, &wits);
        assert!(!res.accept, "concealed identifier must not be coverable");
    }
}
