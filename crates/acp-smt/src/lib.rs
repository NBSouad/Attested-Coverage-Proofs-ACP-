//! Poseidon2-over-Goldilocks sparse Merkle tree (SMT) with inclusion and
//! non-membership proofs.
//!
//! This is the out-of-circuit witness layer of the ACP construction: it
//! produces the Merkle commitment `C_Sigma` to a private inventory and the
//! inclusion / absence witnesses that the in-circuit relation later checks.
//!
//! # Design
//!
//! * Full-depth sparse Merkle tree of depth `D` (the key-bit length).
//! * Each identifier `id` is mapped to a `D`-bit path by hashing it with
//!   Poseidon2 and taking the top `D` bits of the first digest element.
//! * A *present* key stores a leaf `H_in(id_digest || value)`; an *absent*
//!   key's leaf is the canonical empty leaf `[0,0,0,0]`.
//! * **Inclusion** of `id` = a Merkle path proving the leaf at `id`'s path is
//!   the present leaf.
//! * **Non-membership** of `id` = a Merkle path proving the leaf at `id`'s path
//!   is the empty leaf. Sound because a present leaf
//!   `H_in(id_digest || value)` equals `[0,0,0,0]` only with negligible
//!   probability.
//!
//! `H_in` is Poseidon2 over Goldilocks (width 8):
//! * leaf hashing via a padding-free sponge (rate 4, out 4);
//! * 2-to-1 compression via a truncated permutation.

use std::collections::{HashMap, HashSet};

use p3_field::integers::QuotientMap;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_goldilocks::{default_goldilocks_poseidon2_8, Goldilocks, Poseidon2Goldilocks};
use p3_symmetric::{CryptographicHasher, PaddingFreeSponge, PseudoCompressionFunction,
                   TruncatedPermutation};

/// Base field: Goldilocks, `p = 2^64 - 2^32 + 1`.
pub type F = Goldilocks;

/// Number of field elements in a digest (~256-bit space).
pub const DIGEST_ELEMS: usize = 4;

/// A Merkle digest: four Goldilocks elements.
pub type Digest = [F; DIGEST_ELEMS];

/// Width-8 Poseidon2 permutation over Goldilocks.
type Perm = Poseidon2Goldilocks<8>;
/// Leaf hasher: padding-free sponge, width 8, rate 4, out 4.
type LeafHasher = PaddingFreeSponge<Perm, 8, 4, DIGEST_ELEMS>;
/// 2-to-1 compression: truncated permutation, 2 inputs of 4 elems, width 8.
type Compressor = TruncatedPermutation<Perm, 2, DIGEST_ELEMS, 8>;

/// Maximum supported tree depth (paths are stored in a `u64`).
pub const MAX_DEPTH: usize = 64;

/// The canonical empty leaf.
pub const fn empty_leaf() -> Digest {
    [F::ZERO; DIGEST_ELEMS]
}

/// Poseidon2-Goldilocks hashing context (`H_in`).
///
/// Holds an instantiated permutation; cheap to clone. Constructed
/// deterministically, so a verifier can build an identical one.
#[derive(Clone)]
pub struct AcpHasher {
    leaf: LeafHasher,
    compress: Compressor,
}

impl Default for AcpHasher {
    fn default() -> Self {
        Self::new()
    }
}

impl AcpHasher {
    /// Build the hashing context with Plonky3's default Goldilocks constants.
    pub fn new() -> Self {
        let perm = default_goldilocks_poseidon2_8();
        Self {
            leaf: LeafHasher::new(perm.clone()),
            compress: Compressor::new(perm),
        }
    }

    /// Hash an arbitrary byte string to a digest, packing 7 bytes per field
    /// element (56 bits < log2 p, hence always canonical).
    pub fn hash_bytes(&self, bytes: &[u8]) -> Digest {
        let mut felts = Vec::with_capacity(bytes.len() / 7 + 1);
        for chunk in bytes.chunks(7) {
            let mut acc: u64 = 0;
            for (i, &b) in chunk.iter().enumerate() {
                acc |= (b as u64) << (8 * i);
            }
            felts.push(F::from_int(acc));
        }
        // Bind the length to defeat trivial padding collisions.
        felts.push(F::from_int(bytes.len() as u64));
        self.leaf.hash_iter(felts)
    }

    /// Hash an identifier (its full digest is bound into present leaves).
    pub fn id_digest(&self, id: &[u8]) -> Digest {
        self.hash_bytes(id)
    }

    /// Derive the `depth`-bit tree path for an identifier from its digest.
    pub fn path_of(&self, id: &[u8], depth: usize) -> u64 {
        assert!(depth >= 1 && depth <= MAX_DEPTH, "depth out of range");
        let h0 = self.id_digest(id)[0].as_canonical_u64();
        if depth == 64 {
            h0
        } else {
            // Take the top `depth` bits of the 64-bit digest element.
            h0 >> (64 - depth)
        }
    }

    /// Compute a present leaf digest, binding the identifier to its value.
    pub fn leaf_digest(&self, id: &[u8], value: &[F]) -> Digest {
        let idd = self.id_digest(id);
        let mut input = Vec::with_capacity(DIGEST_ELEMS + value.len());
        input.extend_from_slice(&idd);
        input.extend_from_slice(value);
        self.leaf.hash_iter(input)
    }

    /// 2-to-1 node compression.
    #[inline]
    pub fn compress(&self, left: Digest, right: Digest) -> Digest {
        self.compress.compress([left, right])
    }
}

/// A Merkle authentication path from a leaf to the root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath {
    /// Sibling digest at each level `0..depth` (level 0 = leaf's sibling).
    pub siblings: Vec<Digest>,
}

/// A coverage witness for a single sampled identifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoverageProof {
    /// The identifier is present; carries its committed value and the path.
    ///
    /// The leaf is **derived** by the verifier as `H_in(id_digest(id) || value)`
    /// rather than supplied by the prover. Carrying the leaf directly would
    /// bind the path to the identifier only through the `depth`-bit path index:
    /// a prover could grind a junk string `x` with `path_of(x) = path_of(a)`,
    /// insert `x` into its tree, and answer a query on `a` with `x`'s path.
    /// Deriving the leaf raises that binding to the full digest.
    Inclusion { value: Vec<F>, path: MerklePath },
    /// The identifier is absent; the leaf is the empty leaf.
    Absence { path: MerklePath },
}

/// A sparse Merkle tree over a fixed-depth identifier namespace.
pub struct SparseMerkleTree {
    depth: usize,
    hasher: AcpHasher,
    /// Precomputed empty-subtree digests, `empty[h]` = digest of an empty
    /// subtree of height `h`. `empty[0]` = empty leaf, `empty[depth]` = empty root.
    empty: Vec<Digest>,
    /// Materialized nodes keyed by `(height, prefix)`. Absent entries take the
    /// corresponding `empty[height]` value.
    nodes: HashMap<(usize, u64), Digest>,
    /// Occupied leaf paths (for proof-of-membership bookkeeping).
    occupied: HashSet<u64>,
    /// Committed value at each occupied path, needed so that an inclusion
    /// proof can carry the value and let the verifier re-derive the leaf.
    values: HashMap<u64, Vec<F>>,
}

impl SparseMerkleTree {
    /// Build a tree of the given depth from `(identifier, value)` entries.
    ///
    /// Panics if two distinct identifiers collide on the same `depth`-bit path
    /// (a negligible-probability event; surfaced loudly for the prototype).
    pub fn build(depth: usize, entries: &[(Vec<u8>, Vec<F>)]) -> Self {
        assert!(depth >= 1 && depth <= MAX_DEPTH, "depth out of range");
        let hasher = AcpHasher::new();

        // Precompute empty-subtree digests.
        let mut empty = Vec::with_capacity(depth + 1);
        empty.push(empty_leaf());
        for h in 1..=depth {
            let e = empty[h - 1];
            empty.push(hasher.compress(e, e));
        }

        let mut nodes: HashMap<(usize, u64), Digest> = HashMap::new();
        let mut occupied: HashSet<u64> = HashSet::new();
        let mut values: HashMap<u64, Vec<F>> = HashMap::new();

        // Insert leaves.
        for (id, value) in entries {
            let path = hasher.path_of(id, depth);
            assert!(
                occupied.insert(path),
                "path collision at depth {depth}; increase depth or change ids"
            );
            let leaf = hasher.leaf_digest(id, value);
            nodes.insert((0, path), leaf);
            values.insert(path, value.clone());
        }

        // Propagate upward. `frontier` holds materialized prefixes at height `h-1`.
        let mut frontier: HashSet<u64> = occupied.iter().copied().collect();
        for h in 1..=depth {
            let mut parents: HashSet<u64> = HashSet::with_capacity(frontier.len());
            for &p in &frontier {
                parents.insert(p >> 1);
            }
            for &par in &parents {
                let left = Self::get_node(&nodes, &empty, h - 1, par << 1);
                let right = Self::get_node(&nodes, &empty, h - 1, (par << 1) | 1);
                nodes.insert((h, par), hasher.compress(left, right));
            }
            frontier = parents;
        }

        Self { depth, hasher, empty, nodes, occupied, values }
    }

    #[inline]
    fn get_node(
        nodes: &HashMap<(usize, u64), Digest>,
        empty: &[Digest],
        height: usize,
        prefix: u64,
    ) -> Digest {
        nodes
            .get(&(height, prefix))
            .copied()
            .unwrap_or(empty[height])
    }

    /// The tree depth.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// Number of occupied leaves.
    pub fn len(&self) -> usize {
        self.occupied.len()
    }

    /// Whether the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.occupied.is_empty()
    }

    /// The Merkle root (the commitment `C_Sigma`).
    pub fn root(&self) -> Digest {
        Self::get_node(&self.nodes, &self.empty, self.depth, 0)
    }

    /// Borrow the hashing context (e.g. to derive paths consistently).
    pub fn hasher(&self) -> &AcpHasher {
        &self.hasher
    }

    /// Whether an identifier is a member.
    pub fn contains(&self, id: &[u8]) -> bool {
        let path = self.hasher.path_of(id, self.depth);
        self.occupied.contains(&path)
    }

    /// Collect the sibling path for a given leaf path.
    fn auth_path(&self, path: u64) -> MerklePath {
        let mut siblings = Vec::with_capacity(self.depth);
        for h in 0..self.depth {
            let sib_prefix = (path >> h) ^ 1;
            siblings.push(Self::get_node(&self.nodes, &self.empty, h, sib_prefix));
        }
        MerklePath { siblings }
    }

    /// Produce a coverage proof for `id`: an inclusion proof if present,
    /// otherwise a non-membership proof.
    pub fn prove(&self, id: &[u8]) -> CoverageProof {
        let path = self.hasher.path_of(id, self.depth);
        let auth = self.auth_path(path);
        if self.occupied.contains(&path) {
            let value = self.values.get(&path).cloned().unwrap_or_default();
            CoverageProof::Inclusion { value, path: auth }
        } else {
            CoverageProof::Absence { path: auth }
        }
    }
}

/// Recompute the root implied by a leaf, its `depth`-bit path, and a Merkle
/// path, then compare to `root`.
fn recompute_root(
    hasher: &AcpHasher,
    depth: usize,
    leaf: Digest,
    path_index: u64,
    auth: &MerklePath,
    root: Digest,
) -> bool {
    if auth.siblings.len() != depth {
        return false;
    }
    let mut cur = leaf;
    for (h, sib) in auth.siblings.iter().enumerate() {
        let bit = (path_index >> h) & 1;
        cur = if bit == 0 {
            hasher.compress(cur, *sib)
        } else {
            hasher.compress(*sib, cur)
        };
    }
    cur == root
}

/// Verify a coverage proof against a committed root, for a claimed kind.
///
/// `expect_member = true` requires an inclusion proof; `false` requires a
/// non-membership proof. Returns `true` iff the proof is well-formed and the
/// recomputed root matches. The verifier is stateless: it builds its own
/// deterministic hasher and derives the path from `id`.
pub fn verify(root: Digest, depth: usize, id: &[u8], proof: &CoverageProof, expect_member: bool) -> bool {
    let hasher = AcpHasher::new();
    let path_index = hasher.path_of(id, depth);
    match (proof, expect_member) {
        (CoverageProof::Inclusion { value, path }, true) => {
            // Derive the leaf from the *identifier*, so the path is bound to
            // `id` at full digest strength rather than through `path_index`
            // alone. This also makes the empty leaf unreachable, so no separate
            // non-emptiness check is required.
            let leaf = hasher.leaf_digest(id, value);
            recompute_root(&hasher, depth, leaf, path_index, path, root)
        }
        (CoverageProof::Absence { path }, false) => {
            recompute_root(&hasher, depth, empty_leaf(), path_index, path, root)
        }
        // Proof kind does not match the claimed membership.
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn val(x: u64) -> Vec<F> {
        vec![F::from_int(x), F::from_int(x.wrapping_mul(2654435761))]
    }

    fn sample_entries(n: usize) -> Vec<(Vec<u8>, Vec<F>)> {
        (0..n)
            .map(|i| (format!("crypto-asset-{i}").into_bytes(), val(i as u64 + 1)))
            .collect()
    }

    #[test]
    fn empty_tree_root_is_empty_subtree() {
        let t = SparseMerkleTree::build(32, &[]);
        assert!(t.is_empty());
        assert_eq!(t.root(), t.empty[32]);
    }

    #[test]
    fn inclusion_proof_verifies() {
        let entries = sample_entries(100);
        let t = SparseMerkleTree::build(48, &entries);
        let root = t.root();
        for (id, _) in &entries {
            assert!(t.contains(id));
            let proof = t.prove(id);
            assert!(matches!(proof, CoverageProof::Inclusion { .. }));
            assert!(verify(root, t.depth(), id, &proof, true), "inclusion must verify");
        }
    }

    #[test]
    fn absence_proof_verifies() {
        let entries = sample_entries(100);
        let t = SparseMerkleTree::build(48, &entries);
        let root = t.root();
        for i in 1000..1100 {
            let id = format!("absent-asset-{i}").into_bytes();
            assert!(!t.contains(&id));
            let proof = t.prove(&id);
            assert!(matches!(proof, CoverageProof::Absence { .. }));
            assert!(verify(root, t.depth(), &id, &proof, false), "absence must verify");
        }
    }

    #[test]
    fn membership_and_kind_must_match() {
        let entries = sample_entries(50);
        let t = SparseMerkleTree::build(40, &entries);
        let root = t.root();

        // A present id: inclusion proof, but verifying it as absence must fail.
        let present = &entries[7].0;
        let inc = t.prove(present);
        assert!(verify(root, t.depth(), present, &inc, true));
        assert!(!verify(root, t.depth(), present, &inc, false));

        // An absent id: absence proof, but verifying it as inclusion must fail.
        let absent = b"definitely-not-present".to_vec();
        let abs = t.prove(&absent);
        assert!(verify(root, t.depth(), &absent, &abs, false));
        assert!(!verify(root, t.depth(), &absent, &abs, true));
    }

    #[test]
    fn tampered_sibling_is_rejected() {
        let entries = sample_entries(64);
        let t = SparseMerkleTree::build(40, &entries);
        let root = t.root();
        let id = &entries[3].0;
        let mut proof = t.prove(id);
        if let CoverageProof::Inclusion { path, .. } = &mut proof {
            // Corrupt one sibling.
            path.siblings[2][0] += F::ONE;
        }
        assert!(!verify(root, t.depth(), id, &proof, true), "tampered path must fail");
    }

    #[test]
    fn tampered_value_is_rejected() {
        let entries = sample_entries(64);
        let t = SparseMerkleTree::build(40, &entries);
        let root = t.root();
        let id = &entries[9].0;
        let mut proof = t.prove(id);
        if let CoverageProof::Inclusion { value, .. } = &mut proof {
            value[0] += F::ONE;
        }
        assert!(!verify(root, t.depth(), id, &proof, true), "tampered value must fail");
    }

    #[test]
    fn wrong_root_is_rejected() {
        let entries = sample_entries(64);
        let t = SparseMerkleTree::build(40, &entries);
        let id = &entries[1].0;
        let proof = t.prove(id);
        let mut bad_root = t.root();
        bad_root[0] += F::ONE;
        assert!(!verify(bad_root, t.depth(), id, &proof, true));
    }

    #[test]
    fn build_is_deterministic() {
        let entries = sample_entries(200);
        let a = SparseMerkleTree::build(50, &entries);
        let b = SparseMerkleTree::build(50, &entries);
        assert_eq!(a.root(), b.root());
    }

    #[test]
    fn insertion_order_independent() {
        let mut entries = sample_entries(200);
        let a = SparseMerkleTree::build(50, &entries);
        entries.reverse();
        let b = SparseMerkleTree::build(50, &entries);
        assert_eq!(a.root(), b.root());
    }

    #[test]
    fn adding_a_member_changes_root() {
        let entries = sample_entries(100);
        let t1 = SparseMerkleTree::build(50, &entries);
        let mut more = entries.clone();
        more.push((b"new-asset".to_vec(), val(9999)));
        let t2 = SparseMerkleTree::build(50, &more);
        assert_ne!(t1.root(), t2.root());
    }

    #[test]
    fn derived_leaf_is_never_the_empty_leaf() {
        let entries = sample_entries(32);
        let t = SparseMerkleTree::build(40, &entries);
        for (id, v) in &entries {
            assert_ne!(t.hasher().leaf_digest(id, v), empty_leaf());
        }
    }

    #[test]
    fn planted_collision_cannot_impersonate_an_identifier() {
        // The attack the derived leaf defends against. A prover that wants to
        // conceal `target` grinds a junk string sharing its `depth`-bit path,
        // inserts the junk string, and answers a query on `target` with the
        // junk string's inclusion path. Carrying the leaf in the proof would
        // make this succeed, binding the path to only `depth` bits; deriving
        // the leaf from the queried identifier defeats it.
        //
        // A shallow tree keeps the grind cheap enough for a unit test; the
        // attack is identical at depth 48, costing 2^48 hashes per asset.
        const SHALLOW: usize = 12;
        let h = AcpHasher::new();
        let target = b"target.svc.example.gov".to_vec();
        let tp = h.path_of(&target, SHALLOW);

        let mut planted = None;
        for i in 0..2_000_000u64 {
            let cand = format!("junk-{i}").into_bytes();
            if h.path_of(&cand, SHALLOW) == tp && cand != target {
                planted = Some(cand);
                break;
            }
        }
        let planted = planted.expect("should find a shallow-path collision");

        // The prover commits a tree containing the junk string but NOT target.
        let t = SparseMerkleTree::build(SHALLOW, &[(planted.clone(), val(1))]);
        let root = t.root();
        let proof = t.prove(&planted);
        // It genuinely proves inclusion of the planted string...
        assert!(verify(root, SHALLOW, &planted, &proof, true));
        // ...but cannot be replayed as a proof about `target`, even though the
        // two share a path index.
        assert_eq!(h.path_of(&planted, SHALLOW), h.path_of(&target, SHALLOW));
        assert!(
            !verify(root, SHALLOW, &target, &proof, true),
            "a planted path collision must not impersonate the target identifier"
        );
    }
}
