//! In-AIR binding of a Merkle path to a public commitment (single path, q = 1).
//!
//! This closes the gap left by the hashing-only benchmark in [`crate::measure`]:
//! there, the STARK proves that some Poseidon2 permutations were computed, but
//! nothing ties them to the committed root or to the sampled identifier's
//! position. Here the circuit proves the full statement
//!
//! > "I know a Merkle path that hashes the leaf of identifier `id` at position
//! >  `pos` up to the public root `root`, under the Poseidon2 compression used
//! >  by `acp-smt`."
//!
//! with `id_digest`, `pos` and `root` the **public inputs**. The leaf is *not*
//! public: it is derived in circuit as `H(id_digest || value)`, which is what
//! binds the path to the identifier at full digest strength.
//!
//! # Why this is sound (design notes)
//!
//! * **Permutation constraints are not hand-rolled.** Each row carries a full
//!   `Poseidon2Cols` block in columns `[0, P2_COLS)`, and we evaluate Plonky3's
//!   own [`Poseidon2Air`] over exactly that sub-range via [`SubAirBuilder`].
//!   The round constants are [`crate::aligned_constants`], which a known-answer
//!   test proves equal to the permutation `acp-smt` hashes with.
//! * **The leaf is derived, not supplied.** An earlier version of this circuit
//!   took the leaf as a free public input and bound the path to the identifier
//!   only through the `DEPTH`-bit position. That is a real weakness: a prover
//!   can grind a junk string `x` with `path_of(x) = path_of(a)`, plant `x` in
//!   its tree, and answer a query on `a` with `x`'s path -- 2^DEPTH work
//!   classically, and 2^(DEPTH/2) under Grover. The circuit now computes
//!   `H(id_digest || value)` from the *public* `id_digest` and forces the chain
//!   to start there, restoring full-digest binding.
//! * **Position binding uses a bit accumulator, not a 64-bit decomposition.**
//!   Each row's `bit` is constrained boolean, and `acc` accumulates
//!   `sum_i bit_i * 2^i` across rows, checked against the public `pos` on the
//!   last row. Because `DEPTH <= 48` and `2^48 << p` for Goldilocks, this sum
//!   determines the bits uniquely: the non-canonicity of 64-bit
//!   representations mod `p = 2^64 - 2^32 + 1` never arises.
//! * **Child ordering is constrained, not assumed.** The permutation input
//!   halves are forced to `(cur, sib)` or `(sib, cur)` according to `bit`, so a
//!   prover cannot silently swap children to hit a different root.
//!
//! # Scope and caveats
//!
//! One path per proof (`q = 1`), inclusion branch only, and no absence-witness
//! verification in circuit.  Batched binding for `q > 1` is implemented in
//! `bind_batch` using a preprocessed trace to carry the per-path public inputs
//! (position and identifier digest). **The constraint system below has not been
//! externally reviewed and should not be treated as audited.**

use core::borrow::{Borrow, BorrowMut};
use core::mem::MaybeUninit;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_goldilocks::{GenericPoseidon2LinearLayersGoldilocks, Poseidon2Goldilocks};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_poseidon2_air::{
    generate_trace_rows_for_perm, num_cols, Poseidon2Air, Poseidon2Cols,
};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig, SubAirBuilder};
use rand::rngs::SmallRng;
use rand::SeedableRng;

use crate::{
    aligned_constants, Val, HALF_FULL_ROUNDS, PARTIAL_ROUNDS, SBOX_DEGREE, SBOX_REGISTERS, WIDTH,
};

/// Digest width in field elements (matches `acp_smt::DIGEST_ELEMS`).
pub const DIGEST: usize = 4;

/// Number of Poseidon2 trace columns per row.
pub const P2_COLS: usize =
    num_cols::<WIDTH, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>();

// Poseidon2 blocks: the path level, then the leaf hash (row 0 only).
pub const A_OFF: usize = 0;
pub const L_OFF: usize = P2_COLS;
pub const LINK: usize = 2 * P2_COLS;

// Linking columns.
pub const C_CUR: usize = LINK; // current digest entering this level (4)
pub const C_SIB: usize = LINK + DIGEST; // sibling digest at this level (4)
pub const C_BIT: usize = LINK + 2 * DIGEST; // path bit at this level (1)
pub const C_ACC: usize = LINK + 2 * DIGEST + 1; // running sum of bit_i * 2^i (1)
pub const C_POW: usize = LINK + 2 * DIGEST + 2; // running 2^i (1)

/// Total trace width.
pub const TOTAL_COLS: usize = LINK + 2 * DIGEST + 3;

/// Public values: `root(4) || pos(1) || id_digest(4)`. The leaf is derived in
/// circuit and is deliberately *not* public: it commits to a low-entropy value
/// (primitive, status, risk), so publishing it would leak that value to
/// exhaustive search.
pub const NUM_PUBLIC: usize = 2 * DIGEST + 1;
const P_ROOT: usize = 0;
const P_POS: usize = DIGEST;
const P_IDD: usize = DIGEST + 1;

type P2Air = Poseidon2Air<
    Val,
    GenericPoseidon2LinearLayersGoldilocks,
    WIDTH,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS,
    PARTIAL_ROUNDS,
>;

/// AIR proving one Merkle path binds `leaf` at `pos` to `root`.
pub struct MerklePathAir {
    p2: P2Air,
}

impl Default for MerklePathAir {
    fn default() -> Self {
        Self::new()
    }
}

impl MerklePathAir {
    pub fn new() -> Self {
        Self {
            p2: Poseidon2Air::new(aligned_constants()),
        }
    }
}

impl BaseAir<Val> for MerklePathAir {
    fn width(&self) -> usize {
        TOTAL_COLS
    }
    fn num_public_values(&self) -> usize {
        NUM_PUBLIC
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        // The Poseidon2 sub-AIR dominates at SBOX_DEGREE; our linking
        // constraints are degree <= 3 once multiplied by a row selector.
        Some(SBOX_DEGREE as usize)
    }
}

impl<AB: AirBuilder<F = Val>> Air<AB> for MerklePathAir {
    fn eval(&self, builder: &mut AB) {
        // (1) Poseidon2 round constraints for the path block and the leaf-hash
        // block, each over its own disjoint column range.
        for off in [A_OFF, L_OFF] {
            let mut sub: SubAirBuilder<'_, AB, P2Air, AB::Var> =
                SubAirBuilder::new(builder, off..off + P2_COLS);
            self.p2.eval(&mut sub);
        }

        // (2) Linking, ordering, boundary and position constraints.
        let (loc, nxt) = {
            let main = builder.main();
            (main.current_slice().to_vec(), main.next_slice().to_vec())
        };
        let pis: Vec<AB::PublicVar> = builder.public_values().to_vec();

        let p2_loc: &Poseidon2Cols<
            AB::Var,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
        > = loc[A_OFF..A_OFF + P2_COLS].borrow();
        let lf: &Poseidon2Cols<
            AB::Var,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
        > = loc[L_OFF..L_OFF + P2_COLS].borrow();
        let out_loc = &p2_loc.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
        let out_lf = &lf.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;

        let bit = loc[C_BIT];
        let acc = loc[C_ACC];
        let pow = loc[C_POW];

        // bit is boolean.
        builder.assert_zero(bit * (bit.into() - AB::Expr::ONE));

        // Child ordering: the permutation input halves are (cur, sib) when
        // bit = 0 and (sib, cur) when bit = 1.
        for j in 0..DIGEST {
            let cur = loc[C_CUR + j];
            let sib = loc[C_SIB + j];
            let left: AB::Expr = (AB::Expr::ONE - bit.into()) * cur.into() + bit.into() * sib.into();
            let right: AB::Expr =
                (AB::Expr::ONE - bit.into()) * sib.into() + bit.into() * cur.into();
            builder.assert_eq(p2_loc.inputs[j], left);
            builder.assert_eq(p2_loc.inputs[DIGEST + j], right);
        }

        // First row: the chain starts at the *derived* leaf H(id_digest||value).
        // With an empty value the sponge absorbs id_digest into the rate and
        // permutes once, so the leaf-hash block's input is [id_digest || 0].
        {
            let mut first = builder.when_first_row();
            for j in 0..DIGEST {
                first.assert_eq(lf.inputs[j], pis[P_IDD + j]);
                first.assert_zero(lf.inputs[DIGEST + j]);
                first.assert_eq(loc[C_CUR + j], out_lf[j]);
            }
            first.assert_eq(pow, AB::Expr::ONE);
            first.assert_eq(acc, bit);
        }

        // Transition: the next level's current digest is this level's output;
        // pow doubles; acc accumulates the next bit at the next weight.
        {
            let n_bit = nxt[C_BIT];
            let n_acc = nxt[C_ACC];
            let n_pow = nxt[C_POW];
            let mut tr = builder.when_transition();
            for j in 0..DIGEST {
                tr.assert_eq(nxt[C_CUR + j], out_loc[j]);
            }
            tr.assert_eq(n_pow, pow.into() * AB::Expr::TWO);
            tr.assert_eq(n_acc, acc.into() + n_bit.into() * n_pow.into());
        }

        // Last row: the output is the public root and the accumulated bits are
        // the public position.
        {
            let mut last = builder.when_last_row();
            for j in 0..DIGEST {
                last.assert_eq(out_loc[j], pis[P_ROOT + j]);
            }
            last.assert_eq(acc, pis[P_POS]);
        }
    }
}

/// Build the execution trace for one Merkle path.
///
/// The leaf is derived from `id_digest` (empty value), matching what the
/// circuit enforces; `siblings[i]` is the sibling at level `i` and `pos` the
/// leaf's path index. `siblings.len()` must be a power of two.
pub fn generate_trace(
    id_digest: [Val; DIGEST],
    siblings: &[[Val; DIGEST]],
    pos: u64,
) -> RowMajorMatrix<Val> {
    let depth = siblings.len();
    assert!(depth.is_power_of_two(), "depth must be a power of two");
    assert!(depth <= 48, "position accumulator assumes depth <= 48");

    let consts = aligned_constants();
    let mut values = Val::zero_vec(depth * TOTAL_COLS);

    let fill = |row: &mut [Val], off: usize, state: [Val; WIDTH]| -> [Val; DIGEST] {
        {
            let slice = &mut row[off..off + P2_COLS];
            let uninit: &mut [MaybeUninit<Val>] = unsafe { core::mem::transmute(slice) };
            let cols: &mut Poseidon2Cols<
                MaybeUninit<Val>,
                WIDTH,
                SBOX_DEGREE,
                SBOX_REGISTERS,
                HALF_FULL_ROUNDS,
                PARTIAL_ROUNDS,
            > = uninit.borrow_mut();
            generate_trace_rows_for_perm::<
                Val,
                GenericPoseidon2LinearLayersGoldilocks,
                WIDTH,
                SBOX_DEGREE,
                SBOX_REGISTERS,
                HALF_FULL_ROUNDS,
                PARTIAL_ROUNDS,
            >(cols, state, &consts);
        }
        let filled: &Poseidon2Cols<
            Val,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
        > = row[off..off + P2_COLS].borrow();
        let o = filled.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
        [o[0], o[1], o[2], o[3]]
    };

    // The leaf the circuit will enforce on row 0.
    let mut leaf_state = [Val::ZERO; WIDTH];
    leaf_state[..DIGEST].copy_from_slice(&id_digest);
    let mut cur = {
        let mut scratch = Val::zero_vec(TOTAL_COLS);
        fill(&mut scratch, L_OFF, leaf_state)
    };

    let mut acc = Val::ZERO;
    let mut pow = Val::ONE;

    for (i, sib) in siblings.iter().enumerate() {
        let row = &mut values[i * TOTAL_COLS..(i + 1) * TOTAL_COLS];
        let bit = (pos >> i) & 1;

        let mut state = [Val::ZERO; WIDTH];
        let (left, right) = if bit == 0 { (cur, *sib) } else { (*sib, cur) };
        state[..DIGEST].copy_from_slice(&left);
        state[DIGEST..].copy_from_slice(&right);

        row[C_CUR..C_CUR + DIGEST].copy_from_slice(&cur);
        row[C_SIB..C_SIB + DIGEST].copy_from_slice(sib);

        let out = fill(row, A_OFF, state);
        // Row 0 carries the real leaf hash; later rows carry consistent filler.
        let lstate = if i == 0 { leaf_state } else { [Val::ZERO; WIDTH] };
        let _ = fill(row, L_OFF, lstate);

        if i > 0 {
            pow *= Val::TWO;
            acc += Val::from_bool(bit == 1) * pow;
        } else {
            acc = Val::from_bool(bit == 1);
        }
        row[C_BIT] = Val::from_bool(bit == 1);
        row[C_ACC] = acc;
        row[C_POW] = pow;

        cur = out;
    }

    RowMajorMatrix::new(values, TOTAL_COLS)
}

/// The root a path implies, recomputed out of circuit (for test assertions).
pub fn implied_root(
    id_digest: [Val; DIGEST],
    siblings: &[[Val; DIGEST]],
    pos: u64,
) -> [Val; DIGEST] {
    let trace = generate_trace(id_digest, siblings, pos);
    let last = trace.values.len() - TOTAL_COLS;
    let filled: &Poseidon2Cols<
        Val,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
    > = trace.values[last + A_OFF..last + A_OFF + P2_COLS].borrow();
    let out = filled.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
    [out[0], out[1], out[2], out[3]]
}

// --- STARK configuration (mirrors crate::measure) ---
type Challenge = BinomialExtensionField<Val, 2>;
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValPacking = <Val as Field>::Packing;
type ValMmcs = MerkleTreeMmcs<ValPacking, ValPacking, MyHash, MyCompress, 2, 4>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Dft = Radix2DitParallel<Val>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type BindConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn config() -> BindConfig {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters {
        log_blowup: 3,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 28,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri_params);
    BindConfig::new(pcs, Challenger::new(perm))
}

/// Public-value vector `root || pos || id_digest`.
pub fn public_values(root: [Val; DIGEST], pos: u64, id_digest: [Val; DIGEST]) -> Vec<Val> {
    let mut pis = Vec::with_capacity(NUM_PUBLIC);
    pis.extend_from_slice(&root);
    pis.push(Val::from_u64(pos));
    pis.extend_from_slice(&id_digest);
    pis
}

/// Result of proving one bound path.
pub struct BindMeasurement {
    pub depth: usize,
    pub trace_cols: usize,
    pub prove_secs: f64,
    pub verify_secs: f64,
    pub proof_bytes: usize,
}

/// Prove and verify that identifier `id_digest` at `pos` hashes to `root`.
pub fn prove_path(
    id_digest: [Val; DIGEST],
    siblings: &[[Val; DIGEST]],
    pos: u64,
    root: [Val; DIGEST],
) -> BindMeasurement {
    use std::time::Instant;
    let cfg = config();
    let air = MerklePathAir::new();
    let trace = generate_trace(id_digest, siblings, pos);
    let pis = public_values(root, pos, id_digest);

    let t = Instant::now();
    let proof = prove(&cfg, &air, trace, &pis);
    let prove_secs = t.elapsed().as_secs_f64();
    let proof_bytes = postcard::to_allocvec(&proof).expect("serialize").len();

    let t = Instant::now();
    verify(&cfg, &air, &proof, &pis).expect("verification failed");
    let verify_secs = t.elapsed().as_secs_f64();

    BindMeasurement {
        depth: siblings.len(),
        trace_cols: TOTAL_COLS,
        prove_secs,
        verify_secs,
        proof_bytes,
    }
}

/// Directly evaluate the AIR constraints against a claimed public statement,
/// panicking on the first violated constraint.
///
/// This is the honest way to test binding. Verifying a proof under altered
/// public values proves nothing about our constraints, because `uni-stark`
/// absorbs the public values into the Fiat--Shamir transcript: any change
/// breaks the transcript and verification fails even for an AIR with no
/// binding constraints at all.
pub fn check_statement(
    trace: RowMajorMatrix<Val>,
    root: [Val; DIGEST],
    pos: u64,
    id_digest: [Val; DIGEST],
) {
    let air = MerklePathAir::new();
    p3_air::check_constraints(&air, &trace, &public_values(root, pos, id_digest));
}

#[cfg(test)]
mod tests {
    use super::*;
    use acp_smt::{CoverageProof, SparseMerkleTree, F as SmtF};

    /// Power-of-two depth so the trace height needs no padding.
    const D: usize = 32;

    fn honest_case() -> ([Val; DIGEST], Vec<[Val; DIGEST]>, u64, [Val; DIGEST]) {
        let entries: Vec<(Vec<u8>, Vec<SmtF>)> = (0..64)
            .map(|i| (format!("asset-{i}.svc.example.gov").into_bytes(), Vec::new()))
            .collect();
        let tree = SparseMerkleTree::build(D, &entries);
        let root = tree.root();
        let id = &entries[7].0;
        let pos = tree.hasher().path_of(id, D);
        let idd = tree.hasher().id_digest(id);
        match tree.prove(id) {
            CoverageProof::Inclusion { path, .. } => (idd, path.siblings, pos, root),
            _ => panic!("expected an inclusion proof"),
        }
    }

    #[test]
    fn trace_reproduces_the_smt_root() {
        let (idd, sibs, pos, root) = honest_case();
        assert_eq!(implied_root(idd, &sibs, pos), root);
    }

    #[test]
    fn honest_statement_satisfies_the_constraints() {
        let (idd, sibs, pos, root) = honest_case();
        check_statement(generate_trace(idd, &sibs, pos), root, pos, idd);
    }

    #[test]
    fn honest_path_proves_and_verifies() {
        let (idd, sibs, pos, root) = honest_case();
        let m = prove_path(idd, &sibs, pos, root);
        assert_eq!(m.depth, D);
        assert!(m.proof_bytes > 0);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn constraints_reject_wrong_root() {
        let (idd, sibs, pos, root) = honest_case();
        let mut bad = root;
        bad[0] += Val::ONE;
        check_statement(generate_trace(idd, &sibs, pos), bad, pos, idd);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn constraints_reject_wrong_position() {
        let (idd, sibs, pos, root) = honest_case();
        check_statement(generate_trace(idd, &sibs, pos), root, pos ^ 1, idd);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn constraints_reject_wrong_identifier() {
        // The leaf is derived from id_digest, so claiming a different
        // identifier changes the leaf the chain must start from. This is the
        // constraint that defeats the planted-collision attack: sharing a
        // position with the target is no longer sufficient.
        let (idd, sibs, pos, root) = honest_case();
        let trace = generate_trace(idd, &sibs, pos);
        let mut other = idd;
        other[0] += Val::ONE;
        check_statement(trace, root, pos, other);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn constraints_reject_repositioned_path() {
        let (idd, sibs, pos, root) = honest_case();
        let forged = pos ^ 1;
        check_statement(generate_trace(idd, &sibs, forged), root, forged, idd);
    }

    #[test]
    fn repositioned_path_reaches_a_different_root() {
        let (idd, sibs, pos, root) = honest_case();
        let forged = pos ^ 1;
        let other = implied_root(idd, &sibs, forged);
        assert_ne!(other, root);
        check_statement(generate_trace(idd, &sibs, forged), other, forged, idd);
    }
}
