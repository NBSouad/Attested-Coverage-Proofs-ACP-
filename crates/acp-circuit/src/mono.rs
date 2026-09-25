//! Batched in-AIR proof of epoch-to-epoch monotonicity for a committed
//! inventory.
//!
//! This is the dominant VPQM bookkeeping relation: for every asset in the
//! current inventory, the prover shows the same identifier also appears in the
//! previous epoch's committed inventory, at the same position, and the
//! migration-status field does not decrease (Classical < Hybrid < PQC).
//!
//! # Statement
//!
//! Public inputs: current root `C_\Sigma`, previous root `C_\Sigma^{t-1}`.
//! Preprocessed per row: position, identifier digest, path bit, first/last/real
//! flags. Witness per row: current and previous status values. The circuit
//! proves per segment (one asset, `depth` rows):
//!
//! 1. `leaf_cur = H(id_digest || [status_cur])` chains to `C_\Sigma`.
//! 2. `leaf_prev = H(id_digest || [status_prev])` chains to `C_\Sigma^{t-1}`
//!    **at the same position**.
//! 3. `status_cur >= status_prev` in the ordered set `{0,1,2}`.
//!
//! The two Merkle paths share the same position bits and path siblings.  The
//! leaf hash is the same padding-free sponge used by `acp-smt`: one permutation
//! on `[id_digest || 0^4]` and a second permutation that overwrites `state[0]`
//! with the status element and keeps `state[1..8]`.
//!
//! # Caveats
//!
//! * One-status-element records; primitive and risk classes are bundled with
//!   the status into a single field element for this measurement.  The gadget
//!   is representative of the per-asset work: two path openings plus a status
//!   comparison.
//! * Exception signatures are not verified in-circuit (same deferred status as
//!   blind ACP's per-name oracle evidence).  The circuit proves monotonicity
//!   modulo the status values the prover supplies.
//! * **Not externally reviewed.**

use core::borrow::{Borrow, BorrowMut};
use core::mem::MaybeUninit;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, HidingFriPcs, TwoAdicFriPcs};
use p3_goldilocks::{GenericPoseidon2LinearLayersGoldilocks, Poseidon2Goldilocks};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::{MerkleTreeHidingMmcs, MerkleTreeMmcs};
use p3_poseidon2_air::{
    generate_trace_rows_for_perm, Poseidon2Air, Poseidon2Cols,
};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{
    prove_with_preprocessed, setup_preprocessed, verify_with_preprocessed, StarkConfig,
    SubAirBuilder,
};
use rand::rngs::SmallRng;
use rand::SeedableRng;

use crate::{
    aligned_constants, next_pow2, Val, HALF_FULL_ROUNDS, PARTIAL_ROUNDS, SBOX_DEGREE,
    SBOX_REGISTERS, WIDTH,
};
use crate::bind::{DIGEST, P2_COLS};

type P2Air = Poseidon2Air<
    Val,
    GenericPoseidon2LinearLayersGoldilocks,
    WIDTH,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS,
    PARTIAL_ROUNDS,
>;

// Five P2 blocks per row.  A/B are used on all rows; the three leaf blocks are
// meaningful only on the first row of each segment.
const A_OFF: usize = 0;                       // current-tree path
const B_OFF: usize = P2_COLS;                 // previous-tree path
const L0_OFF: usize = 2 * P2_COLS;            // shared leaf first perm
const L1_OFF: usize = 3 * P2_COLS;            // current leaf second perm
const L2_OFF: usize = 4 * P2_COLS;            // previous leaf second perm
const LINK: usize = 5 * P2_COLS;

// Linking columns.
const C_CURA: usize = LINK;                   // current digest (4)
const C_SIBA: usize = LINK + DIGEST;          // current sibling (4)
const C_CURB: usize = LINK + 2 * DIGEST;      // previous digest (4)
const C_SIBB: usize = LINK + 3 * DIGEST;      // previous sibling (4)
const C_BIT: usize = LINK + 4 * DIGEST;       // path bit (1)
const C_ACC: usize = C_BIT + 1;               // position accumulator (1)
const C_POW: usize = C_ACC + 1;               // 2^i (1)
const C_STAT_CUR: usize = C_POW + 1;          // current status (1)
const C_STAT_PREV: usize = C_STAT_CUR + 1;    // previous status (1)

pub const TOTAL_COLS: usize = C_STAT_PREV + 1;

// Preprocessed columns, one per row.
const PP_POS: usize = 0;                      // position (last row only)
const PP_IDD: usize = 1;                      // identifier digest (first row)
const PP_BIT: usize = PP_IDD + DIGEST;        // path bit
const PP_IS_FIRST: usize = PP_BIT + 1;
const PP_IS_LAST: usize = PP_IS_FIRST + 1;
const PP_IS_REAL: usize = PP_IS_LAST + 1;
const PREPROCESSED_WIDTH: usize = PP_IS_REAL + 1;

/// Public values: `root_cur(4) || root_prev(4)`.
pub const NUM_PUBLIC: usize = 2 * DIGEST;
const P_CUR: usize = 0;
const P_PREV: usize = DIGEST;

/// One asset's public inputs (position and identifier digest are public).
#[derive(Clone, Debug)]
pub struct AssetPublic {
    pub id_digest: [Val; DIGEST],
    pub position: u64,
}

/// One asset with all witness data.
#[derive(Clone, Debug)]
pub struct AssetPath {
    pub id_digest: [Val; DIGEST],
    pub position: u64,
    pub status_cur: Val,
    pub status_prev: Val,
    pub siblings_cur: Vec<[Val; DIGEST]>,
    pub siblings_prev: Vec<[Val; DIGEST]>,
}

impl From<&AssetPath> for AssetPublic {
    fn from(p: &AssetPath) -> Self {
        Self {
            id_digest: p.id_digest,
            position: p.position,
        }
    }
}

/// AIR for batched monotonicity: each real segment proves the current and
/// previous records for one asset, with a status-ordering gadget.
pub struct MonoAir {
    pub root_cur: [Val; DIGEST],
    pub root_prev: [Val; DIGEST],
    pub depth: usize,
    pub q: usize,
    pub trace_height: usize,
    preprocessed: RowMajorMatrix<Val>,
}

impl MonoAir {
    pub fn from_public_inputs(
        root_cur: [Val; DIGEST],
        root_prev: [Val; DIGEST],
        depth: usize,
        inputs: &[AssetPublic],
    ) -> Self {
        assert!(depth >= 1 && depth <= 48, "depth must be between 1 and 48");
        let trace_height = next_pow2(inputs.len() * depth);
        let preprocessed = build_preprocessed_trace(depth, trace_height, inputs);
        Self {
            root_cur,
            root_prev,
            depth,
            q: inputs.len(),
            trace_height,
            preprocessed,
        }
    }

    pub fn from_paths(
        root_cur: [Val; DIGEST],
        root_prev: [Val; DIGEST],
        depth: usize,
        paths: &[AssetPath],
    ) -> Self {
        let inputs: Vec<AssetPublic> = paths.iter().map(AssetPublic::from).collect();
        Self::from_public_inputs(root_cur, root_prev, depth, &inputs)
    }
}

impl BaseAir<Val> for MonoAir {
    fn width(&self) -> usize {
        TOTAL_COLS
    }
    fn preprocessed_width(&self) -> usize {
        PREPROCESSED_WIDTH
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<Val>> {
        Some(self.preprocessed.clone())
    }
    fn num_public_values(&self) -> usize {
        NUM_PUBLIC
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(SBOX_DEGREE as usize)
    }
}

impl<AB: AirBuilder<F = Val>> Air<AB> for MonoAir {
    fn eval(&self, builder: &mut AB) {
        for off in [A_OFF, B_OFF, L0_OFF, L1_OFF, L2_OFF] {
            let mut sub: SubAirBuilder<'_, AB, P2Air, AB::Var> =
                SubAirBuilder::new(builder, off..off + P2_COLS);
            let p2_air = P2Air::new(aligned_constants());
            p2_air.eval(&mut sub);
        }

        let (loc, nxt) = {
            let main = builder.main();
            (main.current_slice().to_vec(), main.next_slice().to_vec())
        };
        let prep = builder.preprocessed().current_slice().to_vec();
        let prep_next = builder.preprocessed().next_slice().to_vec();
        let pis = builder.public_values().to_vec();

        type P2ColsT<T> = Poseidon2Cols<T, WIDTH, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>;
        let a: &P2ColsT<AB::Var> = loc[A_OFF..A_OFF + P2_COLS].borrow();
        let b: &P2ColsT<AB::Var> = loc[B_OFF..B_OFF + P2_COLS].borrow();
        let l0: &P2ColsT<AB::Var> = loc[L0_OFF..L0_OFF + P2_COLS].borrow();
        let l1: &P2ColsT<AB::Var> = loc[L1_OFF..L1_OFF + P2_COLS].borrow();
        let l2: &P2ColsT<AB::Var> = loc[L2_OFF..L2_OFF + P2_COLS].borrow();

        let out_a = &a.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
        let out_b = &b.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
        let out_l0 = &l0.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
        let out_l1 = &l1.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
        let out_l2 = &l2.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;

        let is_real = prep[PP_IS_REAL].into();
        let is_first = prep[PP_IS_FIRST].into();
        let is_last = prep[PP_IS_LAST].into();
        let bit = prep[PP_BIT].into();
        let pos = prep[PP_POS].into();
        let idd: Vec<AB::Expr> =
            prep[PP_IDD..PP_IDD + DIGEST].iter().map(|&x| x.into()).collect();

        let nxt_is_real = prep_next[PP_IS_REAL].into();
        let nxt_is_first = prep_next[PP_IS_FIRST].into();
        let nxt_bit = prep_next[PP_BIT].into();

        let stat_cur = loc[C_STAT_CUR];
        let stat_prev = loc[C_STAT_PREV];

        // C_BIT must equal the preprocessed path bit on real rows.
        builder.assert_zero(is_real.clone() * (loc[C_BIT].into() - bit.clone()));

        // Child ordering for both chains, driven by the shared path bit.
        for j in 0..DIGEST {
            let (ca, sa) = (loc[C_CURA + j], loc[C_SIBA + j]);
            let (cb, sb) = (loc[C_CURB + j], loc[C_SIBB + j]);
            let one = AB::Expr::ONE;
            let left_a = (one.clone() - bit.clone()) * ca.into() + bit.clone() * sa.into();
            let right_a = (one.clone() - bit.clone()) * sa.into() + bit.clone() * ca.into();
            builder.assert_zero(is_real.clone() * (a.inputs[j].into() - left_a));
            builder.assert_zero(is_real.clone() * (a.inputs[DIGEST + j].into() - right_a));

            let left_b = (one.clone() - bit.clone()) * cb.into() + bit.clone() * sb.into();
            let right_b = (one.clone() - bit.clone()) * sb.into() + bit.clone() * cb.into();
            builder.assert_zero(is_real.clone() * (b.inputs[j].into() - left_b));
            builder.assert_zero(is_real.clone() * (b.inputs[DIGEST + j].into() - right_b));
        }

        // First row of each real segment: build the two leaves and start chains.
        let first_factor = is_real.clone() * is_first;
        {
            // L0 input: [id_digest || 0^4]
            for j in 0..DIGEST {
                builder.assert_zero(first_factor.clone() * (l0.inputs[j].into() - idd[j].clone()));
                builder.assert_zero(first_factor.clone() * l0.inputs[DIGEST + j].into());
            }
            // L1 input: [status_cur || out_l0[1..8]]
            builder.assert_zero(first_factor.clone() * (l1.inputs[0].into() - stat_cur.into()));
            for j in 1..WIDTH {
                builder.assert_zero(first_factor.clone() * (l1.inputs[j].into() - out_l0[j].into()));
            }
            // L2 input: [status_prev || out_l0[1..8]]
            builder.assert_zero(first_factor.clone() * (l2.inputs[0].into() - stat_prev.into()));
            for j in 1..WIDTH {
                builder.assert_zero(first_factor.clone() * (l2.inputs[j].into() - out_l0[j].into()));
            }
            // Chain starts are the first four lanes of the leaf outputs.
            for j in 0..DIGEST {
                builder.assert_zero(first_factor.clone() * (loc[C_CURA + j].into() - out_l1[j].into()));
                builder.assert_zero(first_factor.clone() * (loc[C_CURB + j].into() - out_l2[j].into()));
            }
            // Position accumulator starts.
            builder.assert_zero(first_factor.clone() * (loc[C_POW].into() - AB::Expr::ONE));
            builder.assert_zero(first_factor.clone() * (loc[C_ACC].into() - bit));

            // Status values are in {0,1,2}.
            builder.assert_zero(first_factor.clone() * stat_cur.into() * (stat_cur.into() - AB::Expr::ONE) * (stat_cur.into() - AB::Expr::TWO));
            builder.assert_zero(first_factor.clone() * stat_prev.into() * (stat_prev.into() - AB::Expr::ONE) * (stat_prev.into() - AB::Expr::TWO));

            // Monotonicity: (sc - sp) is in {0,1,2}, i.e. sc >= sp.
            let diff = stat_cur.into() - stat_prev.into();
            builder.assert_zero(first_factor * diff.clone() * (diff.clone() - AB::Expr::ONE) * (diff - AB::Expr::TWO));
        }

        // Transition: carry both chains; keep status columns constant; update
        // position accumulator.  The leaf blocks run as zero-state filler on
        // non-first rows, so no extra linking is needed for them.
        let trans_factor = nxt_is_real * (AB::Expr::ONE - nxt_is_first);
        {
            let mut tr = builder.when_transition();
            for j in 0..DIGEST {
                tr.assert_zero(trans_factor.clone() * (nxt[C_CURA + j].into() - out_a[j].into()));
                tr.assert_zero(trans_factor.clone() * (nxt[C_CURB + j].into() - out_b[j].into()));
            }
            tr.assert_zero(trans_factor.clone() * (nxt[C_STAT_CUR].into() - stat_cur.into()));
            tr.assert_zero(trans_factor.clone() * (nxt[C_STAT_PREV].into() - stat_prev.into()));
            tr.assert_zero(trans_factor.clone() * (nxt[C_POW].into() - loc[C_POW].into() * AB::Expr::TWO));
            tr.assert_zero(trans_factor * (nxt[C_ACC].into() - loc[C_ACC].into() - nxt_bit * nxt[C_POW].into()));
        }

        // Last row: both chain outputs equal the public roots; acc equals position.
        let last_factor = is_real * is_last;
        for j in 0..DIGEST {
            builder.assert_zero(last_factor.clone() * (out_a[j].into() - pis[P_CUR + j].into()));
            builder.assert_zero(last_factor.clone() * (out_b[j].into() - pis[P_PREV + j].into()));
        }
        builder.assert_zero(last_factor * (loc[C_ACC].into() - pos));
    }
}

fn build_preprocessed_trace(
    depth: usize,
    trace_height: usize,
    inputs: &[AssetPublic],
) -> RowMajorMatrix<Val> {
    assert!(depth >= 1 && depth <= 48);
    let mut values = Val::zero_vec(trace_height * PREPROCESSED_WIDTH);
    for row in 0..trace_height {
        let is_real = row < inputs.len() * depth;
        let base = row * PREPROCESSED_WIDTH;
        if !is_real {
            continue;
        }
        let seg = row / depth;
        let row_in_seg = row % depth;
        let path = &inputs[seg];
        let bit_val = ((path.position >> row_in_seg) & 1) == 1;
        let is_first = row_in_seg == 0;
        let is_last = row_in_seg == depth - 1;

        values[base + PP_POS] = if is_last { Val::from_u64(path.position) } else { Val::ZERO };
        for j in 0..DIGEST {
            values[base + PP_IDD + j] = if is_first { path.id_digest[j] } else { Val::ZERO };
        }
        values[base + PP_BIT] = Val::from_bool(bit_val);
        values[base + PP_IS_FIRST] = Val::from_bool(is_first);
        values[base + PP_IS_LAST] = Val::from_bool(is_last);
        values[base + PP_IS_REAL] = Val::ONE;
    }
    RowMajorMatrix::new(values, PREPROCESSED_WIDTH)
}

// Fill a Poseidon2 block and return the full 8-lane output state.
fn fill_perm_full(row: &mut [Val], off: usize, state: [Val; WIDTH]) -> [Val; WIDTH] {
    let consts = aligned_constants();
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
    core::array::from_fn(|i| filled.ending_full_rounds[HALF_FULL_ROUNDS - 1].post[i])
}

// Fill a Poseidon2 block and return the first 4 lanes (digest output).
fn fill_perm(row: &mut [Val], off: usize, state: [Val; WIDTH]) -> [Val; DIGEST] {
    let out = fill_perm_full(row, off, state);
    [out[0], out[1], out[2], out[3]]
}

/// Build the execution trace for `n` assets, each with two paths of depth `D`.
pub fn generate_trace(
    depth: usize,
    trace_height: usize,
    paths: &[AssetPath],
) -> RowMajorMatrix<Val> {
    assert!(depth >= 1 && depth <= 48);
    assert!(trace_height >= paths.len() * depth);

    let mut values = Val::zero_vec(trace_height * TOTAL_COLS);

    for (seg, path) in paths.iter().enumerate() {
        assert_eq!(path.siblings_cur.len(), depth);
        assert_eq!(path.siblings_prev.len(), depth);

        let mut cur_a = [Val::ZERO; DIGEST];
        let mut cur_b = [Val::ZERO; DIGEST];
        let mut acc = Val::ZERO;
        let mut pow = Val::ONE;

        for i in 0..depth {
            let row = seg * depth + i;
            let row_base = row * TOTAL_COLS;
            let bit = (path.position >> i) & 1;

            // Leaf blocks: meaningful on row 0, zero-state filler otherwise.
            if i == 0 {
                let mut s0 = [Val::ZERO; WIDTH];
                s0[..DIGEST].copy_from_slice(&path.id_digest);
                let out_l0 = fill_perm_full(&mut values[row_base..row_base + TOTAL_COLS], L0_OFF, s0);

                let mut s1 = out_l0;
                s1[0] = path.status_cur;
                let out_l1 = fill_perm_full(&mut values[row_base..row_base + TOTAL_COLS], L1_OFF, s1);

                let mut s2 = out_l0;
                s2[0] = path.status_prev;
                let out_l2 = fill_perm_full(&mut values[row_base..row_base + TOTAL_COLS], L2_OFF, s2);

                cur_a = [out_l1[0], out_l1[1], out_l1[2], out_l1[3]];
                cur_b = [out_l2[0], out_l2[1], out_l2[2], out_l2[3]];
            } else {
                let zero_state = [Val::ZERO; WIDTH];
                let _ = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], L0_OFF, zero_state);
                let _ = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], L1_OFF, zero_state);
                let _ = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], L2_OFF, zero_state);
            }

            // Path blocks A and B.
            let mut state_a = [Val::ZERO; WIDTH];
            let (left_a, right_a) = if bit == 0 { (cur_a, path.siblings_cur[i]) } else { (path.siblings_cur[i], cur_a) };
            state_a[..DIGEST].copy_from_slice(&left_a);
            state_a[DIGEST..].copy_from_slice(&right_a);

            let mut state_b = [Val::ZERO; WIDTH];
            let (left_b, right_b) = if bit == 0 { (cur_b, path.siblings_prev[i]) } else { (path.siblings_prev[i], cur_b) };
            state_b[..DIGEST].copy_from_slice(&left_b);
            state_b[DIGEST..].copy_from_slice(&right_b);

            values[row_base + C_CURA..row_base + C_CURA + DIGEST].copy_from_slice(&cur_a);
            values[row_base + C_SIBA..row_base + C_SIBA + DIGEST].copy_from_slice(&path.siblings_cur[i]);
            values[row_base + C_CURB..row_base + C_CURB + DIGEST].copy_from_slice(&cur_b);
            values[row_base + C_SIBB..row_base + C_SIBB + DIGEST].copy_from_slice(&path.siblings_prev[i]);

            cur_a = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], A_OFF, state_a);
            cur_b = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], B_OFF, state_b);

            if i > 0 {
                pow *= Val::TWO;
                acc += Val::from_bool(bit == 1) * pow;
            } else {
                acc = Val::from_bool(bit == 1);
            }

            values[row_base + C_BIT] = Val::from_bool(bit == 1);
            values[row_base + C_ACC] = acc;
            values[row_base + C_POW] = pow;
            // Status values are constant across the segment so the transition
            // constraint carries them from row 0 through row depth-1.
            values[row_base + C_STAT_CUR] = path.status_cur;
            values[row_base + C_STAT_PREV] = path.status_prev;
        }
    }

    // Padded rows: fill all P2 blocks with the zero-state permutation.
    let zero_state = [Val::ZERO; WIDTH];
    for row in paths.len() * depth..trace_height {
        let row_base = row * TOTAL_COLS;
        let _ = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], A_OFF, zero_state);
        let _ = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], B_OFF, zero_state);
        let _ = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], L0_OFF, zero_state);
        let _ = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], L1_OFF, zero_state);
        let _ = fill_perm(&mut values[row_base..row_base + TOTAL_COLS], L2_OFF, zero_state);
    }

    RowMajorMatrix::new(values, TOTAL_COLS)
}

// --- STARK configuration (same as bind_batch) ---

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
type MonoConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn make_fri_params<C>(mmcs: C) -> FriParameters<C> {
    FriParameters {
        log_blowup: 3,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 28,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs,
    }
}

fn plain_config() -> (MonoConfig, usize) {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri_params = make_fri_params(challenge_mmcs);
    let conjectured_bits = fri_params.conjectured_soundness_bits();
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri_params);
    (MonoConfig::new(pcs, Challenger::new(perm)), conjectured_bits)
}

type ZkValMmcs =
    MerkleTreeHidingMmcs<ValPacking, ValPacking, MyHash, MyCompress, SmallRng, 2, 4, 4>;
type ZkChallengeMmcs = ExtensionMmcs<Val, Challenge, ZkValMmcs>;
type ZkPcs = HidingFriPcs<Val, Dft, ZkValMmcs, ZkChallengeMmcs, SmallRng>;
type ZkMonoConfig = StarkConfig<ZkPcs, Challenge, Challenger>;

fn hiding_config() -> (ZkMonoConfig, usize) {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ZkValMmcs::new(hash, compress, 0, SmallRng::seed_from_u64(2));
    let challenge_mmcs = ZkChallengeMmcs::new(val_mmcs.clone());
    let fri_params = make_fri_params(challenge_mmcs);
    let conjectured_bits = fri_params.conjectured_soundness_bits();
    let pcs = ZkPcs::new(
        Dft::default(),
        val_mmcs,
        fri_params,
        4,
        SmallRng::seed_from_u64(3),
    );
    (ZkMonoConfig::new(pcs, Challenger::new(perm)), conjectured_bits)
}

/// Public-value vector `root_cur || root_prev`.
pub fn public_values(root_cur: [Val; DIGEST], root_prev: [Val; DIGEST]) -> Vec<Val> {
    let mut pis = Vec::with_capacity(NUM_PUBLIC);
    pis.extend_from_slice(&root_cur);
    pis.extend_from_slice(&root_prev);
    pis
}

/// Result of proving `n` monotonicity paths.
#[derive(Clone, Debug)]
pub struct MonoMeasurement {
    pub n: usize,
    pub depth: usize,
    pub trace_cols: usize,
    pub trace_rows: usize,
    pub prove_secs: f64,
    pub verify_secs: f64,
    pub proof_bytes: usize,
    pub conjectured_bits: usize,
}

fn prove_or_verify(
    root_cur: [Val; DIGEST],
    root_prev: [Val; DIGEST],
    depth: usize,
    paths: &[AssetPath],
    zk: bool,
) -> MonoMeasurement {
    use std::time::Instant;

    let trace_height = next_pow2(paths.len() * depth);
    let trace = generate_trace(depth, trace_height, paths);
    let air = MonoAir::from_paths(root_cur, root_prev, depth, paths);
    let public_values = public_values(root_cur, root_prev);
    let degree_bits = log2_strict_usize(trace_height);

    let (prove_secs, verify_secs, proof_bytes, conjectured_bits) = if zk {
        let (cfg, conjectured_bits) = hiding_config();
        let (ppd, vk) = setup_preprocessed::<ZkMonoConfig, _>(&cfg, &air, degree_bits).unwrap();
        let t = Instant::now();
        let proof = prove_with_preprocessed(&cfg, &air, trace, &public_values, Some(&ppd));
        let prove_secs = t.elapsed().as_secs_f64();
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize").len();
        let t = Instant::now();
        verify_with_preprocessed(&cfg, &air, &proof, &public_values, Some(&vk)).expect("verification failed");
        let verify_secs = t.elapsed().as_secs_f64();
        (prove_secs, verify_secs, proof_bytes, conjectured_bits)
    } else {
        let (cfg, conjectured_bits) = plain_config();
        let (ppd, vk) = setup_preprocessed::<MonoConfig, _>(&cfg, &air, degree_bits).unwrap();
        let t = Instant::now();
        let proof = prove_with_preprocessed(&cfg, &air, trace, &public_values, Some(&ppd));
        let prove_secs = t.elapsed().as_secs_f64();
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize").len();
        let t = Instant::now();
        verify_with_preprocessed(&cfg, &air, &proof, &public_values, Some(&vk)).expect("verification failed");
        let verify_secs = t.elapsed().as_secs_f64();
        (prove_secs, verify_secs, proof_bytes, conjectured_bits)
    };

    MonoMeasurement {
        n: paths.len(),
        depth,
        trace_cols: TOTAL_COLS,
        trace_rows: trace_height,
        prove_secs,
        verify_secs,
        proof_bytes,
        conjectured_bits,
    }
}

fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "n must be a power of two");
    n.trailing_zeros() as usize
}

/// Prove and verify `n` monotonicity paths (plain configuration).
pub fn prove(
    root_cur: [Val; DIGEST],
    root_prev: [Val; DIGEST],
    depth: usize,
    paths: &[AssetPath],
) -> MonoMeasurement {
    prove_or_verify(root_cur, root_prev, depth, paths, false)
}

/// Prove and verify `n` monotonicity paths (hiding / zero-knowledge configuration).
pub fn prove_zk(
    root_cur: [Val; DIGEST],
    root_prev: [Val; DIGEST],
    depth: usize,
    paths: &[AssetPath],
) -> MonoMeasurement {
    prove_or_verify(root_cur, root_prev, depth, paths, true)
}

/// Directly evaluate the AIR constraints against a claimed public statement.
pub fn check_statement(
    trace: RowMajorMatrix<Val>,
    root_cur: [Val; DIGEST],
    root_prev: [Val; DIGEST],
    depth: usize,
    paths: &[AssetPath],
) {
    let air = MonoAir::from_paths(root_cur, root_prev, depth, paths);
    p3_air::check_constraints(&air, &trace, &public_values(root_cur, root_prev));
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::integers::QuotientMap;
    use acp_smt::{SparseMerkleTree, F as SmtF};

    const D: usize = 32;

    fn asset_paths(statuses: &[(u64, u64)]) -> (SparseMerkleTree, SparseMerkleTree, Vec<AssetPath>) {
        let ids: Vec<Vec<u8>> = (0..statuses.len())
            .map(|i| format!("asset-{i}.svc.example.gov").into_bytes())
            .collect();
        let cur: Vec<(Vec<u8>, Vec<SmtF>)> = ids
            .iter()
            .zip(statuses.iter())
            .map(|(id, (sc, _))| (id.clone(), vec![SmtF::from_int(*sc)]))
            .collect();
        let prev: Vec<(Vec<u8>, Vec<SmtF>)> = ids
            .iter()
            .zip(statuses.iter())
            .map(|(id, (_, sp))| (id.clone(), vec![SmtF::from_int(*sp)]))
            .collect();

        let tree_cur = SparseMerkleTree::build(D, &cur);
        let tree_prev = SparseMerkleTree::build(D, &prev);
        let h = tree_cur.hasher();

        let paths: Vec<AssetPath> = ids
            .iter()
            .zip(statuses.iter())
            .map(|(id, (sc, sp))| {
                let idd = h.id_digest(id);
                let pos = h.path_of(id, D);
                let inc_cur = tree_cur.prove(id);
                let inc_prev = tree_prev.prove(id);
                AssetPath {
                    id_digest: idd,
                    position: pos,
                    status_cur: Val::from_int(*sc),
                    status_prev: Val::from_int(*sp),
                    siblings_cur: inc_cur.path().siblings.clone(),
                    siblings_prev: inc_prev.path().siblings.clone(),
                }
            })
            .collect();

        (tree_cur, tree_prev, paths)
    }

    // Helper to get the siblings from an inclusion proof.
    trait InclusionPath {
        fn path(&self) -> &acp_smt::MerklePath;
    }
    impl InclusionPath for acp_smt::CoverageProof {
        fn path(&self) -> &acp_smt::MerklePath {
            match self {
                acp_smt::CoverageProof::Inclusion { path, .. } => path,
                _ => panic!("expected inclusion"),
            }
        }
    }

    #[test]
    fn honest_monotonic_paths_satisfy_constraints() {
        let statuses = [(0u64, 0u64), (1, 0), (2, 1), (2, 2)];
        let (tcur, tprev, paths) = asset_paths(&statuses);
        let trace = generate_trace(D, next_pow2(paths.len() * D), &paths);
        check_statement(trace, tcur.root(), tprev.root(), D, &paths);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn forged_regression_rejected() {
        let mut statuses = [(0u64, 0u64), (1, 0), (2, 1), (2, 2)];
        // Flip the third asset to a regression.
        statuses[2] = (1, 2);
        let (tcur, tprev, paths) = asset_paths(&statuses);
        let trace = generate_trace(D, next_pow2(paths.len() * D), &paths);
        check_statement(trace, tcur.root(), tprev.root(), D, &paths);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn mismatched_position_rejected() {
        let statuses = [(0u64, 0u64), (1, 0), (2, 1), (2, 2)];
        let (tcur, tprev, mut paths) = asset_paths(&statuses);
        // Swap the previous sibling set for one asset, so the previous path
        // does not hash to the correct root at the same position.
        paths[0].siblings_prev = paths[1].siblings_prev.clone();
        let trace = generate_trace(D, next_pow2(paths.len() * D), &paths);
        check_statement(trace, tcur.root(), tprev.root(), D, &paths);
    }

    #[test]
    fn honest_proof_proves_and_verifies() {
        let statuses = [(0u64, 0u64), (1, 0), (2, 1), (2, 2)];
        let (tcur, tprev, paths) = asset_paths(&statuses);
        let m = prove(tcur.root(), tprev.root(), D, &paths);
        assert_eq!(m.depth, D);
        assert!(m.proof_bytes > 0);
    }
}
