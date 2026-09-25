//! Batched in-AIR binding of `q` Merkle paths to a public commitment.
//!
//! This extends [`crate::bind`] to a single STARK proof that binds `q` sampled
//! paths to the same commitment `C_\Sigma`.  The per-sample public inputs
//! (position and in-circuit identifier digest) are carried in a preprocessed
//! trace, so the main trace needs only one public value: the Merkle root.
//!
//! The trace has `q * depth` real rows, padded to the next power of two.
//! Each row belongs to one sample ("segment"); the preprocessed trace carries
//! the segment metadata.  The constraint system is the same as the single-path
//! binding, but with the public inputs selected row-by-row from the
//! preprocessed columns.

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
use crate::bind::{
    A_OFF, C_ACC, C_BIT, C_CUR, C_POW, C_SIB, DIGEST, L_OFF, P2_COLS, TOTAL_COLS,
};

type P2Air = Poseidon2Air<
    Val,
    GenericPoseidon2LinearLayersGoldilocks,
    WIDTH,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS,
    PARTIAL_ROUNDS,
>;

// Preprocessed columns, one per row:
const PP_POS: usize = 0; // position, valid on the last row of each segment
const PP_IDD: usize = 1; // identifier digest, valid on the first row of each segment
const PP_BIT: usize = PP_IDD + DIGEST; // path bit at this level
const PP_IS_FIRST: usize = PP_BIT + 1; // first row of a real segment
const PP_IS_LAST: usize = PP_IS_FIRST + 1; // last row of a real segment
const PP_IS_REAL: usize = PP_IS_LAST + 1; // real row (not padding)
const PREPROCESSED_WIDTH: usize = PP_IS_REAL + 1;

/// Public values: the Merkle root `C_\Sigma`.
const NUM_PUBLIC: usize = DIGEST;
const P_ROOT: usize = 0;

/// Public data for one sampled path.
#[derive(Clone, Debug)]
pub struct PathPublic {
    pub id_digest: [Val; DIGEST],
    pub position: u64,
}

/// One sampled path, with the siblings the prover must supply.
#[derive(Clone, Debug)]
pub struct SamplePath {
    pub id_digest: [Val; DIGEST],
    pub position: u64,
    pub siblings: Vec<[Val; DIGEST]>,
}

impl From<&SamplePath> for PathPublic {
    fn from(p: &SamplePath) -> Self {
        Self {
            id_digest: p.id_digest,
            position: p.position,
        }
    }
}

/// AIR proving that `q` Merkle paths hash to `root`.
pub struct BindBatchAir {
    pub root: [Val; DIGEST],
    pub depth: usize,
    pub q: usize,
    pub trace_height: usize,
    preprocessed: RowMajorMatrix<Val>,
}

impl BindBatchAir {
    pub fn from_public_inputs(
        root: [Val; DIGEST],
        depth: usize,
        inputs: &[PathPublic],
    ) -> Self {
        assert!(depth >= 1 && depth <= 48, "depth must be between 1 and 48");
        let trace_height = next_pow2(inputs.len() * depth);
        let preprocessed = build_preprocessed_trace(depth, trace_height, inputs);
        Self {
            root,
            depth,
            q: inputs.len(),
            trace_height,
            preprocessed,
        }
    }

    pub fn from_paths(root: [Val; DIGEST], depth: usize, paths: &[SamplePath]) -> Self {
        let inputs: Vec<PathPublic> = paths.iter().map(PathPublic::from).collect();
        Self::from_public_inputs(root, depth, &inputs)
    }
}

impl BaseAir<Val> for BindBatchAir {
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
}

impl<AB: AirBuilder<F = Val>> Air<AB> for BindBatchAir {
    fn eval(&self, builder: &mut AB) {
        // (1) Poseidon2 round constraints for the path and leaf blocks.
        for off in [A_OFF, L_OFF] {
            let mut sub: SubAirBuilder<'_, AB, P2Air, AB::Var> =
                SubAirBuilder::new(builder, off..off + P2_COLS);
            let p2_air = P2Air::new(aligned_constants());
            p2_air.eval(&mut sub);
        }

        // (2) Linking, ordering, boundary and position constraints.
        let (loc, nxt) = {
            let main = builder.main();
            (main.current_slice().to_vec(), main.next_slice().to_vec())
        };
        let prep = builder.preprocessed().current_slice().to_vec();
        let prep_next = builder.preprocessed().next_slice().to_vec();
        let pis = builder.public_values().to_vec();

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

        // C_BIT must equal the preprocessed path bit on real rows.
        builder.assert_zero(is_real.clone() * (loc[C_BIT].into() - bit.clone()));

        // Child ordering: P2 path input is (cur, sib) or (sib, cur) according to bit.
        for j in 0..DIGEST {
            let cur = loc[C_CUR + j];
            let sib = loc[C_SIB + j];
            let one_minus_bit = AB::Expr::ONE - bit.clone();
            let left = one_minus_bit.clone() * cur.into() + bit.clone() * sib.into();
            let right = one_minus_bit * sib.into() + bit.clone() * cur.into();
            builder.assert_zero(is_real.clone() * (p2_loc.inputs[j].into() - left));
            builder.assert_zero(is_real.clone() * (p2_loc.inputs[DIGEST + j].into() - right));
        }

        // First row of each real segment: derive the leaf and initialize accumulators.
        let first_factor = is_real.clone() * is_first;
        for j in 0..DIGEST {
            builder.assert_zero(first_factor.clone() * (lf.inputs[j].into() - idd[j].clone()));
            builder.assert_zero(first_factor.clone() * lf.inputs[DIGEST + j].into());
            builder.assert_zero(
                first_factor.clone() * (loc[C_CUR + j].into() - out_lf[j].into()),
            );
        }
        builder.assert_zero(first_factor.clone() * (loc[C_POW].into() - AB::Expr::ONE));
        builder.assert_zero(first_factor * (loc[C_ACC].into() - bit));

        // Transition (next row exists and is a non-first real row): carry the chain.
        let trans_factor = nxt_is_real * (AB::Expr::ONE - nxt_is_first);
        {
            let mut tr = builder.when_transition();
            for j in 0..DIGEST {
                tr.assert_zero(
                    trans_factor.clone() * (nxt[C_CUR + j].into() - out_loc[j].into()),
                );
            }
            tr.assert_zero(
                trans_factor.clone()
                    * (nxt[C_POW].into() - loc[C_POW].into() * AB::Expr::TWO),
            );
            tr.assert_zero(
                trans_factor
                    * (nxt[C_ACC].into() - loc[C_ACC].into() - nxt_bit * nxt[C_POW].into()),
            );
        }

        // Last row of each real segment: the path output is the public root and acc = position.
        let last_factor = is_real * is_last;
        for j in 0..DIGEST {
            builder.assert_zero(
                last_factor.clone() * (out_loc[j].into() - pis[P_ROOT + j].into()),
            );
        }
        builder.assert_zero(last_factor * (loc[C_ACC].into() - pos));
    }
}

fn build_preprocessed_trace(
    depth: usize,
    trace_height: usize,
    inputs: &[PathPublic],
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

/// Build the execution trace for `q` paths.
pub fn generate_trace(
    depth: usize,
    trace_height: usize,
    paths: &[SamplePath],
) -> RowMajorMatrix<Val> {
    assert!(depth >= 1 && depth <= 48);
    assert!(trace_height >= paths.len() * depth);

    let consts = aligned_constants();
    let mut values = Val::zero_vec(trace_height * TOTAL_COLS);

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

    for (seg, path) in paths.iter().enumerate() {
        assert_eq!(path.siblings.len(), depth, "siblings length must equal depth");

        // Leaf hash for this segment.
        let mut leaf_state = [Val::ZERO; WIDTH];
        leaf_state[..DIGEST].copy_from_slice(&path.id_digest);
        let mut cur = {
            let mut scratch = Val::zero_vec(TOTAL_COLS);
            fill(&mut scratch, L_OFF, leaf_state)
        };

        let mut acc = Val::ZERO;
        let mut pow = Val::ONE;

        for (i, sib) in path.siblings.iter().enumerate() {
            let row = seg * depth + i;
            let row_base = row * TOTAL_COLS;
            let bit = (path.position >> i) & 1;

            let mut a_state = [Val::ZERO; WIDTH];
            let (left, right) = if bit == 0 { (cur, *sib) } else { (*sib, cur) };
            a_state[..DIGEST].copy_from_slice(&left);
            a_state[DIGEST..].copy_from_slice(&right);

            values[row_base + C_CUR..row_base + C_CUR + DIGEST].copy_from_slice(&cur);
            values[row_base + C_SIB..row_base + C_SIB + DIGEST].copy_from_slice(sib);

            let out = fill(&mut values[row_base..row_base + TOTAL_COLS], A_OFF, a_state);

            let lstate = if i == 0 { leaf_state } else { [Val::ZERO; WIDTH] };
            let _ = fill(&mut values[row_base..row_base + TOTAL_COLS], L_OFF, lstate);

            if i > 0 {
                pow *= Val::TWO;
                acc += Val::from_bool(bit == 1) * pow;
            } else {
                acc = Val::from_bool(bit == 1);
            }
            values[row_base + C_BIT] = Val::from_bool(bit == 1);
            values[row_base + C_ACC] = acc;
            values[row_base + C_POW] = pow;

            cur = out;
        }
    }

    // Padded rows must satisfy the P2 round constraints; fill them with the
    // zero-state permutation output.
    let zero_state = [Val::ZERO; WIDTH];
    for row in paths.len() * depth..trace_height {
        let row_base = row * TOTAL_COLS;
        let _ = fill(&mut values[row_base..row_base + TOTAL_COLS], A_OFF, zero_state);
        let _ = fill(&mut values[row_base..row_base + TOTAL_COLS], L_OFF, zero_state);
    }

    RowMajorMatrix::new(values, TOTAL_COLS)
}

// --- STARK configurations -------------------------------------------------

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
type BindBatchConfig = StarkConfig<Pcs, Challenge, Challenger>;

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

fn plain_config() -> (BindBatchConfig, usize) {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri_params = make_fri_params(challenge_mmcs);
    let conjectured_bits = fri_params.conjectured_soundness_bits();
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri_params);
    (BindBatchConfig::new(pcs, Challenger::new(perm)), conjectured_bits)
}

type ZkValMmcs =
    MerkleTreeHidingMmcs<ValPacking, ValPacking, MyHash, MyCompress, SmallRng, 2, 4, 4>;
type ZkChallengeMmcs = ExtensionMmcs<Val, Challenge, ZkValMmcs>;
type ZkPcs = HidingFriPcs<Val, Dft, ZkValMmcs, ZkChallengeMmcs, SmallRng>;
type ZkBindBatchConfig = StarkConfig<ZkPcs, Challenge, Challenger>;

fn hiding_config() -> (ZkBindBatchConfig, usize) {
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
    (ZkBindBatchConfig::new(pcs, Challenger::new(perm)), conjectured_bits)
}

/// Result of proving `q` bound paths.
#[derive(Clone, Debug)]
pub struct BatchBindMeasurement {
    pub q: usize,
    pub depth: usize,
    pub trace_cols: usize,
    pub trace_rows: usize,
    pub prove_secs: f64,
    pub verify_secs: f64,
    pub proof_bytes: usize,
    pub conjectured_bits: usize,
}

fn prove_or_verify_paths(
    root: [Val; DIGEST],
    depth: usize,
    paths: &[SamplePath],
    zk: bool,
) -> BatchBindMeasurement {
    use std::time::Instant;

    let trace_height = next_pow2(paths.len() * depth);
    let trace = generate_trace(depth, trace_height, paths);

    let air = BindBatchAir::from_paths(root, depth, paths);
    let public_values = root.to_vec();

    let degree_bits = log2_strict_usize(trace_height);

    let (prove_secs, verify_secs, proof_bytes, conjectured_bits) = if zk {
        let (cfg, conjectured_bits) = hiding_config();
        let (ppd, vk) =
            setup_preprocessed::<ZkBindBatchConfig, _>(&cfg, &air, degree_bits).unwrap();

        let t = Instant::now();
        let proof = prove_with_preprocessed(&cfg, &air, trace, &public_values, Some(&ppd));
        let prove_secs = t.elapsed().as_secs_f64();

        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize").len();

        let t = Instant::now();
        verify_with_preprocessed(&cfg, &air, &proof, &public_values, Some(&vk))
            .expect("verification failed");
        let verify_secs = t.elapsed().as_secs_f64();

        (prove_secs, verify_secs, proof_bytes, conjectured_bits)
    } else {
        let (cfg, conjectured_bits) = plain_config();
        let (ppd, vk) =
            setup_preprocessed::<BindBatchConfig, _>(&cfg, &air, degree_bits).unwrap();

        let t = Instant::now();
        let proof = prove_with_preprocessed(&cfg, &air, trace, &public_values, Some(&ppd));
        let prove_secs = t.elapsed().as_secs_f64();

        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize").len();

        let t = Instant::now();
        verify_with_preprocessed(&cfg, &air, &proof, &public_values, Some(&vk))
            .expect("verification failed");
        let verify_secs = t.elapsed().as_secs_f64();

        (prove_secs, verify_secs, proof_bytes, conjectured_bits)
    };

    BatchBindMeasurement {
        q: paths.len(),
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

/// Prove and verify `q` bound paths (plain configuration).
pub fn prove_paths(
    root: [Val; DIGEST],
    depth: usize,
    paths: &[SamplePath],
) -> BatchBindMeasurement {
    prove_or_verify_paths(root, depth, paths, false)
}

/// Prove and verify `q` bound paths (hiding / zero-knowledge configuration).
pub fn prove_paths_zk(
    root: [Val; DIGEST],
    depth: usize,
    paths: &[SamplePath],
) -> BatchBindMeasurement {
    prove_or_verify_paths(root, depth, paths, true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use acp_smt::{CoverageProof, SparseMerkleTree};

    fn paths_from_tree(q: usize, depth: usize) -> Vec<SamplePath> {
        let entries: Vec<(Vec<u8>, Vec<Val>)> = (0..1024)
            .map(|i| (format!("asset-{i}.svc.example.gov").into_bytes(), Vec::new()))
            .collect();
        let tree = SparseMerkleTree::build(depth, &entries);
        let root = tree.root();
        let _ = root; // used in tests
        (0..q)
            .map(|j| {
                let id = entries[(j * 37) % entries.len()].0.clone();
                let pos = tree.hasher().path_of(&id, depth);
                let idd = tree.hasher().id_digest(&id);
                let sibs = match tree.prove(&id) {
                    CoverageProof::Inclusion { path, .. } => path.siblings,
                    _ => panic!("expected inclusion proof"),
                };
                SamplePath {
                    id_digest: idd,
                    position: pos,
                    siblings: sibs,
                }
            })
            .collect()
    }

    #[test]
    fn two_batched_bound_paths_plain() {
        let depth = 32;
        let paths = paths_from_tree(2, depth);
        let root = {
            let entries: Vec<(Vec<u8>, Vec<Val>)> = (0..1024)
                .map(|i| (format!("asset-{i}.svc.example.gov").into_bytes(), Vec::new()))
                .collect();
            let tree = SparseMerkleTree::build(depth, &entries);
            tree.root()
        };
        let m = prove_paths(root, depth, &paths);
        assert!(m.proof_bytes > 0);
        assert_eq!(m.trace_rows, next_pow2(2 * depth));
    }

    #[test]
    fn q10_batched_bound_paths_plain() {
        let depth = 32;
        let paths = paths_from_tree(10, depth);
        let root = {
            let entries: Vec<(Vec<u8>, Vec<Val>)> = (0..1024)
                .map(|i| (format!("asset-{i}.svc.example.gov").into_bytes(), Vec::new()))
                .collect();
            let tree = SparseMerkleTree::build(depth, &entries);
            tree.root()
        };
        let m = prove_paths(root, depth, &paths);
        assert!(m.proof_bytes > 0);
        assert_eq!(m.trace_rows, next_pow2(10 * depth));
    }
}
