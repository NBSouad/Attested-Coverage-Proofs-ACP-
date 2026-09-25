//! In-circuit ACP relation, hashing layer.
//!
//! The dominant in-circuit cost of an ACP coverage proof is verifying the
//! Poseidon2 compressions along each sampled identifier's Merkle path: `q`
//! inclusion/absence proofs of depth `D` require `q * D` width-8 Poseidon2
//! permutations. This crate measures a transparent FRI/STARK over exactly that
//! many Poseidon2 permutations, on the Goldilocks field, using Plonky3's
//! `Poseidon2Air` and `uni-stark`.
//!
//! What this measures and what it does not:
//! * **Measured here:** end-to-end transparent-STARK prove time, verify time,
//!   and proof size for the Poseidon2-permutation work of `q` depth-`D` paths,
//!   at the real Goldilocks round structure (width 8, S-box degree 7, 8 full +
//!   22 partial rounds) and a 100-bit conjectured-soundness FRI configuration.
//!   Poseidon2 is the dominant cost of the relation, so these numbers are
//!   representative of the inclusion/absence circuit's proving cost.
//! * The glue constraints that turn a batch of independent permutations into a
//!   *bound* Merkle-path relation --- path-bit booleanity, sibling ordering, and
//!   leaf/root/position binding to public inputs --- are implemented for a single
//!   path (`q = 1`) in [`bind`] and for batched `q > 1` paths in [`bind_batch`].
//!   The single-path version uses **11 extra columns on top of the 180
//!   Poseidon2 columns (a ~6% column overhead)**, not the sub-1% an earlier
//!   estimate assumed.  In-circuit absence-witness verification remains future
//!   work.
//!
//! Round constants: the `measure` benchmark samples them (cost-faithful:
//! proving time and size depend only on trace dimensions and round counts, not
//! on constant values). Separately, [`aligned_constants`] returns the constants
//! that exactly match `acp-smt`'s `default_goldilocks_poseidon2_8`, so the
//! in-circuit permutation equals the out-of-circuit hash; the test
//! `aligned_air_matches_smt_permutation` verifies this equality (the foundation
//! for in-AIR binding of a real acp-smt Merkle path to its committed root).

pub mod bind;
pub mod bind_batch;
pub mod blind;
pub mod mono;

use std::time::Instant;

use p3_air::BaseAir;
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::Field;
use p3_fri::{FriParameters, HidingFriPcs, TwoAdicFriPcs};
use p3_goldilocks::{
    GenericPoseidon2LinearLayersGoldilocks, Goldilocks, Poseidon2Goldilocks,
    GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL, GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL,
    GOLDILOCKS_POSEIDON2_RC_8_INTERNAL,
};
use p3_merkle_tree::{MerkleTreeHidingMmcs, MerkleTreeMmcs};
use p3_poseidon2_air::{Poseidon2Air, RoundConstants};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig};
use rand::rngs::SmallRng;
use rand::SeedableRng;

/// Round constants for the in-circuit Poseidon2 AIR, **aligned to the exact
/// constants used by `default_goldilocks_poseidon2_8`** (the permutation that
/// `acp-smt` hashes with). With these constants the AIR computes the identical
/// width-8 Goldilocks permutation as the out-of-circuit SMT, so a Merkle path
/// produced by `acp-smt` verifies in circuit. (The `measure` benchmark above
/// uses sampled constants because proving cost is independent of constant
/// values; binding to a real `acp-smt` commitment requires these aligned ones.)
pub fn aligned_constants() -> RoundConstants<Val, WIDTH, HALF_FULL_ROUNDS, PARTIAL_ROUNDS> {
    RoundConstants::new(
        GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL,
        GOLDILOCKS_POSEIDON2_RC_8_INTERNAL,
        GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL,
    )
}

// --- Goldilocks Poseidon2 round structure (width 8) ---
const WIDTH: usize = 8;
const SBOX_DEGREE: u64 = 7;
const SBOX_REGISTERS: usize = 1;
const HALF_FULL_ROUNDS: usize = 4;
const PARTIAL_ROUNDS: usize = 22;

// --- STARK config over Goldilocks (mirrors Plonky3's reference setup) ---
type Val = Goldilocks;
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
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;
type MyAir = Poseidon2Air<
    Val,
    GenericPoseidon2LinearLayersGoldilocks,
    WIDTH,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS,
    PARTIAL_ROUNDS,
>;

/// The SMT depth the prototype uses; one path = `DEPTH` permutations.
pub const DEPTH: usize = 48;

/// One STARK measurement.
#[derive(Clone, Debug)]
pub struct Measurement {
    pub num_perms: usize,
    pub trace_cols: usize,
    pub trace_cells: usize,
    pub prove_secs: f64,
    pub verify_secs: f64,
    pub proof_bytes: usize,
    pub conjectured_bits: usize,
}

/// Round `n` up to the next power of two (the trace height must be a power of 2).
pub fn next_pow2(n: usize) -> usize {
    n.max(1).next_power_of_two()
}

/// Permutations needed for `q` Merkle paths of depth `DEPTH`.
pub fn perms_for_paths(q: usize) -> usize {
    q * DEPTH
}

/// Prove and verify a STARK over `num_perms` Poseidon2 permutations
/// (`num_perms` must be a power of two), returning timing/size measurements.
pub fn measure(num_perms: usize) -> Measurement {
    assert!(num_perms.is_power_of_two(), "num_perms must be a power of two");

    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let challenger = Challenger::new(perm);

    // The Poseidon2 AIR reports max_constraint_degree = SBOX_DEGREE = 7, so the
    // quotient is split into next_pow2(7-1) = 8 chunks and must be committed at
    // a blowup of >= 8 (log_blowup >= 3). The `new_benchmark` preset uses
    // log_blowup = 1 (fine only for degree<=3 AIRs), so we set FRI params
    // explicitly. With log_blowup=3 and 28 queries + 16 PoW bits the conjectured
    // FRI soundness is 3*28 + 16 = 100 bits.
    let fri_params = FriParameters {
        log_blowup: 3,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 28,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
    };
    let conjectured_bits = fri_params.conjectured_soundness_bits();
    let log_blowup = fri_params.log_blowup;

    let constants = RoundConstants::from_rng(&mut rng);
    let air: MyAir = Poseidon2Air::new(constants);
    let trace_cols = air.width();

    let trace = air.generate_trace_rows(num_perms, log_blowup);

    let pcs = Pcs::new(dft, val_mmcs, fri_params);
    let config = MyConfig::new(pcs, challenger);

    let t = Instant::now();
    let proof = prove(&config, &air, trace, &[]);
    let prove_secs = t.elapsed().as_secs_f64();

    let proof_bytes = postcard::to_allocvec(&proof)
        .expect("serialize proof")
        .len();

    let t = Instant::now();
    verify(&config, &air, &proof, &[]).expect("verification failed");
    let verify_secs = t.elapsed().as_secs_f64();

    Measurement {
        num_perms,
        trace_cols,
        trace_cells: num_perms * trace_cols,
        prove_secs,
        verify_secs,
        proof_bytes,
        conjectured_bits,
    }
}

// --- Hiding (zero-knowledge) configuration ------------------------------
// The measurements above use a non-hiding FRI commitment, which is the
// standard configuration for cost measurement but does not hide the witness.
// The types below swap in Plonky3's hiding stack --- a salted Merkle MMCS and
// a hiding FRI PCS that interleaves random rows and appends random codewords
// --- so that the proof satisfies the zero-knowledge property assumed by A5.
// The FRI soundness accounting is unchanged: conjectured soundness is
// `log_blowup * num_queries + query_proof_of_work_bits`, independent of
// hiding, so both configurations sit at 100 bits.

/// Salt elements per leaf. Goldilocks is a 64-bit field, so four elements
/// carry 256 bits of blinding entropy per committed leaf.
const SALT_ELEMS: usize = 4;

/// Random codewords appended by the hiding PCS (matches Plonky3's own
/// hiding-configuration tests).
const NUM_RANDOM_CODEWORDS: usize = 4;

type ZkValMmcs =
    MerkleTreeHidingMmcs<ValPacking, ValPacking, MyHash, MyCompress, SmallRng, 2, 4, SALT_ELEMS>;
type ZkChallengeMmcs = ExtensionMmcs<Val, Challenge, ZkValMmcs>;
type ZkPcs = HidingFriPcs<Val, Dft, ZkValMmcs, ZkChallengeMmcs, SmallRng>;
type ZkConfig = StarkConfig<ZkPcs, Challenge, Challenger>;

/// As [`measure`], but with the hiding commitment stack, so the resulting
/// proof is zero-knowledge rather than merely succinct.
///
/// The hiding PCS interleaves the trace with random rows (doubling committed
/// height) and appends `NUM_RANDOM_CODEWORDS` random columns, so this is
/// strictly more expensive than [`measure`]; the difference is the price of
/// the zero-knowledge property.
pub fn measure_zk(num_perms: usize) -> Measurement {
    assert!(num_perms.is_power_of_two(), "num_perms must be a power of two");

    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ZkValMmcs::new(hash, compress, 0, SmallRng::seed_from_u64(2));
    let challenge_mmcs = ZkChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let challenger = Challenger::new(perm);

    let fri_params = FriParameters {
        log_blowup: 3,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 28,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
    };
    let conjectured_bits = fri_params.conjectured_soundness_bits();
    let log_blowup = fri_params.log_blowup;

    let constants = RoundConstants::from_rng(&mut rng);
    let air: MyAir = Poseidon2Air::new(constants);
    let trace_cols = air.width();
    let trace = air.generate_trace_rows(num_perms, log_blowup);

    let pcs = ZkPcs::new(
        dft,
        val_mmcs,
        fri_params,
        NUM_RANDOM_CODEWORDS,
        SmallRng::seed_from_u64(3),
    );
    let config = ZkConfig::new(pcs, challenger);

    let t = Instant::now();
    let proof = prove(&config, &air, trace, &[]);
    let prove_secs = t.elapsed().as_secs_f64();

    let proof_bytes = postcard::to_allocvec(&proof)
        .expect("serialize proof")
        .len();

    let t = Instant::now();
    verify(&config, &air, &proof, &[]).expect("verification failed");
    let verify_secs = t.elapsed().as_secs_f64();

    Measurement {
        num_perms,
        trace_cols,
        trace_cells: num_perms * trace_cols,
        prove_secs,
        verify_secs,
        proof_bytes,
        conjectured_bits,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hiding_config_proves_and_verifies() {
        // The zero-knowledge configuration must still produce accepting proofs;
        // `measure_zk` panics if verification fails.
        let m = measure_zk(1 << 6);
        assert_eq!(m.conjectured_bits, 100, "hiding must not change FRI soundness");
        assert!(m.proof_bytes > 0);
    }

    #[test]
    fn aligned_air_matches_smt_permutation() {
        // Phase 1 (in-AIR binding): the aligned AIR must compute the IDENTICAL
        // width-8 Goldilocks permutation as `default_goldilocks_poseidon2_8`,
        // which is the permutation `acp-smt` hashes with. If this holds, a real
        // acp-smt Merkle path verifies under the AIR's Poseidon2 constraints.
        use core::borrow::BorrowMut;
        use core::mem::MaybeUninit;
        use p3_field::integers::QuotientMap;
        use p3_goldilocks::default_goldilocks_poseidon2_8;
        use p3_poseidon2_air::{generate_trace_rows_for_perm, num_cols, Poseidon2Cols};
        use p3_symmetric::Permutation;
        use rand::Rng;

        let consts = aligned_constants();
        let reference = default_goldilocks_poseidon2_8();
        let mut rng = SmallRng::seed_from_u64(7);
        let ncols =
            num_cols::<WIDTH, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>();

        for _ in 0..200 {
            let input: [Goldilocks; WIDTH] =
                core::array::from_fn(|_| Goldilocks::from_int(rng.next_u64()));
            let expected = reference.permute(input);

            let mut row: Vec<MaybeUninit<Goldilocks>> =
                (0..ncols).map(|_| MaybeUninit::uninit()).collect();
            let cols: &mut Poseidon2Cols<
                MaybeUninit<Goldilocks>,
                WIDTH,
                SBOX_DEGREE,
                SBOX_REGISTERS,
                HALF_FULL_ROUNDS,
                PARTIAL_ROUNDS,
            > = row.as_mut_slice().borrow_mut();
            generate_trace_rows_for_perm::<
                Goldilocks,
                GenericPoseidon2LinearLayersGoldilocks,
                WIDTH,
                SBOX_DEGREE,
                SBOX_REGISTERS,
                HALF_FULL_ROUNDS,
                PARTIAL_ROUNDS,
            >(cols, input, &consts);

            let out: [Goldilocks; WIDTH] = core::array::from_fn(|i| unsafe {
                cols.ending_full_rounds[HALF_FULL_ROUNDS - 1].post[i].assume_init()
            });
            assert_eq!(
                out, expected,
                "aligned AIR permutation must equal default_goldilocks_poseidon2_8"
            );
        }
    }

    #[test]
    fn small_stark_proves_and_verifies() {
        // 2^8 permutations: small but exercises the full prove/verify path.
        let m = measure(1 << 8);
        assert!(m.prove_secs > 0.0);
        assert!(m.proof_bytes > 0);
        assert_eq!(m.num_perms, 256);
        // 100-bit conjectured FRI soundness for the benchmark parameters.
        assert!(m.conjectured_bits >= 100, "got {} bits", m.conjectured_bits);
    }
}
