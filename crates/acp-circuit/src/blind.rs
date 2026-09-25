//! Blind ACP: a coverage proof that hides *which* branch each sample took.
//!
//! The bound circuit of [`crate::bind`] proves inclusion of a sampled
//! identifier, which tells the verifier that the identifier *is* in the
//! prover's inventory. Across an epoch that discloses the deployment-bit vector
//! `b_S`, and across an audit chain those bits accumulate. Blind ACP removes
//! them: the circuit proves the disjunction
//!
//! > "either the sampled identifier is in my committed inventory `C_Sigma`,
//! >  **or** it is absent from the signed registry `R_reg`"
//!
//! with the branch selector held in the *witness*, so the statement itself no
//! longer says which disjunct holds. The public inputs are only
//! `(C_Sigma, R_reg, pos, id_digest)` --- every one of which the verifier
//! already knows, since the sampled identifier is public.
//!
//! # Structure
//!
//! Each row carries three Poseidon2 blocks, all evaluated by Plonky3's own
//! `Poseidon2Air` over disjoint column ranges via `SubAirBuilder`:
//!
//! | columns        | role                                        |
//! |----------------|---------------------------------------------|
//! | `[0, 180)`     | chain A: one level of the inventory path     |
//! | `[180, 360)`   | chain B: one level of the registry path      |
//! | `[360, 540)`   | leaf hash `H(id_digest ‖ value)` (row 0 only)|
//!
//! Both chains are computed for every sample, so the trace shape is identical
//! whichever branch is real; the unselected chain is a consistent hash chain
//! over dummy siblings whose root is simply left unconstrained.
//!
//! # Why the leaf binding matters
//!
//! Constraining only "some leaf at `pos` chains to `C_Sigma`" would be unsound:
//! when the identifier is *absent* from the inventory the leaf at `pos` is the
//! empty leaf, and that chain verifies against `C_Sigma` perfectly well. A
//! prover could then claim the inclusion branch for a non-member. We therefore
//! force the inclusion chain to start at `H(id_digest ‖ value)`, computed in
//! circuit from the *public* `id_digest`. This binds the leaf to the sampled
//! identifier, and as a side effect makes the empty-leaf attack impossible
//! without any separate non-emptiness gadget.
//!
//! # Scope and caveats
//!
//! * One sample per proof (`q = 1`), as in [`crate::bind`].
//! * `value` is empty here, so the leaf hash is a single permutation; a
//!   `k`-element value costs `ceil(k/4)` further permutations.
//! * The registry signature is verified **out of circuit** (it is public and
//!   shared by every sample in an epoch); only the non-membership path is
//!   in circuit.
//! * Hiding `b_S` from the *statement* is what this circuit achieves. Full
//!   zero knowledge additionally requires a hiding polynomial commitment
//!   (`HidingFriPcs`); the measurements here use the same non-hiding FRI
//!   configuration as the rest of the prototype, so they report cost, not a
//!   zero-knowledge guarantee.
//! * **Not externally reviewed. Do not treat the constraint system as
//!   audited.**

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
use p3_poseidon2_air::{generate_trace_rows_for_perm, Poseidon2Air, Poseidon2Cols};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig, SubAirBuilder};
use rand::rngs::SmallRng;
use rand::SeedableRng;

use crate::bind::{DIGEST, P2_COLS};
use crate::{
    aligned_constants, Val, HALF_FULL_ROUNDS, PARTIAL_ROUNDS, SBOX_DEGREE, SBOX_REGISTERS, WIDTH,
};

// Poseidon2 block offsets.
const A_OFF: usize = 0;
const B_OFF: usize = P2_COLS;
const L_OFF: usize = 2 * P2_COLS;
const LINK: usize = 3 * P2_COLS;

// Linking columns.
const C_CURA: usize = LINK;
const C_SIBA: usize = LINK + DIGEST;
const C_CURB: usize = LINK + 2 * DIGEST;
const C_SIBB: usize = LINK + 3 * DIGEST;
const C_BIT: usize = LINK + 4 * DIGEST;
const C_ACC: usize = LINK + 4 * DIGEST + 1;
const C_POW: usize = LINK + 4 * DIGEST + 2;
const C_BSEL: usize = LINK + 4 * DIGEST + 3;

/// Total trace width.
pub const TOTAL_COLS: usize = LINK + 4 * DIGEST + 4;

/// Public values: `C_Sigma(4) || R_reg(4) || pos(1) || id_digest(4)`.
pub const NUM_PUBLIC: usize = 3 * DIGEST + 1;
const P_CS: usize = 0;
const P_RREG: usize = DIGEST;
const P_POS: usize = 2 * DIGEST;
const P_IDD: usize = 2 * DIGEST + 1;

type P2Air = Poseidon2Air<
    Val,
    GenericPoseidon2LinearLayersGoldilocks,
    WIDTH,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS,
    PARTIAL_ROUNDS,
>;
type P2Cols<T> =
    Poseidon2Cols<T, WIDTH, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>;

/// AIR proving the inclusion-or-absence disjunction without revealing which.
pub struct BlindAcpAir {
    p2: P2Air,
}

impl Default for BlindAcpAir {
    fn default() -> Self {
        Self::new()
    }
}

impl BlindAcpAir {
    pub fn new() -> Self {
        Self {
            p2: Poseidon2Air::new(aligned_constants()),
        }
    }
}

impl BaseAir<Val> for BlindAcpAir {
    fn width(&self) -> usize {
        TOTAL_COLS
    }
    fn num_public_values(&self) -> usize {
        NUM_PUBLIC
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(SBOX_DEGREE as usize)
    }
}

impl<AB: AirBuilder<F = Val>> Air<AB> for BlindAcpAir {
    fn eval(&self, builder: &mut AB) {
        // Permutation constraints for all three blocks, on disjoint ranges.
        for off in [A_OFF, B_OFF, L_OFF] {
            let mut sub: SubAirBuilder<'_, AB, P2Air, AB::Var> =
                SubAirBuilder::new(builder, off..off + P2_COLS);
            self.p2.eval(&mut sub);
        }

        let (loc, nxt) = {
            let main = builder.main();
            (main.current_slice().to_vec(), main.next_slice().to_vec())
        };
        let pis: Vec<AB::PublicVar> = builder.public_values().to_vec();

        let a: &P2Cols<AB::Var> = loc[A_OFF..A_OFF + P2_COLS].borrow();
        let b: &P2Cols<AB::Var> = loc[B_OFF..B_OFF + P2_COLS].borrow();
        let l: &P2Cols<AB::Var> = loc[L_OFF..L_OFF + P2_COLS].borrow();
        let out_a = &a.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
        let out_b = &b.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
        let out_l = &l.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;

        let bit = loc[C_BIT];
        let acc = loc[C_ACC];
        let pow = loc[C_POW];
        let bsel = loc[C_BSEL];

        // Selector bits are boolean.
        builder.assert_zero(bit * (bit.into() - AB::Expr::ONE));
        builder.assert_zero(bsel * (bsel.into() - AB::Expr::ONE));

        // Child ordering for both chains, driven by the shared path bit: both
        // trees key positions by the same identifier hash, so one bit serves.
        for j in 0..DIGEST {
            let (ca, sa) = (loc[C_CURA + j], loc[C_SIBA + j]);
            let (cb, sb) = (loc[C_CURB + j], loc[C_SIBB + j]);
            let one = AB::Expr::ONE;
            builder.assert_eq(
                a.inputs[j],
                (one.clone() - bit.into()) * ca.into() + bit.into() * sa.into(),
            );
            builder.assert_eq(
                a.inputs[DIGEST + j],
                (one.clone() - bit.into()) * sa.into() + bit.into() * ca.into(),
            );
            builder.assert_eq(
                b.inputs[j],
                (one.clone() - bit.into()) * cb.into() + bit.into() * sb.into(),
            );
            builder.assert_eq(
                b.inputs[DIGEST + j],
                (one - bit.into()) * sb.into() + bit.into() * cb.into(),
            );
        }

        // First row.
        {
            let mut first = builder.when_first_row();
            first.assert_eq(pow, AB::Expr::ONE);
            first.assert_eq(acc, bit);

            // Leaf binding: the inventory chain starts at H(id_digest || value).
            // With an empty value the sponge absorbs id_digest into the rate and
            // permutes once, so the leaf-hash block's input is
            // [id_digest(4) || 0(4)] and its output is the leaf.
            for j in 0..DIGEST {
                first.assert_eq(l.inputs[j], pis[P_IDD + j]);
                first.assert_zero(l.inputs[DIGEST + j]);
                first.assert_eq(loc[C_CURA + j], out_l[j]);
                // The registry chain starts at the empty leaf, which is what
                // non-membership means for this sparse Merkle encoding.
                first.assert_zero(loc[C_CURB + j]);
            }
        }

        // Transition: both chains advance; the accumulator tracks the path
        // index; the branch selector is constant along the trace.
        {
            let n_bit = nxt[C_BIT];
            let mut tr = builder.when_transition();
            for j in 0..DIGEST {
                tr.assert_eq(nxt[C_CURA + j], out_a[j]);
                tr.assert_eq(nxt[C_CURB + j], out_b[j]);
            }
            tr.assert_eq(nxt[C_POW], pow.into() * AB::Expr::TWO);
            tr.assert_eq(nxt[C_ACC], acc.into() + n_bit.into() * nxt[C_POW].into());
            tr.assert_eq(nxt[C_BSEL], bsel);
        }

        // Last row: the accumulated bits are the public position, and exactly
        // the *selected* chain must reach its public root. The unselected
        // chain's root is unconstrained, which is what hides the branch.
        {
            let mut last = builder.when_last_row();
            last.assert_eq(acc, pis[P_POS]);
            for j in 0..DIGEST {
                last.assert_zero(bsel.into() * (out_a[j].into() - pis[P_CS + j].into()));
                last.assert_zero(
                    (AB::Expr::ONE - bsel.into()) * (out_b[j].into() - pis[P_RREG + j].into()),
                );
            }
        }
    }
}

/// Which branch the prover actually holds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Branch {
    /// The identifier is in the committed inventory.
    Inclusion,
    /// The identifier is absent from the signed registry.
    Absence,
}

/// Witness for one blind coverage proof.
pub struct BlindWitness {
    pub leaf: [Val; DIGEST],
    pub inv_siblings: Vec<[Val; DIGEST]>,
    pub reg_siblings: Vec<[Val; DIGEST]>,
    pub pos: u64,
    pub branch: Branch,
}

fn fill_perm(row: &mut [Val], off: usize, state: [Val; WIDTH]) -> [Val; DIGEST] {
    let consts = aligned_constants();
    {
        let slice = &mut row[off..off + P2_COLS];
        let uninit: &mut [MaybeUninit<Val>] = unsafe { core::mem::transmute(slice) };
        let cols: &mut P2Cols<MaybeUninit<Val>> = uninit.borrow_mut();
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
    let filled: &P2Cols<Val> = row[off..off + P2_COLS].borrow();
    let out = filled.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
    [out[0], out[1], out[2], out[3]]
}

/// Build the trace. Both chains are always computed; the unselected one runs
/// over the dummy siblings supplied by the caller and its root is ignored.
pub fn generate_trace(w: &BlindWitness, id_digest: [Val; DIGEST]) -> RowMajorMatrix<Val> {
    let depth = w.inv_siblings.len();
    assert_eq!(depth, w.reg_siblings.len(), "chains must have equal depth");
    assert!(depth.is_power_of_two(), "depth must be a power of two");
    assert!(depth <= 48, "position accumulator assumes depth <= 48");

    let mut values = Val::zero_vec(depth * TOTAL_COLS);

    // The inventory chain starts at the bound leaf; the registry chain starts
    // at the empty leaf.
    let mut cur_a = w.leaf;
    let mut cur_b = [Val::ZERO; DIGEST];
    let mut acc = Val::ZERO;
    let mut pow = Val::ONE;

    for i in 0..depth {
        let row = &mut values[i * TOTAL_COLS..(i + 1) * TOTAL_COLS];
        let bit = (w.pos >> i) & 1;
        let sa = w.inv_siblings[i];
        let sb = w.reg_siblings[i];

        let mut state_a = [Val::ZERO; WIDTH];
        let (la, ra) = if bit == 0 { (cur_a, sa) } else { (sa, cur_a) };
        state_a[..DIGEST].copy_from_slice(&la);
        state_a[DIGEST..].copy_from_slice(&ra);

        let mut state_b = [Val::ZERO; WIDTH];
        let (lb, rb) = if bit == 0 { (cur_b, sb) } else { (sb, cur_b) };
        state_b[..DIGEST].copy_from_slice(&lb);
        state_b[DIGEST..].copy_from_slice(&rb);

        // Leaf-hash block: meaningful on row 0, consistent filler elsewhere.
        let mut state_l = [Val::ZERO; WIDTH];
        if i == 0 {
            state_l[..DIGEST].copy_from_slice(&id_digest);
        }

        row[C_CURA..C_CURA + DIGEST].copy_from_slice(&cur_a);
        row[C_SIBA..C_SIBA + DIGEST].copy_from_slice(&sa);
        row[C_CURB..C_CURB + DIGEST].copy_from_slice(&cur_b);
        row[C_SIBB..C_SIBB + DIGEST].copy_from_slice(&sb);

        let out_a = fill_perm(row, A_OFF, state_a);
        let out_b = fill_perm(row, B_OFF, state_b);
        let _ = fill_perm(row, L_OFF, state_l);

        if i > 0 {
            pow *= Val::TWO;
            acc += Val::from_bool(bit == 1) * pow;
        } else {
            acc = Val::from_bool(bit == 1);
        }

        row[C_BIT] = Val::from_bool(bit == 1);
        row[C_ACC] = acc;
        row[C_POW] = pow;
        row[C_BSEL] = Val::from_bool(w.branch == Branch::Inclusion);

        cur_a = out_a;
        cur_b = out_b;
    }

    RowMajorMatrix::new(values, TOTAL_COLS)
}

/// Public statement `C_Sigma || R_reg || pos || id_digest`.
pub fn public_values(
    c_sigma: [Val; DIGEST],
    r_reg: [Val; DIGEST],
    pos: u64,
    id_digest: [Val; DIGEST],
) -> Vec<Val> {
    let mut pis = Vec::with_capacity(NUM_PUBLIC);
    pis.extend_from_slice(&c_sigma);
    pis.extend_from_slice(&r_reg);
    pis.push(Val::from_u64(pos));
    pis.extend_from_slice(&id_digest);
    pis
}

/// Evaluate the constraints directly against a claimed statement, panicking on
/// the first violation. Used by the tests: verifying a proof under altered
/// public values would fail regardless of our constraints, because `uni-stark`
/// absorbs public values into the Fiat--Shamir transcript.
pub fn check_statement(
    trace: RowMajorMatrix<Val>,
    c_sigma: [Val; DIGEST],
    r_reg: [Val; DIGEST],
    pos: u64,
    id_digest: [Val; DIGEST],
) {
    let air = BlindAcpAir::new();
    p3_air::check_constraints(
        &air,
        &trace,
        &public_values(c_sigma, r_reg, pos, id_digest),
    );
}

// --- STARK configuration (same FRI parameters as the rest of the prototype) ---
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
type BlindConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn config() -> BlindConfig {
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
    BlindConfig::new(pcs, Challenger::new(perm))
}

/// Timing/size of one blind coverage proof.
pub struct BlindMeasurement {
    pub depth: usize,
    pub trace_cols: usize,
    pub prove_secs: f64,
    pub verify_secs: f64,
    pub proof_bytes: usize,
}

/// Prove and verify one blind coverage proof.
pub fn prove_blind(
    w: &BlindWitness,
    id_digest: [Val; DIGEST],
    c_sigma: [Val; DIGEST],
    r_reg: [Val; DIGEST],
) -> BlindMeasurement {
    use std::time::Instant;
    let cfg = config();
    let air = BlindAcpAir::new();
    let trace = generate_trace(w, id_digest);
    let pis = public_values(c_sigma, r_reg, w.pos, id_digest);

    let t = Instant::now();
    let proof = prove(&cfg, &air, trace, &pis);
    let prove_secs = t.elapsed().as_secs_f64();
    let proof_bytes = postcard::to_allocvec(&proof).expect("serialize").len();

    let t = Instant::now();
    verify(&cfg, &air, &proof, &pis).expect("verification failed");
    let verify_secs = t.elapsed().as_secs_f64();

    BlindMeasurement {
        depth: w.inv_siblings.len(),
        trace_cols: TOTAL_COLS,
        prove_secs,
        verify_secs,
        proof_bytes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use acp_smt::{AcpHasher, CoverageProof, SparseMerkleTree, F as SmtF};
    use p3_matrix::Matrix;

    const D: usize = 32;

    struct World {
        inv: SparseMerkleTree,
        reg: SparseMerkleTree,
        deployed: Vec<Vec<u8>>,
        h: AcpHasher,
    }

    /// Honest world: the inventory and the registry both hold the deployed set.
    fn world() -> World {
        let deployed: Vec<Vec<u8>> = (0..64)
            .map(|i| format!("dep-{i}.svc.example.gov").into_bytes())
            .collect();
        let entries: Vec<(Vec<u8>, Vec<SmtF>)> =
            deployed.iter().map(|id| (id.clone(), Vec::new())).collect();
        World {
            inv: SparseMerkleTree::build(D, &entries),
            reg: SparseMerkleTree::build(D, &entries),
            deployed,
            h: AcpHasher::new(),
        }
    }

    fn dummy() -> Vec<[Val; DIGEST]> {
        vec![[Val::ZERO; DIGEST]; D]
    }

    fn siblings_of(p: &CoverageProof) -> Vec<[Val; DIGEST]> {
        match p {
            CoverageProof::Inclusion { path, .. } => path.siblings.clone(),
            CoverageProof::Absence { path } => path.siblings.clone(),
        }
    }

    #[test]
    fn honest_inclusion_satisfies_the_constraints() {
        let w = world();
        let id = &w.deployed[7];
        let pos = w.h.path_of(id, D);
        let idd = w.h.id_digest(id);
        let leaf = w.h.leaf_digest(id, &[]);
        let wit = BlindWitness {
            leaf,
            inv_siblings: siblings_of(&w.inv.prove(id)),
            reg_siblings: dummy(),
            pos,
            branch: Branch::Inclusion,
        };
        check_statement(
            generate_trace(&wit, idd),
            w.inv.root(),
            w.reg.root(),
            pos,
            idd,
        );
    }

    #[test]
    fn honest_absence_satisfies_the_constraints() {
        let w = world();
        let id = b"not-deployed-xyz.svc.example.gov".to_vec();
        let pos = w.h.path_of(&id, D);
        let idd = w.h.id_digest(&id);
        let leaf = w.h.leaf_digest(&id, &[]);
        assert!(!w.reg.contains(&id));
        let wit = BlindWitness {
            leaf,
            inv_siblings: dummy(),
            reg_siblings: siblings_of(&w.reg.prove(&id)),
            pos,
            branch: Branch::Absence,
        };
        check_statement(
            generate_trace(&wit, idd),
            w.inv.root(),
            w.reg.root(),
            pos,
            idd,
        );
    }

    #[test]
    fn the_statement_contains_no_branch_indicator() {
        // The public statement is exactly (C_Sigma, R_reg, pos, id_digest).
        // Every component is known to the verifier already, since the sampled
        // identifier is public; nothing in it depends on which disjunct holds.
        // Both branches also yield traces of identical shape, so the branch is
        // invisible in the statement and in the trace dimensions alike.
        assert_eq!(NUM_PUBLIC, 3 * DIGEST + 1);
        let w = world();

        let m = &w.deployed[3];
        let inc = BlindWitness {
            leaf: w.h.leaf_digest(m, &[]),
            inv_siblings: siblings_of(&w.inv.prove(m)),
            reg_siblings: dummy(),
            pos: w.h.path_of(m, D),
            branch: Branch::Inclusion,
        };
        let a = b"other-absent.svc.example.gov".to_vec();
        let abs = BlindWitness {
            leaf: w.h.leaf_digest(&a, &[]),
            inv_siblings: dummy(),
            reg_siblings: siblings_of(&w.reg.prove(&a)),
            pos: w.h.path_of(&a, D),
            branch: Branch::Absence,
        };

        let t_inc = generate_trace(&inc, w.h.id_digest(m));
        let t_abs = generate_trace(&abs, w.h.id_digest(&a));
        assert_eq!(t_inc.values.len(), t_abs.values.len());
        assert_eq!(t_inc.width(), t_abs.width());

        check_statement(t_inc, w.inv.root(), w.reg.root(), inc.pos, w.h.id_digest(m));
        check_statement(t_abs, w.inv.root(), w.reg.root(), abs.pos, w.h.id_digest(&a));
    }

    // --- Soundness: neither branch can be claimed falsely. ---

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn cannot_claim_inclusion_for_a_non_member() {
        // The empty-leaf attack. A non-member's slot in the inventory holds the
        // empty leaf, and the genuine sibling path from that empty leaf *does*
        // reach C_Sigma. The prover supplies exactly that path and claims the
        // inclusion branch. The leaf binding defeats it: the chain is forced to
        // start at H(id_digest || value), not at the empty leaf, so it lands on
        // a different root.
        let w = world();
        let id = b"never-deployed.svc.example.gov".to_vec();
        assert!(!w.inv.contains(&id));
        let idd = w.h.id_digest(&id);
        let wit = BlindWitness {
            leaf: w.h.leaf_digest(&id, &[]),
            inv_siblings: siblings_of(&w.inv.prove(&id)),
            reg_siblings: dummy(),
            pos: w.h.path_of(&id, D),
            branch: Branch::Inclusion,
        };
        check_statement(generate_trace(&wit, idd), w.inv.root(), w.reg.root(), wit.pos, idd);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn cannot_claim_absence_for_a_registered_member() {
        // A deployed identifier is in the registry, so no non-membership path
        // exists. The prover supplies the registry's genuine inclusion path and
        // claims the absence branch; the chain is forced to start at the empty
        // leaf, so it cannot reach R_reg.
        let w = world();
        let id = &w.deployed[11];
        let idd = w.h.id_digest(id);
        let wit = BlindWitness {
            leaf: w.h.leaf_digest(id, &[]),
            inv_siblings: dummy(),
            reg_siblings: siblings_of(&w.reg.prove(id)),
            pos: w.h.path_of(id, D),
            branch: Branch::Absence,
        };
        check_statement(generate_trace(&wit, idd), w.inv.root(), w.reg.root(), wit.pos, idd);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn wrong_position_is_rejected() {
        let w = world();
        let id = &w.deployed[7];
        let idd = w.h.id_digest(id);
        let pos = w.h.path_of(id, D);
        let wit = BlindWitness {
            leaf: w.h.leaf_digest(id, &[]),
            inv_siblings: siblings_of(&w.inv.prove(id)),
            reg_siblings: dummy(),
            pos,
            branch: Branch::Inclusion,
        };
        check_statement(generate_trace(&wit, idd), w.inv.root(), w.reg.root(), pos ^ 1, idd);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn wrong_id_digest_is_rejected() {
        // Directly exercises the leaf binding: claiming a different identifier
        // changes the leaf the chain must start from.
        let w = world();
        let id = &w.deployed[7];
        let pos = w.h.path_of(id, D);
        let mut idd = w.h.id_digest(id);
        let wit = BlindWitness {
            leaf: w.h.leaf_digest(id, &[]),
            inv_siblings: siblings_of(&w.inv.prove(id)),
            reg_siblings: dummy(),
            pos,
            branch: Branch::Inclusion,
        };
        let trace = generate_trace(&wit, idd);
        idd[0] += Val::ONE;
        check_statement(trace, w.inv.root(), w.reg.root(), pos, idd);
    }

    /// A world in which the prover conceals part of its deployment: the
    /// registry attests the full deployed set, the committed inventory omits
    /// some of it. This is exactly the adversary of the coverage experiment.
    fn concealing_world() -> (World, Vec<u8>) {
        let deployed: Vec<Vec<u8>> = (0..64)
            .map(|i| format!("dep-{i}.svc.example.gov").into_bytes())
            .collect();
        let all: Vec<(Vec<u8>, Vec<SmtF>)> =
            deployed.iter().map(|id| (id.clone(), Vec::new())).collect();
        // Inventory omits the last 32 deployed identifiers.
        let kept: Vec<(Vec<u8>, Vec<SmtF>)> = all[..32].to_vec();
        let concealed = deployed[40].clone();
        (
            World {
                inv: SparseMerkleTree::build(D, &kept),
                reg: SparseMerkleTree::build(D, &all),
                deployed,
                h: AcpHasher::new(),
            },
            concealed,
        )
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn concealed_identifier_cannot_use_the_inclusion_branch() {
        // Coverage soundness under blinding, part 1: the concealed identifier
        // is absent from C_Sigma, so the leaf-bound chain cannot reach it.
        let (w, id) = concealing_world();
        assert!(!w.inv.contains(&id) && w.reg.contains(&id));
        let idd = w.h.id_digest(&id);
        let wit = BlindWitness {
            leaf: w.h.leaf_digest(&id, &[]),
            inv_siblings: siblings_of(&w.inv.prove(&id)),
            reg_siblings: dummy(),
            pos: w.h.path_of(&id, D),
            branch: Branch::Inclusion,
        };
        check_statement(generate_trace(&wit, idd), w.inv.root(), w.reg.root(), wit.pos, idd);
    }

    #[test]
    #[should_panic(expected = "constraints not satisfied on row")]
    fn concealed_identifier_cannot_use_the_absence_branch() {
        // Coverage soundness under blinding, part 2: the registry attests the
        // identifier as deployed, so the empty-leaf chain cannot reach R_reg.
        // With part 1, a concealed identifier has no admissible branch at all --
        // which is the coverage guarantee, preserved while the branch stays
        // hidden for honest samples.
        let (w, id) = concealing_world();
        let idd = w.h.id_digest(&id);
        let wit = BlindWitness {
            leaf: w.h.leaf_digest(&id, &[]),
            inv_siblings: dummy(),
            reg_siblings: siblings_of(&w.reg.prove(&id)),
            pos: w.h.path_of(&id, D),
            branch: Branch::Absence,
        };
        check_statement(generate_trace(&wit, idd), w.inv.root(), w.reg.root(), wit.pos, idd);
    }
}
