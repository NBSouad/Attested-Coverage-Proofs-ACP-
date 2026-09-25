# Artifact Evaluation — ACP / VPQM prototype

This artifact is the open-source prototype accompanying *Verifiable Post-Quantum
Migration via Attested Coverage Proofs (ACP)*. It implements and measures the
ACP coverage-proof core, the signed-registry absence oracle, and the dominant
VPQM epoch-to-epoch monotonicity gadget, and reproduces every measured number
in the paper's evaluation (§8) and the data behind its comparison and
detection sweeps.

## Claims supported by this artifact

1. **Functional correctness and coverage soundness.** The sparse Merkle tree
   (inclusion/non-membership), the batched bound STARK, the ML-DSA-signed registry
   absence oracle, and the integrated prover/verifier are correct; a *concealing*
   prover is rejected (coverage soundness in running code).
2. **Measured performance.** Witness generation, the batched bound
   coverage-proof STARK (Table 1), the absence oracle, and the integrated
   end-to-end protocol.
3. **Measured scaling.** 2^15-row sharded proving; single-shot 2^17-row
   bound proving exceeds the original 8 GB working set and is reported as four
   2^15-row shards.
4. **Quantitative comparison.** Detection-vs-concealment matching
   `1-(1-rho)^q`, and a shared-primitive comparison baseline.
5. **VPQM epoch monotonicity.** Two-tree path opening at the same
   position with a status-ordering gadget, measured for up to 100 assets.

This artifact **does** include the in-AIR binding of an inclusion path to the
commitment (`acp-circuit::bind`, with the leaf derived from the identifier),
the batched binding of `q > 1` sampled paths into a single STARK
(`acp-circuit::bind_batch`), the branch-hiding blind construction
(`acp-circuit::blind`), and the dominant VPQM epoch-to-epoch monotonicity
gadget (`acp-circuit::mono`). It does **not** include FRI recursion aggregation
or the full set of VPQM policy/dependency clauses, nor in-circuit verification
of governance-signature exceptions. Both the plain and the hiding
(zero-knowledge) FRI configurations are implemented and measured.

## Requirements

- **Rust** stable `>= 1.85` (the pinned Plonky3 v0.5.1 uses edition 2024). The
  artifact was developed on `rustc 1.95.0`.
- **Internet access on the first build** to fetch the Plonky3 dependency pinned
  at commit `8fa63378fd0a9a4eeaff32b8751579cbf13f58d9`.
- **~5 GB** free disk for the build; **32 GB RAM** for the full measurements (the 2^18
  single-shot proof needs ~3.8 GB; the 2^17 bound hiding proof is the largest
  reported workload and fits in 32 GB only as sharded 2^15-row proofs).
- A POSIX shell and `make` for the convenience targets (optional; the underlying
  `cargo` commands are listed below and can be run directly).

Absolute numbers are hardware-dependent and exhibit ~±15% run-to-run variance on
an unloaded laptop. The artifact was measured on an Apple-silicon laptop
(M4, 32 GB, macOS); the *trends* (linear proving, flat verification,
logarithmic proof size, detection matching `1-(1-rho)^q`) reproduce on any
sufficient machine.

## Getting started (kick-the-tires, ~2–3 min after build)

```sh
cd acp-prototype
make smoke          # builds, runs all tests, runs the detection sweep
```

Expect: all tests pass, and a detection table whose empirical column approaches
the `1-(1-rho)^q` column.

## Full reproduction (~12–15 min)

```sh
make all            # runs every experiment; logs land in results/
```

Each experiment's console output is also written to `results/NN-name.txt`.


## Running individual experiments without `make`

```sh
cargo test  --release
cargo run -q -p acp-bench    --release                 # witness generation
cargo run -q -p acp-circuit  --release                 # unbound path-hashing sweep
cargo test -p acp-circuit --release --test bind_batch_measure -- --nocapture --test-threads=1 # Table 1
cargo run -q -p acp-circuit  --release -- one 18        # single-shot 2^18 (unbound)
cargo run -q -p acp-circuit  --release -- shard 18 16   # 4-way unbound sharding
cargo run -q -p acp-absence  --release                 # absence oracle
cargo run -q -p acp --bin acp         --release         # integrated protocol
cargo run -q -p acp --bin acp         --release -- detect  # detection sweep
cargo run -q -p acp --bin acp-compare --release         # comparison baseline
cargo test -p acp-circuit --release --test mono_measure -- --nocapture --test-threads=1 # VPQM monotonicity
python3 scripts/validate_real_oracle.py                 # offline real-oracle check
```

## Reproducibility notes

- **Determinism.** Plonky3 is pinned by git commit; field arithmetic and the
  SMT are deterministic; benchmark RNGs are seeded. Proving/verification *times*
  vary with hardware and load; *proof sizes*, *constraint/column counts*,
  *witness sizes*, and *roots* are deterministic.
- **Seeds.** The detection sweep averages over 10,000 fixed-but-distinct beacon
  seeds per point and prints a 95% confidence interval; every point should land
  within its interval of the closed form. (At 300 trials, which an earlier
  version used, the smallest `rho` point sat ~3 sigma from theory purely by
  sampling noise.)
- **Zero knowledge.** `make zk` compares the non-hiding FRI stack against the
  hiding stack (`MerkleTreeHidingMmcs` + `HidingFriPcs`) at identical FRI
  parameters. Conjectured soundness is `log_blowup * num_queries + pow_bits`
  in both configurations and is asserted equal by the test.  The headline
  numbers in Table~1 use the hiding configuration.

- **Timing harnesses.** The `bind` and `blind` figures come from `#[test]`
  harnesses, so they need `--nocapture` to print at all and `--test-threads=1`
  to avoid CPU contention; running them in parallel inflates per-proof time by
  roughly 2x. The `make` targets already pass both flags.
- **Memory.** Only `make scale` (2^18 single-shot path hashing) approaches a few GB. If RAM
  is tight, run `cargo run -p acp-circuit --release -- shard 18 16` (4× lower
  peak memory) instead of the single-shot `one 18`.
- **Real-oracle validation.** `python3 scripts/validate_real_oracle.py` (or
  `make validate-oracle`) verifies, fully offline, that the absence-oracle
  evidence of \S6 is produced by real infrastructure: a captured live
  Cloudflare Nimbus2026 signed tree head is checked against the log's
  published key (RFC 6962), and a captured DNSSEC denial-of-existence for a
  nonexistent `ietf.org` name is checked against the zone's captured DNSKEY,
  with the DNSKEY-set RRSIG verified against the zone KSK (RFC 4034
  canonicalization). Fixtures are in `tests/fixtures/`; the script needs only
  python3 and openssl, no network. This validates the *evidence path*
  (the signature layer an oracle's $\Vabs$ adjudicates); the SMT
  non-membership layer is the prototype's own.

## Layout

See `README.md` for the crate-by-crate description and the full results tables.
