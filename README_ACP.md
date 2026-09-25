# ACP prototype

Reference implementation accompanying *Verifiable Post-Quantum Migration via
Attested Coverage Proofs (ACP)*. The prototype realizes the in-circuit
coverage-proof core of the ACP construction on a transparent STARK proof system,
together with the out-of-circuit commitment and witness-generation layer.

**Artifact evaluation:** see [`ARTIFACT.md`](ARTIFACT.md) for a claims→commands
map and reproduction instructions. Quick start: `make smoke`; full reproduction:
`make all`.

## Scope

The prototype implements and measures the component specific to the paper: the
**ACP coverage proof** — proving in zero knowledge the batched Poseidon2 hashing
and binding of `q` depth-`D` inclusion/non-membership Merkle paths to a
committed root, each sampled position, and each sampled identifier digest. This
is the dominant cost of the `Covered`-level coverage relation. The remaining
VPQM sub-relations (policy, dependency graph, monotonicity, exception
signatures) are accounted for analytically in the paper and extrapolated at the
measured per-permutation cost.


In standard (non-blind) ACP the registry root and signature are **public** and
verified out of circuit; only the prover's private-inventory inclusion proofs
(P3) need zero knowledge. In-circuit verification of the registry signature is
required only for the blind-ACP variant that hides the per-sample branch, and is
deferred.

## Cryptographic choices

- **Field:** Goldilocks, `p = 2^64 − 2^32 + 1`.
- **In-circuit hash `H_in`:** Poseidon2 over Goldilocks (width 8), via Plonky3.
  - Leaf hashing: padding-free sponge, rate 4, output 4 (`PaddingFreeSponge<·,8,4,4>`).
  - 2-to-1 compression: `TruncatedPermutation<·,2,4,8>`.
  - Digest = 4 Goldilocks elements (~256-bit space, ~128-bit generic collision).
- **Proof system:** transparent FRI/STARK (Plonky3 `uni-stark` + `Poseidon2Air`).
  - S-box degree 7, 8 full + 22 partial rounds, 180 trace columns per permutation.
  - FRI: `log_blowup = 3` (forced by the degree-7 quotient), 28 queries, 16 PoW
    bits ⇒ **100-bit conjectured FRI soundness** (`3·28 + 16`).

## Measured results

Apple-silicon laptop (M4, 32 GB, macOS), `--release`, single run
(~±15% run-to-run variance on the unloaded machine).

### Out-of-circuit (witness generation, `acp-bench`)

| operation | result |
|---|---|
| Poseidon2 width-8 permute | ≈ 1.8 M/s |
| 2:1 compression | ≈ 1.9 M/s |
| SMT build, N = 10³ / 10⁴ / 10⁵ (depth 48) | 28 ms / 255 ms / 2.61 s |
| prove / query | 2.0–3.4 µs |
| verify / query | 28.4–28.7 µs |
| witness size (inclusion / absence) | 1568 B / 1536 B |

### In-circuit (batched bound coverage-proof STARK, `acp-circuit`, depth D = 48)

Measured with `make bind-batch` (`cargo test -p acp-circuit --release --test
bind_batch_measure -- --nocapture --test-threads=1`). The numbers below are the
**hiding** (zero-knowledge) configuration, which the paper reports as the
deployment cost; `bind_batch_measure` also prints the plain configuration.

| q | detects | q·D | rows | prove | verify | proof |
|---:|---|---:|---:|---:|---:|---:|
| 10 | toy | 480 | 512 | 0.55 s | 5.2 ms | 290.9 KB |
| 100 | small audit | 4 800 | 8 192 | 9.0 s | 6.5 ms | 374.3 KB |
| 406 | ρ ≥ 5% @ 2⁻³⁰ | 19 488 | 32 768 | 36.3 s | 7.4 ms | 422.7 KB |
| **2 100** | **ρ ≥ 1% @ 2⁻³⁰** | **4 × 25 200** | **4 × 32 768** | **4 × 36.4 s** | **7.5 ms** | **4 × 422.8 KB** |

The `q = 2 100` row is four independent `2^15`-row shards of 525 samples each:
~146 s serial, ~37 s wall-clock on four cores, ~1.65 MB combined before
aggregation. The unbound path-hashing baseline (one Poseidon2 block per row,
no binding) is `make bench-stark` (`cargo run -p acp-circuit --release`); the
bound batched proof adds ~13–24 % proving time and ~17–24 % proof size over it
at the same trace height.

### Absence oracle (signed registry, `acp-absence`)

Registry root signed with real ML-DSA-65 (FIPS 204, `fips204` crate).

| metric | result |
|---|---|
| ML-DSA-65 sizes (pk / sk / sig) | 1952 / 4032 / 3309 B |
| keygen / sign / verify | 168 / 300 / 119 µs |
| registry build, N = 10³ / 10⁴ / 10⁵ | 58 ms / 450 ms / 4.37 s |
| epoch verify, q = 100 (1 sig + 100 non-memb) | ≈ 4.85 ms |
| per-epoch overhead | root 32 B + sig 3309 B + pk 1952 B, +1536 B/sample |

The registry root and signature are shared across all q samples, so amortized
epoch verification is **one ML-DSA-65 verify (~100 µs) plus q Poseidon2
non-membership checks**.

**Real-oracle validation.** `make validate-oracle` (or
`python3 scripts/validate_real_oracle.py`) verifies — fully offline — that the
absence evidence of the paper's §6 is produced by real infrastructure: a
captured live Cloudflare Nimbus2026 signed tree head is checked against the
log's published key, and a captured DNSSEC NSEC denial-of-existence for a
nonexistent `ietf.org` name is checked against the zone's captured DNSKEY
(with the DNSKEY-set RRSIG verified against the zone KSK). Fixtures live in
`tests/fixtures/`; needs only python3 + openssl. This exercises the *evidence
path* — the signature layer `V_abs` adjudicates — not freshness or liveness,
which inherently require the live service.

### VPQM epoch monotonicity circuit (`make mono`)

The dominant in-circuit cost of the full migration relation is the
epoch-to-epoch monotonicity check: for every asset, open its current and
previous records at the same position and prove the migration-status field did
not decrease. This is implemented in `acp-circuit/src/mono.rs` and measured in
`tests/mono_measure.rs`.

| n (assets) | trace rows | plain prove | plain verify | plain size | hiding prove (n=10) | hiding size |
|---|---|---|---|---|---|---|
| 10 | 512 | 0.60 s | 6.8 ms | 389 KB | 1.33 s | 476 KB |
| 50 | 4,096 | 4.42 s | 7.6 ms | 440 KB | — | — |
| 100 | 8,192 | 8.92 s | 7.9 ms | 460 KB | — | — |

At the measured rate, a full $10^5$-asset epoch of just the monotonicity
relation is roughly $9{,}000$ seconds (plain FRI) and the padded trace height
exceeds practical single-machine memory, so it must be sharded like the
coverage proof. Policy predicates and dependency ordering are not
independently measured but are lower-order arithmetic gadgets over the same
per-asset openings.

### Integrated protocol (`acp`, q = 100, N = 10³)

Beacon sampling + inventory inclusion + registry absence, end to end.

| | result |
|---|---|
| honest prover | **accepted** (20 inclusion / 80 absence of 100 samples) |
| commit C_Σ / registry build | 48.7 ms / 46.3 ms |
| witness generation | 1.3 ms |
| protocol verification | 12.7 ms |
| ZK bound-batched STARK over the 20 inclusion paths | ~1.08 s, ~5.3 ms verify, ~310.5 KB |
| **concealing prover** (omits 500/1000) | **rejected** at the first sampled concealed id |

The concealment test is coverage soundness in running code: a sample on a
concealed identifier admits neither an inclusion proof against `C_Σ` nor a
registry absence witness, so the two-source check fails.

**Detection vs concealment** (`cargo run -p acp --bin acp -- detect`, 10 000
random-beacon trials/point, q=100, namespace M=10⁴): measured detection tracks
the `1-(1-ρ)^q` characterization, while inventory-trusting schemes detect 0.

| ρ | concealed | empirical detection | 1-(1-ρ)^q |
|---|---|---|---|
| 0.005 | 50 | 0.3904 | 0.394 |
| 0.01 | 100 | 0.6370 | 0.634 |
| 0.02 | 200 | 0.8701 | 0.867 |
| 0.05 | 500 | 0.9952 | 0.994 |
| 0.10 | 1000 | 0.9998 | 1.000 |

This is the capability gap: ACP detects omission against an external namespace;
attested/given SBOMs and plain ZK-over-commitment cannot (detection ≡ 0).

### Scaling (P6)

The bound trace has 371 main columns plus 9 preprocessed columns, so a
single `2^17`-row hiding proof exceeds the 8 GB working set that motivated the
original sharding. The calibrated `q = 2 100` audit is therefore measured as
**four independent `2^15`-row batched shards of 525 samples each**
(`make bind-batch`):

| approach | prove | proof | peak mem |
|---|---|---|---|
| four `2^15`-row shards (hiding) | ~36 s each, ~146 s serial | 4 × 422.8 KB ≈ 1.65 MB (pre-aggregation) | per-shard, fits in 32 GB |
| single-shot `2^17`-row | not measured (exceeds the original 8 GB limit) | — | — |

Because the shards are independent, they can be run in parallel on four cores;
aggregating them into one succinct proof via FRI recursion is the remaining
step (Plonky2/Plonky3 support it).

The older unbound path-hashing sharding demo is still available via

```sh
cargo run -p acp-circuit --release -- one 18      # single proof of 2^18 perms
cargo run -p acp-circuit --release -- shard 18 16 # 2^18 workload as 4x 2^16 shards
```

but the paper's Table 1 and scaling figures now use the bound batched numbers
above.

### Comparison with sampling-based audits (P8)

```sh
cargo run -p acp --bin acp-compare --release
```

All sampling-based audits (Provisions, DAPOL+, Notus, PoR/PDP, ACP) share an
SMT/accumulator-sampling core and the same `(1-ρ)^q` bound. Measured on the same
machine (N=10⁴, q=100):

| | shared SMT core (DAPOL+/Provisions-style) | ACP coverage (this work) |
|---|---|---|
| prove / sample | 3.5 µs | + post-quantum ZK STARK (0.47 s, 166 KB total) |
| verify / sample | 45 µs | + absence oracle ~136 µs/witness (ML-DSA, amortized) |
| external namespace | no | **yes** |
| absence oracle (2nd source) | no | **yes** |
| post-quantum / transparent / ZK | no / — / no | **yes / yes / yes** |

ACP's marginal cost over the shared core is the external-namespace absence
oracle plus the post-quantum transparent ZK proof. DAPOL+ adds Pedersen
commitments + range proofs (classical); Notus uses an RSA accumulator with
trusted setup (O(1) proof). Neither audits an external namespace nor is
post-quantum. This is a same-machine baseline of the *shared primitive*, not a
reimplementation; absolute numbers for the other systems are in their papers and
the qualitative comparison is in the paper's comparison table.

## Dependencies

Plonky3 is pinned to commit `8fa63378fd0a9a4eeaff32b8751579cbf13f58d9`
(crate version `0.5.1`, edition 2024). Requires `rustc >= 1.85`
(developed on 1.95.0).

## Build, test, run

From the workspace root (`acp-prototype/`):

```sh
cargo test --release                    # all crates
cargo test -p acp-smt                   # SMT unit tests (inclusion/absence/tamper)
cargo run  -p acp-bench   --release     # out-of-circuit benchmarks
cargo run  -p acp-circuit --release     # coverage-proof STARK measurements
```

Or from anywhere with `--manifest-path /path/to/acp-prototype/Cargo.toml`.

## Layout

```
acp-prototype/
├── Cargo.toml            # workspace; Plonky3 pin + shared deps
└── crates/
    ├── acp-smt/          # Poseidon2-Goldilocks sparse Merkle tree (P1)
    ├── acp-bench/        # witness-generation benchmarks (P2)
    ├── acp-circuit/      # transparent STARK over Merkle-path hashing and binding (P3)
    ├── acp-absence/      # signed-registry absence oracle, ML-DSA-65 (P4)
    └── acp/              # integrated coverage prover/verifier (P5);
                          #   bins: acp (P5), acp-compare (P8)
```