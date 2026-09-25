//! Comparison micro-baseline: the shared sampling-audit primitive vs. ACP.
//!
//! Sampling-based audits (Provisions, DAPOL+, Notus, PoR/PDP, ACP) share a
//! committed-set sampling core and the same `(1-rho)^q` corrupt-fraction bound.
//! This binary measures that shared core in our system --- a transparent sparse
//! Merkle membership audit, the structural primitive DAPOL+/Provisions build on
//! --- and then measures ACP's coverage proof on the same machine, isolating
//! what ACP adds: an external-namespace absence oracle (a second trust source)
//! and a post-quantum, transparent zero-knowledge proof.
//!
//! This is a same-machine baseline of the *shared primitive*, not a
//! reimplementation of DAPOL+ (which additionally uses Pedersen value
//! commitments and range proofs, and is classical/discrete-log) or Notus (RSA
//! accumulator with trusted setup, O(1) proof). Absolute numbers for those
//! systems are reported in their papers; the qualitative differences are in the
//! paper's comparison table.
//!
//! Run with `cargo run -p acp --bin acp-compare --release`.

use std::time::Instant;

use acp::{sample_indices, verify, Namespace, Prover, SampleWitness};
use acp_absence::{verify_absence, SignedRegistry};
use acp_circuit::{measure, next_pow2};
use acp_smt::{verify as smt_verify, SparseMerkleTree, F};

const DEPTH: usize = 48;

fn ms(s: f64) -> f64 {
    s * 1e3
}

fn main() {
    let n = 10_000usize;
    let q = 100usize;
    let seed = b"comparison-epoch-2026";

    println!("=== ACP prototype: comparison with sampling-based audits ===");
    println!("(N = {n} committed elements, q = {q} samples, SMT depth {DEPTH})\n");

    let ids: Vec<Vec<u8>> = (0..n)
        .map(|i| format!("entity-{i}.example").into_bytes())
        .collect();

    // ---------------------------------------------------------------
    // Baseline: DAPOL+/Provisions-style transparent SMT membership audit.
    // The prover commits its set in a sparse Merkle tree; the auditor samples
    // q members and checks a membership proof for each. This is the shared
    // sampling-audit core (no external namespace, no absence oracle, and --- in
    // this stripped transparent form --- no zero knowledge or post-quantum
    // signature; DAPOL+ adds Pedersen commitments + range proofs on top).
    // ---------------------------------------------------------------
    let entries: Vec<(Vec<u8>, Vec<F>)> = ids.iter().map(|id| (id.clone(), Vec::new())).collect();
    let t = Instant::now();
    let smt = SparseMerkleTree::build(DEPTH, &entries);
    let base_build = ms(t.elapsed().as_secs_f64());
    let root = smt.root();

    let idxs = sample_indices(seed, q, n);
    let samples: Vec<Vec<u8>> = idxs.iter().map(|&i| ids[i].clone()).collect();

    let t = Instant::now();
    let proofs: Vec<_> = samples.iter().map(|id| smt.prove(id)).collect();
    let base_gen = ms(t.elapsed().as_secs_f64());

    let t = Instant::now();
    let mut ok = true;
    for (id, p) in samples.iter().zip(&proofs) {
        ok &= smt_verify(root, DEPTH, id, p, true);
    }
    let base_verify = ms(t.elapsed().as_secs_f64());
    assert!(ok);
    let base_proof_bytes = (DEPTH + 1) * 32;

    println!("[A] Shared sampling core (DAPOL+/Provisions-style transparent SMT membership audit):");
    println!("    build (commit)     : {base_build:.1} ms");
    println!("    prove  q={q}        : {base_gen:.2} ms  ({:.1} us/sample)", base_gen * 1e3 / q as f64);
    println!("    verify q={q}        : {base_verify:.2} ms  ({:.1} us/sample)", base_verify * 1e3 / q as f64);
    println!("    per-sample proof   : {base_proof_bytes} B");
    println!("    properties         : transparent Merkle; NOT zero-knowledge here; NOT post-quantum-bound;");
    println!("                         self-contained set, no external namespace, no absence oracle.\n");

    // ---------------------------------------------------------------
    // ACP coverage (this work): same SMT core, plus an external public
    // namespace, a signed-registry absence oracle (2nd trust source), and a
    // post-quantum transparent zero-knowledge proof of the inclusion paths.
    // ---------------------------------------------------------------
    let deployed: Vec<Vec<u8>> = ids.clone(); // N deployed
    let undeployed: Vec<Vec<u8>> = (0..3 * n)
        .map(|i| format!("undeployed-{i}.example").into_bytes())
        .collect();
    let mut ns_ids = deployed.clone();
    ns_ids.extend(undeployed);
    let ns = Namespace { ids: ns_ids };

    let t = Instant::now();
    let (prover, c_sigma) = Prover::commit(&deployed, DEPTH);
    let acp_commit = ms(t.elapsed().as_secs_f64());

    let t = Instant::now();
    let registry = SignedRegistry::build(&deployed, DEPTH);
    let acp_registry = ms(t.elapsed().as_secs_f64());

    let idxs2 = sample_indices(seed, q, ns.len());
    let samples2: Vec<Vec<u8>> = idxs2.iter().map(|&i| ns.ids[i].clone()).collect();

    let t = Instant::now();
    let wits = prover.cover(&registry, &samples2);
    let acp_cover = ms(t.elapsed().as_secs_f64());

    let t = Instant::now();
    let res = verify(c_sigma, &registry, DEPTH, seed, &ns, &wits);
    let acp_verify = ms(t.elapsed().as_secs_f64());
    assert!(res.accept);
    let inclusions = res.b_s.iter().filter(|&&b| b).count();

    // Cost of one absence-witness verification (ML-DSA verify + non-membership);
    // the registry signature is shared across all q samples in an epoch.
    let mut abs_us = 0.0;
    for (k, w) in wits.iter().enumerate() {
        if let SampleWitness::Absence(aw) = w {
            let t = Instant::now();
            let ok = verify_absence(registry.public_key(), &samples2[k], DEPTH, aw);
            abs_us = t.elapsed().as_secs_f64() * 1e6;
            assert!(ok);
            break;
        }
    }

    // Post-quantum zero-knowledge proof of the inclusion paths.
    let n_perms = next_pow2(inclusions.max(1) * DEPTH);
    let m = measure(n_perms);

    println!("[B] ACP coverage (this work): shared SMT core + absence oracle + PQ transparent ZK:");
    println!("    commit C_Sigma     : {acp_commit:.1} ms");
    println!("    registry build     : {acp_registry:.1} ms  (absence oracle, ML-DSA-65 signed root)");
    println!("    cover (witnesses)  : {acp_cover:.2} ms  ({inclusions} inclusion / {} absence)", q - inclusions);
    println!("    verify (protocol)  : {acp_verify:.2} ms  (one absence witness = ML-DSA verify + non-memb ~{abs_us:.0} us)");
    println!("    PQ ZK STARK        : prove {:.3} s, verify {:.1} ms, proof {:.1} KB, {}-bit",
        m.prove_secs, ms(m.verify_secs), m.proof_bytes as f64 / 1024.0, m.conjectured_bits);
    println!("    properties         : post-quantum + transparent + zero-knowledge;");
    println!("                         audits a private set against an EXTERNAL public namespace,");
    println!("                         sound against omission via the absence oracle (2nd source).\n");

    println!("Summary: the sampling/SMT core is comparable (both ~us/sample, same (1-rho)^q bound).");
    println!("ACP's additions over the shared core are the external-namespace absence oracle");
    println!("(+1 ML-DSA verify, amortized over q) and the post-quantum transparent ZK proof.");
    println!("DAPOL+ adds Pedersen commitments + range proofs (classical); Notus uses an RSA");
    println!("accumulator with trusted setup (O(1) proof). Neither audits an external namespace");
    println!("nor is post-quantum; see the paper's comparison table.");
}
