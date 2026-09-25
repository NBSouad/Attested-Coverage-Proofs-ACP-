//! Measured benchmarks for the out-of-circuit ACP layer.
//!
//! Produces the witness-generation numbers (Poseidon2 throughput, SMT build,
//! per-query prove/verify, witness sizes) that feed the paper's performance
//! section. These are *out-of-circuit* costs; in-circuit STARK proving/verifying
//! is measured separately once the AIR lands (P3+).
//!
//! Run with `cargo run -p acp-bench --release`.

use std::hint::black_box;
use std::time::Instant;

use acp_smt::{verify, AcpHasher, CoverageProof, SparseMerkleTree, DIGEST_ELEMS, F};
use p3_field::integers::QuotientMap;
use p3_goldilocks::default_goldilocks_poseidon2_8;
use p3_symmetric::Permutation;

/// Bytes to serialize one digest (4 Goldilocks elements, 8 bytes each).
const DIGEST_BYTES: usize = DIGEST_ELEMS * 8;

fn fmt_rate(ops: u64, secs: f64) -> String {
    let per_sec = ops as f64 / secs;
    if per_sec >= 1e6 {
        format!("{:.2} M/s", per_sec / 1e6)
    } else if per_sec >= 1e3 {
        format!("{:.2} K/s", per_sec / 1e3)
    } else {
        format!("{per_sec:.1} /s")
    }
}

fn ns_per_op(ops: u64, secs: f64) -> f64 {
    secs * 1e9 / ops as f64
}

fn bench_permutation() {
    let perm = default_goldilocks_poseidon2_8();
    let mut state = [
        F::from_int(1u64), F::from_int(2u64), F::from_int(3u64), F::from_int(4u64),
        F::from_int(5u64), F::from_int(6u64), F::from_int(7u64), F::from_int(8u64),
    ];
    // Warmup.
    for _ in 0..10_000 {
        perm.permute_mut(&mut state);
    }
    let iters: u64 = 2_000_000;
    let t = Instant::now();
    for _ in 0..iters {
        perm.permute_mut(&mut state);
        black_box(&state);
    }
    let s = t.elapsed().as_secs_f64();
    println!(
        "  Poseidon2 width-8 permute    : {:>10}  ({:6.1} ns/op)",
        fmt_rate(iters, s),
        ns_per_op(iters, s)
    );
}

fn bench_hashes() {
    let h = AcpHasher::new();
    let a = h.id_digest(b"left-node-digest-placeholder");
    let b = h.id_digest(b"right-node-digest-placeholder");

    // 2-to-1 compression.
    let iters: u64 = 2_000_000;
    let mut acc = a;
    let t = Instant::now();
    for _ in 0..iters {
        acc = h.compress(acc, b);
        black_box(&acc);
    }
    let s = t.elapsed().as_secs_f64();
    println!(
        "  2:1 compression (1 perm)     : {:>10}  ({:6.1} ns/op)",
        fmt_rate(iters, s),
        ns_per_op(iters, s)
    );

    // Leaf hashing (id_digest + value), representative inventory leaf.
    let value = vec![F::from_int(7u64), F::from_int(42u64)];
    let iters: u64 = 500_000;
    let t = Instant::now();
    for i in 0..iters {
        let id = format!("svc-{i}.example.gov");
        let d = h.leaf_digest(id.as_bytes(), &value);
        black_box(&d);
    }
    let s = t.elapsed().as_secs_f64();
    println!(
        "  leaf hash (id+value)         : {:>10}  ({:6.1} ns/op)",
        fmt_rate(iters, s),
        ns_per_op(iters, s)
    );
}

fn entries(n: usize) -> Vec<(Vec<u8>, Vec<F>)> {
    (0..n)
        .map(|i| {
            let id = format!("asset-{i}.svc.example.gov");
            // value = (primitive-class, migration-status), toy encoding.
            let value = vec![F::from_int((i % 7) as u64), F::from_int((i % 3) as u64)];
            (id.into_bytes(), value)
        })
        .collect()
}

fn bench_tree(n: usize, depth: usize, q: usize) {
    let ents = entries(n);

    // Build.
    let t = Instant::now();
    let tree = SparseMerkleTree::build(depth, &ents);
    let build_s = t.elapsed().as_secs_f64();
    let _root = tree.root();

    // Build a query mix: half present, half absent.
    let mut queries: Vec<(Vec<u8>, bool)> = Vec::with_capacity(q);
    for j in 0..q {
        if j % 2 == 0 {
            queries.push((ents[(j * 7) % n].0.clone(), true));
        } else {
            queries.push((format!("absent-{j}.svc.example.gov").into_bytes(), false));
        }
    }

    // Prove.
    let t = Instant::now();
    let mut proofs: Vec<(Vec<u8>, bool, CoverageProof)> = Vec::with_capacity(q);
    for (id, member) in &queries {
        let p = tree.prove(id);
        proofs.push((id.clone(), *member, p));
    }
    let prove_s = t.elapsed().as_secs_f64();

    // Verify.
    let root = tree.root();
    let t = Instant::now();
    let mut ok = true;
    for (id, member, p) in &proofs {
        ok &= verify(root, depth, id, p, *member);
    }
    let verify_s = t.elapsed().as_secs_f64();
    assert!(ok, "all proofs must verify");

    // Witness size: an inclusion witness is depth siblings + 1 leaf.
    let incl_bytes = (depth + 1) * DIGEST_BYTES;
    let abs_bytes = depth * DIGEST_BYTES;

    println!(
        "  N={:>7}  depth={:>2}  build={:>8.1} ms  prove/q={:>7.1} us  verify/q={:>6.1} us  \
         incl_wit={} B  abs_wit={} B",
        n,
        depth,
        build_s * 1e3,
        prove_s * 1e6 / q as f64,
        verify_s * 1e6 / q as f64,
        incl_bytes,
        abs_bytes,
    );
}

fn main() {
    println!("=== ACP prototype: out-of-circuit benchmarks ===");
    println!("(field = Goldilocks; H_in = Poseidon2 width-8; digest = 4 elems = 32 B)\n");

    println!("Hash primitives:");
    bench_permutation();
    bench_hashes();

    println!("\nSparse Merkle tree (build once, then per-query prove/verify, q=100, 50/50 present/absent):");
    let q = 100;
    bench_tree(1_000, 48, q);
    bench_tree(10_000, 48, q);
    bench_tree(100_000, 48, q);

    println!("\nNote: these are witness-generation (out-of-circuit) costs only.");
    println!("In-circuit STARK proving/verifying is measured by the circuit crate (P3+).");
}
