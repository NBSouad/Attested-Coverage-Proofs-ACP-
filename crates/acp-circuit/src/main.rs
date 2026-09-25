//! Transparent-STARK measurements for the ACP hashing relation.
//!
//! Usage:
//!   cargo run -p acp-circuit --release                 # default sweep + ACP configs
//!   cargo run -p acp-circuit --release -- one  <log2>  # one single-shot proof of 2^log2 perms
//!   cargo run -p acp-circuit --release -- shard <T> <S># 2^T perms as 2^(T-S) shards of 2^S

use acp_circuit::{measure, next_pow2, perms_for_paths, Measurement, DEPTH};

/// Rough prover working-set estimate (GB): trace cells x 8 bytes x ~10
/// (blowup 8 + quotient chunks + FRI Merkle overhead).
fn est_mem_gb(m: &Measurement) -> f64 {
    (m.trace_cells as f64) * 8.0 * 10.0 / 1e9
}

fn print_one(log2: u32, m: &Measurement) {
    println!(
        "  2^{:<2}={:>8}  cols {:>3}  prove {:>8.2} s  verify {:>6.1} ms  proof {:>7.1} KB  ~mem {:>5.1} GB  {} bit",
        log2,
        m.num_perms,
        m.trace_cols,
        m.prove_secs,
        m.verify_secs * 1e3,
        m.proof_bytes as f64 / 1024.0,
        est_mem_gb(m),
        m.conjectured_bits,
    );
}

fn shard_demo(total_log2: u32, shard_log2: u32) {
    assert!(total_log2 >= shard_log2);
    let n_shards = 1usize << (total_log2 - shard_log2);
    let shard_perms = 1usize << shard_log2;
    println!(
        "Sharded proving of a 2^{total_log2}-permutation workload as {n_shards} \
         independent shard(s) of 2^{shard_log2} perms:"
    );
    let mut total_prove = 0.0;
    let mut total_bytes = 0usize;
    let mut per_shard_mem = 0.0;
    for s in 0..n_shards {
        let m = measure(shard_perms);
        total_prove += m.prove_secs;
        total_bytes += m.proof_bytes;
        per_shard_mem = est_mem_gb(&m);
        println!(
            "  shard {:>2}: prove {:>7.2} s  proof {:>7.1} KB  ~mem {:>5.1} GB",
            s,
            m.prove_secs,
            m.proof_bytes as f64 / 1024.0,
            per_shard_mem
        );
    }
    println!(
        "  totals : sequential prove {:.1} s, combined proof {:.1} KB (pre-aggregation), \
         peak mem ~{:.1} GB/shard",
        total_prove,
        total_bytes as f64 / 1024.0,
        per_shard_mem
    );
    println!(
        "  shards are independent => embarrassingly parallel; each fits the per-shard memory\n  \
         bound regardless of total workload. Aggregating the {n_shards} shard proofs into one\n  \
         succinct proof via FRI recursion is the remaining step (Plonky2/Plonky3 support it)."
    );
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() >= 3 && args[1] == "one" {
        let log2: u32 = args[2].parse().expect("log2");
        println!("=== ACP STARK: single proof of 2^{log2} Poseidon2 permutations ===");
        let m = measure(1usize << log2);
        print_one(log2, &m);
        return;
    }
    if args.len() >= 4 && args[1] == "shard" {
        let total: u32 = args[2].parse().expect("total log2");
        let shard: u32 = args[3].parse().expect("shard log2");
        println!("=== ACP STARK: sharded (recursive-composition) scaling ===");
        shard_demo(total, shard);
        return;
    }

    println!("=== ACP prototype: in-circuit STARK (Poseidon2-Goldilocks) ===");
    println!(
        "(width 8, S-box degree 7, {} full + {} partial rounds; FRI benchmark params)\n",
        2 * 4,
        22
    );

    println!("Permutation-count sweep:");
    println!(
        "  {:>10}  {:>5}  {:>10}  {:>11}  {:>11}  {:>10}  {:>6}",
        "perms", "cols", "cells", "prove", "verify", "proof", "bits"
    );
    for log2 in [10u32, 12, 14, 16, 17] {
        let m = measure(1usize << log2);
        println!(
            "  2^{:<2}={:>5}  {:>5}  {:>10}  {:>9.3} s  {:>9.1} ms  {:>7.1} KB  {:>6}",
            log2,
            m.num_perms,
            m.trace_cols,
            m.trace_cells,
            m.prove_secs,
            m.verify_secs * 1e3,
            m.proof_bytes as f64 / 1024.0,
            m.conjectured_bits,
        );
    }

    println!("\nACP coverage configs (depth D = {DEPTH}; perms = q*D rounded up to 2^k):");
    println!(
        "  {:>6}  {:>9}  {:>9}  {:>11}  {:>11}  {:>10}  {:>6}",
        "q", "q*D", "perms", "prove", "verify", "proof", "bits"
    );
    for q in [10usize, 100, 406, 2100] {
        let raw = perms_for_paths(q);
        let n = next_pow2(raw);
        let m = measure(n);
        println!(
            "  {:>6}  {:>9}  {:>9}  {:>9.3} s  {:>9.1} ms  {:>7.1} KB  {:>6}",
            q,
            raw,
            n,
            m.prove_secs,
            m.verify_secs * 1e3,
            m.proof_bytes as f64 / 1024.0,
            m.conjectured_bits,
        );
    }

    println!("\nNote: measures the dominant Poseidon2 hashing of q depth-D paths.");
    println!("Run `-- one <log2>` for a single large proof, `-- shard <T> <S>` for");
    println!("sharded (recursive-composition) scaling.");
}
