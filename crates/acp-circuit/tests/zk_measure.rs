//! Cost of the zero-knowledge (hiding) commitment configuration.
//!
//! Compares the non-hiding FRI stack against the hiding stack (salted Merkle
//! MMCS + hiding FRI PCS) at the same trace sizes and the same 100-bit
//! conjectured FRI soundness. The difference is the price of the
//! zero-knowledge property assumed by A5.
//!
//! Sizes stop at 2^15. Blinding doubles committed height, so on an 8 GB
//! machine 2^16 already pages heavily (~254 s, CPU dipping to 6%) and 2^17
//! does not complete. The bound batched q=2100 audit reported in the paper is
//! measured in `bind_batch_measure` as four independent 2^15-row shards; this
//! test only gives the unbound path-hashing baseline used in the comparison of
//! \S\ref{sec:bind}. Use `ZK_LOG_N=16 cargo test --test zk_one -- --nocapture`
//! to reproduce the paging behaviour directly.

use acp_circuit::{measure, measure_zk};

#[test]
fn measure_hiding_overhead() {
    println!("\n{:>6}  {:>26}  {:>26}  {:>20}", "perms", "plain (prove/verify/proof)", "hiding (prove/verify/proof)", "overhead");
    let mut last_zk = None;
    for log_perms in [9usize, 13, 15] {
        let n = 1usize << log_perms;
        let p = measure(n);
        let z = measure_zk(n);
        assert_eq!(p.conjectured_bits, z.conjectured_bits, "hiding must not change FRI soundness");
        println!(
            "  2^{:<3}  {:>7.2}s {:>6.1}ms {:>8.1}KB  {:>7.2}s {:>6.1}ms {:>8.1}KB  {:.1}x prove {:.2}x proof",
            log_perms,
            p.prove_secs, p.verify_secs * 1e3, p.proof_bytes as f64 / 1024.0,
            z.prove_secs, z.verify_secs * 1e3, z.proof_bytes as f64 / 1024.0,
            z.prove_secs / p.prove_secs,
            z.proof_bytes as f64 / p.proof_bytes as f64,
        );
        last_zk = Some(z);
    }
    let z = last_zk.unwrap();
    println!(
        "\n  Unbound 2^15 hiding baseline: q=2100 would be 4 x 2^15 shards: {:.0}s serial, \
         ~{:.0}s across 4 cores, {:.2}MB combined pre-aggregation. \
         The bound batched q=2100 audit is measured in bind_batch_measure.",
        4.0 * z.prove_secs, z.prove_secs, 4.0 * z.proof_bytes as f64 / (1024.0 * 1024.0)
    );
}
