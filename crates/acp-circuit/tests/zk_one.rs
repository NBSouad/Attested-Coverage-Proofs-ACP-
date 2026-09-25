//! Single-point hiding measurement, for memory profiling at large traces.
use acp_circuit::measure_zk;
#[test]
fn zk_single_point() {
    let log_n: usize = std::env::var("ZK_LOG_N").ok().and_then(|s| s.parse().ok()).unwrap_or(16);
    let m = measure_zk(1usize << log_n);
    println!(
        "ZKONE 2^{} prove={:.2}s verify={:.1}ms proof={:.1}KB bits={}",
        log_n, m.prove_secs, m.verify_secs * 1e3, m.proof_bytes as f64 / 1024.0, m.conjectured_bits
    );
}
