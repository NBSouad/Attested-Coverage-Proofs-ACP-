//! Measurements for the bound single-path circuit (§9.3 of the paper).

use acp_circuit::bind::*;
use acp_smt::{CoverageProof, SparseMerkleTree, F};

const D: usize = 32;

fn tree_and_entries(n: usize) -> (SparseMerkleTree, Vec<(Vec<u8>, Vec<F>)>) {
    let entries: Vec<(Vec<u8>, Vec<F>)> = (0..n)
        .map(|i| (format!("asset-{i}.svc.example.gov").into_bytes(), Vec::new()))
        .collect();
    (SparseMerkleTree::build(D, &entries), entries)
}

#[test]
fn measure_single_bound_path() {
    let (tree, entries) = tree_and_entries(64);
    let root = tree.root();
    let id = &entries[7].0;
    let pos = tree.hasher().path_of(id, D);
    let idd = tree.hasher().id_digest(id);
    let sibs = match tree.prove(id) {
        CoverageProof::Inclusion { path, .. } => path.siblings,
        _ => unreachable!(),
    };
    let m = prove_path(idd, &sibs, pos, root);
    println!(
        "SINGLE  depth={} cols={} (p2={} link={}) prove={:.3}s verify={:.1}ms proof={:.1}KB",
        m.depth,
        m.trace_cols,
        P2_COLS,
        TOTAL_COLS - P2_COLS,
        m.prove_secs,
        m.verify_secs * 1e3,
        m.proof_bytes as f64 / 1024.0
    );
}

#[test]
fn measure_q_independent_bound_paths() {
    // Binding every sampled path with independent proofs, as a comparison for
    // the batched single-proof circuit in bind_batch. Sound with the existing
    // constraint system; proof size grows linearly in q until the paths share
    // one proof.
    let (tree, entries) = tree_and_entries(4096);
    let root = tree.root();
    for &q in &[10usize, 100] {
        let mut total_prove = 0.0;
        let mut total_bytes = 0usize;
        let mut total_verify = 0.0;
        for j in 0..q {
            let id = &entries[(j * 37) % entries.len()].0;
            let pos = tree.hasher().path_of(id, D);
            let idd = tree.hasher().id_digest(id);
            let sibs = match tree.prove(id) {
                CoverageProof::Inclusion { path, .. } => path.siblings,
                _ => unreachable!(),
            };
            let m = prove_path(idd, &sibs, pos, root);
            total_prove += m.prove_secs;
            total_verify += m.verify_secs;
            total_bytes += m.proof_bytes;
        }
        println!(
            "Q={:<4} bound-independent: prove={:.2}s verify={:.0}ms proofs={:.1}MB",
            q,
            total_prove,
            total_verify * 1e3,
            total_bytes as f64 / (1024.0 * 1024.0)
        );
    }
}
