//! Measure batched binding (single STARK for q depth-D Merkle paths).

use acp_circuit::bind_batch::{prove_paths, prove_paths_zk, SamplePath};
use acp_smt::{CoverageProof, SparseMerkleTree, F};

fn tree_and_paths(q: usize, depth: usize) -> (SparseMerkleTree, Vec<SamplePath>) {
    let entries: Vec<(Vec<u8>, Vec<F>)> = (0..8192)
        .map(|i| (format!("asset-{i}.svc.example.gov").into_bytes(), Vec::new()))
        .collect();
    let tree = SparseMerkleTree::build(depth, &entries);
    let paths = (0..q)
        .map(|j| {
            let id = entries[(j * 37) % entries.len()].0.clone();
            let pos = tree.hasher().path_of(&id, depth);
            let idd = tree.hasher().id_digest(&id);
            let sibs = match tree.prove(&id) {
                CoverageProof::Inclusion { path, .. } => path.siblings,
                _ => panic!("expected inclusion proof"),
            };
            SamplePath {
                id_digest: idd,
                position: pos,
                siblings: sibs,
            }
        })
        .collect();
    (tree, paths)
}

#[test]
fn measure_batched_binding_d48() {
    let depth = 48;
    println!(
        "\n=== Batched bound coverage proof, depth D = {}, plain (non-hiding) ===",
        depth
    );
    println!(
        "{:>6}  {:>9}  {:>10}  {:>11}  {:>11}  {:>10}  {:>6}",
        "q", "q*D", "trace_rows", "prove", "verify", "proof", "bits"
    );
    for &q in &[10usize, 100, 406, 525] {
        let (tree, paths) = tree_and_paths(q, depth);
        let m = prove_paths(tree.root(), depth, &paths);
        println!(
            "  {:>6}  {:>9}  {:>10}  {:>9.3}s  {:>9.1}ms  {:>7.1}KB  {:>6}",
            m.q,
            m.q * depth,
            m.trace_rows,
            m.prove_secs,
            m.verify_secs * 1e3,
            m.proof_bytes as f64 / 1024.0,
            m.conjectured_bits,
        );
    }

    println!(
        "\n=== Batched bound coverage proof, depth D = {}, hiding (zero-knowledge) ===",
        depth
    );
    println!(
        "{:>6}  {:>9}  {:>10}  {:>11}  {:>11}  {:>10}  {:>6}",
        "q", "q*D", "trace_rows", "prove", "verify", "proof", "bits"
    );
    for &q in &[10usize, 100, 406, 525] {
        let (tree, paths) = tree_and_paths(q, depth);
        let m = prove_paths_zk(tree.root(), depth, &paths);
        println!(
            "  {:>6}  {:>9}  {:>10}  {:>9.3}s  {:>9.1}ms  {:>7.1}KB  {:>6}",
            m.q,
            m.q * depth,
            m.trace_rows,
            m.prove_secs,
            m.verify_secs * 1e3,
            m.proof_bytes as f64 / 1024.0,
            m.conjectured_bits,
        );
    }
}
