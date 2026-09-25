//! Measurement of the epoch-to-epoch monotonicity circuit (VPQM bookkeeping).
//!
//! Proves that the current inventory is pointwise monotonic in migration status
//! against the previous-epoch inventory.  This is the dominant in-circuit cost
//! of the full VPQM relation: per asset, two depth-48 Merkle paths plus a
//! status-ordering gadget.

use acp_circuit::mono::{prove, prove_zk, AssetPath};
use p3_field::integers::QuotientMap;
use p3_goldilocks::Goldilocks as Val;
use acp_smt::{SparseMerkleTree, F as SmtF};

const DEPTH: usize = 48;

fn build_assets(n: usize, statuses: &[(u64, u64)]) -> (SparseMerkleTree, SparseMerkleTree, Vec<AssetPath>) {
    let ids: Vec<Vec<u8>> = (0..n)
        .map(|i| format!("asset-{i}.svc.example.gov").into_bytes())
        .collect();
    let cur: Vec<(Vec<u8>, Vec<SmtF>)> = ids
        .iter()
        .zip(statuses.iter())
        .map(|(id, (sc, _))| (id.clone(), vec![SmtF::from_int(*sc)]))
        .collect();
    let prev: Vec<(Vec<u8>, Vec<SmtF>)> = ids
        .iter()
        .zip(statuses.iter())
        .map(|(id, (_, sp))| (id.clone(), vec![SmtF::from_int(*sp)]))
        .collect();

    let tree_cur = SparseMerkleTree::build(DEPTH, &cur);
    let tree_prev = SparseMerkleTree::build(DEPTH, &prev);
    let h = tree_cur.hasher();

    let paths: Vec<AssetPath> = ids
        .iter()
        .zip(statuses.iter())
        .map(|(id, (sc, sp))| {
            let cp = tree_cur.prove(id);
            let pp = tree_prev.prove(id);
            acp_circuit::mono::AssetPath {
                id_digest: h.id_digest(id),
                position: h.path_of(id, DEPTH),
                status_cur: Val::from_int(*sc),
                status_prev: Val::from_int(*sp),
                siblings_cur: match cp {
                    acp_smt::CoverageProof::Inclusion { path, .. } => path.siblings.clone(),
                    _ => panic!("inclusion expected"),
                },
                siblings_prev: match pp {
                    acp_smt::CoverageProof::Inclusion { path, .. } => path.siblings.clone(),
                    _ => panic!("inclusion expected"),
                },
            }
        })
        .collect();

    (tree_cur, tree_prev, paths)
}

/// Pick a few status histories that are all monotonic: all move 0->1->2 or
/// stay the same, plus some starting at 1.
fn statuses(n: usize) -> Vec<(u64, u64)> {
    (0..n)
        .map(|i| match i % 5 {
            0 => (0u64, 0u64),
            1 => (1, 0),
            2 => (2, 1),
            3 => (2, 2),
            _ => (1, 1),
        })
        .collect()
}

fn measure_at(n: usize) {
    let s = statuses(n);
    let (tcur, tprev, paths) = build_assets(n, &s);
    let m = prove(tcur.root(), tprev.root(), DEPTH, &paths);
    println!(
        "mono n={:4} depth={:2} trace_rows={:6} cols={:3} | prove={:6.3}s verify={:5.1}ms size={:6.1}KB bits={}",
        n, m.depth, m.trace_rows, m.trace_cols, m.prove_secs, m.verify_secs * 1e3, m.proof_bytes as f64 / 1024.0, m.conjectured_bits
    );
}

#[test]
fn measure_monotonicity_plain() {
    println!("\n=== VPQM epoch monotonicity circuit (plain FRI) ===");
    for n in [10, 50, 100] {
        measure_at(n);
    }
}

#[test]
fn measure_monotonicity_hiding() {
    println!("\n=== VPQM epoch monotonicity circuit (hiding FRI) ===");
    let n = 10;
    let s = statuses(n);
    let (tcur, tprev, paths) = build_assets(n, &s);
    let m = prove_zk(tcur.root(), tprev.root(), DEPTH, &paths);
    println!(
        "mono n={:4} depth={:2} trace_rows={:6} cols={:3} | prove={:6.3}s verify={:5.1}ms size={:6.1}KB bits={}",
        n, m.depth, m.trace_rows, m.trace_cols, m.prove_secs, m.verify_secs * 1e3, m.proof_bytes as f64 / 1024.0, m.conjectured_bits
    );
}
