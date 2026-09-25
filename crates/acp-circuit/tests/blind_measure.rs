//! Cost of the blind (branch-hiding) coverage proof.
use acp_circuit::blind::*;
use acp_smt::{AcpHasher, CoverageProof, SparseMerkleTree, F};

const D: usize = 32;

fn sibs(p: &CoverageProof) -> Vec<[F; 4]> {
    match p {
        CoverageProof::Inclusion { path, .. } => path.siblings.clone(),
        CoverageProof::Absence { path } => path.siblings.clone(),
    }
}

#[test]
fn measure_blind() {
    let deployed: Vec<Vec<u8>> = (0..64)
        .map(|i| format!("dep-{i}.svc.example.gov").into_bytes())
        .collect();
    let entries: Vec<(Vec<u8>, Vec<F>)> =
        deployed.iter().map(|id| (id.clone(), Vec::new())).collect();
    let inv = SparseMerkleTree::build(D, &entries);
    let reg = SparseMerkleTree::build(D, &entries);
    let h = AcpHasher::new();

    // Inclusion branch.
    let id = &deployed[7];
    let w = BlindWitness {
        leaf: h.leaf_digest(id, &[]),
        inv_siblings: sibs(&inv.prove(id)),
        reg_siblings: vec![[F::default(); 4]; D],
        pos: h.path_of(id, D),
        branch: Branch::Inclusion,
    };
    let m = prove_blind(&w, h.id_digest(id), inv.root(), reg.root());
    println!(
        "BLIND(incl) depth={} cols={} prove={:.3}s verify={:.1}ms proof={:.1}KB",
        m.depth, m.trace_cols, m.prove_secs, m.verify_secs * 1e3,
        m.proof_bytes as f64 / 1024.0
    );

    // Absence branch: identical statement shape, identical cost.
    let a = b"absent-1.svc.example.gov".to_vec();
    let w2 = BlindWitness {
        leaf: h.leaf_digest(&a, &[]),
        inv_siblings: vec![[F::default(); 4]; D],
        reg_siblings: sibs(&reg.prove(&a)),
        pos: h.path_of(&a, D),
        branch: Branch::Absence,
    };
    let m2 = prove_blind(&w2, h.id_digest(&a), inv.root(), reg.root());
    println!(
        "BLIND(abs)  depth={} cols={} prove={:.3}s verify={:.1}ms proof={:.1}KB",
        m2.depth, m2.trace_cols, m2.prove_secs, m2.verify_secs * 1e3,
        m2.proof_bytes as f64 / 1024.0
    );
    println!("public values: {} (C_Sigma, R_reg, pos, id_digest) -- no branch bit", NUM_PUBLIC);
}
