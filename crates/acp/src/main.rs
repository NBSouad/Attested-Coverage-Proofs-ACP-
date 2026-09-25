//! End-to-end measurement and demonstration of the integrated ACP protocol.
//!
//! Run with `cargo run -p acp --release`.

use std::time::Instant;

use acp::{sample_indices, verify, Namespace, Prover, SampleWitness};
use acp_absence::SignedRegistry;
use acp_circuit::bind_batch::{prove_paths_zk, SamplePath};
use acp_smt::{AcpHasher, CoverageProof};

const DEPTH: usize = 48;

fn world(deployed: usize, undeployed: usize) -> (Vec<Vec<u8>>, Namespace) {
    let dep: Vec<Vec<u8>> = (0..deployed)
        .map(|i| format!("deployed-{i}.svc.example.gov").into_bytes())
        .collect();
    let und: Vec<Vec<u8>> = (0..undeployed)
        .map(|i| format!("undeployed-{i}.svc.example.gov").into_bytes())
        .collect();
    let mut ids = dep.clone();
    ids.extend(und);
    (dep, Namespace { ids })
}

/// Empirically measure concealment-detection probability vs. concealment
/// fraction, over many random beacon seeds, and compare to 1-(1-rho)^q.
fn detect_sweep() {
    let m = 10_000usize; // namespace size (sampler is uniform over this)
    let n_deployed = 5_000usize; // registry-attested deployed set
    let q = 100usize;
    let trials = 10_000usize;

    let deployed: Vec<Vec<u8>> = (0..n_deployed)
        .map(|i| format!("dep-{i}.svc.example.gov").into_bytes())
        .collect();
    let undeployed: Vec<Vec<u8>> = (0..(m - n_deployed))
        .map(|i| format!("und-{i}.svc.example.gov").into_bytes())
        .collect();
    let mut ns_ids = deployed.clone();
    ns_ids.extend(undeployed);
    let ns = Namespace { ids: ns_ids };
    let registry = SignedRegistry::build(&deployed, DEPTH);

    println!("=== ACP coverage soundness: empirical detection vs concealment ===");
    println!("(namespace M={m}, deployed={n_deployed}, q={q}, {trials} random-seed trials/point)\n");
    println!("  {:>6}  {:>8}  {:>11}  {:>13}  {:>11}", "rho", "conceal", "empirical", "95% CI", "1-(1-rho)^q");
    for &rho in &[0.005f64, 0.01, 0.02, 0.05, 0.10] {
        let n_conceal = (rho * m as f64).round() as usize;
        // Conceal the first n_conceal deployed identifiers (omit from C_Sigma);
        // the registry still attests them, so they are uncoverable.
        let disclosed: Vec<Vec<u8>> = deployed[n_conceal..].to_vec();
        let (prover, c_sigma) = Prover::commit(&disclosed, DEPTH);

        let mut rejected = 0usize;
        for t in 0..trials {
            let seed = format!("detect-{n_conceal}-{t}").into_bytes();
            let idxs = sample_indices(&seed, q, ns.len());
            let samples: Vec<Vec<u8>> = idxs.iter().map(|&i| ns.ids[i].clone()).collect();
            let wits = prover.cover(&registry, &samples);
            if !verify(c_sigma, &registry, DEPTH, &seed, &ns, &wits).accept {
                rejected += 1;
            }
        }
        let emp = rejected as f64 / trials as f64;
        let se = (emp * (1.0 - emp) / trials as f64).sqrt();
        let theo = 1.0 - (1.0 - rho).powi(q as i32);
        println!(
            "  {rho:>6.3}  {n_conceal:>8}  {emp:>11.4}  +/-{:>9.4}  {theo:>11.4}",
            1.96 * se
        );
    }
    println!("\nInventory-trusting schemes (attested/given SBOM, plain ZK-over-commitment)");
    println!("detect omission with probability 0: they verify a given inventory, not its");
    println!("completeness against an external namespace.");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(|s| s == "detect").unwrap_or(false) {
        detect_sweep();
        return;
    }

    println!("=== ACP prototype: integrated coverage protocol (q=100, N=1000) ===\n");

    let n_deployed = 1000usize;
    let n_undeployed = 3000usize; // namespace = 4000, deployed fraction 25%
    let q = 100usize;
    let seed = b"epoch-2026-Q2-beacon";

    let (deployed, ns) = world(n_deployed, n_undeployed);

    // --- Honest prover ---
    let t = Instant::now();
    let (prover, c_sigma) = Prover::commit(&deployed, DEPTH);
    let commit_ms = t.elapsed().as_secs_f64() * 1e3;

    let t = Instant::now();
    let registry = SignedRegistry::build(&deployed, DEPTH);
    let registry_ms = t.elapsed().as_secs_f64() * 1e3;

    let idxs = sample_indices(seed, q, ns.len());
    let samples: Vec<Vec<u8>> = idxs.iter().map(|&i| ns.ids[i].clone()).collect();

    let t = Instant::now();
    let wits = prover.cover(&registry, &samples);
    let cover_ms = t.elapsed().as_secs_f64() * 1e3;

    let t = Instant::now();
    let res = verify(c_sigma, &registry, DEPTH, seed, &ns, &wits);
    let verify_ms = t.elapsed().as_secs_f64() * 1e3;

    let inclusions = res.b_s.iter().filter(|&&b| b).count();
    let absences = q - inclusions;
    println!("Honest prover (discloses full deployed set):");
    println!("  accept            : {}", res.accept);
    println!("  samples           : {q}  ({inclusions} inclusion, {absences} absence)");
    println!("  commit C_Sigma    : {commit_ms:.1} ms (inventory {} leaves)", prover.inventory_size());
    println!("  registry build    : {registry_ms:.1} ms");
    println!("  cover (witnesses) : {cover_ms:.2} ms");
    println!("  verify (protocol) : {verify_ms:.2} ms");

    // --- Malicious prover: conceals 500 deployed identifiers ---
    let disclosed: Vec<Vec<u8>> = deployed[..500].to_vec();
    let (mprover, mc_sigma) = Prover::commit(&disclosed, DEPTH);
    let mwits = mprover.cover(&registry, &samples);
    let mres = verify(mc_sigma, &registry, DEPTH, seed, &ns, &mwits);
    let concealed_sampled = idxs.iter().filter(|&&i| (500..1000).contains(&i)).count();
    println!("\nMalicious prover (conceals 500 of 1000 deployed):");
    println!("  concealed ids sampled : {concealed_sampled} of {q}");
    println!("  accept                : {}  (rejected at sample {:?})", mres.accept, mres.first_failure);
    println!("  => coverage soundness: a sample on a concealed id has no inclusion");
    println!("     proof and no registry absence witness, so the proof fails.");

    // --- Zero-knowledge bound-batched proof of the inclusion paths ---
    let hasher = AcpHasher::default();
    let paths: Vec<SamplePath> = samples
        .iter()
        .zip(wits.iter())
        .filter_map(|(id, w)| match w {
            SampleWitness::Inclusion(CoverageProof::Inclusion { path, .. }) => Some(SamplePath {
                id_digest: hasher.id_digest(id),
                position: hasher.path_of(id, DEPTH),
                siblings: path.siblings.clone(),
            }),
            _ => None,
        })
        .collect();
    let m = prove_paths_zk(c_sigma, DEPTH, &paths);
    println!("\nZK bound-batched proof of the {} inclusion paths (depth {DEPTH} => {} rows, padded {}):",
        paths.len(), paths.len() * DEPTH, m.trace_rows);
    println!("  STARK prove  : {:.3} s", m.prove_secs);
    println!("  STARK verify : {:.1} ms", m.verify_secs * 1e3);
    println!("  proof size   : {:.1} KB  ({}-bit conjectured FRI soundness)",
        m.proof_bytes as f64 / 1024.0, m.conjectured_bits);
    println!("\nNote: in non-blind ACP only the inclusion paths are in zero knowledge;");
    println!("absence witnesses (registry root + signature + non-membership) are public.");
}
