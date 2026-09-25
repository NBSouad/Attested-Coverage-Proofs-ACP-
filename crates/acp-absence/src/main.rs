//! Measurements for the signed-registry absence oracle.
//!
//! Run with `cargo run -p acp-absence --release`.

use std::time::Instant;

use acp_absence::{verify_absence, SignedRegistry, REGISTRY_CTX};
use acp_smt::verify as smt_verify;
use fips204::ml_dsa_65;
use fips204::traits::{Signer, Verifier};

const DEPTH: usize = 48;

fn main() {
    println!("=== ACP prototype: signed-registry absence oracle (ML-DSA-65) ===\n");
    println!(
        "ML-DSA-65 sizes: pk = {} B, sk = {} B, sig = {} B",
        ml_dsa_65::PK_LEN,
        ml_dsa_65::SK_LEN,
        ml_dsa_65::SIG_LEN
    );

    // --- Signature primitive timings (registry side + verifier side) ---
    let iters = 50;
    let (pk, sk) = ml_dsa_65::try_keygen().expect("keygen");

    let t = Instant::now();
    for _ in 0..iters {
        let _ = ml_dsa_65::try_keygen().expect("keygen");
    }
    let keygen_us = t.elapsed().as_secs_f64() * 1e6 / iters as f64;

    let msg = [0x5au8; 32];
    let t = Instant::now();
    let mut sig = sk.try_sign(&msg, REGISTRY_CTX).expect("sign");
    for _ in 0..iters {
        sig = sk.try_sign(&msg, REGISTRY_CTX).expect("sign");
    }
    let sign_us = t.elapsed().as_secs_f64() * 1e6 / iters as f64;

    let t = Instant::now();
    let mut ok = true;
    for _ in 0..iters {
        ok &= pk.verify(&msg, &sig, REGISTRY_CTX);
    }
    let verify_us = t.elapsed().as_secs_f64() * 1e6 / iters as f64;
    assert!(ok, "signature must verify");
    println!(
        "keygen {:.1} us | sign {:.1} us | verify {:.1} us  (avg of {iters})\n",
        keygen_us, sign_us, verify_us
    );

    // --- End-to-end absence oracle at registry sizes ---
    println!("Signed registry + absence witnesses (depth {DEPTH}):");
    let q = 100usize;
    for &n in &[1_000usize, 10_000, 100_000] {
        let deployed: Vec<Vec<u8>> = (0..n)
            .map(|i| format!("deployed-{i}.svc.example.gov").into_bytes())
            .collect();

        let t = Instant::now();
        let reg = SignedRegistry::build(&deployed, DEPTH);
        let build_ms = t.elapsed().as_secs_f64() * 1e3;

        // Sampled identifiers that are genuinely absent from the registry.
        let queries: Vec<Vec<u8>> = (0..q)
            .map(|j| format!("sampled-absent-{j}.svc.example.gov").into_bytes())
            .collect();
        let wits: Vec<_> = queries
            .iter()
            .map(|id| reg.absence_witness(id).expect("absent id has a witness"))
            .collect();

        // Realistic epoch cost: the root + signature are shared across all q
        // samples, so the verifier checks ONE signature and q non-membership
        // proofs. We measure those two pieces separately.
        let (root, rsig) = reg.signed_root();
        let t = Instant::now();
        let sig_ok = reg.public_key().verify(
            &acp_absence::digest_to_bytes(&root),
            &rsig,
            REGISTRY_CTX,
        );
        let sigverify_us = t.elapsed().as_secs_f64() * 1e6;
        assert!(sig_ok);

        let t = Instant::now();
        let mut all = true;
        for (id, w) in queries.iter().zip(&wits) {
            all &= smt_verify(root, DEPTH, id, &w.nonmembership, false);
        }
        let nonmemb_ms = t.elapsed().as_secs_f64() * 1e3;
        assert!(all);

        // Cross-check the full combined verifier on every witness.
        let mut combined = true;
        for (id, w) in queries.iter().zip(&wits) {
            combined &= verify_absence(reg.public_key(), id, DEPTH, w);
        }
        assert!(combined);

        let epoch_ms = sigverify_us / 1e3 + nonmemb_ms;
        println!(
            "  N={:>7}: build {:>7.1} ms | epoch-verify(q={q}) = 1 sig ({:.0} us) + {q} non-memb ({:.2} ms) = {:.2} ms",
            n, build_ms, sigverify_us, nonmemb_ms, epoch_ms
        );
    }

    let per_sample = DEPTH * 32;
    println!(
        "\nPer-epoch absence overhead: shared root {} B + ML-DSA sig {} B + pk {} B,",
        32,
        ml_dsa_65::SIG_LEN,
        ml_dsa_65::PK_LEN
    );
    println!(
        "plus {} B per sampled identifier (depth-{DEPTH} non-membership path).",
        per_sample
    );
    println!("Amortized epoch verification = 1 ML-DSA-65 verify + q Poseidon2 non-membership checks.");
}
