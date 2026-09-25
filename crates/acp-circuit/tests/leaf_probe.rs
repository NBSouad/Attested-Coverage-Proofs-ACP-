//! Empirically pin down `leaf_digest(id, [v])`'s sponge structure so the
//! in-circuit leaf block reproduces it exactly.

use acp_smt::AcpHasher;
use p3_field::PrimeCharacteristicRing;
use p3_field::integers::QuotientMap;
use p3_goldilocks::{default_goldilocks_poseidon2_8, Goldilocks};
use p3_symmetric::Permutation;

#[test]
fn leaf_with_value_is_two_perms() {
    let h = AcpHasher::new();
    let id = b"probe.svc.example.gov";
    let v = Goldilocks::from_int(7u64);
    let want = h.leaf_digest(id, &[v]);
    let idd = h.id_digest(id);

    let perm = default_goldilocks_poseidon2_8();

    // Block 1: absorb id_digest into the rate of the zero state.
    let mut s = [Goldilocks::ZERO; 8];
    s[..4].copy_from_slice(&idd);
    let s1 = perm.permute(s);

    // Candidate A: second absorb overwrites state[0] with v, keeps s1[1..8].
    let mut s2a = s1;
    s2a[0] = v;
    let out_a = perm.permute(s2a);

    // Candidate B: second absorb adds v into state[0].
    let mut s2b = s1;
    s2b[0] += v;
    let out_b = perm.permute(s2b);

    // Candidate C: fresh state [v || 0^7].
    let mut s2c = [Goldilocks::ZERO; 8];
    s2c[0] = v;
    let out_c = perm.permute(s2c);

    println!("leaf_digest = {want:?}");
    println!("A (overwrite, keep capacity+rate): {:?}", &out_a[..4]);
    println!("B (add into rate[0]):              {:?}", &out_b[..4]);
    println!("C (fresh state):                   {:?}", &out_c[..4]);
    assert_eq!(&out_a[..4], &want[..], "candidate A must match");
}
