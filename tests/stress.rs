use accumulator::group::Rsa2048;
use accumulator::{Accumulator, AccumulatorWithHashToPrime};
use rand::Rng;
use rug::Integer;

/// Adds 10,000 random primes to accumulator (unverified), then tests 100 more random additions
/// (with verification) and 100 random elements are verified to be nonmembers.
///
/// Takes about 5 minutes.
///
/// TODO: Use a counter instead of random bits.
#[test]
#[ignore]
fn stress_test() {
    let mut acc_set = Vec::new();
    let mut acc = Accumulator::<Rsa2048, Integer, AccumulatorWithHashToPrime>::empty();
    for _ in 0..100 {
        let random_elem = rand::thread_rng().gen::<u128>();
        acc_set.push(Integer::from(random_elem));
    }
    println!("Starting add");
    acc = acc.clone().add(&acc_set);
    println!("{}", acc_set.len());
    for _ in 0..100 {
        let new_elem = rand::thread_rng().gen::<u128>();
        assert!(!acc_set.contains(&new_elem.into()));
        let (new_acc, add_proof) = acc.clone().add_with_proof(&[new_elem.into()]);
        assert!(new_acc.verify_membership(&new_elem.into(), &add_proof));
        let (_, del_proof) = new_acc
            .clone()
            .delete_with_proof(&[(new_elem.into(), add_proof.witness)])
            .unwrap();
        assert!(new_acc.verify_membership(&new_elem.into(), &del_proof));
        let nonmem_proof = acc
            .prove_nonmembership(&acc_set, &[new_elem.into()])
            .expect("It works");
        assert!(acc.verify_nonmembership(&[new_elem.into()], &nonmem_proof));
    }
}
