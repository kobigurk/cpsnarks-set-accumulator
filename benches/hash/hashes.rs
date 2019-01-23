/// See https://bheisler.github.io/criterion.rs/book/getting_started.html to add more benchmarks.
#[macro_use]
extern crate criterion;

use criterion::Criterion;
use crypto::hash::{Blake2b, hash, hash_to_prime};
use rand::Rng;

fn bench_blake2() {
  hash(&Blake2b::default, b"werg");
}

fn bench_h_prime() {
  let random_bytes = rand::thread_rng().gen::<[u8; 32]>();
  hash_to_prime(&Blake2b::default, &random_bytes);
}

fn criterion_benchmark(c: &mut Criterion) {
  c.bench_function("blake2", |b| b.iter(|| bench_blake2()));
  c.bench_function("h_prime", |b| b.iter(|| bench_h_prime()));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
