#[macro_use]
extern crate criterion;

extern crate fid;
extern crate rand;

use criterion::{BenchmarkId, Criterion};
use fid::{BitVector, FID};
use rand::{Rng, SeedableRng, StdRng};

const SIZES: [u64; 2] = [1_000_000, 100_000_000];
const PERC: [f64; 3] = [0.01, 0.5, 0.99];

pub fn bench_rank1(c: &mut Criterion) {
    for (n, p) in SIZES.iter().copied().zip(PERC) {
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        let mut bv = BitVector::new();
        for _ in 0..n {
            let b = rng.gen_bool(p);
            bv.push(b);
        }
        c.bench_with_input(
            BenchmarkId::new("rank1", format!("{:?}", (n, p))),
            &bv,
            move |b, bv| {
                b.iter(|| {
                    bv.rank1(rng.gen_range(0, n));
                })
            },
        );
    }
}

pub fn bench_select1(c: &mut Criterion) {
    for (n, p) in SIZES.iter().copied().zip(PERC) {
        let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
        let mut bv = BitVector::new();
        let mut rank = 0;
        for _ in 0..n {
            let b = rng.gen_bool(p);
            bv.push(b);
            rank += b as u64;
        }
        c.bench_with_input(
            BenchmarkId::new("rank1", format!("{:?}", (n, p))),
            &bv,
            |b, bv| {
                b.iter(|| {
                    bv.select1(rng.gen_range(0, rank));
                })
            },
        );
    }
}

criterion_group!(benches, bench_rank1, bench_select1);
criterion_main!(benches);
