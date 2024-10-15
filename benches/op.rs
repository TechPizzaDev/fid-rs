#[macro_use]
extern crate criterion;

extern crate fid;
extern crate rand;

use criterion::{black_box, BenchmarkId, Criterion, Throughput};
use fid::{BitVector, FID};
use rand::{Rng, SeedableRng, StdRng};

const SIZES: [u64; 2] = [1 << 20, 1 << 24];
const PERC: [f64; 3] = [0.01, 0.5, 0.99];

pub fn bench_rank1(c: &mut Criterion) {
    for n in SIZES {
        for p in PERC {
            let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
            let mut bv = BitVector::new();
            let mut indices = Vec::new();
            for _ in 0..n {
                let b = rng.gen_bool(p);
                bv.push(b);
                indices.push(rng.gen_range(0, n));
            }

            let mut g = c.benchmark_group("rank1");
            g.throughput(Throughput::Elements(n));
            g.bench_with_input(
                BenchmarkId::from_parameter(format!("N={}, %={}", n, p * 100.0)),
                &(bv, indices),
                |b, (bv, indices)| {
                    b.iter(|| {
                        for i in 0..n {
                            let x = bv.rank1(indices[i as usize]);
                            black_box(x);
                        }
                    })
                },
            );
        }
    }
}

pub fn bench_select1(c: &mut Criterion) {
    for n in SIZES {
        for p in PERC {
            let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
            let mut bv = BitVector::new();
            let mut rank = 0;
            for _ in 0..n {
                let b = rng.gen_bool(p);
                bv.push(b);
                rank += b as u64;
            }

            let mut indices = Vec::new();
            for _ in 0..n {
                indices.push(rng.gen_range(0, rank));
            }

            let mut g = c.benchmark_group("rank1");
            g.throughput(Throughput::Elements(n));
            g.bench_with_input(
                BenchmarkId::from_parameter(format!("N={}, %={}", n, p * 100.0)),
                &(bv, indices),
                |b, (bv, indices)| {
                    b.iter(|| {
                        for i in 0..n {
                            let x = bv.select1(indices[i as usize]);
                            black_box(x);
                        }
                    })
                },
            );
        }
    }
}

criterion_group!(benches, bench_rank1, bench_select1);
criterion_main!(benches);
