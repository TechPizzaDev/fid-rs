#[allow(dead_code)]
#[allow(unused_imports)]
#[path = "../src/coding.rs"]
mod coding;

#[allow(dead_code)]
#[path = "../src/tables.rs"]
mod tables;

#[allow(dead_code)]
#[path = "../src/util.rs"]
mod util;

use std::ops::Range;

use coding::{encode, select0_raw};
use criterion::{
    black_box, criterion_group, criterion_main, measurement::WallTime, BatchSize, BenchmarkGroup, BenchmarkId, Criterion, Throughput
};
use fid::{BitVector, FID};
use rand::{Rng, SeedableRng, StdRng};

const SIZES: [u64; 2] = [1 << 16, 1 << 19];
const PERC: [f64; 3] = [0.01, 0.5, 0.99];

fn make_indices(rng: &mut impl Rng, n: u64, range: Range<u64>) -> Vec<u64> {
    let mut indices = Vec::with_capacity(n as usize);
    for _ in 0..n {
        indices.push(rng.gen_range(range.start, range.end));
    }
    indices
}

fn make_bitvec(rng: &mut impl Rng, n: u64, p: f64) -> BitVector {
    let mut bv = BitVector::with_odds(n, p);
    for _ in 0..n {
        let b = rng.gen_bool(p);
        bv.push(b);
    }
    bv
}

pub fn bench_rank1(c: &mut Criterion) {
    for n in SIZES {
        for p in PERC {
            let mut rng: StdRng = SeedableRng::from_seed([0; 32]);

            let bv = make_bitvec(&mut rng, n, p);
            let indices = make_indices(&mut rng, 1024, 0..n);

            let mut g = c.benchmark_group("rank1");
            g.throughput(Throughput::Elements(indices.len() as u64));
            g.bench_with_input(
                BenchmarkId::from_parameter(format!("N={}, %={}", n, p * 100.0)),
                &(bv, indices),
                |b, (bv, indices)| {
                    b.iter(|| {
                        for idx in indices.iter() {
                            let x = bv.rank1(*idx);
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

            let bv = make_bitvec(&mut rng, n, p);
            let rank = bv.rank(true, bv.len());
            let indices = make_indices(&mut rng, 1024, 0..rank);

            let mut g = c.benchmark_group("select1");
            g.throughput(Throughput::Elements(indices.len() as u64));
            g.bench_with_input(
                BenchmarkId::from_parameter(format!("N={}, %={}", n, p * 100.0)),
                &(bv, indices),
                |b, (bv, indices)| {
                    b.iter(|| {
                        for idx in indices.iter() {
                            let x = bv.select1(*idx);
                            black_box(x);
                        }
                    })
                },
            );
        }
    }
}

fn bench_select0_raw(c: &mut Criterion) {
    let mut g = c.benchmark_group("select0_raw");

    for p in PERC {
        bench_lambda(&mut g, p, "lzcnt", select0_raw);
        bench_lambda(&mut g, p, "naive", |mut bits: u64, mut r: u64| {
            let mut i = 0;
            while i < 64 {
                if bits & 1 == 0 {
                    if r == 0 {
                        return i;
                    }
                    r -= 1;
                }
                i += 1;
                bits >>= 1;
            }
            64
        });
    }

    fn bench_lambda(
        g: &mut BenchmarkGroup<'_, WallTime>,
        p: f64,
        name: &str,
        f: impl Fn(u64, u64) -> u64,
    ) {
        let parameter = format!("p={}", p * 100.0);
        g.bench_function(BenchmarkId::new(name, parameter), |b| {
            let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
            b.iter_batched(
                || {
                    let bits: u64 = rng.gen();
                    let k = bits.count_ones();
                    (encode(bits, k as usize).0 as u64, k as u64)
                },
                |(bits, k)| {
                    for r in 0..k {
                        let x = f(bits, r);
                        black_box(x);
                    }
                },
                BatchSize::SmallInput,
            )
        });
    }
}

criterion_group!(
    name = benches;
    config = Criterion::default().sample_size(200);
    targets = bench_rank1,
    bench_select1,
    bench_select0_raw
);
criterion_main!(benches);
