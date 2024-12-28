use criterion::{BenchmarkId, Criterion, Throughput};
use fid::BitVector;
use rand::{Rng, SeedableRng, StdRng};

const SIZES: [u64; 1] = [1 << 16];
const PERC: [f64; 3] = [0.01, 0.5, 0.99];

pub fn bench_push(c: &mut Criterion) {
    for n in SIZES {
        for p in PERC {
            let mut data = Vec::with_capacity(n as usize);
            let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
            for _ in 0..n {
                let b = rng.gen_bool(p);
                data.push(b);
            }

            let mut g = c.benchmark_group("push");
            g.throughput(Throughput::Elements(n));
            g.bench_with_input(
                BenchmarkId::from_parameter(format!("N={}, %={}", n, p * 100.0)),
                &data,
                |b, data| {
                    b.iter_with_large_drop(|| {
                        let mut bv = BitVector::with_odds(n, p);
                        for b in data {
                            bv.push(*b);
                        }
                        bv
                    })
                },
            );
        }
    }
}

criterion_group!(
    name = benches;
    config = Criterion::default()
        .sample_size(50);
    targets = bench_push);
criterion_main!(benches);
