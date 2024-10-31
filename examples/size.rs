extern crate fid;
extern crate rand;

use fid::BitVector;
use mem_dbg::{MemSize, SizeFlags};
use rand::{Rng, SeedableRng, StdRng};

fn generate_random_vector(n: u64, p: f64) -> BitVector {
    let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
    let mut bv = BitVector::with_odds(n, p as f32);
    for _ in 0..n {
        let b = rng.gen_bool(p);
        bv.push(b);
    }
    bv
}

fn main() {
    let test_cases = &[
        (1_000_000, 0.99),
        (1_000_000, 0.5),
        (1_000_000, 0.01),
        (10_000_000, 0.99),
        (10_000_000, 0.5),
        (10_000_000, 0.01),
    ];

    println!("n: # of nodes, p: density of 1s\n");

    for &(n, p) in test_cases {
        let bv = generate_random_vector(n, p);
        let size = bv.mem_size(SizeFlags::empty());
        let rate = (size * 8) as f64 / n as f64;
        println!(
            "n = {}, p = {}: {} bytes ({} bit / orig bit)",
            n, p, size, rate
        );
    }
}
