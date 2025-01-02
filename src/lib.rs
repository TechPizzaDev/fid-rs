//! FID (Fully Indexable Dictionary) implementation for Rust
//!
//! This crate provides a succinct bit vector that supports two kinds of bit operations in constant-time:
//!
//! - `rank(i)` computes the number of 0s (or 1s) in [0..i)
//! - `select(r)` locates the (r+1)-th position of 0 (or 1).
//!
//! Structures supporting these two operations are called FID (fully indexable dictionary).
//!
//! # Basic usage
//!
//! ```
//! use fid::{bit_vec, FID};
//!
//! // 01101101
//! let mut bv = bit_vec![false, true, true, false, true, true, false, true];
//! assert_eq!(bv.rank0(5), 2);
//! assert_eq!(bv.rank1(5), 3);
//! assert_eq!(bv.select0(2), 6);
//! assert_eq!(bv.select1(2), 4);
//! ```
//!
//! # About implementation
//!
//! Compression and computation algorithms for `BitVector` are
//! originally from [1] and its practical implementation ideas are from [2].
//!
//! [1] Gonzalo Navarro and Eliana Providel. 2012. Fast, small, simple rank/select on bitmaps.
//! In Proceedings of the 11th international conference on Experimental Algorithms (SEA'12),
//! Ralf Klasing (Ed.). Springer-Verlag, Berlin, Heidelberg, 295-306.
//! DOI=http://dx.doi.org/10.1007/978-3-642-30850-5_26
//!
//! [2] rsdic by Daisuke Okanohara.
//! [https://github.com/hillbig/rsdic](https://github.com/hillbig/rsdic)

mod bit_array;
mod bit_vector;
mod coding;
mod fid;
mod fid_iter;
mod util;

pub use crate::bit_array::BitArray;
pub use crate::bit_vector::BitVector;
pub use crate::fid::FID;
pub use crate::fid_iter::FidBitIter;