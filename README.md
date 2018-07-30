# Overview
A native Rust implementation of the high-performance [Ryū](https://github.com/ulfjack/ryu) float-to-string conversion
algorithm by Ulf Adams of Google Germany.  

## Description
The purpose of this crate is to improve the speed of converting `f32` and `f64` to string representations, 
which is particularly important when performing bulk serialisation of JSON, CSV, XLSX, and scientific data formats 
where all numbers are internally treated as floating point. In some cases, this can be the bottleneck to serialisation.

During development of this code it was noted that the [serde_json](https://github.com/serde-rs/json/) crate
references the [dtoa](https://github.com/dtolnay/dtoa) crate, which is both slower and contains unsafe
code. This crate uses no unsafe code, and could potentially use `#![no_std]` as well.

## Status
Things are looking promising, with the Ryū `bench_write_f32_shortest` function significantly outperforming the 
currently available alternatives:

```
test tests::bench_dtoa               ... bench:          45 ns/iter (+/- 1)
test tests::bench_f32_debug          ... bench:         108 ns/iter (+/- 0)
test tests::bench_f32_format         ... bench:         109 ns/iter (+/- 0)
test tests::bench_write_f32_shortest ... bench:          25 ns/iter (+/- 0)
```

The `f32` version of the function has been exhaustively tested in version 0.1.1 of the crate, guaranteeing that all possible 2^32 float values can round-trip with no loss of precision when converted using this library:

```
...
99.930916% complete
99.95419% complete
99.97748% complete
test test_exhaustive_roundtrip ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
```

A less exhaustive test for the `f64` version is available, but obviously can't be exhaustive, as it would take years to run.

## Pending Tasks
[ ] Implement 2-digit lookup table and benchmark.
[ ] Compare performance to alternatives when the cache has been flushed.
[ ] Add JSON-style printing that uses the integer representation for whole numbers.

## References
* https://github.com/ulfjack/ryu
* https://dl.acm.org/citation.cfm?id=3192369
