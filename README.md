# Overview
A Rust version of the Ryū float-to-string conversion algorithm by Ulf Adams of Google Germany.  

## Description

The goal of this project is to improve the speed of converting `f32` and `f64` to and from string
representations, which is particularly important when performing high-performance serialisation of
JSON where all numbers are internally treated as `f64`.

Additionally, during development of this code it was noted that the [serde_json](https://github.com/serde-rs/json/) crate
references the [dtoa](https://github.com/dtoa-rs/) crate, which is both slower and contains unsafe
code. This crate is uses no unsafe code, and could potentially use `#![no_std]` as well.

## Status

This library is currently very much in the work-in-progress state, and is not yet usable. However,
things are looking promising, with the ryu `bench_float_to_decimal_common_shortest` function absolutely
smoking the currently available alternatives:

```
test tests::bench_dtoa                             ... bench:          45 ns/iter (+/- 1)
test tests::bench_f32_debug                        ... bench:         108 ns/iter (+/- 0)
test tests::bench_f32_format                       ... bench:         109 ns/iter (+/- 0)
test tests::bench_float_to_decimal_common_shortest ... bench:          25 ns/iter (+/- 0)
```