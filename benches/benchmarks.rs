#![feature(test)]

extern crate float_fast_print;
extern crate test;

use float_fast_print::*;
use test::Bencher;
use std::io::Write;

#[bench]
fn bench_f32_debug(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f32 = -28215.12291248e-43;

    b.iter(|| {
        buffer.clear();
        write!(&mut buffer, "{:?}", x);
    });
}

#[bench]
fn bench_f32_format(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f32 = -28215.12291248e-43;

    b.iter(|| {
        buffer.clear();
        write!(&mut buffer, "{}", x);
    });
}

#[bench]
fn bench_f64_debug(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f64 = -28215.12291248e-43;

    b.iter(|| {
        buffer.clear();
        write!(&mut buffer, "{:?}", x);
    });
}

#[bench]
fn bench_f64_format(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f64 = -28215.12291248e-43;

    b.iter(|| {
        buffer.clear();
        write!(&mut buffer, "{}", x);
    });
}

#[bench]
fn bench_write_f32_shortest(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f32 = -28215.12291248e-43;

    b.iter(|| {
        buffer.clear();

        let _ = write_f32_shortest(&mut buffer, x).unwrap();
    });
}

#[bench]
fn bench_write_f64_shortest(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f64 = -28215.12291248e-43;

    b.iter(|| {
        buffer.clear();

        let _ = write_f64_shortest(&mut buffer, x).unwrap();
    });
}

