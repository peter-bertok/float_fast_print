#![feature(test)]

extern crate ryu;
extern crate test;
extern crate dtoa;

use ryu::*;
use test::Bencher;
use dtoa::*;
use std::io::Write;

#[bench]
fn bench_f32_debug(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f32 = 215.1291248e-43;

    b.iter(|| {
        buffer.clear();
        write!(&mut buffer, "{:?}", x);
    });
}

#[bench]
fn bench_f32_format(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f32 = 215.1291248e-43;

    b.iter(|| {
        buffer.clear();
        write!(&mut buffer, "{}", x);
    });
}


#[bench]
fn bench_float_to_decimal_common_shortest(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f32 = 215.1291248e-43;

    b.iter(|| {
        buffer.clear();

        let _ = write_f32_shortest(&mut buffer, x).unwrap();
    });
}

#[bench]
fn bench_dtoa(b: &mut Bencher) {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
    let x: f32 = 215.1291248e-43;

    b.iter(|| {
        buffer.clear();
        let _ = write( &mut buffer, x).unwrap();
    });
}

