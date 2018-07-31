#![feature(test)]
extern crate float_fast_print;
extern crate rand;

use float_fast_print::{write_f32_shortest,write_f64_shortest};
use rand::{thread_rng,Rng};

/// This is exhaustive round-trip test, validating that all possible 32-bit
/// floating-point input numbers can be parsed back into the original number.
#[test]
#[ignore]
fn f32_test_exhaustive_roundtrip() {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );

    for bits in 0u32..=std::u32::MAX {
        let float = f32::from_bits( bits );
        buffer.clear();
        let _ = write_f32_shortest(&mut buffer, float ).unwrap();

        let float_str = std::str::from_utf8( &buffer ).unwrap();
        let parsed = float_str.parse::<f32>().unwrap();

        if 0 == ( bits % 1000000 ) {
            println!("f32 exhaustive {}% complete", ( bits as f64 * 100.0 / (std::u32::MAX as f64 )) as f32 );
        }

        if !(parsed.is_nan() && float.is_nan()) {
            if parsed != float {
                println!("for bits: {} float {} => \"{}\" != {} (parsed)", bits, float, float_str, parsed );
            }

            assert_eq!(parsed,float);
        }
    }
}

/// Note that this is NOT an exhaustive round-trip test. Instead this test
/// generates 2^32 random 64-bit floating point numbers, which can be tested
/// in a few hours on a modern desktop processor.
#[test]
#[ignore]
fn f64_test_many_roundtrip() {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );

    let mut rng = thread_rng();

    for progress in 0u32..=std::u32::MAX {
        let bits = rng.gen();
        let float = f64::from_bits( bits );
        buffer.clear();
        let _ = write_f64_shortest(&mut buffer, float ).unwrap();

        let float_str = std::str::from_utf8( &buffer ).unwrap();
        let parsed = float_str.parse::<f64>().unwrap();

        if 0 == ( bits % 1000000 ) {
            println!("f64 strong testing {}% complete", ( progress as f64 * 100.0 / (std::u32::MAX as f64 )) as f64 );
        }

        if !(parsed.is_nan() && float.is_nan()) {
            if parsed != float {
                println!("for bits: {} float {} => \"{}\" != {} (parsed)", bits, float, float_str, parsed );
            }

            assert_eq!(parsed,float);
        }
    }
}
