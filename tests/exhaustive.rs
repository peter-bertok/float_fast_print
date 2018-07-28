#![feature(test)]

extern crate ryu;

use ryu::*;

#[test]
fn test_exhaustive_roundtrip() {
    let mut buffer : Vec<u8> = Vec::with_capacity( 32 );

    for bits in 0u32..=std::u32::MAX {
        let float = f32::from_bits( bits );
        buffer.clear();
        let _ = write_f32_shortest(&mut buffer, float ).unwrap();

        let float_str = std::str::from_utf8( &buffer ).unwrap();
        let parsed = float_str.parse::<f32>().unwrap();

        if 0 == ( bits % 100000 ) {
            println!("{}% complete", bits as f64 * 100.0 / (std::u32::MAX as f64 ));
        }

        if parsed != float {
            println!("for bits: {} float {} => \"{}\" != {} (parsed)", bits, float, float_str, parsed );
        }

        assert_eq!(parsed,float);
    }
}

