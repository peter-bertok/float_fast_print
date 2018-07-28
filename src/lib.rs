use std::io::{Write,Result};
//use std::fmt::{LowerExp, UpperExp, Display, Debug};

/// Returns e == 0 ? 1 : ceil(log_2(5^e)).
#[inline]
fn pow5bits( e: u32 ) -> u32 {
    // This function has only been tested for 0 <= e <= 1500.
    debug_assert!(e <= 1500);

    ((e * 1217359) >> 19) + 1
}

/// Returns floor(log_10(2^e)).
#[inline]
fn log_10_pow_2(e: u32 ) -> u32
{
    // This function has only been tested for 0 <= e <= 1500.
    debug_assert!(e <= 1500);

    (e * 78913) >> 18
}

/// Returns floor(log_10(5^e)).
#[inline]
fn log_10_pow_5(e: u32 ) -> u32
{
    // This function has only been tested for 0 <= e <= 1500.
    debug_assert!(e <= 1500);
    return (e * 732923) >> 20;
}

const FLOAT_POW5_INV_BITCOUNT : u32 = 59;
const FLOAT_POW5_INV_SPLIT : [u64;31] = [
    576460752303423489u64, 461168601842738791u64, 368934881474191033u64, 295147905179352826u64,
    472236648286964522u64, 377789318629571618u64, 302231454903657294u64, 483570327845851670u64,
    386856262276681336u64, 309485009821345069u64, 495176015714152110u64, 396140812571321688u64,
    316912650057057351u64, 507060240091291761u64, 405648192073033409u64, 324518553658426727u64,
    519229685853482763u64, 415383748682786211u64, 332306998946228969u64, 531691198313966350u64,
    425352958651173080u64, 340282366920938464u64, 544451787073501542u64, 435561429658801234u64,
    348449143727040987u64, 557518629963265579u64, 446014903970612463u64, 356811923176489971u64,
    570899077082383953u64, 456719261665907162u64, 365375409332725730u64
];

const FLOAT_POW5_BITCOUNT: u32 = 61;

const FLOAT_POW5_SPLIT : [u64;47] = [
    1152921504606846976u64, 1441151880758558720u64, 1801439850948198400u64, 2251799813685248000u64,
    1407374883553280000u64, 1759218604441600000u64, 2199023255552000000u64, 1374389534720000000u64,
    1717986918400000000u64, 2147483648000000000u64, 1342177280000000000u64, 1677721600000000000u64,
    2097152000000000000u64, 1310720000000000000u64, 1638400000000000000u64, 2048000000000000000u64,
    1280000000000000000u64, 1600000000000000000u64, 2000000000000000000u64, 1250000000000000000u64,
    1562500000000000000u64, 1953125000000000000u64, 1220703125000000000u64, 1525878906250000000u64,
    1907348632812500000u64, 1192092895507812500u64, 1490116119384765625u64, 1862645149230957031u64,
    1164153218269348144u64, 1455191522836685180u64, 1818989403545856475u64, 2273736754432320594u64,
    1421085471520200371u64, 1776356839400250464u64, 2220446049250313080u64, 1387778780781445675u64,
    1734723475976807094u64, 2168404344971008868u64, 1355252715606880542u64, 1694065894508600678u64,
    2117582368135750847u64, 1323488980084844279u64, 1654361225106055349u64, 2067951531382569187u64,
    1292469707114105741u64, 1615587133892632177u64, 2019483917365790221u64
];

#[inline]
fn pow_5_factor(mut value: u32 ) -> u32 {
    for count in 0.. {
        if value <= 0 {
           break;
        }
        if value % 5 != 0 {
            return count;
        }
        value /= 5;
    }

    return 0;
}

/// Returns true if value is divisible by 5^p.
#[inline]
fn multiple_of_power_of_5(value: u32, p: i32) -> bool {
    // @@@ Is this necessary? Is p ever negative?
    if p < 0 { return false; }
    return pow_5_factor(value) >= p as u32;
}

fn mul_shift(m: u32, factor: u64, shift: u32 ) -> u32 {
    debug_assert!(shift > 32);

    let factor_lo: u32 = factor as u32; // @@@ may need unchecked or something
    let factor_hi: u32 = (factor >> 32) as u32;
    let bits_0: u64 = (m as u64) * (factor_lo as u64);
    let bits_1: u64 = (m as u64) * (factor_hi as u64);

    let sum : u64 = (bits_0 >> 32) + bits_1;
    let shifted_sum : u64 = sum >> (shift - 32);

    debug_assert!(shifted_sum <= std::u32::MAX as u64);

    return shifted_sum as u32;
}

#[inline]
fn mul_pow5inv_div_pow2(m: u32, q: u32, j: u32 ) -> u32 {
    mul_shift(m, FLOAT_POW5_INV_SPLIT[q as usize], j)
}

#[inline]
fn mul_pow5div_pow2(m: u32, i: u32, j: u32 ) -> u32 {
    mul_shift(m, FLOAT_POW5_SPLIT[i as usize], j)
}

fn decimal_length(v: u32 ) -> u32 {
    // Function precondition: v is not a 10-digit number.
    // (9 digits are sufficient for round-tripping.)
    debug_assert!(v < 1000000000);
    
    if v >= 100000000 { return 9; }
    if v >= 10000000 { return 8; }
    if v >= 1000000 { return 7; }
    if v >= 100000 { return 6; }
    if v >= 10000 { return 5; }
    if v >= 1000 { return 4; }
    if v >= 100 { return 3; }
    if v >= 10 { return 2; }
    return 1;
}

const F32_MANTISSA_BITS: u32 = 23;
const F32_EXP_BITS: u32 = 8;
const F32_OFFSET: u32 = (1u32 << (F32_EXP_BITS - 1)) - 1;

pub fn write_f32_shortest<W: Write>(mut writer: W, num: f32 ) -> Result<usize> {

    // TODO: may want to extract the bulk of this code to prevent large amounts of code being generated if using multiple Write implementations...

    let bits = num.to_bits();

    let sign: bool = ((bits >> (F32_MANTISSA_BITS + F32_EXP_BITS)) & 1) != 0;
    let ieee_mantissa: u32 = bits & ((1u32 << F32_MANTISSA_BITS) - 1);
    let ieee_exponent: u32 = (bits >> F32_MANTISSA_BITS) & ((1u32 << F32_EXP_BITS) - 1);

    let e2: i32;
    let m2: u32;

    if ieee_exponent == ( 1 << F32_EXP_BITS ) - 1 {
        // @@@
        if ieee_mantissa != 0 {
            return writer.write( "NaN".as_bytes() );
        }
        else {
            if sign {
                return writer.write( "-inf".as_bytes() );
            }
            else {
                return writer.write( "inf".as_bytes() );
            }
        }
    }
    else if ieee_exponent == 0 {
        if ieee_mantissa == 0 {
            if sign {
                return writer.write( "-0".as_bytes() );
            }
            else {
                return writer.write( "0".as_bytes() );
            }
        }
            // We subtract 2 so that the bounds computation has 2 additional bits.
            e2 = 1i32 - ( F32_OFFSET as i32 ) - ( F32_MANTISSA_BITS as i32 ) - 2;
            m2 = ieee_mantissa;
    }
    else
    {
        e2 = ( ieee_exponent as i32 ) - ( F32_OFFSET as i32 ) - ( F32_MANTISSA_BITS as i32 ) - 2;
        m2 = (1u32 << F32_MANTISSA_BITS) | ieee_mantissa;
    }

    let even = (m2 & 1) == 0;
    let accept_bounds = even; // @@@ remove?

    // Step 2: Determine the interval of legal decimal representations.
    let mv: u32 = 4 * m2;
    let mp: u32 = 4 * m2 + 2;
    let mm: u32 = 4 * m2 - ( if (m2 != (1u32 << F32_MANTISSA_BITS)) || (ieee_exponent <= 1) { 2 } else { 1 } );

    // Step 3: Convert to a decimal power base using 64-bit arithmetic.
    let mut vr: u32;
    let mut vp: u32;
    let mut vm: u32;
    let e10: i32;
    let mut vm_is_trailing_zeros = false;
    let mut vr_is_trailing_zeros = false;
    let mut last_removed_digit: u8 = 0;

    if e2 >= 0 {
        let q = log_10_pow_2(e2 as u32 );
        e10 = q as i32;
        let k = ( FLOAT_POW5_INV_BITCOUNT as u32 ) + pow5bits(q ) - 1;
        let i = -e2 + q as i32 + ( k as i32 );
        vr = mul_pow5inv_div_pow2(mv, q, i as u32);
        vp = mul_pow5inv_div_pow2(mp, q, i as u32);
        vm = mul_pow5inv_div_pow2(mm, q, i as u32);

        if q != 0 && ((vp - 1) / 10 <= vm / 10) {
            // We need to know one removed digit even if we are not going to loop below. We could use
            // q = X - 1 above, except that would require 33 bits for the result, and we've found that
            // 32-bit arithmetic is faster even on 64-bit machines.
            let l: i32 = ( FLOAT_POW5_INV_BITCOUNT as i32 ) + ( pow5bits(q - 1) as i32 ) - 1;
            last_removed_digit = (mul_pow5inv_div_pow2(mv, q - 1, (-e2 + ( q as i32) - 1 + l) as u32) % 10) as u8;
        }
        if q <= 9 {
            // Only one of mp, mv, and mm can be a multiple of 5, if any.
            if mv % 5 == 0 {
                vr_is_trailing_zeros = multiple_of_power_of_5(mv, q as i32);
            } else {
                if accept_bounds {
                    vm_is_trailing_zeros = multiple_of_power_of_5(mm, q as i32);
                } else {
                    vp -= if multiple_of_power_of_5(mp, q as i32) { 1 } else { 0 };
                }
            }
        }
    } else {
        let q = log_10_pow_5((-e2) as u32 ) as i32;
        e10 = ( q as i32 ) + e2;
        let i = ( -e2 - ( q as i32 )) as u32;
        let k: i32 = pow5bits(i) as i32 - FLOAT_POW5_BITCOUNT as i32;
        let mut j= ( q - k ) as u32;
        vr = mul_pow5div_pow2(mv, i, j);
        vp = mul_pow5div_pow2(mp, i, j);
        vm = mul_pow5div_pow2(mm, i, j);

        if q != 0 && ((vp - 1) / 10 <= vm / 10) {
            j = ( q - 1 - (pow5bits(i + 1) as i32 - FLOAT_POW5_BITCOUNT as i32)) as u32;
            last_removed_digit = (mul_pow5div_pow2(mv, i + 1, j) % 10) as u8;
        }

        if q <= 1 {
            vr_is_trailing_zeros = (!mv & 1) >= q as u32;
            if accept_bounds {
                vm_is_trailing_zeros = (!mm & 1) >= q as u32;
            }
            else {
                vp -= 1;
            }
        } else if q < 31 { // TODO(ulfjack): Use a tighter bound here.
            vr_is_trailing_zeros = (mv & ((1u32 << (q - 1)) - 1)) == 0;
        }
    }

    // Step 4: Find the shortest decimal representation in the interval of legal representations.
    let mut removed: u32 = 0;
    let mut output: u32;
    if vm_is_trailing_zeros || vr_is_trailing_zeros {
        // General case, which happens rarely.
        while vp / 10 > vm / 10 {
            vm_is_trailing_zeros &= vm % 10 == 0;
            vr_is_trailing_zeros &= last_removed_digit == 0;
            last_removed_digit = (vr % 10) as u8;
            vr /= 10;
            vp /= 10;
            vm /= 10;
            removed += 1;
        }
        if vm_is_trailing_zeros {
            while vm % 10 == 0 {
                vr_is_trailing_zeros &= last_removed_digit == 0;
                last_removed_digit = (vr % 10) as u8;
                vr /= 10;
                vp /= 10;
                vm /= 10;
                removed += 1;
            }
        }
        if vr_is_trailing_zeros && (last_removed_digit == 5) && (vr % 2 == 0) {
            // Round down not up if the number ends in X50000.
            last_removed_digit = 4;
        }
        // We need to take vr+1 if vr is outside bounds or we need to round up.
        output = vr + if (vr == vm && (!accept_bounds || !vm_is_trailing_zeros)) || last_removed_digit >= 5 { 1 } else { 0 };
    } else {
        // Common case.
        while vp / 10 > vm / 10 {
            last_removed_digit = (vr % 10) as u8;
            vr /= 10;
            vp /= 10;
            vm /= 10;
            removed += 1;
        }
        // We need to take vr+1 if vr is outside bounds or we need to round up.
        output = vr + if vr == vm || last_removed_digit >= 5 { 1 } else { 0 };
    }
    let o_length: u32 = decimal_length(output);
    let vp_length: u32 = o_length + removed;

    let mut exp: i32 = ( e10 + vp_length  as i32 ) as i32 - 1;

    // Step 5: Print the decimal representation.
    let mut index: usize = 0;
    let mut result: [u8;24] = [0; 24];

    if sign {
        result[index] = '-' as u8;
        index += 1;
    }

    // @@@ Removed DIGIT TABLE optimisation

    // Print decimal digits after the decimal point.
    for i in 0 .. o_length as usize - 1 {
        let c: u32 = output % 10;
        output /= 10;
        result[index + o_length as usize - i] = (( '0' as u32 ) + c ) as u8;
    }

    // Print the leading decimal digit.
    result[index] = '0' as u8 + ( output % 10 ) as u8;

    // Print decimal point if needed.
    if o_length > 1 {
        result[index + 1] = '.' as u8;
        index += o_length as usize + 1;
    } else {
        index+=1;
    }

    // Print the exponent.
    result[index] = 'e' as u8;
    index+=1;
    if exp < 0 {
        result[index] = '-' as u8;
        index+=1;
        exp = -exp;
    }

    // @@@ Removed DIGIT TABLE optimisation

    if exp >= 10 {
        result[index] = '0' as u8 + ( (exp / 10) % 10 ) as u8;
        index+=1;
    }
    result[index] = '0' as u8 + ( exp % 10 ) as u8;
    index += 1;

    writer.write(&result[0..index] )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f32_test_num( number: f32, text: &str ) {
        let mut buffer : Vec<u8> = Vec::with_capacity( 32 );
        write_f32_shortest( &mut buffer, number ).unwrap();

        assert_eq!(std::str::from_utf8(&buffer).unwrap(),text);
    }

    #[test]
    fn f32_samples() {
        f32_test_num(-215.1291248e-43,"-2.1513e-41");
        f32_test_num(0.0,"0");
        f32_test_num(std::f32::INFINITY,"inf");
        f32_test_num(-std::f32::INFINITY,"-inf");
        f32_test_num(std::f32::MAX,"3.4028235e38");
        f32_test_num(std::f32::MIN,"-3.4028235e38");
    }
}