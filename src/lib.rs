use std::io::{Write,Result};
//use std::fmt::{LowerExp, UpperExp, Display, Debug};

const F32_MANTISSA_BITS: u32 = 23;
const F32_EXP_BITS: u32 = 8;
const F32_OFFSET: u32 = (1u32 << (F32_EXP_BITS - 1)) - 1;
const F32_POW5_BIT_COUNT: u32 = 61;
const F32_POW5_INV_BIT_COUNT: u32 = 59;
const F64_MANTISSA_BITS: i32 = 52;
const F64_EXP_BITS: i32 = 11;
const F64_OFFSET: i32 = (1 << (F64_EXP_BITS - 1)) - 1;
const F64_POW5_BIT_COUNT: i32 = 121;
const F64_POW5_INV_BIT_COUNT: u32 = 122;


/// Returns e == 0 ? 1 : ceil(log_2(5^e)).
#[inline]
fn pow5_bits(e: u32 ) -> u32 {
    // This function has only been tested for 0 <= e <= 1500.
    debug_assert!(e <= 1500);

    ((e * 1217359) >> 19) + 1
}

/// Returns floor(log10(2^e)).
#[inline]
fn log10_pow2(e: u32 ) -> u32
{
    // This function has only been tested for 0 <= e <= 1500.
    debug_assert!(e <= 1500);

    (e * 78913) >> 18
}

/// Returns floor(log10(5^e)).
#[inline]
fn log10_pow5(e: u32 ) -> u32
{
    // This function has only been tested for 0 <= e <= 1500.
    debug_assert!(e <= 1500);

    (e * 732923) >> 20
}



#[inline]
fn pow5_factor_32(mut value: u32 ) -> u32 {
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

#[inline]
fn pow5_factor_64(mut value: u64 ) -> u32 {
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
fn multiple_of_pow5_32(value: u32, p: i32) -> bool {
    // @@@ Is this necessary? Is p ever negative?
    if p < 0 { return false; }
    return pow5_factor_32(value) >= p as u32;
}

/// Returns true if value is divisible by 5^p.
#[inline]
fn multiple_of_pow5_64(value: u64, p: i32) -> bool {
    // @@@ Is this necessary? Is p ever negative?
    if p < 0 { return false; }
    return pow5_factor_64(value) >= p as u32;
}

fn mul_shift_32(m: u32, factor: u64, shift: u32 ) -> u32 {
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

/// We need a 64x128-bit multiplication and a subsequent 128-bit shift.
/// Multiplication:
///   The 64-bit factor is variable and passed in, the 128-bit factor comes
///   from a lookup table. We know that the 64-bit factor only has 55
///   significant bits (i.e., the 9 topmost bits are zeros). The 128-bit
///   factor only has 124 significant bits (i.e., the 4 topmost bits are
///   zeros).
/// Shift:
///   In principle, the multiplication result requires 55+124=179 bits to
///   represent. However, we then shift this value to the right by j, which is
///   at least j >= 115, so the result is guaranteed to fit into 179-115=64
///   bits. This means that we only need the topmost 64 significant bits of
///   the 64x128-bit multiplication.
#[inline]
fn mul_shift_64( m: u64, mul0: u64, mul1: u64, shift: u32 ) -> u64 {
    debug_assert!(shift > 64);

    let b0: u128 = m as u128 * mul0 as u128;
    let b2: u128 = m as u128 * mul1 as u128;
    (((b0 >> 64) + b2) >> (shift - 64)) as u64
}

#[inline]
fn mul_pow5_inv_div_pow2(m: u32, q: u32, j: u32 ) -> u32 {
    mul_shift_32(m, F32_POW5_INV_SPLIT[q as usize], j)
}

#[inline]
fn mul_pow5_div_pow2(m: u32, i: u32, j: u32 ) -> u32 {
    mul_shift_32(m, F32_POW5_SPLIT[i as usize], j)
}

fn decimal_length_32(v: u32 ) -> u32 {
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

fn decimal_length_64(v: u64) -> u32 {

    // This is slightly faster than a loop.
    // The average output length is 16.38 digits, so we check high-to-low.
    // Function precondition: v is not an 18, 19, or 20-digit number.
    // (17 digits are sufficient for round-tripping.)
    debug_assert!(v < 100000000000000000u64);

    if v >= 10000000000000000u64 { return 17; }
    if v >= 1000000000000000u64 { return 16; }
    if v >= 100000000000000u64 { return 15; }
    if v >= 10000000000000u64 { return 14; }
    if v >= 1000000000000u64 { return 13; }
    if v >= 100000000000u64 { return 12; }
    if v >= 10000000000u64 { return 11; }
    if v >= 1000000000u64 { return 10; }
    if v >= 100000000u64 { return 9; }
    if v >= 10000000u64 { return 8; }
    if v >= 1000000u64 { return 7; }
    if v >= 100000u64 { return 6; }
    if v >= 10000u64 { return 5; }
    if v >= 1000u64 { return 4; }
    if v >= 100u64 { return 3; }
    if v >= 10u64 { return 2; }
    return 1;
}

pub fn write_f32_shortest<W: Write>(mut writer: W, num: f32 ) -> Result<usize> {

    // TODO: may want to extract the bulk of this code to prevent large amounts of code being generated if using multiple Write implementations...

    let bits = num.to_bits();

    let sign: bool = ((bits >> (F32_MANTISSA_BITS + F32_EXP_BITS)) & 1) != 0;
    let ieee_mantissa: u32 = bits & ((1u32 << F32_MANTISSA_BITS) - 1);
    let ieee_exponent: u32 = (bits >> F32_MANTISSA_BITS) & ((1u32 << F32_EXP_BITS) - 1);

    let e2: i32;
    let m2: u32;

    if ieee_exponent == ( 1 << F32_EXP_BITS ) - 1 {
        if ieee_mantissa != 0 {
            return writer.write( b"NaN" );
        }
        else {
            if sign {
                return writer.write( b"-inf" );
            }
            else {
                return writer.write( b"inf" );
            }
        }
    }
    else if ieee_exponent == 0 {
        if ieee_mantissa == 0 {
            if sign {
                return writer.write( b"-0e0" );
            }
            else {
                return writer.write( b"0e0" );
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
        let q = log10_pow2(e2 as u32 );
        e10 = q as i32;
        let k = ( F32_POW5_INV_BIT_COUNT as u32 ) + pow5_bits(q ) - 1;
        let i = -e2 + q as i32 + ( k as i32 );
        vr = mul_pow5_inv_div_pow2(mv, q, i as u32);
        vp = mul_pow5_inv_div_pow2(mp, q, i as u32);
        vm = mul_pow5_inv_div_pow2(mm, q, i as u32);

        if q != 0 && ((vp - 1) / 10 <= vm / 10) {
            // We need to know one removed digit even if we are not going to loop below. We could use
            // q = X - 1 above, except that would require 33 bits for the result, and we've found that
            // 32-bit arithmetic is faster even on 64-bit machines.
            let l: i32 = ( F32_POW5_INV_BIT_COUNT as i32 ) + ( pow5_bits(q - 1) as i32 ) - 1;
            last_removed_digit = (mul_pow5_inv_div_pow2(mv, q - 1, (-e2 + ( q as i32) - 1 + l) as u32) % 10) as u8;
        }
        if q <= 9 {
            // Only one of mp, mv, and mm can be a multiple of 5, if any.
            if mv % 5 == 0 {
                vr_is_trailing_zeros = multiple_of_pow5_32(mv, q as i32);
            } else {
                if accept_bounds {
                    vm_is_trailing_zeros = multiple_of_pow5_32(mm, q as i32);
                } else {
                    vp -= if multiple_of_pow5_32(mp, q as i32) { 1 } else { 0 };
                }
            }
        }
    } else {
        let q = log10_pow5((-e2) as u32 ) as i32;
        e10 = ( q as i32 ) + e2;
        let i = ( -e2 - ( q as i32 )) as u32;
        let k: i32 = pow5_bits(i) as i32 - F32_POW5_BIT_COUNT as i32;
        let mut j= ( q - k ) as u32;
        vr = mul_pow5_div_pow2(mv, i, j);
        vp = mul_pow5_div_pow2(mp, i, j);
        vm = mul_pow5_div_pow2(mm, i, j);

        if q != 0 && ((vp - 1) / 10 <= vm / 10) {
            j = ( q - 1 - (pow5_bits(i + 1) as i32 - F32_POW5_BIT_COUNT as i32)) as u32;
            last_removed_digit = (mul_pow5_div_pow2(mv, i + 1, j) % 10) as u8;
        }

        if q <= 1 {
            vr_is_trailing_zeros = (!mv & 1) >= q as u32;
            if accept_bounds {
                vm_is_trailing_zeros = (!mm & 1) >= q as u32;
            }
            else {
                vp -= 1;
            }
        } else if q < 31 { // TODO: @u32fjack: Use a tighter bound here.
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
    let o_length: u32 = decimal_length_32(output);
    let vp_length: u32 = o_length + removed;

    let mut exp: i32 = ( e10 + vp_length  as i32 ) as i32 - 1;

    // Step 5: Print the decimal representation.
    let mut index: usize = 0;
    let mut result: [u8;24] = [0; 24];

    if sign {
        result[index] = '-' as u8;
        index += 1;
    }

    // @@@ Removed DIGIT_TABLE optimisation

    // Print decimal digits after the decimal point.
    for i in 0 .. o_length as usize - 1 {
        let c = ( output % 10 ) as u8;
        output /= 10;
        result[index + o_length as usize - i] = b'0' + c;
    }

    // Print the leading decimal digit.
    result[index] = b'0' + ( output % 10 ) as u8;

    // Print decimal point if needed.
    if o_length > 1 {
        result[index + 1] = '.' as u8;
        index += o_length as usize + 1;
    } else {
        index+=1;
    }

    // Print the exponent.
    result[index] = b'e';
    index+=1;
    if exp < 0 {
        result[index] = b'-';
        index+=1;
        exp = -exp;
    }

    // @@@ Removed DIGIT_TABLE optimisation

    if exp >= 10 {
        result[index] = b'0' + ( (exp / 10) % 10 ) as u8;
        index+=1;
    }
    result[index] = b'0' + ( exp % 10 ) as u8;
    index += 1;

    writer.write(&result[0..index] )
}

pub fn write_f64_shortest<W: Write>(mut writer: W, num: f64 ) -> Result<usize> {
    // Step 1: Decode the floating-point number, and unify normalized and subnormal cases.
     let bits: u64 = num.to_bits();

    // Decode bits into sign, mantissa, and exponent.
    let sign: bool =  ((bits >> (F64_MANTISSA_BITS + F64_EXP_BITS)) & 1) != 0;
    let ieee_mantissa: u64 = bits & ((1u64 << F64_MANTISSA_BITS) - 1);
    let ieee_exponent: u32 = ((bits >> F64_MANTISSA_BITS) & ((1u64 << F64_EXP_BITS) - 1)) as u32;

    let e2: i32;
    let m2: u64;
    // Case distinction; exit early for the easy cases.
    if ieee_exponent == ((1u32 << F64_EXP_BITS) - 1u32) || (ieee_exponent == 0 && ieee_mantissa == 0) {
        if ieee_mantissa != 0 {
            return writer.write( b"NaN" );
        }
        if ieee_exponent != 0 {
            if sign {
                return writer.write( b"-inf" );
            }  else {
                return writer.write( b"inf" );
            }
        }
        if sign {
            return writer.write( b"-0e0" );
        } else {
            return writer.write( b"0e0" );
        }
    } else if ieee_exponent == 0 {
        // We subtract 2 so that the bounds computation has 2 additional bits.
        e2 = 1 - F64_OFFSET - F64_MANTISSA_BITS - 2;
        m2 = ieee_mantissa;
    } else {
        e2 = ieee_exponent as i32 - F64_OFFSET - F64_MANTISSA_BITS - 2;
        m2 = (1u64 << F64_MANTISSA_BITS) | ieee_mantissa;
    }
    let even: bool =  (m2 & 1) == 0;
    let accept_bounds: bool =  even;

    // Step 2: Determine the interval of legal decimal representations.
    let mv: u64 =  4 * m2;
    // Implicit bool -> int conversion. True is 1, false is 0.
    let mm_shift: u64 = if (m2 != (1u64 << F64_MANTISSA_BITS)) || (ieee_exponent <= 1) { 1 } else { 0 };
    // We would compute mp and mm like this:
    //  u64 mp = 4 * m2 + 2;
    //  u64 mm = mv - 1 - mm_shift;

    // Step 3: Convert to a decimal power base using 128-bit arithmetic.
    let mut vr: u64;
    let mut vp: u64;
    let mut vm: u64;
    let e10: i32;
    let mut vm_is_trailing_zeros = false;
    let mut vr_is_trailing_zeros = false;
    if e2 >= 0 {
        // I tried special-casing q == 0, but there was no effect on performance.
        // This expression is slightly faster than max(0, log10Pow2(e2) - 1).
        let q: i32 = log10_pow2(e2 as u32) as i32 - if e2 > 3 { 1 } else { 0 };
        e10 = q;
        let k: i32 = ( F64_POW5_INV_BIT_COUNT + pow5_bits(q as u32 )) as i32 - 1;
        let i: i32 = -e2 + q + k;

        let mul0: u64 = DOUBLE_POW5_INV_SPLIT[q as usize][0];
        let mul1: u64 = DOUBLE_POW5_INV_SPLIT[q as usize][1];
        vr = mul_shift_64(4 * m2,                mul0, mul1, i as u32);
        vp = mul_shift_64(4 * m2 + 2,            mul0, mul1, i as u32);
        vm = mul_shift_64(4 * m2 - 1 - mm_shift, mul0, mul1, i as u32);

        if q <= 21 {
            // Only one of mp, mv, and mm can be a multiple of 5, if any.
            if mv % 5 == 0 {
                vr_is_trailing_zeros = multiple_of_pow5_64(mv, q);
            }
                else {
                    if accept_bounds {
                        // Same as min(e2 + (~mm & 1), pow5Factor(mm)) >= q
                        // <=> e2 + (~mm & 1) >= q && pow5Factor(mm) >= q
                        // <=> true && pow5Factor(mm) >= q, since e2 >= q.
                        vm_is_trailing_zeros = multiple_of_pow5_64(mv - 1 - mm_shift, q);
                    }
                        else {
                            // Same as min(e2 + 1, pow5Factor(mp)) >= q.
                            vp -= if multiple_of_pow5_64(mv + 2, q) { 1 } else { 0 };
                        }
                }
        }
    } else {
        // This expression is slightly faster than max(0, log10_pow5_64(-e2) - 1).
        let q: i32 = log10_pow5(( -e2 ) as u32) as i32 - ( if -e2 > 1 { 1 } else { 0 });
        e10 = q + e2;
        let i: i32 = -e2 - q;
        let k: i32 = pow5_bits(i as u32 ) as i32 - F64_POW5_BIT_COUNT;
        let j: i32 = q - k;

        let mul0: u64 = DOUBLE_POW5_SPLIT[i as usize][0];
        let mul1: u64 = DOUBLE_POW5_SPLIT[i as usize][1];
        vr = mul_shift_64(4 * m2,                       mul0, mul1, j as u32);
        vp = mul_shift_64(4 * m2 + 2,                   mul0, mul1, j as u32);
        vm = mul_shift_64(4 * m2 - 1 - mm_shift as u64, mul0, mul1, j as u32);


        if q <= 1 {
            vr_is_trailing_zeros = (!(mv as u32) & 1) >= q as u32;
            if accept_bounds {
                vm_is_trailing_zeros = (!((mv - 1 - mm_shift as u64) as u32) & 1) >= q as u32;
            } else {
                vp -= 1;
            }
        }  else if q < 63 { // TODO(u32fjack): Use a tighter bound here.
            // We need to compute min(ntz(mv), pow5Factor(mv) - e2) >= q-1
            // <=> ntz(mv) >= q-1  &&  pow5Factor(mv) - e2 >= q-1
            // <=> ntz(mv) >= q-1
            // <=> (mv & ((1 << (q-1)) - 1)) == 0
            // We also need to make sure that the left shift does not overflow.
            vr_is_trailing_zeros = (mv & ((1u64 << (q - 1)) - 1)) == 0;
        }
    }

    // Step 4: Find the shortest decimal representation in the interval of legal representations.
    let mut removed: usize = 0;
    let mut last_removed_digit: u8 = 0;
    let mut output: u64;
    // On average, we remove ~2 digits.
    if vm_is_trailing_zeros || vr_is_trailing_zeros {
        // General case, which happens rarely (<1%).
        while vp / 10 > vm / 10 {
            // https://bugs.llvm.org/show_bug.cgi?id=23106
            // The compiler does not realize that vm % 10 can be computed from vm / 10
            // as vm - (vm / 10) * 10.
            vm_is_trailing_zeros &= vm - (vm / 10) * 10 == 0;
            // vm_is_trailing_zeros &= vm % 10 == 0;
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
        output = vr + if (vr == vm && (!accept_bounds || !vm_is_trailing_zeros)) || (last_removed_digit >= 5) { 1 } else { 0 };
    } else {
        // Specialized for the common case (>99%).
        while vp / 10 > vm / 10 {
            last_removed_digit = (vr % 10) as u8;
            vr /= 10;
            vp /= 10;
            vm /= 10;
            removed += 1;
        }

        // We need to take vr+1 if vr is outside bounds or we need to round up.
        output = vr + ( if (vr == vm) || (last_removed_digit >= 5) { 1 } else { 0 } );
    }
    // The average output length is 16.38 digits.
    let o_length: usize =  decimal_length_64(output) as usize;
    let vp_length: usize =  o_length + removed;
    let mut exp: i32 = e10 + vp_length as i32 - 1;

    // Step 5: Print the decimal representation.
    let mut result: [u8;24] = [0; 24]; // the longest required is apparently: -2.2250738585072020E−308
    let mut index: usize = 0;
    if sign {
        result[index] = b'-';
        index+=1;
    }

        // Print decimal digits after the decimal point.
    for i in 0 .. o_length - 1 {
        let c = output % 10;
        output /= 10;
        result[index + o_length - i] = b'0' + c as u8;
    }
    // Print the leading decimal digit.
    result[index] = b'0' + ( output % 10 ) as u8;

    // Print decimal point if needed.
    if o_length > 1 {
        result[index + 1] = b'.';
        index += o_length + 1;
    } else {
        index+=1;
    }

    // Print the exponent.
    result[index] = b'e';
    index += 1;
    if exp < 0 {
        result[index] = b'-';
        index += 1;
        exp = -exp;
    }

    if exp >= 100 {
        result[index] = b'0' + ( exp / 100 ) as u8;
        index += 1;
    }
    if exp >= 10 {
        result[index] = b'0' + ((exp / 10) % 10) as u8;
        index += 1;
    }
    result[index] = b'0' + ( exp % 10 ) as u8;
    index += 1;


    writer.write(&result[0..index] )
}

const F32_POW5_INV_SPLIT: [u64;31] = [
    576460752303423489u64, 461168601842738791u64, 368934881474191033u64, 295147905179352826u64,
    472236648286964522u64, 377789318629571618u64, 302231454903657294u64, 483570327845851670u64,
    386856262276681336u64, 309485009821345069u64, 495176015714152110u64, 396140812571321688u64,
    316912650057057351u64, 507060240091291761u64, 405648192073033409u64, 324518553658426727u64,
    519229685853482763u64, 415383748682786211u64, 332306998946228969u64, 531691198313966350u64,
    425352958651173080u64, 340282366920938464u64, 544451787073501542u64, 435561429658801234u64,
    348449143727040987u64, 557518629963265579u64, 446014903970612463u64, 356811923176489971u64,
    570899077082383953u64, 456719261665907162u64, 365375409332725730u64
];

const F32_POW5_SPLIT: [u64;47] = [
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

const DOUBLE_POW5_INV_SPLIT: [[u64;2];292] = [
    [                    1u64, 288230376151711744u64 ], [  3689348814741910324u64, 230584300921369395u64 ],
    [  2951479051793528259u64, 184467440737095516u64 ], [ 17118578500402463900u64, 147573952589676412u64 ],
    [ 12632330341676300947u64, 236118324143482260u64 ], [ 10105864273341040758u64, 188894659314785808u64 ],
    [ 15463389048156653253u64, 151115727451828646u64 ], [ 17362724847566824558u64, 241785163922925834u64 ],
    [ 17579528692795369969u64, 193428131138340667u64 ], [  6684925324752475329u64, 154742504910672534u64 ],
    [ 18074578149087781173u64, 247588007857076054u64 ], [ 18149011334012135262u64, 198070406285660843u64 ],
    [  3451162622983977240u64, 158456325028528675u64 ], [  5521860196774363583u64, 253530120045645880u64 ],
    [  4417488157419490867u64, 202824096036516704u64 ], [  7223339340677503017u64, 162259276829213363u64 ],
    [  7867994130342094503u64, 259614842926741381u64 ], [  2605046489531765280u64, 207691874341393105u64 ],
    [  2084037191625412224u64, 166153499473114484u64 ], [ 10713157136084480204u64, 265845599156983174u64 ],
    [ 12259874523609494487u64, 212676479325586539u64 ], [ 13497248433629505913u64, 170141183460469231u64 ],
    [ 14216899864323388813u64, 272225893536750770u64 ], [ 11373519891458711051u64, 217780714829400616u64 ],
    [  5409467098425058518u64, 174224571863520493u64 ], [  4965798542738183305u64, 278759314981632789u64 ],
    [  7661987648932456967u64, 223007451985306231u64 ], [  2440241304404055250u64, 178405961588244985u64 ],
    [  3904386087046488400u64, 285449538541191976u64 ], [ 17880904128604832013u64, 228359630832953580u64 ],
    [ 14304723302883865611u64, 182687704666362864u64 ], [ 15133127457049002812u64, 146150163733090291u64 ],
    [ 16834306301794583852u64, 233840261972944466u64 ], [  9778096226693756759u64, 187072209578355573u64 ],
    [ 15201174610838826053u64, 149657767662684458u64 ], [  2185786488890659746u64, 239452428260295134u64 ],
    [  5437978005854438120u64, 191561942608236107u64 ], [ 15418428848909281466u64, 153249554086588885u64 ],
    [  6222742084545298729u64, 245199286538542217u64 ], [ 16046240111861969953u64, 196159429230833773u64 ],
    [  1768945645263844993u64, 156927543384667019u64 ], [ 10209010661905972635u64, 251084069415467230u64 ],
    [  8167208529524778108u64, 200867255532373784u64 ], [ 10223115638361732810u64, 160693804425899027u64 ],
    [  1599589762411131202u64, 257110087081438444u64 ], [  4969020624670815285u64, 205688069665150755u64 ],
    [  3975216499736652228u64, 164550455732120604u64 ], [ 13739044029062464211u64, 263280729171392966u64 ],
    [  7301886408508061046u64, 210624583337114373u64 ], [ 13220206756290269483u64, 168499666669691498u64 ],
    [ 17462981995322520850u64, 269599466671506397u64 ], [  6591687966774196033u64, 215679573337205118u64 ],
    [ 12652048002903177473u64, 172543658669764094u64 ], [  9175230360419352987u64, 276069853871622551u64 ],
    [  3650835473593572067u64, 220855883097298041u64 ], [ 17678063637842498946u64, 176684706477838432u64 ],
    [ 13527506561580357021u64, 282695530364541492u64 ], [  3443307619780464970u64, 226156424291633194u64 ],
    [  6443994910566282300u64, 180925139433306555u64 ], [  5155195928453025840u64, 144740111546645244u64 ],
    [ 15627011115008661990u64, 231584178474632390u64 ], [ 12501608892006929592u64, 185267342779705912u64 ],
    [  2622589484121723027u64, 148213874223764730u64 ], [  4196143174594756843u64, 237142198758023568u64 ],
    [ 10735612169159626121u64, 189713759006418854u64 ], [ 12277838550069611220u64, 151771007205135083u64 ],
    [ 15955192865369467629u64, 242833611528216133u64 ], [  1696107848069843133u64, 194266889222572907u64 ],
    [ 12424932722681605476u64, 155413511378058325u64 ], [  1433148282581017146u64, 248661618204893321u64 ],
    [ 15903913885032455010u64, 198929294563914656u64 ], [  9033782293284053685u64, 159143435651131725u64 ],
    [ 14454051669254485895u64, 254629497041810760u64 ], [ 11563241335403588716u64, 203703597633448608u64 ],
    [ 16629290697806691620u64, 162962878106758886u64 ], [   781423413297334329u64, 260740604970814219u64 ],
    [  4314487545379777786u64, 208592483976651375u64 ], [  3451590036303822229u64, 166873987181321100u64 ],
    [  5522544058086115566u64, 266998379490113760u64 ], [  4418035246468892453u64, 213598703592091008u64 ],
    [ 10913125826658934609u64, 170878962873672806u64 ], [ 10082303693170474728u64, 273406340597876490u64 ],
    [  8065842954536379782u64, 218725072478301192u64 ], [ 17520720807854834795u64, 174980057982640953u64 ],
    [  5897060404116273733u64, 279968092772225526u64 ], [  1028299508551108663u64, 223974474217780421u64 ],
    [ 15580034865808528224u64, 179179579374224336u64 ], [ 17549358155809824511u64, 286687326998758938u64 ],
    [  2971440080422128639u64, 229349861599007151u64 ], [ 17134547323305344204u64, 183479889279205720u64 ],
    [ 13707637858644275364u64, 146783911423364576u64 ], [ 14553522944347019935u64, 234854258277383322u64 ],
    [  4264120725993795302u64, 187883406621906658u64 ], [ 10789994210278856888u64, 150306725297525326u64 ],
    [  9885293106962350374u64, 240490760476040522u64 ], [   529536856086059653u64, 192392608380832418u64 ],
    [  7802327114352668369u64, 153914086704665934u64 ], [  1415676938738538420u64, 246262538727465495u64 ],
    [  1132541550990830736u64, 197010030981972396u64 ], [ 15663428499760305882u64, 157608024785577916u64 ],
    [ 17682787970132668764u64, 252172839656924666u64 ], [ 10456881561364224688u64, 201738271725539733u64 ],
    [ 15744202878575200397u64, 161390617380431786u64 ], [ 17812026976236499989u64, 258224987808690858u64 ],
    [  3181575136763469022u64, 206579990246952687u64 ], [ 13613306553636506187u64, 165263992197562149u64 ],
    [ 10713244041592678929u64, 264422387516099439u64 ], [ 12259944048016053467u64, 211537910012879551u64 ],
    [  6118606423670932450u64, 169230328010303641u64 ], [  2411072648389671274u64, 270768524816485826u64 ],
    [ 16686253377679378312u64, 216614819853188660u64 ], [ 13349002702143502650u64, 173291855882550928u64 ],
    [ 17669055508687693916u64, 277266969412081485u64 ], [ 14135244406950155133u64, 221813575529665188u64 ],
    [   240149081334393137u64, 177450860423732151u64 ], [ 11452284974360759988u64, 283921376677971441u64 ],
    [  5472479164746697667u64, 227137101342377153u64 ], [ 11756680961281178780u64, 181709681073901722u64 ],
    [  2026647139541122378u64, 145367744859121378u64 ], [ 18000030682233437097u64, 232588391774594204u64 ],
    [ 18089373360528660001u64, 186070713419675363u64 ], [  3403452244197197031u64, 148856570735740291u64 ],
    [ 16513570034941246220u64, 238170513177184465u64 ], [ 13210856027952996976u64, 190536410541747572u64 ],
    [  3189987192878576934u64, 152429128433398058u64 ], [  1414630693863812771u64, 243886605493436893u64 ],
    [  8510402184574870864u64, 195109284394749514u64 ], [ 10497670562401807014u64, 156087427515799611u64 ],
    [  9417575270359070576u64, 249739884025279378u64 ], [ 14912757845771077107u64, 199791907220223502u64 ],
    [  4551508647133041040u64, 159833525776178802u64 ], [ 10971762650154775986u64, 255733641241886083u64 ],
    [ 16156107749607641435u64, 204586912993508866u64 ], [  9235537384944202825u64, 163669530394807093u64 ],
    [ 11087511001168814197u64, 261871248631691349u64 ], [ 12559357615676961681u64, 209496998905353079u64 ],
    [ 13736834907283479668u64, 167597599124282463u64 ], [ 18289587036911657145u64, 268156158598851941u64 ],
    [ 10942320814787415393u64, 214524926879081553u64 ], [ 16132554281313752961u64, 171619941503265242u64 ],
    [ 11054691591134363444u64, 274591906405224388u64 ], [ 16222450902391311402u64, 219673525124179510u64 ],
    [ 12977960721913049122u64, 175738820099343608u64 ], [ 17075388340318968271u64, 281182112158949773u64 ],
    [  2592264228029443648u64, 224945689727159819u64 ], [  5763160197165465241u64, 179956551781727855u64 ],
    [  9221056315464744386u64, 287930482850764568u64 ], [ 14755542681855616155u64, 230344386280611654u64 ],
    [ 15493782960226403247u64, 184275509024489323u64 ], [  1326979923955391628u64, 147420407219591459u64 ],
    [  9501865507812447252u64, 235872651551346334u64 ], [ 11290841220991868125u64, 188698121241077067u64 ],
    [  1653975347309673853u64, 150958496992861654u64 ], [ 10025058185179298811u64, 241533595188578646u64 ],
    [  4330697733401528726u64, 193226876150862917u64 ], [ 14532604630946953951u64, 154581500920690333u64 ],
    [  1116074521063664381u64, 247330401473104534u64 ], [  4582208431592841828u64, 197864321178483627u64 ],
    [ 14733813189500004432u64, 158291456942786901u64 ], [ 16195403473716186445u64, 253266331108459042u64 ],
    [  5577625149489128510u64, 202613064886767234u64 ], [  8151448934333213131u64, 162090451909413787u64 ],
    [ 16731667109675051333u64, 259344723055062059u64 ], [ 17074682502481951390u64, 207475778444049647u64 ],
    [  6281048372501740465u64, 165980622755239718u64 ], [  6360328581260874421u64, 265568996408383549u64 ],
    [  8777611679750609860u64, 212455197126706839u64 ], [ 10711438158542398211u64, 169964157701365471u64 ],
    [  9759603424184016492u64, 271942652322184754u64 ], [ 11497031554089123517u64, 217554121857747803u64 ],
    [ 16576322872755119460u64, 174043297486198242u64 ], [ 11764721337440549842u64, 278469275977917188u64 ],
    [ 16790474699436260520u64, 222775420782333750u64 ], [ 13432379759549008416u64, 178220336625867000u64 ],
    [  3045063541568861850u64, 285152538601387201u64 ], [ 17193446092222730773u64, 228122030881109760u64 ],
    [ 13754756873778184618u64, 182497624704887808u64 ], [ 18382503128506368341u64, 145998099763910246u64 ],
    [  3586563302416817083u64, 233596959622256395u64 ], [  2869250641933453667u64, 186877567697805116u64 ],
    [ 17052795772514404226u64, 149502054158244092u64 ], [ 12527077977055405469u64, 239203286653190548u64 ],
    [ 17400360011128145022u64, 191362629322552438u64 ], [  2852241564676785048u64, 153090103458041951u64 ],
    [ 15631632947708587046u64, 244944165532867121u64 ], [  8815957543424959314u64, 195955332426293697u64 ],
    [ 18120812478965698421u64, 156764265941034957u64 ], [ 14235904707377476180u64, 250822825505655932u64 ],
    [  4010026136418160298u64, 200658260404524746u64 ], [ 17965416168102169531u64, 160526608323619796u64 ],
    [  2919224165770098987u64, 256842573317791675u64 ], [  2335379332616079190u64, 205474058654233340u64 ],
    [  1868303466092863352u64, 164379246923386672u64 ], [  6678634360490491686u64, 263006795077418675u64 ],
    [  5342907488392393349u64, 210405436061934940u64 ], [  4274325990713914679u64, 168324348849547952u64 ],
    [ 10528270399884173809u64, 269318958159276723u64 ], [ 15801313949391159694u64, 215455166527421378u64 ],
    [  1573004715287196786u64, 172364133221937103u64 ], [ 17274202803427156150u64, 275782613155099364u64 ],
    [ 17508711057483635243u64, 220626090524079491u64 ], [ 10317620031244997871u64, 176500872419263593u64 ],
    [ 12818843235250086271u64, 282401395870821749u64 ], [ 13944423402941979340u64, 225921116696657399u64 ],
    [ 14844887537095493795u64, 180736893357325919u64 ], [ 15565258844418305359u64, 144589514685860735u64 ],
    [  6457670077359736959u64, 231343223497377177u64 ], [ 16234182506113520537u64, 185074578797901741u64 ],
    [  9297997190148906106u64, 148059663038321393u64 ], [ 11187446689496339446u64, 236895460861314229u64 ],
    [ 12639306166338981880u64, 189516368689051383u64 ], [ 17490142562555006151u64, 151613094951241106u64 ],
    [  2158786396894637579u64, 242580951921985771u64 ], [ 16484424376483351356u64, 194064761537588616u64 ],
    [  9498190686444770762u64, 155251809230070893u64 ], [ 11507756283569722895u64, 248402894768113429u64 ],
    [ 12895553841597688639u64, 198722315814490743u64 ], [ 17695140702761971558u64, 158977852651592594u64 ],
    [ 17244178680193423523u64, 254364564242548151u64 ], [ 10105994129412828495u64, 203491651394038521u64 ],
    [  4395446488788352473u64, 162793321115230817u64 ], [ 10722063196803274280u64, 260469313784369307u64 ],
    [  1198952927958798777u64, 208375451027495446u64 ], [ 15716557601334680315u64, 166700360821996356u64 ],
    [ 17767794532651667857u64, 266720577315194170u64 ], [ 14214235626121334286u64, 213376461852155336u64 ],
    [  7682039686155157106u64, 170701169481724269u64 ], [  1223217053622520399u64, 273121871170758831u64 ],
    [ 15735968901865657612u64, 218497496936607064u64 ], [ 16278123936234436413u64, 174797997549285651u64 ],
    [   219556594781725998u64, 279676796078857043u64 ], [  7554342905309201445u64, 223741436863085634u64 ],
    [  9732823138989271479u64, 178993149490468507u64 ], [   815121763415193074u64, 286389039184749612u64 ],
    [ 11720143854957885429u64, 229111231347799689u64 ], [ 13065463898708218666u64, 183288985078239751u64 ],
    [  6763022304224664610u64, 146631188062591801u64 ], [  3442138057275642729u64, 234609900900146882u64 ],
    [ 13821756890046245153u64, 187687920720117505u64 ], [ 11057405512036996122u64, 150150336576094004u64 ],
    [  6623802375033462826u64, 240240538521750407u64 ], [ 16367088344252501231u64, 192192430817400325u64 ],
    [ 13093670675402000985u64, 153753944653920260u64 ], [  2503129006933649959u64, 246006311446272417u64 ],
    [ 13070549649772650937u64, 196805049157017933u64 ], [ 17835137349301941396u64, 157444039325614346u64 ],
    [  2710778055689733971u64, 251910462920982955u64 ], [  2168622444551787177u64, 201528370336786364u64 ],
    [  5424246770383340065u64, 161222696269429091u64 ], [  1300097203129523457u64, 257956314031086546u64 ],
    [ 15797473021471260058u64, 206365051224869236u64 ], [  8948629602435097724u64, 165092040979895389u64 ],
    [  3249760919670425388u64, 264147265567832623u64 ], [  9978506365220160957u64, 211317812454266098u64 ],
    [ 15361502721659949412u64, 169054249963412878u64 ], [  2442311466204457120u64, 270486799941460606u64 ],
    [ 16711244431931206989u64, 216389439953168484u64 ], [ 17058344360286875914u64, 173111551962534787u64 ],
    [ 12535955717491360170u64, 276978483140055660u64 ], [ 10028764573993088136u64, 221582786512044528u64 ],
    [ 15401709288678291155u64, 177266229209635622u64 ], [  9885339602917624555u64, 283625966735416996u64 ],
    [  4218922867592189321u64, 226900773388333597u64 ], [ 14443184738299482427u64, 181520618710666877u64 ],
    [  4175850161155765295u64, 145216494968533502u64 ], [ 10370709072591134795u64, 232346391949653603u64 ],
    [ 15675264887556728482u64, 185877113559722882u64 ], [  5161514280561562140u64, 148701690847778306u64 ],
    [   879725219414678777u64, 237922705356445290u64 ], [   703780175531743021u64, 190338164285156232u64 ],
    [ 11631070584651125387u64, 152270531428124985u64 ], [   162968861732249003u64, 243632850284999977u64 ],
    [ 11198421533611530172u64, 194906280227999981u64 ], [  5269388412147313814u64, 155925024182399985u64 ],
    [  8431021459435702103u64, 249480038691839976u64 ], [  3055468352806651359u64, 199584030953471981u64 ],
    [ 17201769941212962380u64, 159667224762777584u64 ], [ 16454785461715008838u64, 255467559620444135u64 ],
    [ 13163828369372007071u64, 204374047696355308u64 ], [ 17909760324981426303u64, 163499238157084246u64 ],
    [  2830174816776909822u64, 261598781051334795u64 ], [  2264139853421527858u64, 209279024841067836u64 ],
    [ 16568707141704863579u64, 167423219872854268u64 ], [  4373838538276319787u64, 267877151796566830u64 ],
    [  3499070830621055830u64, 214301721437253464u64 ], [  6488605479238754987u64, 171441377149802771u64 ],
    [  3003071137298187333u64, 274306203439684434u64 ], [  6091805724580460189u64, 219444962751747547u64 ],
    [ 15941491023890099121u64, 175555970201398037u64 ], [ 10748990379256517301u64, 280889552322236860u64 ],
    [  8599192303405213841u64, 224711641857789488u64 ], [ 14258051472207991719u64, 179769313486231590u64 ]
];

const DOUBLE_POW5_SPLIT: [[u64;2];326] = [
    [                    0u64,  72057594037927936u64 ], [                    0u64,  90071992547409920u64 ],
    [                    0u64, 112589990684262400u64 ], [                    0u64, 140737488355328000u64 ],
    [                    0u64,  87960930222080000u64 ], [                    0u64, 109951162777600000u64 ],
    [                    0u64, 137438953472000000u64 ], [                    0u64,  85899345920000000u64 ],
    [                    0u64, 107374182400000000u64 ], [                    0u64, 134217728000000000u64 ],
    [                    0u64,  83886080000000000u64 ], [                    0u64, 104857600000000000u64 ],
    [                    0u64, 131072000000000000u64 ], [                    0u64,  81920000000000000u64 ],
    [                    0u64, 102400000000000000u64 ], [                    0u64, 128000000000000000u64 ],
    [                    0u64,  80000000000000000u64 ], [                    0u64, 100000000000000000u64 ],
    [                    0u64, 125000000000000000u64 ], [                    0u64,  78125000000000000u64 ],
    [                    0u64,  97656250000000000u64 ], [                    0u64, 122070312500000000u64 ],
    [                    0u64,  76293945312500000u64 ], [                    0u64,  95367431640625000u64 ],
    [                    0u64, 119209289550781250u64 ], [  4611686018427387904u64,  74505805969238281u64 ],
    [ 10376293541461622784u64,  93132257461547851u64 ], [  8358680908399640576u64, 116415321826934814u64 ],
    [   612489549322387456u64,  72759576141834259u64 ], [ 14600669991935148032u64,  90949470177292823u64 ],
    [ 13639151471491547136u64, 113686837721616029u64 ], [  3213881284082270208u64, 142108547152020037u64 ],
    [  4314518811765112832u64,  88817841970012523u64 ], [   781462496279003136u64, 111022302462515654u64 ],
    [ 10200200157203529728u64, 138777878078144567u64 ], [ 13292654125893287936u64,  86736173798840354u64 ],
    [  7392445620511834112u64, 108420217248550443u64 ], [  4628871007212404736u64, 135525271560688054u64 ],
    [ 16728102434789916672u64,  84703294725430033u64 ], [  7075069988205232128u64, 105879118406787542u64 ],
    [ 18067209522111315968u64, 132348898008484427u64 ], [  8986162942105878528u64,  82718061255302767u64 ],
    [  6621017659204960256u64, 103397576569128459u64 ], [  3664586055578812416u64, 129246970711410574u64 ],
    [ 16125424340018921472u64,  80779356694631608u64 ], [  1710036351314100224u64, 100974195868289511u64 ],
    [ 15972603494424788992u64, 126217744835361888u64 ], [  9982877184015493120u64,  78886090522101180u64 ],
    [ 12478596480019366400u64,  98607613152626475u64 ], [ 10986559581596820096u64, 123259516440783094u64 ],
    [  2254913720070624656u64,  77037197775489434u64 ], [ 12042014186943056628u64,  96296497219361792u64 ],
    [ 15052517733678820785u64, 120370621524202240u64 ], [  9407823583549262990u64,  75231638452626400u64 ],
    [ 11759779479436578738u64,  94039548065783000u64 ], [ 14699724349295723422u64, 117549435082228750u64 ],
    [  4575641699882439235u64,  73468396926392969u64 ], [ 10331238143280436948u64,  91835496157991211u64 ],
    [  8302361660673158281u64, 114794370197489014u64 ], [  1154580038986672043u64, 143492962746861268u64 ],
    [  9944984561221445835u64,  89683101716788292u64 ], [ 12431230701526807293u64, 112103877145985365u64 ],
    [  1703980321626345405u64, 140129846432481707u64 ], [ 17205888765512323542u64,  87581154020301066u64 ],
    [ 12283988920035628619u64, 109476442525376333u64 ], [  1519928094762372062u64, 136845553156720417u64 ],
    [ 12479170105294952299u64,  85528470722950260u64 ], [ 15598962631618690374u64, 106910588403687825u64 ],
    [  5663645234241199255u64, 133638235504609782u64 ], [ 17374836326682913246u64,  83523897190381113u64 ],
    [  7883487353071477846u64, 104404871487976392u64 ], [  9854359191339347308u64, 130506089359970490u64 ],
    [ 10770660513014479971u64,  81566305849981556u64 ], [ 13463325641268099964u64, 101957882312476945u64 ],
    [  2994098996302961243u64, 127447352890596182u64 ], [ 15706369927971514489u64,  79654595556622613u64 ],
    [  5797904354682229399u64,  99568244445778267u64 ], [  2635694424925398845u64, 124460305557222834u64 ],
    [  6258995034005762182u64,  77787690973264271u64 ], [  3212057774079814824u64,  97234613716580339u64 ],
    [ 17850130272881932242u64, 121543267145725423u64 ], [ 18073860448192289507u64,  75964541966078389u64 ],
    [  8757267504958198172u64,  94955677457597987u64 ], [  6334898362770359811u64, 118694596821997484u64 ],
    [ 13182683513586250689u64,  74184123013748427u64 ], [ 11866668373555425458u64,  92730153767185534u64 ],
    [  5609963430089506015u64, 115912692208981918u64 ], [ 17341285199088104971u64,  72445432630613698u64 ],
    [ 12453234462005355406u64,  90556790788267123u64 ], [ 10954857059079306353u64, 113195988485333904u64 ],
    [ 13693571323849132942u64, 141494985606667380u64 ], [ 17781854114260483896u64,  88434366004167112u64 ],
    [  3780573569116053255u64, 110542957505208891u64 ], [   114030942967678664u64, 138178696881511114u64 ],
    [  4682955357782187069u64,  86361685550944446u64 ], [ 15077066234082509644u64, 107952106938680557u64 ],
    [  5011274737320973344u64, 134940133673350697u64 ], [ 14661261756894078100u64,  84337583545844185u64 ],
    [  4491519140835433913u64, 105421979432305232u64 ], [  5614398926044292391u64, 131777474290381540u64 ],
    [ 12732371365632458552u64,  82360921431488462u64 ], [  6692092170185797382u64, 102951151789360578u64 ],
    [ 17588487249587022536u64, 128688939736700722u64 ], [ 15604490549419276989u64,  80430587335437951u64 ],
    [ 14893927168346708332u64, 100538234169297439u64 ], [ 14005722942005997511u64, 125672792711621799u64 ],
    [ 15671105866394830300u64,  78545495444763624u64 ], [  1142138259283986260u64,  98181869305954531u64 ],
    [ 15262730879387146537u64, 122727336632443163u64 ], [  7233363790403272633u64,  76704585395276977u64 ],
    [ 13653390756431478696u64,  95880731744096221u64 ], [  3231680390257184658u64, 119850914680120277u64 ],
    [  4325643253124434363u64,  74906821675075173u64 ], [ 10018740084832930858u64,  93633527093843966u64 ],
    [  3300053069186387764u64, 117041908867304958u64 ], [ 15897591223523656064u64,  73151193042065598u64 ],
    [ 10648616992549794273u64,  91438991302581998u64 ], [  4087399203832467033u64, 114298739128227498u64 ],
    [ 14332621041645359599u64, 142873423910284372u64 ], [ 18181260187883125557u64,  89295889943927732u64 ],
    [  4279831161144355331u64, 111619862429909666u64 ], [ 14573160988285219972u64, 139524828037387082u64 ],
    [ 13719911636105650386u64,  87203017523366926u64 ], [  7926517508277287175u64, 109003771904208658u64 ],
    [   684774848491833161u64, 136254714880260823u64 ], [  7345513307948477581u64,  85159196800163014u64 ],
    [ 18405263671790372785u64, 106448996000203767u64 ], [ 18394893571310578077u64, 133061245000254709u64 ],
    [ 13802651491282805250u64,  83163278125159193u64 ], [  3418256308821342851u64, 103954097656448992u64 ],
    [  4272820386026678563u64, 129942622070561240u64 ], [  2670512741266674102u64,  81214138794100775u64 ],
    [ 17173198981865506339u64, 101517673492625968u64 ], [  3019754653622331308u64, 126897091865782461u64 ],
    [  4193189667727651020u64,  79310682416114038u64 ], [ 14464859121514339583u64,  99138353020142547u64 ],
    [ 13469387883465536574u64, 123922941275178184u64 ], [  8418367427165960359u64,  77451838296986365u64 ],
    [ 15134645302384838353u64,  96814797871232956u64 ], [   471562554271496325u64, 121018497339041196u64 ],
    [  9518098633274461011u64,  75636560836900747u64 ], [  7285937273165688360u64,  94545701046125934u64 ],
    [ 18330793628311886258u64, 118182126307657417u64 ], [  4539216990053847055u64,  73863828942285886u64 ],
    [ 14897393274422084627u64,  92329786177857357u64 ], [  4786683537745442072u64, 115412232722321697u64 ],
    [ 14520892257159371055u64,  72132645451451060u64 ], [ 18151115321449213818u64,  90165806814313825u64 ],
    [  8853836096529353561u64, 112707258517892282u64 ], [  1843923083806916143u64, 140884073147365353u64 ],
    [ 12681666973447792349u64,  88052545717103345u64 ], [  2017025661527576725u64, 110065682146379182u64 ],
    [ 11744654113764246714u64, 137582102682973977u64 ], [   422879793461572340u64,  85988814176858736u64 ],
    [   528599741826965425u64, 107486017721073420u64 ], [   660749677283706782u64, 134357522151341775u64 ],
    [  7330497575943398595u64,  83973451344588609u64 ], [ 13774807988356636147u64, 104966814180735761u64 ],
    [  3383451930163631472u64, 131208517725919702u64 ], [ 15949715511634433382u64,  82005323578699813u64 ],
    [  6102086334260878016u64, 102506654473374767u64 ], [  3015921899398709616u64, 128133318091718459u64 ],
    [ 18025852251620051174u64,  80083323807324036u64 ], [  4085571240815512351u64, 100104154759155046u64 ],
    [ 14330336087874166247u64, 125130193448943807u64 ], [ 15873989082562435760u64,  78206370905589879u64 ],
    [ 15230800334775656796u64,  97757963631987349u64 ], [  5203442363187407284u64, 122197454539984187u64 ],
    [   946308467778435600u64,  76373409087490117u64 ], [  5794571603150432404u64,  95466761359362646u64 ],
    [ 16466586540792816313u64, 119333451699203307u64 ], [  7985773578781816244u64,  74583407312002067u64 ],
    [  5370530955049882401u64,  93229259140002584u64 ], [  6713163693812353001u64, 116536573925003230u64 ],
    [ 18030785363914884337u64,  72835358703127018u64 ], [ 13315109668038829614u64,  91044198378908773u64 ],
    [  2808829029766373305u64, 113805247973635967u64 ], [ 17346094342490130344u64, 142256559967044958u64 ],
    [  6229622945628943561u64,  88910349979403099u64 ], [  3175342663608791547u64, 111137937474253874u64 ],
    [ 13192550366365765242u64, 138922421842817342u64 ], [  3633657960551215372u64,  86826513651760839u64 ],
    [ 18377130505971182927u64, 108533142064701048u64 ], [  4524669058754427043u64, 135666427580876311u64 ],
    [  9745447189362598758u64,  84791517238047694u64 ], [  2958436949848472639u64, 105989396547559618u64 ],
    [ 12921418224165366607u64, 132486745684449522u64 ], [ 12687572408530742033u64,  82804216052780951u64 ],
    [ 11247779492236039638u64, 103505270065976189u64 ], [   224666310012885835u64, 129381587582470237u64 ],
    [  2446259452971747599u64,  80863492239043898u64 ], [ 12281196353069460307u64, 101079365298804872u64 ],
    [ 15351495441336825384u64, 126349206623506090u64 ], [ 14206370669262903769u64,  78968254139691306u64 ],
    [  8534591299723853903u64,  98710317674614133u64 ], [ 15279925143082205283u64, 123387897093267666u64 ],
    [ 14161639232853766206u64,  77117435683292291u64 ], [ 13090363022639819853u64,  96396794604115364u64 ],
    [ 16362953778299774816u64, 120495993255144205u64 ], [ 12532689120651053212u64,  75309995784465128u64 ],
    [ 15665861400813816515u64,  94137494730581410u64 ], [ 10358954714162494836u64, 117671868413226763u64 ],
    [  4168503687137865320u64,  73544917758266727u64 ], [   598943590494943747u64,  91931147197833409u64 ],
    [  5360365506546067587u64, 114913933997291761u64 ], [ 11312142901609972388u64, 143642417496614701u64 ],
    [  9375932322719926695u64,  89776510935384188u64 ], [ 11719915403399908368u64, 112220638669230235u64 ],
    [ 10038208235822497557u64, 140275798336537794u64 ], [ 10885566165816448877u64,  87672373960336121u64 ],
    [ 18218643725697949000u64, 109590467450420151u64 ], [ 18161618638695048346u64, 136988084313025189u64 ],
    [ 13656854658398099168u64,  85617552695640743u64 ], [ 12459382304570236056u64, 107021940869550929u64 ],
    [  1739169825430631358u64, 133777426086938662u64 ], [ 14922039196176308311u64,  83610891304336663u64 ],
    [ 14040862976792997485u64, 104513614130420829u64 ], [  3716020665709083144u64, 130642017663026037u64 ],
    [  4628355925281870917u64,  81651261039391273u64 ], [ 10397130925029726550u64, 102064076299239091u64 ],
    [  8384727637859770284u64, 127580095374048864u64 ], [  5240454773662356427u64,  79737559608780540u64 ],
    [  6550568467077945534u64,  99671949510975675u64 ], [  3576524565420044014u64, 124589936888719594u64 ],
    [  6847013871814915412u64,  77868710555449746u64 ], [ 17782139376623420074u64,  97335888194312182u64 ],
    [ 13004302183924499284u64, 121669860242890228u64 ], [ 17351060901807587860u64,  76043662651806392u64 ],
    [  3242082053549933210u64,  95054578314757991u64 ], [ 17887660622219580224u64, 118818222893447488u64 ],
    [ 11179787888887237640u64,  74261389308404680u64 ], [ 13974734861109047050u64,  92826736635505850u64 ],
    [  8245046539531533005u64, 116033420794382313u64 ], [ 16682369133275677888u64,  72520887996488945u64 ],
    [  7017903361312433648u64,  90651109995611182u64 ], [ 17995751238495317868u64, 113313887494513977u64 ],
    [  8659630992836983623u64, 141642359368142472u64 ], [  5412269370523114764u64,  88526474605089045u64 ],
    [ 11377022731581281359u64, 110658093256361306u64 ], [  4997906377621825891u64, 138322616570451633u64 ],
    [ 14652906532082110942u64,  86451635356532270u64 ], [  9092761128247862869u64, 108064544195665338u64 ],
    [  2142579373455052779u64, 135080680244581673u64 ], [ 12868327154477877747u64,  84425425152863545u64 ],
    [  2250350887815183471u64, 105531781441079432u64 ], [  2812938609768979339u64, 131914726801349290u64 ],
    [  6369772649532999991u64,  82446704250843306u64 ], [ 17185587848771025797u64, 103058380313554132u64 ],
    [  3035240737254230630u64, 128822975391942666u64 ], [  6508711479211282048u64,  80514359619964166u64 ],
    [ 17359261385868878368u64, 100642949524955207u64 ], [ 17087390713908710056u64, 125803686906194009u64 ],
    [  3762090168551861929u64,  78627304316371256u64 ], [  4702612710689827411u64,  98284130395464070u64 ],
    [ 15101637925217060072u64, 122855162994330087u64 ], [ 16356052730901744401u64,  76784476871456304u64 ],
    [  1998321839917628885u64,  95980596089320381u64 ], [  7109588318324424010u64, 119975745111650476u64 ],
    [ 13666864735807540814u64,  74984840694781547u64 ], [ 12471894901332038114u64,  93731050868476934u64 ],
    [  6366496589810271835u64, 117163813585596168u64 ], [  3979060368631419896u64,  73227383490997605u64 ],
    [  9585511479216662775u64,  91534229363747006u64 ], [  2758517312166052660u64, 114417786704683758u64 ],
    [ 12671518677062341634u64, 143022233380854697u64 ], [  1002170145522881665u64,  89388895863034186u64 ],
    [ 10476084718758377889u64, 111736119828792732u64 ], [ 13095105898447972362u64, 139670149785990915u64 ],
    [  5878598177316288774u64,  87293843616244322u64 ], [ 16571619758500136775u64, 109117304520305402u64 ],
    [ 11491152661270395161u64, 136396630650381753u64 ], [   264441385652915120u64,  85247894156488596u64 ],
    [   330551732066143900u64, 106559867695610745u64 ], [  5024875683510067779u64, 133199834619513431u64 ],
    [ 10058076329834874218u64,  83249896637195894u64 ], [  3349223375438816964u64, 104062370796494868u64 ],
    [  4186529219298521205u64, 130077963495618585u64 ], [ 14145795808130045513u64,  81298727184761615u64 ],
    [ 13070558741735168987u64, 101623408980952019u64 ], [ 11726512408741573330u64, 127029261226190024u64 ],
    [  7329070255463483331u64,  79393288266368765u64 ], [ 13773023837756742068u64,  99241610332960956u64 ],
    [ 17216279797195927585u64, 124052012916201195u64 ], [  8454331864033760789u64,  77532508072625747u64 ],
    [  5956228811614813082u64,  96915635090782184u64 ], [  7445286014518516353u64, 121144543863477730u64 ],
    [  9264989777501460624u64,  75715339914673581u64 ], [ 16192923240304213684u64,  94644174893341976u64 ],
    [  1794409976670715490u64, 118305218616677471u64 ], [  8039035263060279037u64,  73940761635423419u64 ],
    [  5437108060397960892u64,  92425952044279274u64 ], [ 16019757112352226923u64, 115532440055349092u64 ],
    [   788976158365366019u64,  72207775034593183u64 ], [ 14821278253238871236u64,  90259718793241478u64 ],
    [  9303225779693813237u64, 112824648491551848u64 ], [ 11629032224617266546u64, 141030810614439810u64 ],
    [ 11879831158813179495u64,  88144256634024881u64 ], [  1014730893234310657u64, 110180320792531102u64 ],
    [ 10491785653397664129u64, 137725400990663877u64 ], [  8863209042587234033u64,  86078375619164923u64 ],
    [  6467325284806654637u64, 107597969523956154u64 ], [ 17307528642863094104u64, 134497461904945192u64 ],
    [ 10817205401789433815u64,  84060913690590745u64 ], [ 18133192770664180173u64, 105076142113238431u64 ],
    [ 18054804944902837312u64, 131345177641548039u64 ], [ 18201782118205355176u64,  82090736025967524u64 ],
    [  4305483574047142354u64, 102613420032459406u64 ], [ 14605226504413703751u64, 128266775040574257u64 ],
    [  2210737537617482988u64,  80166734400358911u64 ], [ 16598479977304017447u64, 100208418000448638u64 ],
    [ 11524727934775246001u64, 125260522500560798u64 ], [  2591268940807140847u64,  78287826562850499u64 ],
    [ 17074144231291089770u64,  97859783203563123u64 ], [ 16730994270686474309u64, 122324729004453904u64 ],
    [ 10456871419179046443u64,  76452955627783690u64 ], [  3847717237119032246u64,  95566194534729613u64 ],
    [  9421332564826178211u64, 119457743168412016u64 ], [  5888332853016361382u64,  74661089480257510u64 ],
    [ 16583788103125227536u64,  93326361850321887u64 ], [ 16118049110479146516u64, 116657952312902359u64 ],
    [ 16991309721690548428u64,  72911220195563974u64 ], [ 12015765115258409727u64,  91139025244454968u64 ],
    [ 15019706394073012159u64, 113923781555568710u64 ], [  9551260955736489391u64, 142404726944460888u64 ],
    [  5969538097335305869u64,  89002954340288055u64 ], [  2850236603241744433u64, 111253692925360069u64 ],
];

#[cfg(test)]
mod tests {
    use super::*;

    fn f32_test_text(number: f32, text: &str) {
        let mut buffer: Vec<u8> = Vec::with_capacity(32);
        write_f32_shortest(&mut buffer, number).unwrap();

        assert_eq!(std::str::from_utf8(&buffer).unwrap(), text);
    }

    fn f64_test_text(number: f64, text: &str) {
        let mut buffer: Vec<u8> = Vec::with_capacity(32);
        write_f64_shortest(&mut buffer, number).unwrap();

        assert_eq!(std::str::from_utf8(&buffer).unwrap(), text);
    }

    fn f32_test_roundtrip(number: f32) {
        let mut buffer: Vec<u8> = Vec::with_capacity(32);
        write_f32_shortest(&mut buffer, number).unwrap();
        let text = std::str::from_utf8(&buffer).unwrap();
        let parsed = text.parse::<f32>().unwrap();

        assert_eq!(number, parsed);
    }

    fn f64_test_roundtrip(number: f64) {
        let mut buffer: Vec<u8> = Vec::with_capacity(32);
        write_f64_shortest(&mut buffer, number).unwrap();
        let text = std::str::from_utf8(&buffer).unwrap();
        let parsed = text.parse::<f64>().unwrap();

        assert_eq!(number, parsed);
    }


    #[test]
    fn f32_special_cases() {
        f32_test_text(1.0, "1e0");
        f32_test_text(-1.0, "-1e0");
        f32_test_text(0.0, "0e0");
        f32_test_text(std::f32::INFINITY, "inf");
        f32_test_text(std::f32::NEG_INFINITY, "-inf");
    }

    #[test]
    fn f64_special_cases() {
        f64_test_text(1.0, "1e0");
        f64_test_text(-1.0, "-1e0");
        f64_test_text(0.0, "0e0");
        f64_test_text(std::f64::INFINITY, "inf");
        f64_test_text(std::f64::NEG_INFINITY, "-inf");
    }

    #[test]
    fn f32_special_cases_roundtrip() {
        f32_test_roundtrip(0.0);
        f32_test_roundtrip(1.0);
        f32_test_roundtrip(-1.0);
        f32_test_roundtrip(0.1);
        f32_test_roundtrip(-0.1);
        f32_test_roundtrip(std::f32::INFINITY);
        f32_test_roundtrip(std::f32::NEG_INFINITY);
        f32_test_roundtrip(std::f32::MAX);
        f32_test_roundtrip(std::f32::MIN);
        f32_test_roundtrip(std::f32::EPSILON);
        f32_test_roundtrip(std::f32::MIN_POSITIVE);
    }

    #[test]
    fn f64_special_cases_roundtrip() {
        f64_test_roundtrip(0.0);
        f64_test_roundtrip(1.0);
        f64_test_roundtrip(-1.0);
        f64_test_roundtrip(0.1);
        f64_test_roundtrip(-0.1);
        f64_test_roundtrip(std::f64::INFINITY);
        f64_test_roundtrip(std::f64::NEG_INFINITY);
        f64_test_roundtrip(std::f64::MAX);
        f64_test_roundtrip(std::f64::MIN);
        f64_test_roundtrip(std::f64::EPSILON);
        f64_test_roundtrip(std::f64::MIN_POSITIVE);
    }

}
