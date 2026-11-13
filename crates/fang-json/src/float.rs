// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Python's `repr` of a float (Python/pystrtod.c, format code 'r' with Py_DTSF_ADD_DOT_0).

/// `repr(value)` as Python prints it, or `None` for NaN and the infinities.
///
/// The digits are the shortest that round-trip. Rust's `{:e}` gives the shortest length; when
/// the value lies exactly halfway between two such strings, Python's dtoa takes the one with
/// an even last digit and Rust's may not, so that case is decided here from the exact
/// decimal expansion of the value. Python writes the digits in fixed notation when the
/// decimal point position `decpt` satisfies -4 < decpt <= 16, adding ".0" to an integral
/// value, and otherwise as d[.ddd]e±XX with at least two exponent digits.
pub fn python_float_repr(value: f64) -> Option<String> {
    if !value.is_finite() {
        return None;
    }
    if value == 0.0 {
        return Some(
            if value.is_sign_negative() {
                "-0.0"
            } else {
                "0.0"
            }
            .to_owned(),
        );
    }
    let magnitude = value.abs();
    let scientific = format!("{magnitude:e}");
    let (mantissa, exponent) = scientific.split_once('e')?;
    let exponent: i32 = exponent.parse().ok()?;
    let mut digits: Vec<u8> = mantissa.bytes().filter(|byte| *byte != b'.').collect();
    let mut point = exponent + 1;
    if let Some((even, even_point)) = half_even(magnitude, &digits, point) {
        digits = even;
        point = even_point;
    }
    let digits = String::from_utf8(digits).ok()?;
    let count = digits.len() as i32;
    let mut text = String::new();
    if value.is_sign_negative() {
        text.push('-');
    }
    if point <= -4 || point > 16 {
        text.push_str(&digits[..1]);
        if count > 1 {
            text.push('.');
            text.push_str(&digits[1..]);
        }
        let shown = point - 1;
        text.push('e');
        text.push(if shown < 0 { '-' } else { '+' });
        text.push_str(&format!("{:02}", shown.abs()));
    } else if point <= 0 {
        text.push_str("0.");
        for _ in 0..-point {
            text.push('0');
        }
        text.push_str(&digits);
    } else if point < count {
        text.push_str(&digits[..point as usize]);
        text.push('.');
        text.push_str(&digits[point as usize..]);
    } else {
        text.push_str(&digits);
        for _ in 0..point - count {
            text.push('0');
        }
        text.push_str(".0");
    }
    Some(text)
}

/// The other candidate when `digits` (with decimal point position `point`) is one of two
/// shortest strings exactly equidistant from `value`, has an odd last digit, and the even
/// candidate also reads back as `value`.
fn half_even(value: f64, digits: &[u8], point: i32) -> Option<(Vec<u8>, i32)> {
    if digits.last()? % 2 == 0 {
        return None;
    }
    let (exact, exact_point) = exact_decimal(value);
    if exact.len() != digits.len() + 1 || *exact.last()? != b'5' || exact_point != point {
        return None;
    }
    // The two candidates are the exact expansion cut to the length of `digits`, and that plus one unit.
    let lower: Vec<u8> = exact[..digits.len()].to_vec();
    let mut upper = lower.clone();
    let mut index = upper.len();
    loop {
        if index == 0 {
            return None;
        }
        index -= 1;
        if upper[index] == b'9' {
            upper[index] = b'0';
        } else {
            upper[index] += 1;
            break;
        }
    }
    let other = if lower == digits {
        upper
    } else if upper == digits {
        lower
    } else {
        return None;
    };
    if other.last()? % 2 != 0 {
        return None;
    }
    let mut candidate = String::from("0.");
    candidate.push_str(std::str::from_utf8(&other).ok()?);
    candidate.push_str(&format!("e{point}"));
    if candidate.parse::<f64>().ok()? != value {
        return None;
    }
    let mut other = other;
    while other.len() > 1 && other.last() == Some(&b'0') {
        other.pop();
    }
    Some((other, point))
}

/// The significant decimal digits of a positive finite double, exactly, and the position of
/// the decimal point relative to the first digit (value = 0.DIGITS × 10^point).
fn exact_decimal(value: f64) -> (Vec<u8>, i32) {
    let bits = value.to_bits();
    let raw_exponent = ((bits >> 52) & 0x7ff) as i32;
    let fraction = bits & ((1u64 << 52) - 1);
    let (mantissa, exponent) = if raw_exponent == 0 {
        (fraction, -1074)
    } else {
        (fraction | (1u64 << 52), raw_exponent - 1075)
    };
    // value = mantissa × 2^exponent. With a negative exponent, value = mantissa × 5^-exponent / 10^-exponent.
    let mut number = Big::from(mantissa);
    let mut shift = 0i32;
    // Multiply in chunks that keep every limb product below 2^64: 2^29 and 5^13 times a limb under 10^9.
    let (base, chunk, mut count) = if exponent >= 0 {
        (2u64, 29u32, exponent)
    } else {
        (5u64, 13u32, -exponent)
    };
    while count > 0 {
        let step = count.min(chunk as i32);
        number.multiply(base.pow(step as u32));
        count -= step;
    }
    if exponent < 0 {
        shift = exponent;
    }
    let mut digits = number.decimal();
    let point = digits.len() as i32 + shift;
    while digits.len() > 1 && digits.last() == Some(&b'0') {
        digits.pop();
    }
    (digits, point)
}

/// A non-negative integer in base 10^9 limbs, least significant first.
struct Big(Vec<u32>);

const LIMB: u64 = 1_000_000_000;

impl Big {
    fn from(value: u64) -> Big {
        let mut limbs = Vec::new();
        let mut rest = value;
        while rest > 0 {
            limbs.push((rest % LIMB) as u32);
            rest /= LIMB;
        }
        Big(limbs)
    }

    fn multiply(&mut self, factor: u64) {
        let mut carry = 0u64;
        for limb in &mut self.0 {
            let product = u64::from(*limb) * factor + carry;
            *limb = (product % LIMB) as u32;
            carry = product / LIMB;
        }
        while carry > 0 {
            self.0.push((carry % LIMB) as u32);
            carry /= LIMB;
        }
    }

    fn decimal(&self) -> Vec<u8> {
        let mut text = String::new();
        for (index, limb) in self.0.iter().rev().enumerate() {
            if index == 0 {
                text.push_str(&limb.to_string());
            } else {
                text.push_str(&format!("{limb:09}"));
            }
        }
        if text.is_empty() {
            text.push('0');
        }
        text.into_bytes()
    }
}
