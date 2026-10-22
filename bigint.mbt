///|
// Exact signed integer arithmetic (精確整數), built on `BigNat` magnitudes
// (SPEC §四 item 9(d)).
//
// `symalg.mbt`'s `Rat{num:Int32, den:Int32}` underlies every exact-algebra
// layer (`QPoly`, `QMat`, `Jacobi_interval`'s rational endpoints): `rat_add`
// and `rat_mul` cross-cancel a `gcd` first specifically to delay `Int32`
// overflow, but a handful of `gcd`/cross-multiplications through a chain of
// polynomial or matrix operations still overflows silently — the same
// problem `BigNat` solved for cardinalities. `BigInt` is the signed
// counterpart needed to port that arithmetic core to unbounded precision:
// sign-magnitude representation, magnitude held as a `BigNat`.

///|
/// Sign-magnitude representation: `sign` is `-1`, `0` or `1`; `mag` is the
/// absolute value. Canonical: `sign == 0` iff `mag` is zero (so zero has a
/// single representation and structural equality is numeric equality).
pub struct BigInt {
  sign : Int32
  mag : BigNat
} derive(Debug, Eq)

///|
pub extend BigInt with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BigInt with Eq::{not_equal, equal}

///|
fn bigint_raw(sign : Int32, mag : BigNat) -> BigInt {
  if bignat_is_zero(mag) {
    BigInt::{ sign: 0, mag: bignat_of_int(0) }
  } else {
    BigInt::{ sign, mag }
  }
}

///|
/// The integer `0`.
pub fn bigint_zero() -> BigInt {
  BigInt::{ sign: 0, mag: bignat_of_int(0) }
}

///|
/// The signed integer `x`, built from an `Int32`.
pub fn bigint_of_int(x : Int32) -> BigInt {
  if x == 0 {
    bigint_zero()
  } else if x > 0 {
    BigInt::{ sign: 1, mag: bignat_of_int(x) }
  } else {
    BigInt::{ sign: -1, mag: bignat_of_int(0 - x) }
  }
}

///|
/// The non-negative integer `x`, as a signed value (`sign` is `0` or `1`).
pub fn bigint_of_bignat(x : BigNat) -> BigInt {
  bigint_raw(1, x)
}

///|
/// Is this zero?
pub fn bigint_is_zero(x : BigInt) -> Bool {
  x.sign == 0
}

///|
/// `-1`, `0` or `1` according to the sign of `x`.
pub fn bigint_sign(x : BigInt) -> Int32 {
  x.sign
}

///|
/// Negation.
pub fn bigint_neg(x : BigInt) -> BigInt {
  bigint_raw(0 - x.sign, x.mag)
}

///|
/// Absolute value, as a `BigNat`.
pub fn bigint_abs(x : BigInt) -> BigNat {
  x.mag
}

///|
/// Three-way comparison: `-1`, `0` or `1` as `x < y`, `x = y`, `x > y`.
pub fn bigint_cmp(x : BigInt, y : BigInt) -> Int32 {
  if x.sign != y.sign {
    if x.sign < y.sign {
      -1
    } else {
      1
    }
  } else if x.sign == 0 {
    0
  } else if x.sign > 0 {
    bignat_cmp(x.mag, y.mag)
  } else {
    // Both negative: larger magnitude means smaller value.
    0 - bignat_cmp(x.mag, y.mag)
  }
}

///|
/// `x < y`.
pub fn bigint_lt(x : BigInt, y : BigInt) -> Bool {
  bigint_cmp(x, y) < 0
}

///|
/// Exact sum.
pub fn bigint_add(x : BigInt, y : BigInt) -> BigInt {
  if x.sign == 0 {
    y
  } else if y.sign == 0 {
    x
  } else if x.sign == y.sign {
    bigint_raw(x.sign, bignat_add(x.mag, y.mag))
  } else if bignat_cmp(x.mag, y.mag) >= 0 {
    bigint_raw(x.sign, bignat_sub(x.mag, y.mag))
  } else {
    bigint_raw(y.sign, bignat_sub(y.mag, x.mag))
  }
}

///|
/// Exact difference `x - y`.
pub fn bigint_sub(x : BigInt, y : BigInt) -> BigInt {
  bigint_add(x, bigint_neg(y))
}

///|
/// Exact product.
pub fn bigint_mul(x : BigInt, y : BigInt) -> BigInt {
  bigint_raw(x.sign * y.sign, bignat_mul(x.mag, y.mag))
}

///|
/// Exact quotient/remainder, truncating toward zero (matching `Int32`'s
/// `/`/`%` convention): `x == add(mul(q, y), r)` and `|r| < |y|`, with `r`
/// taking the sign of `x` (or zero). Aborts on a zero divisor.
pub fn bigint_divmod(x : BigInt, y : BigInt) -> (BigInt, BigInt) {
  if y.sign == 0 {
    abort("bigint_divmod: division by zero")
  }
  let (qm, rm) = bignat_divmod(x.mag, y.mag)
  let q = bigint_raw(x.sign * y.sign, qm)
  let r = bigint_raw(x.sign, rm)
  (q, r)
}

///|
/// Greatest common divisor of the magnitudes, as a non-negative `BigInt`.
pub fn bigint_gcd(x : BigInt, y : BigInt) -> BigInt {
  bigint_of_bignat(bignat_gcd(x.mag, y.mag))
}

///|
/// Decimal rendering, with a leading `-` for negative values.
pub fn bigint_to_string(x : BigInt) -> String {
  if x.sign < 0 {
    "-" + bignat_to_string(x.mag)
  } else {
    bignat_to_string(x.mag)
  }
}

///|
/// Partial conversion to `Int64`: `None` on overflow instead of wrapping.
pub fn bigint_to_int64(x : BigInt) -> Int64? {
  match bignat_to_int64(x.mag) {
    None => None
    Some(v) => if x.sign < 0 { Some(0L - v) } else { Some(v) }
  }
}
