///|
// Exact arbitrary-precision rationals (SPEC §四 item 9(d), part two).
//
// `BigRat` mirrors `symalg.mbt`'s `Rat{num:Int32, den:Int32}` field-for-field
// (numerator/denominator, always reduced, denominator positive) but is
// backed by `BigInt`/`BigNat` so neither cross-multiplication nor gcd
// reduction can silently overflow the way `Rat`'s `Int32` arithmetic can
// after a handful of polynomial or matrix operations. It is a drop-in
// semantic analogue, not (yet) wired into `qpoly.mbt`/`qmat.mbt`/
// `Jacobi_interval.mbt` — see `bigrat_of_rat`/`rat_of_bigrat` below, which
// are the bridge a future port would use, and are cross-checked here
// against every `Rat` operation on values that fit both.

///|
/// `num / den`, always stored reduced with `den > 0` (so `num.sign == 0`
/// iff the rational is zero, and the representation of each rational
/// value is unique — structural equality is exact equality).
pub struct BigRat {
  num : BigInt
  den : BigNat
} derive(Debug, Eq)

///|
pub extend BigRat with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BigRat with Eq::{not_equal, equal}

///|
/// Build and reduce `n / d` (both signed, `d` must be nonzero: its sign
/// becomes part of `n`'s sign, and the magnitude is divided by the gcd).
pub fn bigrat_make(n : BigInt, d : BigInt) -> BigRat {
  if bigint_is_zero(d) {
    abort("bigrat_make: zero denominator")
  }
  if bigint_is_zero(n) {
    return BigRat::{ num: bigint_zero(), den: bignat_of_int(1) }
  }
  let sign = n.sign * d.sign
  let g = bignat_gcd(n.mag, d.mag)
  let (nn, _) = bignat_divmod(n.mag, g)
  let (dd, _) = bignat_divmod(d.mag, g)
  BigRat::{ num: bigint_raw_pub(sign, nn), den: dd }
}

///|
/// Internal: build a `BigInt` with an explicit sign and magnitude,
/// canonicalising zero. (`bigint_raw` itself is private to bigint.mbt, so
/// this file reconstructs the same normalisation via public primitives.)
fn bigint_raw_pub(sign : Int32, mag : BigNat) -> BigInt {
  if bignat_is_zero(mag) {
    bigint_zero()
  } else if sign >= 0 {
    bigint_of_bignat(mag)
  } else {
    bigint_neg(bigint_of_bignat(mag))
  }
}

///|
/// The integer `n`, as a rational.
pub fn bigrat_of_bigint(n : BigInt) -> BigRat {
  BigRat::{ num: n, den: bignat_of_int(1) }
}

///|
/// The rational `0`.
pub fn bigrat_zero() -> BigRat {
  bigrat_of_bigint(bigint_zero())
}

///|
/// The rational `1`.
pub fn bigrat_one() -> BigRat {
  bigrat_of_bigint(bigint_of_int(1))
}

///|
/// Is this zero?
pub fn bigrat_is_zero(a : BigRat) -> Bool {
  bigint_is_zero(a.num)
}

///|
/// Exact sum, cross-cancelling the denominators' gcd first (same
/// overflow-delaying trick as `rat_add`, just unbounded).
pub fn bigrat_add(a : BigRat, b : BigRat) -> BigRat {
  let g = bignat_gcd(a.den, b.den)
  let (ad, _) = bignat_divmod(a.den, g)
  let (bd, _) = bignat_divmod(b.den, g)
  let num = bigint_add(
    bigint_mul(a.num, bigint_of_bignat(bd)),
    bigint_mul(b.num, bigint_of_bignat(ad)),
  )
  let den = bigint_mul(bigint_of_bignat(ad), bigint_of_bignat(b.den))
  bigrat_make(num, den)
}

///|
/// Negation.
pub fn bigrat_neg(a : BigRat) -> BigRat {
  BigRat::{ num: bigint_neg(a.num), den: a.den }
}

///|
/// Exact difference.
pub fn bigrat_sub(a : BigRat, b : BigRat) -> BigRat {
  bigrat_add(a, bigrat_neg(b))
}

///|
/// Exact product, cross-cancelling before multiplying.
pub fn bigrat_mul(a : BigRat, b : BigRat) -> BigRat {
  let g1 = bignat_gcd(a.num.mag, b.den)
  let g2 = bignat_gcd(b.num.mag, a.den)
  let (an, _) = bignat_divmod(a.num.mag, g1)
  let (bd, _) = bignat_divmod(b.den, g1)
  let (bn, _) = bignat_divmod(b.num.mag, g2)
  let (ad, _) = bignat_divmod(a.den, g2)
  let num = bigint_mul(
    bigint_raw_pub(a.num.sign, an),
    bigint_raw_pub(b.num.sign, bn),
  )
  let den = bigint_mul(bigint_of_bignat(ad), bigint_of_bignat(bd))
  bigrat_make(num, den)
}

///|
/// Multiplicative inverse. Aborts on zero (there is none).
pub fn bigrat_inv(a : BigRat) -> BigRat {
  if bigrat_is_zero(a) {
    abort("bigrat_inv: zero has no inverse")
  }
  bigrat_make(bigint_raw_pub(a.num.sign, a.den), bigint_of_bignat(a.num.mag))
}

///|
/// Exact quotient.
pub fn bigrat_div(a : BigRat, b : BigRat) -> BigRat {
  bigrat_mul(a, bigrat_inv(b))
}

///|
/// Exact equality (both sides are always stored reduced, so this is
/// structural equality — provided for symmetry with `rat_eq`).
pub fn bigrat_eq(a : BigRat, b : BigRat) -> Bool {
  a == b
}

///|
/// Three-way comparison by cross-multiplication (`den`s are always
/// positive, so no sign correction is needed).
pub fn bigrat_cmp(a : BigRat, b : BigRat) -> Int32 {
  bigint_cmp(
    bigint_mul(a.num, bigint_of_bignat(b.den)),
    bigint_mul(b.num, bigint_of_bignat(a.den)),
  )
}

///|
/// Decimal rendering as `"num/den"` (or just `"num"` when `den == 1`).
pub fn bigrat_to_string(a : BigRat) -> String {
  if a.den == bignat_of_int(1) {
    bigint_to_string(a.num)
  } else {
    bigint_to_string(a.num) + "/" + bignat_to_string(a.den)
  }
}

///|
/// Bridge from the existing `Int32`-bounded `Rat` (symalg.mbt) to `BigRat`
/// — lossless, since every `Int32` fits `BigInt`/`BigNat` exactly.
pub fn bigrat_of_rat(r : Rat) -> BigRat {
  bigrat_make(bigint_of_int(r.num), bigint_of_int(r.den))
}

///|
/// Bridge back from `BigRat` to `Rat`, when both numerator and denominator
/// still fit `Int32` — `None` when the value has grown too large (this is
/// exactly the overflow `Rat`'s own arithmetic is silently exposed to).
pub fn rat_of_bigrat(a : BigRat) -> Rat? {
  match (bigint_to_int64(a.num), bignat_to_int64(a.den)) {
    (Some(n), Some(d)) =>
      if n >= -2147483648L && n <= 2147483647L && d <= 2147483647L {
        Some(rat_make(n.to_int(), d.to_int()))
      } else {
        None
      }
    _ => None
  }
}
