///|
// Exact natural-number arithmetic (精確自然數).
//
// The counting layer of computable univalence multiplies and raises
// cardinalities.  In `Int32` that overflows long before it looks dangerous:
// `fact(13) = 6227020800` already exceeds `2^31 − 1`, and at 16 elements
// `int_pow(16, 16) = 2^64 ≡ 0 (mod 2^32)` — `fin_map_count` silently
// returns 0 and every "decision" downstream becomes vacuous.
//
// `BigNat` is an unbounded non-negative integer held as little-endian
// base-10⁹ limbs (`0 ≤ limb < 10⁹`, no trailing zero limbs, zero is the
// empty array).  Every counting formula — `|B|^|A|`, `n!`, the number of
// equivalences — is therefore exact at any size; conversions to machine
// integers are *partial* and report overflow (`None`) instead of wrapping.

///|
/// Little-endian base-10⁹ limbs, canonical: no trailing (most significant)
/// zero limbs, so `[]` is the unique representation of zero and structural
/// equality is numeric equality.
pub struct BigNat {
  limbs : Array[Int64]
} derive(Debug, Eq)

///|
pub extend BigNat with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BigNat with Eq::{not_equal, equal}

///|
fn bignat_base() -> Int64 {
  1000000000L
}

///|
fn bignat_canonical(limbs : Array[Int64]) -> BigNat {
  let mut end = limbs.length()
  while end > 0 && limbs[end - 1] == 0L {
    end = end - 1
  }
  let out : Array[Int64] = []
  for i in 0..<end {
    out.push(limbs[i])
  }
  BigNat::{ limbs: out, }
}

///|
/// The natural number `x`.  Aborts on negative input: `BigNat` is unsigned.
pub fn bignat_of_int(x : Int32) -> BigNat {
  if x < 0 {
    abort("bignat_of_int: negative")
  }
  bignat_of_int64(x.to_int64())
}

///|
/// The natural number `x`.  Aborts on negative input.
pub fn bignat_of_int64(x : Int64) -> BigNat {
  if x < 0L {
    abort("bignat_of_int64: negative")
  }
  let limbs : Array[Int64] = []
  let mut rest = x
  while rest > 0L {
    limbs.push(rest % bignat_base())
    rest = rest / bignat_base()
  }
  BigNat::{ limbs, }
}

///|
/// Is this zero?
pub fn bignat_is_zero(x : BigNat) -> Bool {
  x.limbs.length() == 0
}

///|
/// Three-way comparison: −1, 0 or 1 as `x < y`, `x = y`, `x > y`.
/// Canonical representations make the comparison structural.
pub fn bignat_cmp(x : BigNat, y : BigNat) -> Int32 {
  if x.limbs.length() < y.limbs.length() {
    return -1
  }
  if x.limbs.length() > y.limbs.length() {
    return 1
  }
  let mut i = x.limbs.length()
  while i > 0 {
    i = i - 1
    if x.limbs[i] < y.limbs[i] {
      return -1
    }
    if x.limbs[i] > y.limbs[i] {
      return 1
    }
  }
  0
}

///|
/// `x < y`.
pub fn bignat_lt(x : BigNat, y : BigNat) -> Bool {
  bignat_cmp(x, y) < 0
}

///|
/// Exact sum.
pub fn bignat_add(x : BigNat, y : BigNat) -> BigNat {
  let out : Array[Int64] = []
  let n = if x.limbs.length() > y.limbs.length() {
    x.limbs.length()
  } else {
    y.limbs.length()
  }
  let mut carry = 0L
  for i in 0..<n {
    let a = if i < x.limbs.length() { x.limbs[i] } else { 0L }
    let b = if i < y.limbs.length() { y.limbs[i] } else { 0L }
    let s = a + b + carry
    out.push(s % bignat_base())
    carry = s / bignat_base()
  }
  if carry > 0L {
    out.push(carry)
  }
  BigNat::{ limbs: out, }
}

///|
/// Exact product.  Each limb step computes
/// `out + xᵢ·yⱼ + carry < 10⁹ + 10¹⁸ + 10⁹`, well inside `Int64`.
pub fn bignat_mul(x : BigNat, y : BigNat) -> BigNat {
  if x.limbs.length() == 0 || y.limbs.length() == 0 {
    return BigNat::{ limbs: [], }
  }
  let out : Array[Int64] = []
  for _i in 0..<(x.limbs.length() + y.limbs.length()) {
    out.push(0L)
  }
  for i in 0..<x.limbs.length() {
    let mut carry = 0L
    for j in 0..<y.limbs.length() {
      let cur = out[i + j] + x.limbs[i] * y.limbs[j] + carry
      out[i + j] = cur % bignat_base()
      carry = cur / bignat_base()
    }
    let mut k = i + y.limbs.length()
    while carry > 0L {
      let cur = out[k] + carry
      out[k] = cur % bignat_base()
      carry = cur / bignat_base()
      k = k + 1
    }
  }
  bignat_canonical(out)
}

///|
/// Exact power `base^exp` by square-and-multiply.  Aborts on negative
/// exponent.
pub fn bignat_pow(base : BigNat, exp : Int32) -> BigNat {
  if exp < 0 {
    abort("bignat_pow: negative exponent")
  }
  let mut acc = bignat_of_int(1)
  let mut b = base
  let mut e = exp
  while e > 0 {
    if e % 2 == 1 {
      acc = bignat_mul(acc, b)
    }
    b = bignat_mul(b, b)
    e = e / 2
  }
  acc
}

///|
/// Exact factorial `n!`.  Aborts on negative input.
pub fn bignat_fact(n : Int32) -> BigNat {
  if n < 0 {
    abort("bignat_fact: negative")
  }
  let mut acc = bignat_of_int(1)
  for i in 2..<=n {
    acc = bignat_mul(acc, bignat_of_int(i))
  }
  acc
}

///|
/// Decimal rendering (base-10⁹ limbs print as nine-digit chunks).
pub fn bignat_to_string(x : BigNat) -> String {
  if x.limbs.length() == 0 {
    return "0"
  }
  let mut s = ""
  let mut i = x.limbs.length()
  while i > 0 {
    i = i - 1
    let chunk = x.limbs[i].to_string()
    if i == x.limbs.length() - 1 {
      s = s + chunk
    } else {
      let mut padded = chunk
      while padded.length() < 9 {
        padded = "0" + padded
      }
      s = s + padded
    }
  }
  s
}

///|
/// Partial conversion to `Int64`: `None` on overflow instead of wrapping.
pub fn bignat_to_int64(x : BigNat) -> Int64? {
  let max = 9223372036854775807L
  let mut acc = 0L
  let mut i = x.limbs.length()
  while i > 0 {
    i = i - 1
    let limb = x.limbs[i]
    if acc > (max - limb) / bignat_base() {
      return None
    }
    acc = acc * bignat_base() + limb
  }
  Some(acc)
}

///|
/// Partial conversion to `Int32`: `None` on overflow instead of wrapping.
pub fn bignat_to_int32(x : BigNat) -> Int32? {
  match bignat_to_int64(x) {
    None => None
    Some(v) => if v > 2147483647L { None } else { Some(v.to_int()) }
  }
}

///|
/// Exact difference `x - y`.  Aborts if `x < y` — `BigNat` is unsigned, so
/// the signed difference belongs to `BigInt` (bigint.mbt), which calls
/// this only on the correctly-ordered magnitudes.
pub fn bignat_sub(x : BigNat, y : BigNat) -> BigNat {
  if bignat_lt(x, y) {
    abort("bignat_sub: negative result")
  }
  let out : Array[Int64] = []
  let mut borrow = 0L
  for i in 0..<x.limbs.length() {
    let a = x.limbs[i]
    let b = if i < y.limbs.length() { y.limbs[i] } else { 0L }
    let mut d = a - b - borrow
    if d < 0L {
      d = d + bignat_base()
      borrow = 1L
    } else {
      borrow = 0L
    }
    out.push(d)
  }
  bignat_canonical(out)
}

///|
/// Exact quotient/remainder by a general positive `BigNat` divisor
/// (schoolbook long division, one output limb at a time, each digit found
/// by binary search over `[0, base)` — simple and exact rather than
/// fastest, which is adequate at the sizes `BigRat` reduction needs).
/// Aborts on a zero divisor.
pub fn bignat_divmod(x : BigNat, y : BigNat) -> (BigNat, BigNat) {
  if bignat_is_zero(y) {
    abort("bignat_divmod: division by zero")
  }
  if bignat_lt(x, y) {
    return (BigNat::{ limbs: [], }, x)
  }
  let n = x.limbs.length()
  let qlimbs : Array[Int64] = []
  for _i in 0..<n {
    qlimbs.push(0L)
  }
  let mut rem = BigNat::{ limbs: [], }
  let mut i = n
  while i > 0 {
    i = i - 1
    // rem = rem * base + x.limbs[i]
    let shifted : Array[Int64] = [x.limbs[i]]
    for k in 0..<rem.limbs.length() {
      shifted.push(rem.limbs[k])
    }
    rem = bignat_canonical(shifted)
    // Binary search the largest digit d in [0, base) with y*d <= rem.
    let mut lo = 0L
    let mut hi = bignat_base() - 1L
    while lo < hi {
      let mid = (lo + hi + 1L) / 2L
      if bignat_cmp(bignat_mul(y, bignat_of_int64(mid)), rem) <= 0 {
        lo = mid
      } else {
        hi = mid - 1L
      }
    }
    qlimbs[i] = lo
    rem = bignat_sub(rem, bignat_mul(y, bignat_of_int64(lo)))
  }
  (bignat_canonical(qlimbs), rem)
}

///|
/// Greatest common divisor by the Euclidean algorithm on `BigNat`
/// magnitudes.  `gcd(0, 0) = 0`, matching the usual convention (unlike
/// `int_gcd`'s `1`, since `BigRat` reduction only ever calls this on a
/// known-nonzero denominator).
pub fn bignat_gcd(x : BigNat, y : BigNat) -> BigNat {
  let mut a = x
  let mut b = y
  while !bignat_is_zero(b) {
    let (_q, r) = bignat_divmod(a, b)
    a = b
    b = r
  }
  a
}

///|
/// Exact quotient/remainder by a small positive divisor, used for mixed
/// base conversion of enumeration codes.
pub fn bignat_divmod_small(x : BigNat, d : Int64) -> (BigNat, Int64) {
  if d <= 0L {
    abort("bignat_divmod_small: non-positive divisor")
  }
  if x.limbs.length() == 0 {
    return (BigNat::{ limbs: [], }, 0L)
  }
  let out : Array[Int64] = []
  for _i in 0..<x.limbs.length() {
    out.push(0L)
  }
  let mut rem = 0L
  let mut i = x.limbs.length()
  while i > 0 {
    i = i - 1
    let cur = rem * bignat_base() + x.limbs[i]
    out[i] = cur / d
    rem = cur % d
  }
  (bignat_canonical(out), rem)
}
