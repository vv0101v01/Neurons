///|
// Exact univariate polynomials over Q.
//
// `QPoly` is the coefficient-level counterpart of the symbolic
// `RPoly`: coefficients are normalized rationals, polynomials are
// stored low-to-high with no trailing zeros, and the module provides
// division, gcd and extended gcd, derivatives, Yun's squarefree
// factorization, and rational-root extraction.  These are the
// operations needed for repeated eigenvalues, primary
// decompositions, and algebraic-number normal forms.  As everywhere
// in the exact layers, integer arithmetic is `Int32`; the algorithms
// are exact whenever no intermediate numerator/denominator exceeds
// that range.

///|
pub fn rat_inv(a : Rat) -> Rat {
  if a.num == 0 {
    rat_zero()
  } else {
    rat_make(a.den, a.num)
  }
}

///|
pub fn rat_div(a : Rat, b : Rat) -> Rat {
  rat_mul(a, rat_inv(b))
}

///|
pub fn rat_eq(a : Rat, b : Rat) -> Bool {
  a.num == b.num && a.den == b.den
}

///|
pub fn rat_is_one(a : Rat) -> Bool {
  a.num == 1 && a.den == 1
}

///|
pub fn rat_sign(a : Rat) -> Int32 {
  if a.num > 0 {
    1
  } else if a.num < 0 {
    -1
  } else {
    0
  }
}

///|
pub struct QPoly {
  coeffs : Array[Rat] // low to high, normalized
} derive(Debug, Eq)

///|
pub extend QPoly with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QPoly with Eq::{not_equal, equal}

///|
pub fn qpoly_normalize(coeffs : Array[Rat]) -> QPoly {
  let mut last = -1
  for i in 0..<coeffs.length() {
    if !rat_is_zero(coeffs[i]) {
      last = i
    }
  }
  let out : Array[Rat] = []
  if last < 0 {
    out.push(rat_zero())
  } else {
    for i in 0..<(last + 1) {
      out.push(rat_make(coeffs[i].num, coeffs[i].den))
    }
  }
  QPoly::{ coeffs: out, }
}

///|
pub fn qpoly_zero() -> QPoly {
  QPoly::{ coeffs: [rat_zero()], }
}

///|
pub fn qpoly_one() -> QPoly {
  QPoly::{ coeffs: [rat_one()], }
}

///|
pub fn qpoly_x() -> QPoly {
  QPoly::{ coeffs: [rat_zero(), rat_one()], }
}

///|
pub fn qpoly_const(c : Rat) -> QPoly {
  qpoly_normalize([c])
}

///|
pub fn qpoly_int(n : Int32) -> QPoly {
  qpoly_const(rat_int(n))
}

///|
pub fn qpoly_is_zero(p : QPoly) -> Bool {
  p.coeffs.length() == 1 && rat_is_zero(p.coeffs[0])
}

///|
/// Degree, with the zero polynomial of degree -1.
pub fn qpoly_degree(p : QPoly) -> Int32 {
  if qpoly_is_zero(p) {
    -1
  } else {
    p.coeffs.length() - 1
  }
}

///|
pub fn qpoly_coeff(p : QPoly, i : Int32) -> Rat {
  if i >= 0 && i < p.coeffs.length() {
    p.coeffs[i]
  } else {
    rat_zero()
  }
}

///|
pub fn qpoly_leading(p : QPoly) -> Rat {
  if qpoly_is_zero(p) {
    rat_zero()
  } else {
    p.coeffs[p.coeffs.length() - 1]
  }
}

///|
pub fn qpoly_add(a : QPoly, b : QPoly) -> QPoly {
  let n = if a.coeffs.length() > b.coeffs.length() {
    a.coeffs.length()
  } else {
    b.coeffs.length()
  }
  let out : Array[Rat] = []
  for i in 0..<n {
    out.push(rat_add(qpoly_coeff(a, i), qpoly_coeff(b, i)))
  }
  qpoly_normalize(out)
}

///|
pub fn qpoly_neg(a : QPoly) -> QPoly {
  let out : Array[Rat] = []
  for i in 0..<a.coeffs.length() {
    out.push(rat_neg(a.coeffs[i]))
  }
  qpoly_normalize(out)
}

///|
pub fn qpoly_sub(a : QPoly, b : QPoly) -> QPoly {
  qpoly_add(a, qpoly_neg(b))
}

///|
pub fn qpoly_scale(c : Rat, a : QPoly) -> QPoly {
  let out : Array[Rat] = []
  for i in 0..<a.coeffs.length() {
    out.push(rat_mul(c, a.coeffs[i]))
  }
  qpoly_normalize(out)
}

///|
pub fn qpoly_mul(a : QPoly, b : QPoly) -> QPoly {
  if qpoly_is_zero(a) || qpoly_is_zero(b) {
    return qpoly_zero()
  }
  let out : Array[Rat] = []
  for _i in 0..<(a.coeffs.length() + b.coeffs.length() - 1) {
    out.push(rat_zero())
  }
  for i in 0..<a.coeffs.length() {
    for j in 0..<b.coeffs.length() {
      out[i + j] = rat_add(out[i + j], rat_mul(a.coeffs[i], b.coeffs[j]))
    }
  }
  qpoly_normalize(out)
}

///|
pub fn qpoly_pow(a : QPoly, n : Int32) -> QPoly {
  let mut acc = qpoly_one()
  for _i in 0..<n {
    acc = qpoly_mul(acc, a)
  }
  acc
}

///|
pub fn qpoly_eq(a : QPoly, b : QPoly) -> Bool {
  qpoly_is_zero(qpoly_sub(a, b))
}

///|
pub fn qpoly_is_one(a : QPoly) -> Bool {
  qpoly_eq(a, qpoly_one())
}

///|
pub fn qpoly_monic(a : QPoly) -> QPoly {
  if qpoly_is_zero(a) {
    a
  } else {
    qpoly_scale(rat_inv(qpoly_leading(a)), a)
  }
}

///|
pub fn qpoly_eval(p : QPoly, x : Rat) -> Rat {
  let mut acc = rat_zero()
  for i = p.coeffs.length() - 1; i >= 0; i = i - 1 {
    acc = rat_add(rat_mul(acc, x), p.coeffs[i])
  }
  acc
}

///|
/// The primitive integer representative of a nonzero polynomial:
/// denominators cleared, integer content divided out, and leading
/// coefficient positive.  Zero is unchanged.
pub fn qpoly_primitive_part(p : QPoly) -> QPoly {
  if qpoly_is_zero(p) {
    return p
  }
  let ints = qpoly_integer_coeffs(p)
  let out : Array[Rat] = []
  for i in 0..<ints.length() {
    out.push(rat_int(ints[i]))
  }
  qpoly_normalize(out)
}

///|
/// Pseudo-remainder: for `e = deg(a) − deg(b) + 1`, a polynomial `r`
/// of degree below `deg(b)` with `lc(b)^e · a = q·b + r`.  Integer
/// inputs give integer outputs, which keeps the gcd remainder
/// sequence free of rational coefficient explosion.
pub fn qpoly_pseudo_remainder(a : QPoly, b : QPoly) -> QPoly {
  if qpoly_is_zero(b) || qpoly_degree(a) < qpoly_degree(b) {
    return a
  }
  let db = qpoly_degree(b)
  let lb = qpoly_leading(b)
  let mut r = a
  while !qpoly_is_zero(r) && qpoly_degree(r) >= db {
    let shift = qpoly_degree(r) - db
    // r := lb*r − lc(r)·X^shift·b
    let sub : Array[Rat] = []
    for _i in 0..<shift {
      sub.push(rat_zero())
    }
    for i in 0..<b.coeffs.length() {
      sub.push(rat_mul(qpoly_leading(r), b.coeffs[i]))
    }
    r = qpoly_sub(qpoly_scale(lb, r), qpoly_normalize(sub))
  }
  r
}

///|
pub fn qpoly_derivative(p : QPoly) -> QPoly {
  let out : Array[Rat] = []
  for i in 1..<p.coeffs.length() {
    out.push(rat_mul(rat_int(i), p.coeffs[i]))
  }
  qpoly_normalize(out)
}

///|
pub struct QPolyDiv {
  quotient : QPoly
  remainder : QPoly
}

///|
/// Euclidean division; a zero divisor yields quotient and remainder
/// zero (callers needing the distinction test the divisor first).
pub fn qpoly_divmod(a : QPoly, b : QPoly) -> QPolyDiv {
  if qpoly_is_zero(b) {
    return QPolyDiv::{ quotient: qpoly_zero(), remainder: qpoly_zero(), }
  }
  let db = qpoly_degree(b)
  let qcoeffs : Array[Rat] = []
  let qlen = if qpoly_degree(a) >= db { qpoly_degree(a) - db + 1 } else { 1 }
  for _i in 0..<qlen {
    qcoeffs.push(rat_zero())
  }
  let mut rem = a
  let lb = qpoly_leading(b)
  while !qpoly_is_zero(rem) && qpoly_degree(rem) >= db {
    let shift = qpoly_degree(rem) - db
    let coeff = rat_div(qpoly_leading(rem), lb)
    qcoeffs[shift] = coeff
    let sub : Array[Rat] = []
    for _i in 0..<shift {
      sub.push(rat_zero())
    }
    for i in 0..<b.coeffs.length() {
      sub.push(rat_mul(coeff, b.coeffs[i]))
    }
    rem = qpoly_sub(rem, qpoly_normalize(sub))
  }
  QPolyDiv::{ quotient: qpoly_normalize(qcoeffs), remainder: rem, }
}

///|
pub fn qpoly_mod(a : QPoly, b : QPoly) -> QPoly {
  qpoly_divmod(a, b).remainder
}

///|
pub fn qpoly_div_exact(a : QPoly, b : QPoly) -> QPoly {
  qpoly_divmod(a, b).quotient
}

///|
pub fn qpoly_gcd(a0 : QPoly, b0 : QPoly) -> QPoly {
  // Primitive pseudo-remainder sequence: exact over Q up to the
  // final monic scaling, without intermediate fraction growth.
  let mut a = qpoly_primitive_part(a0)
  let mut b = qpoly_primitive_part(b0)
  if qpoly_degree(a) < qpoly_degree(b) {
    let tmp = a
    a = b
    b = tmp
  }
  while !qpoly_is_zero(b) {
    let r = qpoly_primitive_part(qpoly_pseudo_remainder(a, b))
    a = b
    b = r
  }
  qpoly_monic(a)
}

///|
pub struct QPolyExtGcd {
  g : QPoly
  s : QPoly
  t : QPoly
}

///|
/// Extended gcd: `s·a + t·b = g`, with `g` monic.
pub fn qpoly_extgcd(a0 : QPoly, b0 : QPoly) -> QPolyExtGcd {
  let mut old_r = a0
  let mut r = b0
  let mut old_s = qpoly_one()
  let mut s = qpoly_zero()
  let mut old_t = qpoly_zero()
  let mut t = qpoly_one()
  while !qpoly_is_zero(r) {
    let dm = qpoly_divmod(old_r, r)
    let q = dm.quotient
    // Keep the remainder sequence primitive.  Replacing the
    // remainder by a rational scalar multiple is compensated by
    // scaling the Bezout coefficient recurrence by the same scalar.
    let next_r0 = dm.remainder
    let next_r = qpoly_primitive_part(next_r0)
    let scalar = if qpoly_is_zero(next_r0) {
      rat_one()
    } else {
      rat_div(qpoly_leading(next_r), qpoly_leading(next_r0))
    }
    let next_s = qpoly_scale(scalar, qpoly_sub(old_s, qpoly_mul(q, s)))
    let next_t = qpoly_scale(scalar, qpoly_sub(old_t, qpoly_mul(q, t)))
    old_r = r
    r = next_r
    old_s = s
    s = next_s
    old_t = t
    t = next_t
  }
  if qpoly_is_zero(old_r) {
    QPolyExtGcd::{ g: old_r, s: old_s, t: old_t, }
  } else {
    let inv = rat_inv(qpoly_leading(old_r))
    QPolyExtGcd::{
      g: qpoly_monic(old_r),
      s: qpoly_scale(inv, old_s),
      t: qpoly_scale(inv, old_t),
    }
  }
}

///|
/// The squarefree kernel (radical) `p / gcd(p, p')`, monic.
pub fn qpoly_squarefree_part(p : QPoly) -> QPoly {
  if qpoly_degree(p) <= 0 {
    return qpoly_one()
  }
  let f = qpoly_monic(p)
  let g = qpoly_gcd(f, qpoly_derivative(f))
  qpoly_monic(qpoly_div_exact(f, g))
}

///|
pub fn qpoly_is_squarefree(p : QPoly) -> Bool {
  qpoly_degree(p) <= 0 || qpoly_is_one(qpoly_gcd(p, qpoly_derivative(p)))
}

///|
pub struct QPolyFactor {
  factor : QPoly
  multiplicity : Int32
}

///|
pub fn qpoly_factor(factor : QPoly, multiplicity : Int32) -> QPolyFactor {
  QPolyFactor::{ factor, multiplicity, }
}

///|
/// Yun's squarefree factorization: monic squarefree factors grouped
/// by the multiplicity with which they occur in `p`.
pub fn qpoly_squarefree_factorization(p : QPoly) -> Array[QPolyFactor] {
  let out : Array[QPolyFactor] = []
  if qpoly_degree(p) <= 0 {
    return out
  }
  let f = qpoly_monic(p)
  let df = qpoly_derivative(f)
  let a0 = qpoly_gcd(f, df)
  let mut b = qpoly_div_exact(f, a0)
  let mut c = qpoly_div_exact(df, a0)
  let mut d = qpoly_sub(c, qpoly_derivative(b))
  let mut i = 1
  while qpoly_degree(b) > 0 {
    let a = qpoly_gcd(b, d)
    if qpoly_degree(a) > 0 {
      out.push(qpoly_factor(qpoly_monic(a), i))
    }
    b = qpoly_div_exact(b, a)
    c = qpoly_div_exact(d, a)
    i = i + 1
    d = qpoly_sub(c, qpoly_derivative(b))
  }
  out
}

///|
pub fn qpoly_root_factor(r : Rat) -> QPoly {
  QPoly::{ coeffs: [rat_neg(r), rat_one()], }
}

///|
/// Multiplicity of the rational root `r` (0 when not a root).
pub fn qpoly_root_multiplicity(p : QPoly, r : Rat) -> Int32 {
  if qpoly_is_zero(p) {
    return 0
  }
  let factor = qpoly_root_factor(r)
  let mut q = p
  let mut count = 0
  while !qpoly_is_zero(q) {
    let dm = qpoly_divmod(q, factor)
    if !qpoly_is_zero(dm.remainder) {
      break
    }
    q = dm.quotient
    count = count + 1
  }
  count
}

///|
fn int_lcm(a : Int32, b : Int32) -> Int32 {
  if a == 0 || b == 0 {
    0
  } else {
    int_abs(a / int_gcd(a, b) * b)
  }
}

///|
/// A primitive integer representative of `p`: common denominators
/// cleared, content divided out, leading coefficient positive.
pub fn qpoly_integer_coeffs(p : QPoly) -> Array[Int32] {
  let mut lcm = 1
  for i in 0..<p.coeffs.length() {
    lcm = int_lcm(lcm, p.coeffs[i].den)
  }
  let out : Array[Int32] = []
  let mut content = 0
  for i in 0..<p.coeffs.length() {
    let v = p.coeffs[i].num * (lcm / p.coeffs[i].den)
    out.push(v)
    content = int_gcd(content, v)
  }
  if content > 1 {
    for i in 0..<out.length() {
      out[i] = out[i] / content
    }
  }
  if out.length() > 0 && out[out.length() - 1] < 0 {
    for i in 0..<out.length() {
      out[i] = 0 - out[i]
    }
  }
  out
}

///|
fn int_divisors(n0 : Int32) -> Array[Int32] {
  let n = int_abs(n0)
  let out : Array[Int32] = []
  let mut d = 1
  while d <= n {
    if n % d == 0 {
      out.push(d)
    }
    d = d + 1
  }
  out
}

///|
fn rat_array_contains(xs : Array[Rat], x : Rat) -> Bool {
  for i in 0..<xs.length() {
    if rat_eq(xs[i], x) {
      return true
    }
  }
  false
}

///|
/// All distinct rational roots, by the rational-root theorem.  For
/// the zero polynomial the (infinite) root set is reported as empty.
pub fn qpoly_rational_roots(p : QPoly) -> Array[Rat] {
  let out : Array[Rat] = []
  if qpoly_is_zero(p) || qpoly_degree(p) <= 0 {
    return out
  }
  let mut q = p
  // Extract the root 0 first so the remaining constant term is nonzero.
  while qpoly_degree(q) > 0 && rat_is_zero(qpoly_coeff(q, 0)) {
    q = qpoly_div_exact(q, qpoly_x())
  }
  if qpoly_degree(q) != qpoly_degree(p) {
    out.push(rat_zero())
  }
  if qpoly_degree(q) <= 0 {
    return out
  }
  let ints = qpoly_integer_coeffs(q)
  let ps = int_divisors(ints[0])
  let qs = int_divisors(ints[ints.length() - 1])
  for pi in 0..<ps.length() {
    for qi in 0..<qs.length() {
      for sign in 0..<2 {
        let num = if sign == 0 { ps[pi] } else { 0 - ps[pi] }
        let cand = rat_make(num, qs[qi])
        if !rat_array_contains(out, cand) && rat_is_zero(qpoly_eval(q, cand)) {
          out.push(cand)
        }
      }
    }
  }
  out
}

///|
pub struct QPolyRationalFactorization {
  roots : Array[Rat]
  multiplicities : Array[Int32]
  residual : QPoly
}

///|
/// Factor out every rational root with its multiplicity; the monic
/// residual has no rational roots.
pub fn qpoly_factor_rational_roots(p : QPoly) -> QPolyRationalFactorization {
  let roots = qpoly_rational_roots(p)
  let multiplicities : Array[Int32] = []
  let mut residual = qpoly_monic(p)
  for i in 0..<roots.length() {
    let m = qpoly_root_multiplicity(p, roots[i])
    multiplicities.push(m)
    for _k in 0..<m {
      residual = qpoly_div_exact(residual, qpoly_root_factor(roots[i]))
    }
  }
  QPolyRationalFactorization::{
    roots,
    multiplicities,
    residual: qpoly_monic(residual),
  }
}

///|
/// Irreducibility over Q, decided for degrees at most 3 (where the
/// absence of a rational root is decisive).  Higher degrees report
/// `false`; use the quotient-ring normal forms of `AlgNum`, whose
/// division is partial and therefore sound for any modulus.
pub fn qpoly_irreducible_upto3(p : QPoly) -> Bool {
  let d = qpoly_degree(qpoly_monic(p))
  if d == 1 {
    true
  } else if d == 2 || d == 3 {
    qpoly_rational_roots(p).length() == 0
  } else {
    false
  }
}
