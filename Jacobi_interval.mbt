///|
// Certified Hermitian Jacobi iteration by rational interval arithmetic.
//
// A point Hermitian matrix with rational complex entries is enclosed
// by a complex interval matrix.  At every step the pivot and the
// Jacobi angle are chosen from the midpoint matrix (an ordinary exact
// rational matrix), but the coefficients c, s and a/|a| of the exact
// unitary rotation are replaced by rational intervals proved to
// contain them by interval arithmetic, including outward square-root
// enclosures.  The similarity transform and the accumulated
// eigenvector transform are then evaluated over interval matrices and
// outwardly rounded to a fixed dyadic denominator.
//
// Every stored rotation is independently checkable:
//   * coefficient intervals contain the coefficients recomputed from
//     the stored before-matrix;
//   * J† J - I, evaluated in interval arithmetic, contains zero;
//   * the stored after-matrix contains J† · before · J;
//   * the stored transform-after contains transform-before · J.
// The final eigenvalue intervals are the Gershgorin discs of the
// final Hermitian interval matrix, grouped into clusters with counts.

///|
pub fn rat_cmp_exact(a : Rat, b : Rat) -> Int32 {
  // Cross-multiply in Int64 instead of subtracting in Int32: Jacobi
  // coefficients can have large dyadic numerators even when their
  // values are modest.
  let left = a.num.to_int64() * b.den.to_int64()
  let right = b.num.to_int64() * a.den.to_int64()
  if left > right {
    1
  } else if left < right {
    -1
  } else {
    0
  }
}

///|
pub fn rat_le_exact(a : Rat, b : Rat) -> Bool {
  rat_cmp_exact(a, b) <= 0
}

///|
pub fn rat_abs_exact(a : Rat) -> Rat {
  if a.num < 0 {
    rat_neg(a)
  } else {
    a
  }
}

///|
fn rat_min_exact(a : Rat, b : Rat) -> Rat {
  if rat_le_exact(a, b) {
    a
  } else {
    b
  }
}

///|
fn rat_max_exact(a : Rat, b : Rat) -> Rat {
  if rat_le_exact(a, b) {
    b
  } else {
    a
  }
}

///|
fn rat_to_double_exact(a : Rat) -> Double {
  a.num.to_double() / a.den.to_double()
}

///|
fn pow2_nonneg(k : Int32) -> Int32 {
  let mut out = 1
  for _i in 0..<k {
    out = out * 2
  }
  out
}

///|
fn floor_scaled_rat(a : Rat, scale : Int32) -> Int32 {
  if a.num >= 0 {
    let q = a.num / a.den
    let r = a.num % a.den
    q * scale + r * scale / a.den
  } else {
    let pos = 0 - a.num
    let q = pos / a.den
    let r = pos % a.den
    let ceil_part = q * scale + (r * scale + a.den - 1) / a.den
    0 - ceil_part
  }
}

///|
/// The greatest multiple of `2^-bits` not above `a`.
pub fn rat_round_down_pow2(a : Rat, bits : Int32) -> Rat {
  let b = if bits < 0 { 0 } else if bits > 14 { 14 } else { bits }
  let scale = pow2_nonneg(b)
  rat_make(floor_scaled_rat(a, scale), scale)
}

///|
/// The least multiple of `2^-bits` not below `a`.
pub fn rat_round_up_pow2(a : Rat, bits : Int32) -> Rat {
  rat_neg(rat_round_down_pow2(rat_neg(a), bits))
}

///|
pub struct RatInterval {
  lo : Rat
  hi : Rat
} derive(Debug, Eq)

///|
pub extend RatInterval with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend RatInterval with Eq::{not_equal, equal}

///|
pub fn rat_interval(lo : Rat, hi : Rat) -> RatInterval {
  if rat_le_exact(lo, hi) {
    RatInterval::{ lo, hi, }
  } else {
    RatInterval::{ lo: hi, hi: lo, }
  }
}

///|
pub fn rat_interval_point(a : Rat) -> RatInterval {
  RatInterval::{ lo: a, hi: a, }
}

///|
pub fn rat_interval_contains(x : RatInterval, a : Rat) -> Bool {
  rat_le_exact(x.lo, a) && rat_le_exact(a, x.hi)
}

///|
pub fn rat_interval_subset(a : RatInterval, b : RatInterval) -> Bool {
  rat_le_exact(b.lo, a.lo) && rat_le_exact(a.hi, b.hi)
}

///|
pub fn rat_interval_hull(a : RatInterval, b : RatInterval) -> RatInterval {
  RatInterval::{ lo: rat_min_exact(a.lo, b.lo), hi: rat_max_exact(a.hi, b.hi), }
}

///|
pub fn rat_interval_midpoint(a : RatInterval) -> Rat {
  rat_div(rat_add(a.lo, a.hi), rat_int(2))
}

///|
pub fn rat_interval_normalize(a : RatInterval, bits : Int32) -> RatInterval {
  RatInterval::{
    lo: rat_round_down_pow2(a.lo, bits),
    hi: rat_round_up_pow2(a.hi, bits),
  }
}

///|
pub fn rat_interval_add(a : RatInterval, b : RatInterval) -> RatInterval {
  RatInterval::{ lo: rat_add(a.lo, b.lo), hi: rat_add(a.hi, b.hi), }
}

///|
pub fn rat_interval_neg(a : RatInterval) -> RatInterval {
  RatInterval::{ lo: rat_neg(a.hi), hi: rat_neg(a.lo), }
}

///|
pub fn rat_interval_sub(a : RatInterval, b : RatInterval) -> RatInterval {
  rat_interval_add(a, rat_interval_neg(b))
}

///|
pub fn rat_interval_mul(a : RatInterval, b : RatInterval) -> RatInterval {
  let p1 = rat_mul(a.lo, b.lo)
  let p2 = rat_mul(a.lo, b.hi)
  let p3 = rat_mul(a.hi, b.lo)
  let p4 = rat_mul(a.hi, b.hi)
  RatInterval::{
    lo: rat_min_exact(rat_min_exact(p1, p2), rat_min_exact(p3, p4)),
    hi: rat_max_exact(rat_max_exact(p1, p2), rat_max_exact(p3, p4)),
  }
}

///|
pub fn rat_interval_abs(a : RatInterval) -> RatInterval {
  if rat_le_exact(rat_zero(), a.lo) {
    a
  } else if rat_le_exact(a.hi, rat_zero()) {
    rat_interval_neg(a)
  } else {
    RatInterval::{
      lo: rat_zero(),
      hi: rat_max_exact(rat_abs_exact(a.lo), rat_abs_exact(a.hi)),
    }
  }
}

///|
pub fn rat_interval_recip(a : RatInterval) -> RatInterval? {
  if rat_interval_contains(a, rat_zero()) {
    None
  } else {
    Some(rat_interval(rat_inv(a.lo), rat_inv(a.hi)))
  }
}

///|
pub fn rat_interval_div(a : RatInterval, b : RatInterval) -> RatInterval? {
  match rat_interval_recip(b) {
    Some(r) => Some(rat_interval_mul(a, r))
    None => None
  }
}

///|
fn scaled_square_le(m : Int32, scale : Int32, x : Rat) -> Bool {
  // `(m/scale)^2 <= x`, cross-multiplied in Int64 so the binary
  // search remains exact for the large dyadic numerators that occur
  // when a Jacobi pivot is tiny (hence tau is large).
  let left = m.to_int64() * m.to_int64() * x.den.to_int64()
  let right = x.num.to_int64() * scale.to_int64() * scale.to_int64()
  left <= right
}

///|
/// An exact rational interval around `sqrt(x)` of width at most
/// `2^-bits`, found by integer binary search and checked with exact
/// rational squares.  Returns None for negative `x`.
pub fn rat_sqrt_interval(x : Rat, bits : Int32) -> RatInterval? {
  if rat_cmp_exact(x, rat_zero()) < 0 {
    return None
  }
  let b = if bits < 0 { 0 } else if bits > 12 { 12 } else { bits }
  let scale = pow2_nonneg(b)
  let approx = rat_to_double_exact(x).sqrt()
  let mut hi = ((approx + 2.0) * scale.to_double()).to_int() + 2
  if hi < 1 {
    hi = 1
  }
  while scaled_square_le(hi, scale, x) {
    hi = hi * 2
    if hi > 1000000 {
      return None
    }
  }
  let mut lo = 0
  while lo + 1 < hi {
    let mid = (lo + hi) / 2
    if scaled_square_le(mid, scale, x) {
      lo = mid
    } else {
      hi = mid
    }
  }
  let lo_rat = rat_make(lo, scale)
  if rat_eq(rat_mul(lo_rat, lo_rat), x) {
    Some(rat_interval_point(lo_rat))
  } else {
    Some(RatInterval::{ lo: lo_rat, hi: rat_make(lo + 1, scale), })
  }
}

///|
pub fn rat_interval_sqrt(a : RatInterval, bits : Int32) -> RatInterval? {
  match (rat_sqrt_interval(a.lo, bits), rat_sqrt_interval(a.hi, bits)) {
    (Some(x), Some(y)) => Some(RatInterval::{ lo: x.lo, hi: y.hi, })
    _ => None
  }
}

///|
pub struct QCpx {
  re : Rat
  im : Rat
} derive(Debug, Eq)

///|
pub extend QCpx with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QCpx with Eq::{not_equal, equal}

///|
pub fn qcpx(re : Rat, im : Rat) -> QCpx {
  QCpx::{ re, im, }
}

///|
pub fn qcpx_real(re : Rat) -> QCpx {
  QCpx::{ re, im: rat_zero(), }
}

///|
pub fn qcpx_is_zero(a : QCpx) -> Bool {
  rat_is_zero(a.re) && rat_is_zero(a.im)
}

///|
pub struct QCpxMat {
  n : Int32
  rows : Array[Array[QCpx]]
} derive(Debug, Eq)

///|
pub extend QCpxMat with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QCpxMat with Eq::{not_equal, equal}

///|
pub fn qcpx_mat_from_rows(rows : Array[Array[QCpx]]) -> QCpxMat {
  QCpxMat::{ n: rows.length(), rows, }
}

///|
pub fn qcpx_mat_from_qmat(a : QMat) -> QCpxMat {
  let rows : Array[Array[QCpx]] = []
  for i in 0..<a.rows.length() {
    let row : Array[QCpx] = []
    for j in 0..<a.rows[i].length() {
      row.push(qcpx_real(a.rows[i][j]))
    }
    rows.push(row)
  }
  qcpx_mat_from_rows(rows)
}

///|
pub fn qcpx_mat_is_hermitian(a : QCpxMat) -> Bool {
  if a.rows.length() != a.n {
    return false
  }
  for i in 0..<a.n {
    if a.rows[i].length() != a.n || !rat_is_zero(a.rows[i][i].im) {
      return false
    }
    for j in (i + 1)..<a.n {
      let x = a.rows[i][j]
      let y = a.rows[j][i]
      if !rat_eq(x.re, y.re) || !rat_eq(x.im, rat_neg(y.im)) {
        return false
      }
    }
  }
  true
}

///|
pub struct CInterval {
  re : RatInterval
  im : RatInterval
} derive(Debug, Eq)

///|
pub extend CInterval with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend CInterval with Eq::{not_equal, equal}

///|
pub fn cinterval_point(a : QCpx) -> CInterval {
  CInterval::{ re: rat_interval_point(a.re), im: rat_interval_point(a.im), }
}

///|
pub fn cinterval_zero() -> CInterval {
  cinterval_point(qcpx_real(rat_zero()))
}

///|
pub fn cinterval_one() -> CInterval {
  cinterval_point(qcpx_real(rat_one()))
}

///|
pub fn cinterval_conj(a : CInterval) -> CInterval {
  CInterval::{ re: a.re, im: rat_interval_neg(a.im), }
}

///|
pub fn cinterval_add(a : CInterval, b : CInterval) -> CInterval {
  CInterval::{
    re: rat_interval_add(a.re, b.re),
    im: rat_interval_add(a.im, b.im),
  }
}

///|
pub fn cinterval_neg(a : CInterval) -> CInterval {
  CInterval::{ re: rat_interval_neg(a.re), im: rat_interval_neg(a.im), }
}

///|
pub fn cinterval_sub(a : CInterval, b : CInterval) -> CInterval {
  cinterval_add(a, cinterval_neg(b))
}

///|
pub fn cinterval_mul(a : CInterval, b : CInterval) -> CInterval {
  CInterval::{
    re: rat_interval_sub(
      rat_interval_mul(a.re, b.re),
      rat_interval_mul(a.im, b.im),
    ),
    im: rat_interval_add(
      rat_interval_mul(a.re, b.im),
      rat_interval_mul(a.im, b.re),
    ),
  }
}

///|
pub fn cinterval_contains(a : CInterval, x : QCpx) -> Bool {
  rat_interval_contains(a.re, x.re) && rat_interval_contains(a.im, x.im)
}

///|
pub fn cinterval_subset(a : CInterval, b : CInterval) -> Bool {
  rat_interval_subset(a.re, b.re) && rat_interval_subset(a.im, b.im)
}

///|
pub fn cinterval_hull(a : CInterval, b : CInterval) -> CInterval {
  CInterval::{
    re: rat_interval_hull(a.re, b.re),
    im: rat_interval_hull(a.im, b.im),
  }
}

///|
pub fn cinterval_normalize(a : CInterval, bits : Int32) -> CInterval {
  CInterval::{
    re: rat_interval_normalize(a.re, bits),
    im: rat_interval_normalize(a.im, bits),
  }
}

///|
pub fn cinterval_midpoint(a : CInterval) -> QCpx {
  QCpx::{ re: rat_interval_midpoint(a.re), im: rat_interval_midpoint(a.im), }
}

///|
fn cinterval_abs_sq_upper(a : CInterval) -> Rat {
  let re = rat_interval_abs(a.re).hi
  let im = rat_interval_abs(a.im).hi
  rat_add(rat_mul(re, re), rat_mul(im, im))
}

///|
pub struct QCIntervalMat {
  n : Int32
  rows : Array[Array[CInterval]]
} derive(Debug, Eq)

///|
pub extend QCIntervalMat with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QCIntervalMat with Eq::{not_equal, equal}

///|
pub fn qci_mat_from_rows(rows : Array[Array[CInterval]]) -> QCIntervalMat {
  QCIntervalMat::{ n: rows.length(), rows, }
}

///|
pub fn qci_mat_from_point(a : QCpxMat) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.rows.length() {
    let row : Array[CInterval] = []
    for j in 0..<a.rows[i].length() {
      row.push(cinterval_point(a.rows[i][j]))
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_identity(n : Int32) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<n {
    let row : Array[CInterval] = []
    for j in 0..<n {
      row.push(if i == j { cinterval_one() } else { cinterval_zero() })
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_zero(n : Int32) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for _i in 0..<n {
    let row : Array[CInterval] = []
    for _j in 0..<n {
      row.push(cinterval_zero())
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_adjoint(a : QCIntervalMat) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.n {
    let row : Array[CInterval] = []
    for j in 0..<a.n {
      row.push(cinterval_conj(a.rows[j][i]))
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_sub(a : QCIntervalMat, b : QCIntervalMat) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.n {
    let row : Array[CInterval] = []
    for j in 0..<a.n {
      row.push(cinterval_sub(a.rows[i][j], b.rows[i][j]))
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_mul(a : QCIntervalMat, b : QCIntervalMat) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.n {
    let row : Array[CInterval] = []
    for j in 0..<a.n {
      let mut acc = cinterval_zero()
      for k in 0..<a.n {
        acc = cinterval_add(acc, cinterval_mul(a.rows[i][k], b.rows[k][j]))
      }
      row.push(acc)
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_normalize(a : QCIntervalMat, bits : Int32) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.n {
    let row : Array[CInterval] = []
    for j in 0..<a.n {
      row.push(cinterval_normalize(a.rows[i][j], bits))
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
/// Outward Hermitian symmetrization.  If both off-diagonal boxes
/// contain conjugate exact entries, replacing the pair by their hull
/// (and its conjugate) still contains those entries.
pub fn qci_mat_hermitian_hull(a : QCIntervalMat) -> QCIntervalMat {
  let out = qci_mat_zero(a.n)
  for i in 0..<a.n {
    for j in 0..<a.n {
      out.rows[i][j] = a.rows[i][j]
    }
  }
  for i in 0..<a.n {
    let d = out.rows[i][i]
    if rat_interval_contains(d.im, rat_zero()) {
      out.rows[i][i] = CInterval::{
        re: d.re,
        im: rat_interval_point(rat_zero()),
      }
    }
    for j in (i + 1)..<a.n {
      let common = cinterval_hull(
        out.rows[i][j],
        cinterval_conj(out.rows[j][i]),
      )
      out.rows[i][j] = common
      out.rows[j][i] = cinterval_conj(common)
    }
  }
  out
}

///|
pub fn qci_mat_is_hermitian(a : QCIntervalMat) -> Bool {
  for i in 0..<a.n {
    if a.rows[i][i].im.lo != rat_zero() || a.rows[i][i].im.hi != rat_zero() {
      return false
    }
    for j in (i + 1)..<a.n {
      if a.rows[j][i] != cinterval_conj(a.rows[i][j]) {
        return false
      }
    }
  }
  true
}

///|
pub fn qci_mat_contains(a : QCIntervalMat, b : QCIntervalMat) -> Bool {
  if a.n != b.n {
    return false
  }
  for i in 0..<a.n {
    for j in 0..<a.n {
      if !cinterval_subset(b.rows[i][j], a.rows[i][j]) {
        return false
      }
    }
  }
  true
}

///|
pub fn qci_mat_midpoint(a : QCIntervalMat) -> QCpxMat {
  let rows : Array[Array[QCpx]] = []
  for i in 0..<a.n {
    let row : Array[QCpx] = []
    for j in 0..<a.n {
      row.push(cinterval_midpoint(a.rows[i][j]))
    }
    rows.push(row)
  }
  qcpx_mat_from_rows(rows)
}

///|
/// An exact rational upper bound on the squared off-diagonal
/// Frobenius norm of every matrix in the enclosure.
pub fn qci_off_frobenius_sq_upper(a : QCIntervalMat) -> Rat {
  let mut acc = rat_zero()
  for i in 0..<a.n {
    for j in 0..<a.n {
      if i != j {
        acc = rat_add(acc, cinterval_abs_sq_upper(a.rows[i][j]))
      }
    }
  }
  acc
}

///|
pub struct JacobiCoefficients {
  p : Int32
  q : Int32
  cosine : RatInterval
  sine : RatInterval
  phase : CInterval
  modulus : RatInterval
} derive(Debug, Eq)

///|
pub extend JacobiCoefficients with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend JacobiCoefficients with Eq::{not_equal, equal}

///|
fn jacobi_largest_pivot(a : QCpxMat) -> (Int32, Int32, Rat) {
  let mut best_p = -1
  let mut best_q = -1
  let mut best = rat_zero()
  for i in 0..<a.n {
    for j in (i + 1)..<a.n {
      let x = a.rows[i][j]
      let score = rat_add(rat_mul(x.re, x.re), rat_mul(x.im, x.im))
      if rat_cmp_exact(score, best) > 0 {
        best = score
        best_p = i
        best_q = j
      }
    }
  }
  (best_p, best_q, best)
}

///|
/// Interval enclosures of the exact complex Jacobi coefficients for
/// the displayed pivot of a point Hermitian matrix.  With
/// `u = a_pq/|a_pq|`, the unitary block is
/// `[[c, s u],[-s conj(u), c]]`.
pub fn jacobi_coefficients(
  a : QCpxMat,
  p : Int32,
  q : Int32,
  bits : Int32,
) -> JacobiCoefficients? {
  if p < 0 || q <= p || q >= a.n || !qcpx_mat_is_hermitian(a) {
    return None
  }
  let entry = a.rows[p][q]
  if qcpx_is_zero(entry) {
    return None
  }
  let mod_sq = rat_add(rat_mul(entry.re, entry.re), rat_mul(entry.im, entry.im))
  let modulus = match rat_sqrt_interval(mod_sq, bits) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let phase_re = match rat_interval_div(rat_interval_point(entry.re), modulus) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let phase_im = match rat_interval_div(rat_interval_point(entry.im), modulus) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let alpha = a.rows[p][p].re
  let beta = a.rows[q][q].re
  let numerator = rat_sub(beta, alpha)
  let tau = match
    rat_interval_div(
      rat_interval_point(numerator),
      rat_interval_mul(rat_interval_point(rat_int(2)), modulus),
    ) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let tau_sq = rat_interval_mul(tau, tau)
  let root = match
    rat_interval_sqrt(
      rat_interval_add(rat_interval_point(rat_one()), tau_sq),
      bits,
    ) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let denom = rat_interval_add(rat_interval_abs(tau), root)
  let sign = if rat_cmp_exact(numerator, rat_zero()) < 0 {
    rat_int(-1)
  } else {
    rat_int(1)
  }
  let t = match rat_interval_div(rat_interval_point(sign), denom) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let c_root = match
    rat_interval_sqrt(
      rat_interval_add(rat_interval_point(rat_one()), rat_interval_mul(t, t)),
      bits,
    ) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let cosine = match rat_interval_div(rat_interval_point(rat_one()), c_root) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let sine = rat_interval_normalize(rat_interval_mul(t, cosine), bits)
  Some(JacobiCoefficients::{
    p,
    q,
    cosine,
    sine,
    phase: CInterval::{ re: phase_re, im: phase_im, },
    modulus,
  })
}

///|
/// The interval unitary matrix for enclosed Jacobi coefficients.
pub fn jacobi_unitary_interval(
  n : Int32,
  coeffs : JacobiCoefficients,
  bits~ : Int32 = 10,
) -> QCIntervalMat {
  let precision = bits
  let out = qci_mat_identity(n)
  let c = CInterval::{ re: coeffs.cosine, im: rat_interval_point(rat_zero()), }
  let s = CInterval::{ re: coeffs.sine, im: rat_interval_point(rat_zero()), }
  out.rows[coeffs.p][coeffs.p] = c
  out.rows[coeffs.q][coeffs.q] = c
  out.rows[coeffs.p][coeffs.q] = cinterval_mul(s, coeffs.phase)
  out.rows[coeffs.q][coeffs.p] = cinterval_neg(
    cinterval_mul(s, cinterval_conj(coeffs.phase)),
  )
  // Outward dyadic rounding bounds every denominator before the
  // subsequent similarity/residual multiplications.
  qci_mat_normalize(out, precision)
}

///|
pub fn jacobi_unitary_residual_contains_zero(
  u : QCIntervalMat,
  bits : Int32,
) -> Bool {
  let residual = qci_mat_normalize(
    qci_mat_sub(qci_mat_mul(qci_mat_adjoint(u), u), qci_mat_identity(u.n)),
    bits,
  )
  for i in 0..<u.n {
    for j in 0..<u.n {
      if !cinterval_contains(residual.rows[i][j], qcpx_real(rat_zero())) {
        return false
      }
    }
  }
  true
}

///|
pub struct JacobiRotationCertificate {
  before : QCIntervalMat
  after : QCIntervalMat
  transform_before : QCIntervalMat
  transform_after : QCIntervalMat
  coeffs : JacobiCoefficients
  unitary_residual_contains_zero : Bool
  before_off_sq_upper : Rat
  after_off_sq_upper : Rat
} derive(Debug, Eq)

///|
pub extend JacobiRotationCertificate with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend JacobiRotationCertificate with Eq::{not_equal, equal}

///|
pub struct EigenInterval {
  lo : Rat
  hi : Rat
  count : Int32
} derive(Debug, Eq)

///|
pub extend EigenInterval with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend EigenInterval with Eq::{not_equal, equal}

///|
pub struct JacobiCertificate {
  precision_bits : Int32
  initial : QCIntervalMat
  final_matrix : QCIntervalMat
  transform : QCIntervalMat
  rotations : Array[JacobiRotationCertificate]
  eigenvalues : Array[EigenInterval]
} derive(Debug, Eq)

///|
pub extend JacobiCertificate with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend JacobiCertificate with Eq::{not_equal, equal}

///|
/// Interval similarity transform with outward dyadic rounding after
/// each multiplication.  Rounding the intermediate product is essential:
/// it both preserves inclusion and keeps Int32 rational numerators in
/// the range where the next exact endpoint arithmetic is meaningful.
pub fn jacobi_similarity_interval(
  a : QCIntervalMat,
  u : QCIntervalMat,
  bits : Int32,
) -> QCIntervalMat {
  let middle = qci_mat_normalize(qci_mat_mul(a, u), bits)
  qci_mat_hermitian_hull(
    qci_mat_normalize(qci_mat_mul(qci_mat_adjoint(u), middle), bits),
  )
}

///|
fn jacobi_apply_step(
  current : QCIntervalMat,
  transform : QCIntervalMat,
  coeffs : JacobiCoefficients,
  bits : Int32,
) -> JacobiRotationCertificate {
  let u = jacobi_unitary_interval(current.n, coeffs, bits~)
  let after = jacobi_similarity_interval(current, u, bits)
  let transform_after = qci_mat_normalize(qci_mat_mul(transform, u), bits)
  JacobiRotationCertificate::{
    before: current,
    after,
    transform_before: transform,
    transform_after,
    coeffs,
    unitary_residual_contains_zero: jacobi_unitary_residual_contains_zero(
      u, bits,
    ),
    before_off_sq_upper: qci_off_frobenius_sq_upper(current),
    after_off_sq_upper: qci_off_frobenius_sq_upper(after),
  }
}

///|
fn jacobi_eigenvalue_intervals(
  a : QCIntervalMat,
  bits : Int32,
) -> Array[EigenInterval] {
  let discs : Array[EigenInterval] = []
  for i in 0..<a.n {
    let mut radius = rat_interval_point(rat_zero())
    for j in 0..<a.n {
      if i != j {
        let root = match
          rat_sqrt_interval(cinterval_abs_sq_upper(a.rows[i][j]), bits) {
          Some(x) => x
          None => rat_interval_point(rat_zero())
        }
        radius = rat_interval_add(radius, root)
      }
    }
    radius = rat_interval_normalize(radius, bits)
    discs.push(EigenInterval::{
      lo: rat_sub(a.rows[i][i].re.lo, radius.hi),
      hi: rat_add(a.rows[i][i].re.hi, radius.hi),
      count: 1,
    })
  }
  // Insertion sort by lower endpoint (the matrices here are small).
  for i in 1..<discs.length() {
    let mut j = i
    while j > 0 && rat_cmp_exact(discs[j - 1].lo, discs[j].lo) > 0 {
      let tmp = discs[j - 1]
      discs[j - 1] = discs[j]
      discs[j] = tmp
      j = j - 1
    }
  }
  let out : Array[EigenInterval] = []
  for i in 0..<discs.length() {
    if out.length() == 0 {
      out.push(discs[i])
    } else {
      let last = out[out.length() - 1]
      if rat_le_exact(discs[i].lo, last.hi) {
        out[out.length() - 1] = EigenInterval::{
          lo: last.lo,
          hi: rat_max_exact(last.hi, discs[i].hi),
          count: last.count + 1,
        }
      } else {
        out.push(discs[i])
      }
    }
  }
  out
}

///|
/// Run certified Jacobi sweeps.  `tolerance_sq` is applied to the
/// largest squared off-diagonal entry of the midpoint matrix; the
/// returned certificate is meaningful whether or not that stopping
/// threshold was reached.
pub fn jacobi_interval_eigen(
  input : QCpxMat,
  max_steps~ : Int32 = 24,
  tolerance_sq~ : Rat = rat_make(1, 1048576),
  precision_bits~ : Int32 = 10,
) -> JacobiCertificate? {
  let steps = max_steps
  let tol = tolerance_sq
  let bits = precision_bits
  if !qcpx_mat_is_hermitian(input) || steps < 0 {
    return None
  }
  let initial = qci_mat_from_point(input)
  let mut current = initial
  let mut transform = qci_mat_identity(input.n)
  let rotations : Array[JacobiRotationCertificate] = []
  for _step in 0..<steps {
    let midpoint = qci_mat_midpoint(current)
    let (p, q, score) = jacobi_largest_pivot(midpoint)
    if p < 0 || rat_le_exact(score, tol) {
      break
    }
    match jacobi_coefficients(midpoint, p, q, bits) {
      Some(coeffs) => {
        let cert = jacobi_apply_step(current, transform, coeffs, bits)
        current = cert.after
        transform = cert.transform_after
        rotations.push(cert)
      }
      None => break
    }
  }
  Some(JacobiCertificate::{
    precision_bits: bits,
    initial,
    final_matrix: current,
    transform,
    rotations,
    eigenvalues: jacobi_eigenvalue_intervals(current, bits),
  })
}

///|
fn jacobi_coefficients_contained(
  expected : JacobiCoefficients,
  candidate : JacobiCoefficients,
) -> Bool {
  candidate.p == expected.p &&
  candidate.q == expected.q &&
  rat_interval_subset(expected.cosine, candidate.cosine) &&
  rat_interval_subset(expected.sine, candidate.sine) &&
  rat_interval_subset(expected.modulus, candidate.modulus) &&
  cinterval_subset(expected.phase, candidate.phase)
}

///|
/// Independently verify the symbolic interval inclusions in one
/// Jacobi rotation and in the final Gershgorin eigenvalue discs.
pub fn jacobi_certificate_sound(
  input : QCpxMat,
  cert : JacobiCertificate,
) -> Bool {
  if !qcpx_mat_is_hermitian(input) {
    return false
  }
  if cert.initial != qci_mat_from_point(input) ||
    !qci_mat_is_hermitian(cert.final_matrix) {
    return false
  }
  let mut expected_before = cert.initial
  let mut expected_transform = qci_mat_identity(input.n)
  for i in 0..<cert.rotations.length() {
    let step = cert.rotations[i]
    if step.before != expected_before ||
      step.transform_before != expected_transform {
      return false
    }
    let midpoint = qci_mat_midpoint(step.before)
    let expected_coeffs = match
      jacobi_coefficients(
        midpoint,
        step.coeffs.p,
        step.coeffs.q,
        cert.precision_bits,
      ) {
      Some(x) => x
      None => return false
    }
    if !jacobi_coefficients_contained(expected_coeffs, step.coeffs) {
      return false
    }
    let u = jacobi_unitary_interval(
      input.n,
      step.coeffs,
      bits=cert.precision_bits,
    )
    if !step.unitary_residual_contains_zero ||
      !jacobi_unitary_residual_contains_zero(u, cert.precision_bits) {
      return false
    }
    let computed_after = jacobi_similarity_interval(
      step.before,
      u,
      cert.precision_bits,
    )
    if !qci_mat_contains(step.after, computed_after) {
      return false
    }
    let computed_transform = qci_mat_normalize(
      qci_mat_mul(step.transform_before, u),
      cert.precision_bits,
    )
    if !qci_mat_contains(step.transform_after, computed_transform) {
      return false
    }
    if step.before_off_sq_upper != qci_off_frobenius_sq_upper(step.before) ||
      step.after_off_sq_upper != qci_off_frobenius_sq_upper(step.after) {
      return false
    }
    expected_before = step.after
    expected_transform = step.transform_after
  }
  if expected_before != cert.final_matrix ||
    expected_transform != cert.transform {
    return false
  }
  let expected_eigs = jacobi_eigenvalue_intervals(
    cert.final_matrix,
    cert.precision_bits,
  )
  if expected_eigs.length() != cert.eigenvalues.length() {
    return false
  }
  let mut total = 0
  for i in 0..<expected_eigs.length() {
    if expected_eigs[i] != cert.eigenvalues[i] {
      return false
    }
    total = total + cert.eigenvalues[i].count
  }
  total == input.n
}

///|
pub fn eigen_interval_contains(e : EigenInterval, x : Rat) -> Bool {
  rat_le_exact(e.lo, x) && rat_le_exact(x, e.hi)
}

///|
pub fn check_Jacobi_interval() -> Bool {
  let sqrt2 = match rat_sqrt_interval(rat_int(2), 10) {
    Some(x) =>
      rat_le_exact(rat_mul(x.lo, x.lo), rat_int(2)) &&
      rat_le_exact(rat_int(2), rat_mul(x.hi, x.hi))
    None => false
  }
  if !sqrt2 {
    return false
  }
  let block = qcpx_mat_from_qmat(
    qmat_from_int_rows([[2, 1, 0], [1, 2, 0], [0, 0, -1]]),
  )
  let block_cert = match jacobi_interval_eigen(block) {
    Some(c) => c
    None => return false
  }
  if !jacobi_certificate_sound(block, block_cert) ||
    block_cert.eigenvalues.length() != 3 {
    return false
  }
  if !eigen_interval_contains(block_cert.eigenvalues[0], rat_int(-1)) ||
    !eigen_interval_contains(block_cert.eigenvalues[1], rat_int(1)) ||
    !eigen_interval_contains(block_cert.eigenvalues[2], rat_int(3)) {
    return false
  }
  for i in 0..<block_cert.eigenvalues.length() {
    let e = block_cert.eigenvalues[i]
    if e.count != 1 || rat_cmp_exact(rat_sub(e.hi, e.lo), rat_make(1, 8)) > 0 {
      return false
    }
  }
  // A genuinely complex Hermitian example.  Its characteristic
  // polynomial is checked only through certified disjoint discs and
  // the trace interval.
  let complex_input = qcpx_mat_from_rows([
    [qcpx_real(rat_int(2)), qcpx(rat_zero(), rat_int(1)), qcpx_real(rat_zero())],
    [
      qcpx(rat_zero(), rat_int(-1)),
      qcpx_real(rat_int(3)),
      qcpx_real(rat_int(1)),
    ],
    [qcpx_real(rat_zero()), qcpx_real(rat_int(1)), qcpx_real(rat_int(6))],
  ])
  let complex_cert = match jacobi_interval_eigen(complex_input, max_steps=30) {
    Some(c) => c
    None => return false
  }
  if !jacobi_certificate_sound(complex_input, complex_cert) ||
    complex_cert.eigenvalues.length() != 3 {
    return false
  }
  let mut trace_lo = rat_zero()
  let mut trace_hi = rat_zero()
  for i in 0..<complex_cert.eigenvalues.length() {
    let e = complex_cert.eigenvalues[i]
    trace_lo = rat_add(trace_lo, e.lo)
    trace_hi = rat_add(trace_hi, e.hi)
  }
  rat_le_exact(trace_lo, rat_int(11)) && rat_le_exact(rat_int(11), trace_hi)
}
