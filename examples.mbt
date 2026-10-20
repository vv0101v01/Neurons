///|
// The worked examples that several layers and the theorem registry share.
//
// These used to live in verify.mbt, which forced the acceptance layer to sit
// *below* the categories it checks (categories.mbt needed example_projector).
// Moving the data down makes verify.mbt a pure aggregator again.

///|
/// 1/√2 to double precision.
pub fn inv_sqrt2() -> Double {
  0.7071067811865476
}

///|
/// Unit vector spanning the example eigenspace: v = (1, i, 0)/√2.
pub fn example_unit() -> CVec {
  [cx(inv_sqrt2(), 0.0), cx(0.0, inv_sqrt2()), cx_zero()]
}

///|
/// The example Hermitian idempotent: P = v·v†.
pub fn example_projector() -> CMat {
  outer(example_unit())
}

///|
pub fn vec_e3() -> CVec {
  [cx_zero(), cx_zero(), cx_real(1.0)]
}

///|
pub fn sample_vectors() -> Array[CVec] {
  [
    [cx_real(1.0), cx(0.0, 1.0), cx(2.0, -1.0)],
    [cx_zero(), cx_zero(), cx_zero()],
    [cx(-1.0, 2.0), cx(0.5, 0.25), cx(0.0, -3.0)],
    example_unit(),
    vec_e3(),
  ]
}

///|
pub fn grid() -> Array[Double] {
  [0.0, 0.25, 0.5, 0.75, 1.0]
}
