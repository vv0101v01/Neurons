///|
// Whitebox tests for the n-dimensional cube algorithm.

///|
fn alg_p0() -> CVec {
  [cx_real(0.0), cx_real(1.0)]
}

///|
fn alg_p1() -> CVec {
  [cx_real(1.0), cx_real(2.0)]
}

///|
fn alg_p2() -> CVec {
  [cx_real(2.0), cx_real(-1.0)]
}

///|
fn alg_p3() -> CVec {
  [cx_real(0.5), cx_real(3.0)]
}

///|
/// An ambient test path a ~ b.
fn alg_path(a : CVec, b : CVec) -> Cube {
  path_line(a, b)
}

///|
test "cube algorithm: 2-D box meets the hand-written square fill on the boundary" {
  let bottom = alg_path(alg_p0(), alg_p1())
  let left = alg_path(alg_p0(), alg_p2())
  let right = alg_path(alg_p1(), alg_p3())
  let samples = default_samples()
  inspect(open_box_wf(bottom, left, right), content="true")
  // the general filler satisfies the same boundary problem ...
  inspect(
    nfill_respects_box(nbox_of_square(bottom, left, right), samples),
    content="true",
  )
  inspect(
    nfill_agrees_with_square_on_given_faces(bottom, left, right, samples),
    content="true",
  )
  inspect(
    ncomp_endpoints_match_legacy_comp(bottom, left, right),
    content="true",
  )
  // ... and is a different section of it than the bottom-anchored formula
  inspect(nfill_differs_from_square_fill(bottom, left, right), content="true")
}

///|
/// A genuinely nonlinear ambient 3-cube, so that the fill is not recovering
/// a multilinear object by accident.
fn alg_cube3() -> Cube {
  Cube::{
    dim: 3,
    cell: pt => {
      let i = pt[0]
      let j = pt[1]
      let k = pt[2]
      [
        cx_real(1.0 + 0.3 * i - 0.7 * j + 0.5 * i * j + 0.2 * k * i),
        cx_real(-0.4 + 0.9 * j * k - 0.25 * i * j * k),
      ]
    },
  }
}

///|
/// The open box of `alg_cube3` missing the face `k = endpoint`.
fn alg_box3(missing_dim : Int32, missing_endpoint : Int32) -> NBox {
  let g = alg_cube3()
  let sides : Array[NBoxSide] = []
  for d in 0..<3 {
    for s in 0..<2 {
      if d == missing_dim && s == missing_endpoint {
        continue
      }
      sides.push(nbox_side(d, s, restrict_face(g, d, s.to_double())))
    }
  }
  nbox(3, missing_dim, missing_endpoint, sides)
}

///|
test "cube algorithm: 3-D boxes are well-formed and the filler respects every given face" {
  let samples = default_samples()
  for k in 0..<3 {
    let b = alg_box3(k, 1)
    inspect(nbox_wf(b, samples), content="true")
    inspect(nfill_respects_box(b, samples), content="true")
    // the filler itself is a 3-cube, and comp drops the missing dimension
    inspect(nfill(b).dim, content="3")
    inspect(ncomp(b).dim, content="2")
  }
}

///|
test "cube algorithm: a malformed box (incompatible faces) is rejected" {
  let samples = default_samples()
  let bottom = alg_path(alg_p0(), alg_p1())
  let left = alg_path(alg_p0(), alg_p2())
  // wrong corner: left(0) no longer meets bottom(0)
  let bad_right = alg_path(alg_p3(), alg_p1())
  let b = nbox_of_square(bottom, left, bad_right)
  inspect(nbox_wf(b, samples), content="false")
}

///|
test "cube algorithm: missing face may be any (dimension, endpoint)" {
  let samples = default_samples()
  let b = alg_box3(1, 0)
  inspect(nbox_wf(b, samples), content="true")
  inspect(nfill_respects_box(b, samples), content="true")
  // comp is the face opposite the missing one
  inspect(ncomp(b).dim, content="2")
}

///|
test "cube algorithm: filling commutes with relabelling dimensions" {
  let samples = default_samples()
  let b = alg_box3(2, 1)
  // (i,j,k) ↦ (k,i,j)
  inspect(nfill_permutation_natural(b, [2, 0, 1], samples), content="true")
  // reversal of two coordinates
  inspect(nfill_permutation_natural(b, [1, 0, 2], samples), content="true")
}

///|
test "cube algorithm: cost is 2^(2n-1)-1 and admits a budget decision" {
  inspect(nfill_term_count(1), content="1")
  inspect(nfill_term_count(2), content="7")
  inspect(nfill_term_count(3), content="31")
  inspect(nfill_term_count(4), content="127")
  inspect(nfill_within_budget(3, 31), content="true")
  inspect(nfill_within_budget(3, 30), content="false")
  inspect(nfill_within_budget(0, 10), content="false")
}

///|
test "cube algorithm: 4-D box boundary" {
  let samples = [0.0, 0.5, 1.0]
  let g = Cube::{
    dim: 4,
    cell: pt => {
      [
        cx_real(pt[0] * pt[1] - 0.3 * pt[2] + 0.5 * pt[3] * pt[1]),
        cx_real(1.0 - 0.2 * pt[3] + 0.7 * pt[0] * pt[2]),
      ]
    },
  }
  let sides : Array[NBoxSide] = []
  for d in 0..<4 {
    for s in 0..<2 {
      if d == 2 && s == 1 {
        continue
      }
      sides.push(nbox_side(d, s, restrict_face(g, d, s.to_double())))
    }
  }
  let b = nbox(4, 2, 1, sides)
  inspect(nbox_wf(b, samples), content="true")
  inspect(nfill_respects_box(b, samples), content="true")
}
