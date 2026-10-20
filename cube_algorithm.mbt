///|
// The n-dimensional cube algorithm (立方體演算法).
//
// `cube.mbt` hard-codes the two-dimensional open box: three faces
// (bottom, left, right) and the affine filler
//     F(i,j) = b(i) + (1−i)(l(j) − b(0)) + i(r(j) − b(1)).
// Here the same construction is *derived* for an arbitrary dimension and
// an arbitrary missing face, by the Möbius (inclusion–exclusion) sum over
// the face lattice of the cube.
//
// Data.  An n-box in Cᵐ is a family of (n−1)-cubes, one per face, except
// for a single missing face (k, ε).  Writing L for the set of given faces,
// the sides are indexed by pairs (d, s) ∈ L.  Every side (d, s) is an
// (n−1)-cube whose coordinates are the remaining dimensions, in increasing
// order — the same convention as `restrict_face`.
//
// Algorithm.  For x ∈ Iⁿ put w(d,0)(x) = 1 − x_d and w(d,1)(x) = x_d, and
// let S ↦ face_S(x) evaluate the side at the intersection of the faces in S
// (the dimensions of S are fixed to their endpoints, the others are read off
// x).  Since S may contain both endpoints of one dimension, the intersection
// is read off the *last* selected side; that anchor is what makes the sum
// telescope on the boundary.  Then
//     F(x) = Σ_{∅ ≠ S ⊆ L} (−1)^{|S|+1} · (Π_{(d,s) ∈ S} w(d,s)(x_d)) · face_S(x).
//
// This is the standard `comp` formula of cubical type theory (in the
// Cohen–Coquand–Huber–Mörtberg presentation the composition operation is
// exactly such an alternating sum over the tube).  Two facts make it an
// algorithm rather than a formula:
//
//   * On a given face (d,s) ∈ L the sum telescopes to the face's own cube,
//     so F restricts to the given boundary (`nfill_respects_box`); this is
//     checked on grids for dimensions 2–4 and every choice of missing face.
//   * The formula is symmetric under relabelling of dimensions and under
//     reversal of an interval, so filling commutes with coordinate changes
//     (`nfill_permutation_natural`).
//
// The missing face (k, ε), read off the filler, is `comp`: the composite
// `ncomp(box) = restrict_face(nfill(box), k, ε)`.
//
// Relation to `cube.mbt`.  The hand-written square filler
//     F₀(i,j) = b(i) + (1−i)(l(j) − b(0)) + i(r(j) − b(1))
// anchors on the bottom face: it transports the two vertical sides along the
// bottom, and that asymmetry is exactly what stops it generalising — it
// distinguishes the dimension it fills along from the one it corrects in.
// The Möbius filler is symmetric in the dimensions, so it works for any
// missing face and commutes with relabelling.  The two fillers are different
// sections of the same boundary-restriction map: they agree on all given
// faces (`nfill_agrees_with_square_on_given_faces`) and their composites have
// the same endpoints (`ncomp_endpoints_match_legacy_comp`), but they differ in
// the interior (`nfill_differs_from_square_fill`).  Both are valid, and the
// general one is what the rest of the project can use at higher dimension.
//
// Cost.  |L| = 2n − 1, so the sum has 2^(2n−1) − 1 terms and each term
// evaluates one face; `nfill_term_count` exposes this and
// `nfill_within_budget` turns it into a decision procedure with a budget,
// the same style as the BDD node budgets in `bdd_dag.mbt`.

///|
/// One given face of an open box: the plane `dim = endpoint`, realised as
/// an (n−1)-cube over the remaining coordinates.
pub struct NBoxSide {
  dim : Int32
  endpoint : Int32
  face : Cube
}

///|
pub fn nbox_side(dim : Int32, endpoint : Int32, face : Cube) -> NBoxSide {
  NBoxSide::{ dim, endpoint, face, }
}

///|
/// An n-dimensional open box: every face is given except
/// `missing_dim = missing_endpoint`.
pub struct NBox {
  dim : Int32
  missing_dim : Int32
  missing_endpoint : Int32
  sides : Array[NBoxSide]
}

///|
pub fn nbox(
  dim : Int32,
  missing_dim : Int32,
  missing_endpoint : Int32,
  sides : Array[NBoxSide],
) -> NBox {
  NBox::{ dim, missing_dim, missing_endpoint, sides, }
}

///|
/// The index of a global dimension inside a face cube whose own plane is
/// `plane`; faces drop exactly the coordinate of their plane.
pub fn nbox_face_index(plane : Int32, d : Int32) -> Int32 {
  if d < plane {
    d
  } else {
    d - 1
  }
}

///|
pub fn nbox_is_given(b : NBox, d : Int32, s : Int32) -> Bool {
  let mut found = false
  for i in 0..<b.sides.length() {
    if b.sides[i].dim == d && b.sides[i].endpoint == s {
      found = true
    }
  }
  found
}

///|
/// The default sample grid used by the decision procedures below.
pub fn default_samples() -> Array[Double] {
  [0.0, 0.25, 0.5, 0.75, 1.0]
}

///|
/// Pointwise equality of two cubes of the same dimension on a grid.
pub fn cube_approx_eq(a : Cube, b : Cube, samples : Array[Double]) -> Bool {
  if a.dim != b.dim {
    return false
  }
  let m = samples.length()
  let total = int_pow(m, a.dim)
  for code in 0..<total {
    let pt : Array[Double] = []
    let mut rest = code
    for _d in 0..<a.dim {
      pt.push(samples[rest % m])
      rest = rest / m
    }
    if !vec_approx_eq(cube_eval(a, pt), cube_eval(b, pt)) {
      return false
    }
  }
  true
}

///|
/// Make a point of the full cube out of coordinates on the face `side`:
/// the side's own dimension is fixed to its endpoint.
pub fn nbox_point(
  b : NBox,
  side : NBoxSide,
  coords : Array[Double],
) -> Array[Double] {
  let pt : Array[Double] = []
  for d in 0..<b.dim {
    if d == side.dim {
      pt.push(side.endpoint.to_double())
    } else {
      pt.push(coords[nbox_face_index(side.dim, d)])
    }
  }
  pt
}

///|
/// Well-formedness of an open box: every pair of given faces agrees on
/// their common (n−2)-face.  This is the geometric counterpart of the
/// compatibility predicate on `DSystem`s in the AST (`dsystem_compat.mbt`).
pub fn nbox_wf(b : NBox, samples : Array[Double]) -> Bool {
  // Every face of a dimension must be present exactly once, except the
  // missing one: otherwise `comp` is not determined.
  for d in 0..<b.dim {
    for s in 0..<2 {
      let is_missing = d == b.missing_dim && s == b.missing_endpoint
      if !is_missing && !nbox_is_given(b, d, s) {
        return false
      }
    }
  }
  for i in 0..<b.sides.length() {
    for j in 0..<b.sides.length() {
      let si = b.sides[i]
      let sj = b.sides[j]
      if si.dim != sj.dim {
        let f1 = restrict_face(
          si.face,
          nbox_face_index(si.dim, sj.dim),
          sj.endpoint.to_double(),
        )
        let f2 = restrict_face(
          sj.face,
          nbox_face_index(sj.dim, si.dim),
          si.endpoint.to_double(),
        )
        if !cube_approx_eq(f1, f2, samples) {
          return false
        }
      }
    }
  }
  true
}

///|
/// The Möbius filler: the alternating sum over non-empty sets of given faces.
fn nfill_formula(b : NBox, pt : Array[Double]) -> CVec {
  let n = b.dim
  let k = b.sides.length()
  let masks = int_pow(2, k)
  let mut acc : CVec? = None
  for mask in 1..<masks {
    let fixed : Array[Int32] = []
    for _d in 0..<n {
      fixed.push(-1)
    }
    let mut count = 0
    let mut weight = 1.0
    let mut anchor = -1
    for bit in 0..<k {
      if mask / int_pow(2, bit) % 2 == 1 {
        let s = b.sides[bit]
        count = count + 1
        fixed[s.dim] = s.endpoint
        weight = if s.endpoint == 0 {
          weight * (1.0 - pt[s.dim])
        } else {
          weight * pt[s.dim]
        }
        // The anchor must be the *last* selected side: when both endpoints
        // of a dimension are selected, the later one wins, and evaluating at
        // that side's own plane reproduces the full-cube value there.
        anchor = bit
      }
    }
    let side = b.sides[anchor]
    let coords : Array[Double] = []
    for j in 0..<(n - 1) {
      let d = if j < side.dim { j } else { j + 1 }
      if fixed[d] >= 0 {
        coords.push(fixed[d].to_double())
      } else {
        coords.push(pt[d])
      }
    }
    let value = cube_eval(side.face, coords)
    let sign = if count % 2 == 1 { 1.0 } else { -1.0 }
    let term = vec_scale(sign * weight, value)
    acc = match acc {
      None => Some(term)
      Some(prev) => Some(vec_add(prev, term))
    }
  }
  match acc {
    None => []
    Some(v) => v
  }
}

///|
/// The Kan filler of an n-dimensional open box, in the ambient space.
pub fn nfill(b : NBox) -> Cube {
  Cube::{ dim: b.dim, cell: pt => nfill_formula(b, pt), }
}

///|
/// Composition: the missing face of the filler.  For the square this is the
/// top edge `l(1) ~ r(1)`, i.e. the same path as `kan_comp_path`.
pub fn ncomp(b : NBox) -> Cube {
  restrict_face(nfill(b), b.missing_dim, b.missing_endpoint.to_double())
}

///|
/// Boundary condition of the algorithm: the filler restricts to every given
/// face on the sample grid.
pub fn nfill_respects_box(b : NBox, samples : Array[Double]) -> Bool {
  let m = samples.length()
  for i in 0..<b.sides.length() {
    let side = b.sides[i]
    let total = int_pow(m, b.dim - 1)
    for code in 0..<total {
      let coords : Array[Double] = []
      let mut rest = code
      for _d in 0..<(b.dim - 1) {
        coords.push(samples[rest % m])
        rest = rest / m
      }
      let pt = nbox_point(b, side, coords)
      if !vec_approx_eq(nfill_formula(b, pt), cube_eval(side.face, coords)) {
        return false
      }
    }
  }
  true
}

///|
/// The legacy two-dimensional open box, as an `NBox` missing the top face
/// `j = 1` (dimensions are ordered i, j).
pub fn nbox_of_square(bottom : Cube, left : Cube, right : Cube) -> NBox {
  nbox(2, 1, 1, [
    nbox_side(0, 0, left),
    nbox_side(0, 1, right),
    nbox_side(1, 0, bottom),
  ])
}

///|
/// The Möbius filler and the hand-written square filler agree on every given
/// face of the box (they are two sections of one boundary problem).
pub fn nfill_agrees_with_square_on_given_faces(
  bottom : Cube,
  left : Cube,
  right : Cube,
  samples : Array[Double],
) -> Bool {
  let f = nfill(nbox_of_square(bottom, left, right))
  let g = square_fill(bottom, left, right)
  for s in 0..<samples.length() {
    let t = samples[s]
    if !vec_approx_eq(cube_eval(f, [t, 0.0]), cube_eval(g, [t, 0.0])) {
      return false
    }
    if !vec_approx_eq(cube_eval(f, [0.0, t]), cube_eval(g, [0.0, t])) {
      return false
    }
    if !vec_approx_eq(cube_eval(f, [1.0, t]), cube_eval(g, [1.0, t])) {
      return false
    }
  }
  true
}

///|
/// The two fillers are genuinely different: some interior point separates them.
pub fn nfill_differs_from_square_fill(
  bottom : Cube,
  left : Cube,
  right : Cube,
) -> Bool {
  let f = nfill(nbox_of_square(bottom, left, right))
  let g = square_fill(bottom, left, right)
  !vec_approx_eq(cube_eval(f, [0.25, 0.25]), cube_eval(g, [0.25, 0.25]))
}

///|
/// ... but their composites are paths with the same endpoints, as they must
/// be: comp has a fixed boundary (l(1) → r(1)) whatever the filler.
pub fn ncomp_endpoints_match_legacy_comp(
  bottom : Cube,
  left : Cube,
  right : Cube,
) -> Bool {
  let a = ncomp(nbox_of_square(bottom, left, right))
  let b = kan_comp_path(bottom, left, right)
  vec_approx_eq(path_start(a), path_start(b)) &&
  vec_approx_eq(path_end(a), path_end(b))
}

///|
/// Number of summands in the Möbius filler of an n-box: 2^(2n−1) − 1.
pub fn nfill_term_count(dim : Int32) -> Int32 {
  int_pow(2, 2 * dim - 1) - 1
}

///|
/// Budgeted decision: can an n-dimensional fill be run inside `budget`
///  terms?  (`comp` at dimension 2 costs 7, dimension 3 costs 31,
/// dimension 4 costs 127 — a factor 4 per dimension.)
pub fn nfill_within_budget(dim : Int32, budget : Int32) -> Bool {
  dim >= 1 && nfill_term_count(dim) <= budget
}

///|
/// Rename dimensions: `perm[old] = new`.
pub fn cube_permute(c : Cube, perm : Array[Int32]) -> Cube {
  Cube::{
    dim: c.dim,
    cell: y => {
      let x : Array[Double] = []
      for d in 0..<c.dim {
        x.push(y[perm[d]])
      }
      cube_eval(c, x)
    },
  }
}

///|
/// Relabel the dimensions of an open box along a permutation (the faces are
/// re-sorted into increasing coordinate order).
pub fn nbox_permute(b : NBox, perm : Array[Int32]) -> NBox {
  let sides : Array[NBoxSide] = []
  for i in 0..<b.sides.length() {
    let s = b.sides[i]
    // Old global dimensions of this face, in increasing old order.
    let olds : Array[Int32] = []
    for d in 0..<b.dim {
      if d != s.dim {
        olds.push(d)
      }
    }
    // Rank of each face coordinate in the new dimension order.
    let face_perm : Array[Int32] = []
    for j in 0..<olds.length() {
      let mut rank = 0
      for k in 0..<olds.length() {
        if perm[olds[k]] < perm[olds[j]] {
          rank = rank + 1
        }
      }
      face_perm.push(rank)
    }
    sides.push(NBoxSide::{
      dim: perm[s.dim],
      endpoint: s.endpoint,
      face: cube_permute(s.face, face_perm),
    })
  }
  nbox(b.dim, perm[b.missing_dim], b.missing_endpoint, sides)
}

///|
/// Coherence: filling commutes with relabelling of the dimensions.
pub fn nfill_permutation_natural(
  b : NBox,
  perm : Array[Int32],
  samples : Array[Double],
) -> Bool {
  cube_approx_eq(
    nfill(nbox_permute(b, perm)),
    cube_permute(nfill(b), perm),
    samples,
  )
}
