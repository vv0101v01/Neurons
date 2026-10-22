///|
// Connects the computable-univalence layer (`univalence_compute.mbt`'s
// `FinMap`/`CPath`) to the exact-algebra layer (`qpoly.mbt`'s `QPoly`,
// `qmat.mbt`'s `QMat`): a polynomial's *rational* root array (likewise a
// matrix's rational eigenvalues, found through its characteristic
// polynomial) is a concrete finite set, and univalence's machinery
// genuinely applies to it — any permutation of that finite set is a
// witnessed equivalence (`fin_map_is_equiv`), with a computable ua-path
// (`cpath_ua`) and transport (`cpath_coe`) through it, while a
// non-injective relabelling is correctly rejected rather than vacuously
// accepted.  SPEC §四 item 9 ("wire BigRat/the computable-univalence
// result onto qpoly/qmat"): the user clarified the actual requirement is
// this connection — univalence's decision procedures must be *usable on*
// qpoly/qmat's own data — not a change of qpoly/qmat's internal Rat/BigRat
// representation (which the user explicitly said does not matter here).

///|
/// The finite type indexing a polynomial's known rational roots, or
/// `None` if `qpoly_rational_roots` found none (`fin_ty` needs `n >= 1`).
pub fn qpoly_roots_ty(p : QPoly) -> Ty? {
  let n = qpoly_rational_roots(p).length()
  if n == 0 {
    None
  } else {
    Some(fin_ty(n))
  }
}

///|
/// A candidate relabelling of `p`'s rational roots (an `Array[Int32]`
/// indexed the same way as `qpoly_rational_roots(p)`) as a `FinMap` on
/// the finite type `qpoly_roots_ty(p)`.  `None` when `p` has no known
/// rational roots; well-formedness (and hence whether it is actually an
/// equivalence) is left to `fin_map_wf`/`fin_map_is_equiv`, not decided
/// here.
pub fn qpoly_root_permutation_equiv(p : QPoly, table : Array[Int32]) -> FinMap? {
  match qpoly_roots_ty(p) {
    None => None
    Some(ty) => Some(FinMap::{ src: ty, dst: ty, table, })
  }
}

///|
/// Whether `table` is a genuine self-equivalence of `p`'s rational root
/// set (an injective — hence, same-cardinality — relabelling); `false`
/// both when `p` has no rational roots and when `table` is not injective
/// or malformed.
pub fn qpoly_root_permutation_is_equiv(p : QPoly, table : Array[Int32]) -> Bool {
  match qpoly_root_permutation_equiv(p, table) {
    None => false
    Some(fm) => fin_map_is_equiv(fm)
  }
}

///|
/// `ua` applied to a root-set permutation: `Some` exactly when `table` is
/// a genuine equivalence, giving a computable path (`CPath`) whose
/// `cpath_coe` transports root-indices of `p` according to `table` (and
/// its inverse in the other direction) — SPEC §四 item 9's univalence
/// machinery made to act on concrete qpoly data, not merely on abstract
/// `Ty`.
pub fn qpoly_root_permutation_ua(p : QPoly, table : Array[Int32]) -> CPath? {
  match qpoly_root_permutation_equiv(p, table) {
    None => None
    Some(fm) => if fin_map_is_equiv(fm) { Some(cpath_ua(fm)) } else { None }
  }
}

///|
/// The same construction one level up: `a`'s *rational* eigenvalues are
/// exactly the rational roots of its characteristic polynomial
/// (`qmat_charpoly`), so a permutation of them is decided by the same
/// machinery as `qpoly_root_permutation_equiv` — this is what actually
/// wires `QMat` into the computable-univalence layer (rather than
/// `qmat.mbt`'s own Rat-vs-BigRat representation, which is orthogonal).
pub fn qmat_eigenvalue_permutation_equiv(
  a : QMat,
  table : Array[Int32],
) -> FinMap? {
  qpoly_root_permutation_equiv(qmat_charpoly(a), table)
}

///|
pub fn qmat_eigenvalue_permutation_is_equiv(
  a : QMat,
  table : Array[Int32],
) -> Bool {
  qpoly_root_permutation_is_equiv(qmat_charpoly(a), table)
}

///|
pub fn qmat_eigenvalue_permutation_ua(a : QMat, table : Array[Int32]) -> CPath? {
  qpoly_root_permutation_ua(qmat_charpoly(a), table)
}

///|
/// All `n!` permutations of `0 .. n`, as index tables.  Meant for small
/// `n` (the degree of a polynomial with that many known rational roots);
/// this is a plain enumeration, not a search, so it is only ever called
/// here on root/eigenvalue counts that are small in practice.
pub fn all_permutations(n : Int32) -> Array[Array[Int32]] {
  if n <= 0 {
    return [[]]
  }
  let out : Array[Array[Int32]] = []
  let used : Array[Bool] = []
  for _i in 0..<n {
    used.push(false)
  }
  let current : Array[Int32] = []
  fn go() -> Unit {
    if current.length() == n {
      out.push(current.copy())
      return
    }
    for i in 0..<n {
      if !used[i] {
        used[i] = true
        current.push(i)
        go()
        ignore(current.pop())
        used[i] = false
      }
    }
  }

  go()
  out
}

///|
/// The theorem this file exists to demonstrate: *every* permutation of a
/// polynomial's rational root set is a univalence-witnessed equivalence
/// (the full symmetric group acts on the root set, and `ua` turns each
/// member into a genuine path) — checked exhaustively, not sampled.
/// `false` only when `p` has no rational roots (vacuously nothing to
/// permute) so callers can tell "no roots" from "a genuine failure".
pub fn qpoly_all_root_permutations_are_equivalences(p : QPoly) -> Bool {
  match qpoly_roots_ty(p) {
    None => false
    Some(ty) => {
      let n = ty_card(ty)
      let perms = all_permutations(n)
      for k in 0..<perms.length() {
        if !qpoly_root_permutation_is_equiv(p, perms[k]) {
          return false
        }
        match qpoly_root_permutation_ua(p, perms[k]) {
          None => return false
          Some(_) => ()
        }
      }
      true
    }
  }
}
