///|
// Differential validation for qpoly_univalence.mbt: univalence's
// machinery (FinMap/fin_map_is_equiv/cpath_ua/cpath_coe) applied to real
// qpoly/qmat data, checked exhaustively against an injectivity oracle.

///|
fn is_permutation_oracle(table : Array[Int32], n : Int32) -> Bool {
  if table.length() != n {
    return false
  }
  let seen : Array[Bool] = []
  for _i in 0..<n {
    seen.push(false)
  }
  for i in 0..<table.length() {
    let j = table[i]
    if j < 0 || j >= n || seen[j] {
      return false
    }
    seen[j] = true
  }
  true
}

///|
fn quadratic_with_four_roots() -> QPoly {
  // (x-1)(x-2)(x-3)(x-4), four distinct rational roots.
  let f1 = qpoly_root_factor(rat_make(1, 1))
  let f2 = qpoly_root_factor(rat_make(2, 1))
  let f3 = qpoly_root_factor(rat_make(3, 1))
  let f4 = qpoly_root_factor(rat_make(4, 1))
  qpoly_mul(qpoly_mul(f1, f2), qpoly_mul(f3, f4))
}

///|
test "all_permutations enumerates exactly n! distinct permutations, each genuinely a permutation" {
  for n in [1, 2, 3, 4] {
    let perms = all_permutations(n)
    inspect(
      bignat_to_string(bignat_of_int(perms.length())) ==
      bignat_to_string(fact(n)),
      content="true",
    )
    for k in 0..<perms.length() {
      assert_true(is_permutation_oracle(perms[k], n))
    }
    // No duplicate permutations.
    for a in 0..<perms.length() {
      for b in (a + 1)..<perms.length() {
        assert_true(perms[a] != perms[b])
      }
    }
  }
}

///|
test "qpoly root permutations: univalence decides every S4 relabelling of 4 real rational roots" {
  let p = quadratic_with_four_roots()
  let roots = qpoly_rational_roots(p)
  assert_true(roots.length() == 4)
  assert_true(qpoly_all_root_permutations_are_equivalences(p))
  // Spot-check one non-trivial permutation end to end: equivalence,
  // ua-path, and transport computing the expected index both ways.
  let table = [1, 2, 3, 0]
  assert_true(qpoly_root_permutation_is_equiv(p, table))
  match qpoly_root_permutation_ua(p, table) {
    None => assert_true(false)
    Some(path) => {
      for i in 0..<4 {
        assert_true(cpath_coe_index(path, 0, 1, i) == table[i])
      }
      // Forth-and-back is the identity (section/retraction, concretely
      // on this polynomial's root indices).
      for i in 0..<4 {
        assert_true(
          cpath_coe_index(path, 1, 0, cpath_coe_index(path, 0, 1, i)) == i,
        )
      }
    }
  }
}

///|
test "qpoly root permutations: a non-injective relabelling is rejected, not vacuously accepted" {
  let p = quadratic_with_four_roots()
  let bad = [0, 0, 2, 3] // collapses indices 0 and 1
  assert_true(!qpoly_root_permutation_is_equiv(p, bad))
  assert_true(qpoly_root_permutation_ua(p, bad) is None)
  // A well-formed but wrong-length table is likewise rejected (FinMap's
  // own well-formedness check), not treated as a partial match.
  let short = [0, 1, 2]
  assert_true(!qpoly_root_permutation_is_equiv(p, short))
}

///|
test "qpoly roots: no rational roots is reported distinctly from a rejected permutation" {
  // x^2 + 1 has no rational (indeed no real) roots.
  let p = qpoly_add(qpoly_mul(qpoly_x(), qpoly_x()), qpoly_one())
  assert_true(qpoly_rational_roots(p).length() == 0)
  assert_true(qpoly_roots_ty(p) is None)
  assert_true(!qpoly_root_permutation_is_equiv(p, []))
  assert_true(qpoly_root_permutation_ua(p, []) is None)
}

///|
test "qmat eigenvalue permutations: univalence decides relabellings of a diagonal matrix's rational spectrum" {
  // diag(1,2,3): characteristic polynomial (x-1)(x-2)(x-3), three
  // distinct rational eigenvalues, found via the *same* qpoly machinery
  // that drives qpoly_root_permutation_equiv.
  let a = qmat_from_int_rows([[1, 0, 0], [0, 2, 0], [0, 0, 3]])
  let cp = qmat_charpoly(a)
  let roots = qpoly_rational_roots(cp)
  assert_true(roots.length() == 3)
  // Every permutation of the three eigenvalues is a genuine equivalence,
  // each with a computable ua-path.
  for k in 0..<all_permutations(3).length() {
    let table = all_permutations(3)[k]
    assert_true(qmat_eigenvalue_permutation_is_equiv(a, table))
    assert_true(qmat_eigenvalue_permutation_ua(a, table) is Some(_))
  }
  // A collapsing (non-injective) relabelling is still rejected at this
  // level too.
  assert_true(!qmat_eigenvalue_permutation_is_equiv(a, [0, 0, 2]))
  assert_true(qmat_eigenvalue_permutation_ua(a, [0, 0, 2]) is None)
}
