///|
test "hermitian idempotent projector" {
  assert_true(check_projector())
  assert_true(check_eigenspace())
  assert_true(check_commuting())
}

///|
test "interval, faces, systems modulo quotient" {
  assert_true(check_interval_faces())
  assert_true(check_systems())
}

///|
test "cubes, Kan comp, eigenspace pruning" {
  assert_true(check_cube_comp())
  assert_true(check_kan_pruning())
}

///|
test "NbE single-valuedness and definitional coe" {
  assert_true(check_nbe())
  assert_true(check_coe_definitional())
  assert_true(check_hoas())
}

///|
test "ua, PathP exchange, Glue, J" {
  assert_true(check_ua_coe())
  assert_true(check_pathp_exchange())
  assert_true(check_glue())
  assert_true(check_j())
}

///|
test "computable univalence and the n-dimensional cube algorithm" {
  assert_true(univalence_compute_all())
  assert_true(check_cube_algorithm())
}

///|
test "decoupling surgery is certified by univalence" {
  assert_true(refactor_certificates_sound())
}

///|
test "orthogonal round-trip and full registry" {
  assert_true(check_orthogonal_roundtrip())
  assert_true(all_checks_pass())
  assert_eq(run_all_checks().length(), 43)
}

///|
test "spot values" {
  // coe along ua(swap) is swap, definitionally and semantically.
  assert_true(
    nf(TmApp(TmCoeUaSwap, TmPair(TmBool(true), TmUnit)), 0) ==
    TmPair(TmUnit, TmBool(true)),
  )
  assert_true(
    coe_upath(
      iso_to_path(iso_swap(TyBool, TyUnit)),
      0,
      1,
      PVPair(PVBool(true), PVUnit),
    ) ==
    PVPair(PVUnit, PVBool(true)),
  )
  // Pruning a vector lands in the eigenspace, orthogonally to its kernel part.
  let p = example_projector()
  let (v1, v0) = decompose(p, [cx_real(1.0), cx_real(2.0), cx_real(3.0)])
  assert_true(in_image(p, v1))
  assert_true(in_kernel(p, v0))
  assert_true(vec_orthogonal(v1, v0))
}
