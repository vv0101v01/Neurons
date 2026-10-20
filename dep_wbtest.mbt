///|
test "dependent NbE: universes, Pi, Sigma, dependent substitution, eta" {
  assert_true(check_dep_universe())
  assert_true(check_dep_pi())
  assert_true(check_dep_sigma())
  assert_true(check_dep_all())
}

///|
test "Kan coe/comp for Pi, Sigma, Universe and all embedded types" {
  assert_true(check_kan_coe_pi_sigma())
  assert_true(check_kan_coe_dependent())
  assert_true(check_kan_comp_tube())
  assert_true(check_kan_embeddings())
  assert_true(check_kan_all_types())
}

///|
test "symbolic spectral algebra and affine filler identities" {
  assert_true(check_spectral_identities())
  assert_true(check_spectral_matrices())
  assert_true(check_symbolic_affine_filler())
  assert_true(check_symbolic_nonlinear_boundary())
  assert_true(check_symbolic_pruning())
  assert_true(check_symbolic_algebra_all())
}
