///|
test "general Glue comp (finite lines + eigenspace lines)" {
  assert_true(check_glue_comp_finite())
  assert_true(check_glue_comp_vec())
  assert_true(check_glue_comp_all())
}

///|
test "categorifications (Karoubi, face poset, cube category, syntactic CCC)" {
  assert_true(check_karoubi_category())
  assert_true(check_face_poset_category())
  assert_true(check_syntactic_category())
  assert_true(check_categories_all())
}
