///|
// Differential validation for ptrunc.mbt / the `dhit_face_var` schema
// extension in schema.mbt (SPEC §四 item 3's propositional-truncation
// gap): the generic HIT well-formedness check accepts `Squash`'s
// self-variable faces, and the generic HIT cell smart constructor reduces
// `squash x y` to `x`/`y` at the two endpoints via that new face kind.
//
// `DValue` has no `Eq` impl (semantic values are compared up to
// conversion, not structurally), so every comparison below goes through
// `conv_at`/`conv_hit_cell_at` at the `Squash Bool` type, matching the
// convention the rest of the schema layer's tests use.

///|
fn squash_bool_conv(a : DValue, b : DValue) -> Bool {
  conv_at(10000, 10000, squash_type_value(DVBoolTy), a, b)
}

///|
test "Squash schema is well-formed under the generic HIT validator" {
  assert_true(hit_schema_validate(squash_schema()))
  assert_true(ptrunc_schema("Squash") is Some(_))
  // An empty name is rejected before validation is even attempted.
  assert_true(ptrunc_schema("") is None)
}

///|
test "squash's two faces reduce, at their respective endpoints, to its own two arguments" {
  let x = squash_point_value(DVBoolTy, DVBool(true))
  let y = squash_point_value(DVBoolTy, DVBool(false))
  // dhit_face_var(0, 2) fires at dim = 0: squash x y @0 ≡ x.
  assert_true(squash_bool_conv(squash_path_value(DVBoolTy, x, y, DZero), x))
  // dhit_face_var(1, 2) fires at dim = 1: squash x y @1 ≡ y.
  assert_true(squash_bool_conv(squash_path_value(DVBoolTy, x, y, DOne), y))
  // At a free dimension variable neither face fires: the cell stays a
  // genuine (unreduced) higher cell, not accidentally collapsed to x or y.
  let open_path = squash_path_value(DVBoolTy, x, y, DVar(0))
  assert_true(!squash_bool_conv(open_path, x))
  assert_true(!squash_bool_conv(open_path, y))
  match open_path {
    DVHitCell(spec, cell, _, args, dims) => {
      assert_true(spec == squash_schema())
      assert_true(cell == 1)
      assert_true(args.length() == 2)
      assert_true(squash_bool_conv(args[0], x))
      assert_true(squash_bool_conv(args[1], y))
      assert_true(dims.length() == 1 && dims[0] == DVar(0))
    }
    _ => assert_true(false)
  }
}

///|
test "squash is symmetric in its arguments: swapping x and y swaps the two endpoints" {
  let x = squash_point_value(DVBoolTy, DVBool(true))
  let y = squash_point_value(DVBoolTy, DVBool(false))
  // squash y x @0 ≡ y, squash y x @1 ≡ x — dhit_face_var(0,2)/(1,2) always
  // pick out *this call's* first/second argument, not a fixed identity.
  assert_true(squash_bool_conv(squash_path_value(DVBoolTy, y, x, DZero), y))
  assert_true(squash_bool_conv(squash_path_value(DVBoolTy, y, x, DOne), x))
}

///|
test "squash between a point and itself is the constant path at both ends" {
  let p = squash_point_value(DVBoolTy, DVBool(true))
  assert_true(squash_bool_conv(squash_path_value(DVBoolTy, p, p, DZero), p))
  assert_true(squash_bool_conv(squash_path_value(DVBoolTy, p, p, DOne), p))
}

///|
test "the propositional-truncation type is well-typed as the generic HIT semantic type" {
  let ty = squash_type_value(DVBoolTy)
  match ty {
    DVHitType(spec, params, indices) => {
      assert_true(spec == squash_schema())
      assert_true(params.length() == 1)
      assert_true(indices.length() == 0)
    }
    _ => assert_true(false)
  }
  // The type former itself type-checks as a Type0, concretely at A := Bool.
  match
    d_check(
      squash_type_term(),
      DVUniv(0),
      schema_env([DVUniv(0)]),
      schema_env([DVBoolTy]),
      schema_dim_env([]),
    ) {
    Some(_) => ()
    None => assert_true(false)
  }
  // Two different points are not convertible; a point is convertible with
  // itself — the generic HIT conversion check applies to Squash cells
  // exactly as it does to any other generic HIT's cells.
  let x = squash_point_value(DVBoolTy, DVBool(true))
  let y = squash_point_value(DVBoolTy, DVBool(false))
  assert_true(conv_hit_cell_at(10000, 10000, squash_schema(), [DVBoolTy], x, x))
  assert_true(
    !conv_hit_cell_at(10000, 10000, squash_schema(), [DVBoolTy], x, y),
  )
}
