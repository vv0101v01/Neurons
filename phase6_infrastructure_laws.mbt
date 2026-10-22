///|
fn check_checked_lines() -> Bool {
  let invalid = match checked_type_line_closed(DBoolLit(true)) {
    Some(_) => false
    None => true
  }
  let constant_ok = match checked_constant_type_line_closed(DBoolTy) {
    Some(line) => {
      let (a, b) = checked_line_endpoints(line)
      checked_line_is_constant(line) &&
      conv_ty(0, 0, a, DVBoolTy) &&
      conv_ty(0, 0, b, DVBoolTy) &&
      equiv_bool_is(checked_coe_value(line, DZero, DOne, DVBool(true), 0), true)
    }
    None => false
  }
  let ua_ok = match
    checked_ua_line(
      bool_not_equiv_term(),
      denv_empty(),
      denv_empty(),
      ddim_empty(),
    ) {
    Some(line) => {
      let (a, b) = checked_line_endpoints(line)
      conv_ty(0, 0, a, DVBoolTy) &&
      conv_ty(0, 0, b, DVBoolTy) &&
      equiv_bool_is(
        checked_coe_value(line, DZero, DOne, DVBool(true), 0),
        false,
      ) &&
      equiv_bool_is(
        checked_coe_value(line, DOne, DZero, DVBool(true), 0),
        false,
      ) &&
      checked_line_quote_body(0, 0, line) ==
      quote_ty(0, 1, checked_line_at(line, DVar(0)))
    }
    None => false
  }
  let reify_ok = match
    d_infer(bool_not_equiv_term(), denv_empty(), denv_empty(), ddim_empty()) {
    Some(ev) =>
      match
        checked_line_reify_closed(
          ua_line_value(ev.value, DVBoolTy, DVBoolTy, 0),
        ) {
        Some(line) =>
          equiv_bool_is(
            checked_coe_value(line, DZero, DOne, DVBool(true), 0),
            false,
          )
        None => false
      }
    None => false
  }
  // A host line which inspects whether its dimension is a variable
  // is not a substitutable type line and is rejected by reification.
  let non_natural = (d : Dim) => {
    match d {
      DVar(_) => DVBoolTy
      _ => DVUnitTy
    }
  }
  let rejected = match checked_line_reify_closed(non_natural) {
    Some(_) => false
    None => true
  }
  // `checked_line_of_pathp_term` on a constant `DPath` matches the
  // `DPath` branch and agrees with `checked_constant_type_line`
  // directly; on a (here, trivially non-dependent) `DPathP` it matches
  // the `DPathP` branch via `checked_type_line`; on a non-Path term it
  // is `None`.
  let pathp_of_dpath_ok = match
    checked_line_of_pathp_term(
      DPath(DBoolTy, DBoolLit(true), DBoolLit(false)),
      denv_empty(),
      denv_empty(),
      ddim_empty(),
    ) {
    Some(line) => {
      let (a, b) = checked_line_endpoints(line)
      checked_line_is_constant(line) &&
      conv_ty(0, 0, a, DVBoolTy) &&
      conv_ty(0, 0, b, DVBoolTy)
    }
    None => false
  }
  let pathp_of_dpathp_ok = match
    checked_line_of_pathp_term(
      DPathP(DBoolTy, DBoolLit(true), DBoolLit(false)),
      denv_empty(),
      denv_empty(),
      ddim_empty(),
    ) {
    Some(line) => {
      let (a, b) = checked_line_endpoints(line)
      conv_ty(0, 0, a, DVBoolTy) && conv_ty(0, 0, b, DVBoolTy)
    }
    None => false
  }
  let pathp_of_non_path_rejected = match
    checked_line_of_pathp_term(
      DBoolLit(true),
      denv_empty(),
      denv_empty(),
      ddim_empty(),
    ) {
    Some(_) => false
    None => true
  }
  // `checked_line_conv`: a line is convertible with itself, and the
  // constant-`Bool` line is not convertible with the constant-`Unit`
  // line.
  let conv_lines_ok = match
    (
      checked_constant_type_line_closed(DBoolTy),
      checked_constant_type_line_closed(DUnitTy),
    ) {
    (Some(bool_line), Some(unit_line)) =>
      checked_line_conv(0, 0, bool_line, bool_line) &&
      checked_line_conv(0, 0, unit_line, unit_line) &&
      !checked_line_conv(0, 0, bool_line, unit_line)
    _ => false
  }
  // `checked_pathp_type`: the PathP type built over a checked line
  // agrees, endpoint for endpoint, with one built directly from the
  // line's own semantic function.
  let pathp_type_ok = match checked_constant_type_line_closed(DBoolTy) {
    Some(line) =>
      match checked_pathp_type(line, DVBool(true), DVBool(false)) {
        DVPathTy(line_fn, l, r) =>
          conv_ty(0, 0, line_fn(DZero), checked_line_at(line, DZero)) &&
          conv_ty(0, 0, line_fn(DOne), checked_line_at(line, DOne)) &&
          equiv_bool_is(l, true) &&
          equiv_bool_is(r, false)
        _ => false
      }
    None => false
  }
  invalid &&
  constant_ok &&
  ua_ok &&
  reify_ok &&
  rejected &&
  pathp_of_dpath_ok &&
  pathp_of_dpathp_ok &&
  pathp_of_non_path_rejected &&
  conv_lines_ok &&
  pathp_type_ok
}

///|
fn check_schema_registry() -> Bool {
  let registry = schema_registry_new()
  let spec = vec_schema()
  let first = schema_registry_register_inductive(registry, spec)
  let second = schema_registry_register_inductive(registry, vec_schema())
  let hit = schema_registry_register_hit(registry, circle_schema())
  let by_name = match schema_registry_inductive_by_name(registry, spec.name) {
    Some(plan) => plan.id == first.id
    None => false
  }
  let by_id = match schema_registry_hit_by_id(registry, hit.id) {
    Some(plan) => plan.spec == circle_schema()
    None => false
  }
  let params = inductive_param_types_cached(registry, spec, [DVBoolTy])
  let params2 = inductive_param_types_cached(registry, spec, [DVBoolTy])
  let indices = inductive_index_types_cached(registry, spec, [DVBoolTy], [
    DVZeroNat,
  ])
  let telescope = [
    dtelescope_entry("A", DUniv(0)),
    dtelescope_entry("x", DTVar(0)),
  ]
  let types = telescope_type_values_cached(registry, telescope, [], [], [
    DVBoolTy,
    DVBool(true),
  ])
  let types2 = telescope_type_values_cached(registry, telescope, [], [], [
    DVBoolTy,
    DVBool(true),
  ])
  first.valid &&
  second.id == first.id &&
  hit.valid &&
  by_name &&
  by_id &&
  registry.validation_misses == 2 &&
  registry.validation_hits == 1 &&
  registry.telescope_hits >= 2 &&
  registry.telescope_misses >= 2 &&
  params.length() == 1 &&
  conv_ty(0, 0, params[0], DVUniv(0)) &&
  conv_ty(0, 0, params2[0], DVUniv(0)) &&
  indices.length() == 1 &&
  conv_ty(0, 0, indices[0], DVNatTy) &&
  types.length() == 2 &&
  conv_ty(0, 0, types[1], DVBoolTy) &&
  conv_ty(0, 0, types2[1], DVBoolTy) &&
  inductive_plan_type_term(first, [DBoolTy, DNatZero]) ==
  DInductive(spec, [DBoolTy, DNatZero])
}

///|
pub fn check_phase6_infrastructure() -> Bool {
  check_checked_lines() && check_schema_registry()
}
