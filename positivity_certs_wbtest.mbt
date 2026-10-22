///|
// Whitebox tests for the variance-certificate registry: positivity of
// operator-style parameter uses (c) and certified neutral type-operator
// applications (e) (SPEC §四 item 1 (c)+(e)).

///|
fn positivity_probe_family() -> DTerm {
  DInductive(dinductive_spec("ProbeS", 0, [], [], []), [])
}

///|
fn wrap_operator_spec() -> DInductiveSpec {
  // WrapU : (F : Type -> Type) -> Type with mk : F Nat -> WrapU F.
  // The parameter F is used only as an applied type operator.
  let params = [dtelescope_entry("F", DPi(DUniv(0), DUniv(0)))]
  dinductive_spec("WrapU", 0, params, [], [
    dconstructor_spec("mk", [darg_external("x", DApp(DTVar(0), DNatTy))]),
  ])
}

///|
fn certs_with(variance : DVariance) -> DPositivityCerts {
  dpositivity_certs_add(
    dpositivity_certs_empty(),
    dpositivity_cert("F", [variance]),
  )
}

///|
test "positivity certs (c): operator-style parameter uses certify strictly positive" {
  // Before the operator-spine rule, the applied probe was an unknown
  // occurrence and the parameter certificate stayed conservative.
  let r = inductive_parameter_positivity(wrap_operator_spec(), 0)
  inspect(r.occurs, content="true")
  inspect(r.strictly_positive, content="true")
  inspect(r.unknown, content="false")
  // The certificate now recognises indirect uses through the family:
  // WrapU ProbeS mentions ProbeS strictly positively.
  let applied = DInductive(wrap_operator_spec(), [positivity_probe_family()])
  let r2 = dterm_family_positivity(applied, "ProbeS")
  inspect(r2.occurs, content="true")
  inspect(r2.strictly_positive, content="true")
  inspect(r2.unknown, content="false")
  // A multi-argument transparent alias also reduces now.
  let alias_app = DApp(
    DApp(DLam(DUnitTy, DLam(DUnitTy, positivity_probe_family())), DUnitLit),
    DUnitLit,
  )
  inspect(
    dterm_family_positivity(alias_app, "ProbeS").strictly_positive,
    content="true",
  )
}

///|
test "positivity certs (e): registered neutral operators judged by variance" {
  let op = DApp(DTVar(0), positivity_probe_family()) // F ProbeS
  // Strict certificate: occurrences keep polarity and strictness.
  let r = dterm_family_positivity_with(
    op,
    "ProbeS",
    ["F"],
    certs_with(VarianceStrict),
  )
  inspect(r.occurs, content="true")
  inspect(r.strictly_positive, content="true")
  inspect(r.unknown, content="false")
  // No certificate: the conservative unknown verdict remains.
  let r0 = dterm_family_positivity_with(
    op,
    "ProbeS",
    ["F"],
    dpositivity_certs_empty(),
  )
  inspect(r0.occurs, content="true")
  inspect(r0.unknown, content="true")
  inspect(r0.strictly_positive, content="false")
  // Positive certificate: polarity kept, strictness lost.
  let rp = dterm_family_positivity_with(
    op,
    "ProbeS",
    ["F"],
    certs_with(VariancePositive),
  )
  inspect(rp.occurs, content="true")
  inspect(rp.strictly_positive, content="false")
  inspect(rp.positive_polarity, content="true")
  inspect(rp.unknown, content="false")
  // Negative certificate: polarity flipped, strictness lost.
  let rn = dterm_family_positivity_with(
    op,
    "ProbeS",
    ["F"],
    certs_with(VarianceNegative),
  )
  inspect(rn.occurs, content="true")
  inspect(rn.strictly_positive, content="false")
  inspect(rn.negative_polarity, content="true")
  inspect(rn.unknown, content="false")
}

///|
test "positivity certs: multi-position variances, binder depth, arity overflow" {
  let probe = positivity_probe_family()
  // F a b with per-position variances [strict, negative].
  let certs2 = dpositivity_certs_add(
    dpositivity_certs_empty(),
    dpositivity_cert("F", [VarianceStrict, VarianceNegative]),
  )
  let op2 = DApp(DApp(DTVar(0), probe), probe)
  let r = dterm_family_positivity_with(op2, "ProbeS", ["F"], certs2)
  inspect(r.occurs, content="true")
  inspect(r.positive_polarity, content="true")
  inspect(r.negative_polarity, content="true")
  inspect(r.strictly_positive, content="false")
  inspect(r.unknown, content="false")
  // Under a binder the telescope indices shift: DTVar(1) is still F.
  let under = DPi(DUnitTy, DApp(DTVar(1), probe))
  let r3 = dterm_family_positivity_with(
    under,
    "ProbeS",
    ["F"],
    certs_with(VarianceStrict),
  )
  inspect(r3.occurs, content="true")
  inspect(r3.strictly_positive, content="true")
  // DTVar(0) under the binder is the anonymous Pi bound variable.
  let wrong = DPi(DUnitTy, DApp(DTVar(0), probe))
  inspect(
    dterm_family_positivity_with(
      wrong,
      "ProbeS",
      ["F"],
      certs_with(VarianceStrict),
    ).unknown,
    content="true",
  )
  // More arguments than certified positions: conservative.
  let over = DApp(DApp(DTVar(0), probe), probe)
  inspect(
    dterm_family_positivity_with(
      over,
      "ProbeS",
      ["F"],
      certs_with(VarianceStrict),
    ).unknown,
    content="true",
  )
  // An unregistered operator stays conservative even under a registry.
  let other = DApp(DTVar(0), probe)
  inspect(
    dterm_family_positivity_with(
      other,
      "ProbeS",
      ["G"],
      certs_with(VarianceStrict),
    ).unknown,
    content="true",
  )
}

///|
test "positivity certs: registry add/replace/lookup" {
  let base = certs_with(VarianceStrict)
  inspect(dpositivity_certs_size(base), content="1")
  inspect(dpositivity_certs_size(dpositivity_certs_empty()), content="0")
  let replaced = dpositivity_certs_add(
    base,
    dpositivity_cert("F", [VarianceNegative]),
  )
  inspect(dpositivity_certs_size(replaced), content="1")
  inspect(dpositivity_certs_size(base), content="1")
  match dpositivity_certs_lookup(replaced, "F") {
    Some(c) => {
      inspect(c.variances.length(), content="1")
      inspect(c.variances[0] == VarianceNegative, content="true")
    }
    None => inspect(false, content="true")
  }
  inspect(dpositivity_certs_lookup(replaced, "G") is None, content="true")
  inspect(dpositivity_certs_lookup(replaced, "") is None, content="true")
  inspect(base == base, content="true")
  inspect(base == replaced, content="false")
  // Preset single-position certificates agree with the general form.
  inspect(
    dpositivity_cert_strict("F") == dpositivity_cert("F", [VarianceStrict]),
    content="true",
  )
  inspect(
    dpositivity_cert_positive("F") == dpositivity_cert("F", [VariancePositive]),
    content="true",
  )
  inspect(
    dpositivity_cert_negative("F") == dpositivity_cert("F", [VarianceNegative]),
    content="true",
  )
  inspect(
    dpositivity_cert_strict("F") == dpositivity_cert_negative("F"),
    content="false",
  )
}

///|
test "positivity certs (e): certified validation replaces the unknown rejection" {
  // NeuU : (F : Type -> Type) -> Type with mk : F (NeuU°) -> NeuU F,
  // where the occurrence marker NeuU° recognises the family by name.
  let params = [dtelescope_entry("F", DPi(DUniv(0), DUniv(0)))]
  let arg_ty = DApp(
    DTVar(0),
    DInductive(dinductive_spec("NeuU", 0, [], [], []), []),
  )
  let spec = dinductive_spec("NeuU", 0, params, [], [
    dconstructor_spec("mk", [darg_external("x", arg_ty)]),
  ])
  // Under a strict certificate every occurrence is strictly positive:
  // accepted.
  inspect(
    inductive_schema_validate_with_certs(spec, certs_with(VarianceStrict)),
    content="true",
  )
  // The conservative default still rejects any occurrence.
  inspect(inductive_schema_validate(spec), content="false")
  // Negative and merely positive certificates are rejected.
  inspect(
    inductive_schema_validate_with_certs(spec, certs_with(VarianceNegative)),
    content="false",
  )
  inspect(
    inductive_schema_validate_with_certs(spec, certs_with(VariancePositive)),
    content="false",
  )
  // The cache key includes the certificates: results round-trip without
  // cross-contamination.
  inspect(
    inductive_schema_validate_with_certs(spec, certs_with(VarianceStrict)),
    content="true",
  )
  inspect(
    inductive_schema_validate_with_certs(spec, certs_with(VarianceNegative)),
    content="false",
  )
  // Function domains stay occurrence-free even under strict
  // certificates (they are negative positions).
  let fn_params = [dtelescope_entry("F", DPi(DUniv(0), DUniv(0)))]
  let fn_arg_ty = DApp(
    DTVar(0),
    DInductive(dinductive_spec("NeuG", 0, [], [], []), []),
  )
  let fn_spec = dinductive_spec("NeuG", 0, fn_params, [], [
    dconstructor_spec("mk", [darg_function("f", fn_arg_ty, index=[])]),
  ])
  inspect(
    inductive_schema_validate_with_certs(fn_spec, certs_with(VarianceStrict)),
    content="false",
  )
  // An empty registry agrees exactly with the default entry.
  inspect(
    inductive_schema_validate_with_certs(spec, dpositivity_certs_empty()),
    content="false",
  )
}

///|
test "positivity certs: certified HIT validation" {
  let params = [dtelescope_entry("F", DPi(DUniv(0), DUniv(0)))]
  let arg_ty = DApp(
    DTVar(0),
    DInductive(dinductive_spec("NeuH", 0, [], [], []), []),
  )
  let spec = dhit_spec("NeuH", 0, params, [], [
    dhit_cell_spec("base", 0, [darg_external("x", arg_ty)], []),
  ])
  inspect(
    hit_schema_validate_with_certs(spec, certs_with(VarianceStrict)),
    content="true",
  )
  inspect(hit_schema_validate(spec), content="false")
  inspect(
    hit_schema_validate_with_certs(spec, certs_with(VarianceNegative)),
    content="false",
  )
  inspect(
    hit_schema_validate_with_certs(spec, certs_with(VarianceStrict)),
    content="true",
  )
}
