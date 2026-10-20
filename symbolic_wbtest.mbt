///|
// Differential validation: the enumeration oracle lives ONLY here, in
// tests, as an independent check on the symbolic decision procedures.

///|
fn brute_sat(f : Face, n : Int32) -> Bool {
  for mask in 0..<pow2(n) {
    if face_holds(f, assignment_of_mask(mask, n)) {
      return true
    }
  }
  false
}

///|
fn brute_le(f : Face, g : Face, n : Int32) -> Bool {
  for mask in 0..<pow2(n) {
    let env = assignment_of_mask(mask, n)
    if face_holds(f, env) && !face_holds(g, env) {
      return false
    }
  }
  true
}

///|
fn brute_system_eq(a : VecSystem, b : VecSystem, n : Int32) -> Bool {
  for mask in 0..<pow2(n) {
    let env = assignment_of_mask(mask, n)
    match (system_lookup(a, env), system_lookup(b, env)) {
      (None, None) => ()
      (Some(x), Some(y)) => if !vec_approx_eq(x, y) { return false }
      _ => return false
    }
  }
  true
}

///|
test "BDD decisions agree with enumeration oracle" {
  let i0 = face_var0(0)
  let i1 = face_var1(0)
  let j0 = face_var0(1)
  let j1 = face_var1(1)
  let forms = [
    FTop,
    FBot,
    i0,
    i1,
    FAnd(i0, i1),
    FOr(i0, j1),
    FAnd(FOr(i0, j0), FOr(i1, j1)),
    FOr(FAnd(i0, j1), FAnd(i1, j0)),
    FEq1(DNeg(DVar(0))),
    FEq0(DOr(DVar(0), DVar(1))),
  ]
  for a in 0..<forms.length() {
    assert_true(bdd_sat_face(forms[a], 2) == brute_sat(forms[a], 2))
    for b in 0..<forms.length() {
      assert_true(
        bdd_face_le(forms[a], forms[b], 2) == brute_le(forms[a], forms[b], 2),
      )
      assert_true(
        bdd_face_eq(forms[a], forms[b], 2) ==
        (brute_le(forms[a], forms[b], 2) && brute_le(forms[b], forms[a], 2)),
      )
    }
  }
  assert_true(check_bdd_canonical())
}

///|
test "symbolic system equality agrees with enumeration oracle" {
  let v1 : CVec = [cx_real(1.0), cx_zero()]
  let v2 : CVec = [cx_zero(), cx_real(1.0)]
  let s1 = system_of([
    branch(face_var0(0), v1),
    branch(face_var1(0), v2),
    branch(FAnd(face_var0(0), face_var0(1)), v1),
    branch(FAnd(face_var0(0), face_var1(0)), v2),
  ])
  let s2 = prune_system(s1, 2)
  let s3 = system_of([branch(face_var1(0), v2), branch(face_var0(0), v1)])
  let s4 = system_of([branch(face_var0(0), v2), branch(face_var1(0), v1)])
  assert_true(system_eq_mod_sym(s1, s2, 2) == brute_system_eq(s1, s2, 2))
  assert_true(system_eq_mod_sym(s1, s3, 2) == brute_system_eq(s1, s3, 2))
  assert_true(system_eq_mod_sym(s1, s4, 2) == brute_system_eq(s1, s4, 2))
  assert_true(system_eq_mod_sym(s1, s2, 2))
  assert_true(!system_eq_mod_sym(s1, s4, 2))
}

///|
test "wiring category and coherence" {
  assert_true(check_wiring_category())
  assert_true(check_wiring_coherence())
  let w = wiring_prod(wiring_not(), wiring_swap(TyBool, TyUnit))
  assert_true(wiring_wf(w))
  assert_true(
    wiring_apply(w, PVPair(PVBool(true), PVPair(PVBool(false), PVUnit))) ==
    PVPair(PVBool(false), PVPair(PVUnit, PVBool(false))),
  )
  assert_true(
    wiring_apply(
      wiring_inv(w),
      wiring_apply(w, PVPair(PVBool(true), PVPair(PVBool(false), PVUnit))),
    ) ==
    PVPair(PVBool(true), PVPair(PVBool(false), PVUnit)),
  )
}

///|
test "symbolic equiv decisions agree with extensional oracles" {
  let e1 = equiv_prod(equiv_bool_not(), equiv_swap(TyBool, TyUnit))
  let e2 = equiv_comp(
    equiv_swap(TyBool, TyProd(TyBool, TyUnit)),
    equiv_prod(equiv_swap(TyBool, TyUnit), equiv_bool_not()),
  )
  let e3 = equiv_inv(e1)
  assert_true(equiv_wf(e1) == equiv_wf_extensional(e1))
  assert_true(equiv_wf(e2) == equiv_wf_extensional(e2))
  assert_true(equiv_ext_eq(e1, e2) == equiv_ext_eq_oracle(e1, e2))
  assert_true(equiv_ext_eq(e1, e3) == equiv_ext_eq_oracle(e1, e3))
  assert_true(equiv_ext_eq(equiv_comp(e1, e3), equiv_id(e1.src)))
}
