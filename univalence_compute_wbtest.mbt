///|
// Whitebox tests for computable univalence.

///|
test "univalence: an equivalence is decided by search, and exists iff sizes agree" {
  inspect(fin_equiv_search(TyBool, TyBool) is Some(_), content="true")
  inspect(fin_equiv_search(TyUnit, TyBool) is Some(_), content="false")
  inspect(univalence_decides(TyBool, TyBool), content="true")
  inspect(univalence_decides(TyUnit, TyUnit), content="true")
  inspect(univalence_decides(TyUnit, TyBool), content="true")
  inspect(univalence_decides(TyProd(TyBool, TyBool), TyBool), content="true")
  inspect(
    univalence_decides(TyProd(TyBool, TyBool), TyProd(TyBool, TyBool)),
    content="true",
  )
}

///|
test "univalence: the type of paths has n! elements" {
  inspect(univalence_path_count(TyUnit, TyUnit), content="1")
  inspect(univalence_path_count(TyBool, TyBool), content="2")
  inspect(univalence_path_count(TyBool, TyUnit), content="0")
  inspect(
    univalence_path_count(TyProd(TyBool, TyBool), TyProd(TyBool, TyBool)),
    content="24",
  )
  inspect(fact(4), content="24")
}

///|
test "univalence: transport along ua computes the equivalence" {
  let n = fin_not_bool()
  let s = fin_swap_bool_pair()
  inspect(fin_map_is_equiv(n), content="true")
  inspect(fin_map_is_equiv(s), content="true")
  inspect(ua_transport_computes(n), content="true")
  inspect(ua_transport_computes(s), content="true")
  inspect(transport_roundtrip(n), content="true")
  inspect(transport_roundtrip(s), content="true")
  // a non-equivalence table is refused, not silently transported
  let bad = fin_map(TyBool, TyBool, [0, 0])
  inspect(fin_map_is_equiv(bad), content="false")
  inspect(ua_transport_computes(bad), content="false")
}

///|
test "univalence: ua id = refl, ua g∘f = ua g ∘ ua f, ua (e⁻¹) = ¬(ua e)" {
  inspect(ua_refl_is_identity(TyBool), content="true")
  inspect(ua_refl_is_identity(TyProd(TyBool, TyBool)), content="true")
  let n = fin_not_bool()
  let s = fin_swap_bool_pair()
  inspect(ua_functorial(n, n), content="true")
  inspect(ua_functorial(s, s), content="true")
  inspect(ua_inverse(n), content="true")
  inspect(ua_inverse(s), content="true")
}

///|
test "univalence is an equivalence: section and retraction laws hold exhaustively" {
  let tys = [TyUnit, TyBool, TyProd(TyBool, TyBool)]
  for i in 0..<tys.length() {
    for j in 0..<tys.length() {
      inspect(ua_section_all(tys[i], tys[j]), content="true")
      inspect(ua_retraction_all(tys[i], tys[j]), content="true")
      inspect(transport_preserves_cardinality(tys[i], tys[j]), content="true")
    }
  }
  inspect(ua_section(fin_not_bool()), content="true")
  inspect(ua_retraction(cpath_ua(fin_swap_bool_pair())), content="true")
}

///|
test "univalence: J on ua-paths and the aggregate battery" {
  inspect(j_rule_on_ua(fin_not_bool()), content="true")
  inspect(j_rule_on_ua(fin_swap_bool_pair()), content="true")
  inspect(univalence_compute_all(), content="true")
}
