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
test "univalence: the search returns the lexicographically first table" {
  // The first equivalence in base-|B| code order: the reversed identity
  // (the same table the old code-ascending scan returned first).
  match fin_equiv_search(TyBool, TyBool) {
    Some(m) => {
      inspect(m.table.length(), content="2")
      inspect(m.table[0], content="1")
      inspect(m.table[1], content="0")
    }
    None => inspect("none", content="unreachable")
  }
  match fin_equiv_search(TyProd(TyBool, TyBool), TyProd(TyBool, TyBool)) {
    Some(m) => {
      inspect(m.table.length(), content="4")
      inspect(m.table[0], content="3")
      inspect(m.table[1], content="2")
      inspect(m.table[2], content="1")
      inspect(m.table[3], content="0")
    }
    None => inspect("none", content="unreachable")
  }
}

///|
test "univalence: the type of paths has n! elements" {
  inspect(bignat_to_string(univalence_path_count(TyUnit, TyUnit)), content="1")
  inspect(bignat_to_string(univalence_path_count(TyBool, TyBool)), content="2")
  inspect(bignat_to_string(univalence_path_count(TyBool, TyUnit)), content="0")
  inspect(
    bignat_to_string(
      univalence_path_count(TyProd(TyBool, TyBool), TyProd(TyBool, TyBool)),
    ),
    content="24",
  )
  inspect(bignat_to_string(fact(4)), content="24")
}

///|
test "univalence: counting is exact where Int32 overflowed (13! … 20!, 16^16)" {
  inspect(bignat_to_string(fact(12)), content="479001600")
  inspect(bignat_to_string(fact(13)), content="6227020800")
  inspect(bignat_to_string(fact(16)), content="20922789888000")
  inspect(bignat_to_string(fact(20)), content="2432902008176640000")
  let b4 = TyProd(TyBool, TyBool)
  let b16 = TyProd(b4, b4)
  // |B|^|A| at 16 elements = 2^64 — exactly zero in wrapped Int32.
  inspect(
    bignat_to_string(fin_map_count(b16, b16)),
    content="18446744073709551616",
  )
  // n! decided by enumeration agrees with the closed form.
  inspect(
    bignat_to_string(univalence_path_count(b16, b16)),
    content="20922789888000",
  )
  inspect(univalence_path_count(b16, b16) == fact(16), content="true")
  inspect(univalence_decides(b16, b16), content="true")
  inspect(univalence_decides(b16, b4), content="true")
  inspect(fin_equiv_search(b16, b4) is None, content="true")
  inspect(bignat_to_string(fin_map_count(b16, b4)), content="4294967296")
}

///|
test "univalence: 16-element search, transport and roundtrip are robust" {
  let b4 = TyProd(TyBool, TyBool)
  let b16 = TyProd(b4, b4)
  match fin_equiv_search(b16, b16) {
    Some(m) => {
      inspect(fin_map_is_equiv(m), content="true")
      inspect(m.table.length(), content="16")
      inspect(m.table[0], content="15")
      inspect(m.table[15], content="0")
      inspect(ua_transport_computes(m), content="true")
      inspect(transport_roundtrip(m), content="true")
      inspect(ua_section(m), content="true")
      inspect(ua_retraction(cpath_ua(m)), content="true")
      inspect(ua_inverse(m), content="true")
    }
    None => inspect("none", content="unreachable")
  }
  inspect(transport_preserves_cardinality(b16, b16), content="true")
  // no equivalence relates 16 to 4 — and that is exactly the law
  inspect(transport_preserves_cardinality(b16, b4), content="true")
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
      inspect(ua_section_all(tys[i], tys[j]) == LawHolds, content="true")
      inspect(ua_retraction_all(tys[i], tys[j]) == LawHolds, content="true")
      inspect(transport_preserves_cardinality(tys[i], tys[j]), content="true")
    }
  }
  inspect(ua_section(fin_not_bool()), content="true")
  inspect(ua_retraction(cpath_ua(fin_swap_bool_pair())), content="true")
}

///|
test "univalence: law exhaustion is honest at 16 elements (undecided, not sampled)" {
  let b4 = TyProd(TyBool, TyBool)
  let b16 = TyProd(b4, b4)
  // 16! equivalences and 2^64 tables exceed every honest *search* budget —
  // the raw exhaustion machinery alone reports `LawUndecided` here, the
  // same convention as BDD node budgets.
  inspect(
    exhaust_tables(
      b16,
      b16,
      m => !fin_map_is_equiv(m) || ua_section(m),
      law_table_budget(),
    ) ==
    LawUndecided,
    content="true",
  )
  inspect(
    exhaust_equiv(b16, b16, ua_section, law_enum_budget()) == LawUndecided,
    content="true",
  )
  // But `ua_section_all`/`ua_retraction_all` themselves never surface
  // `LawUndecided` for this law (SPEC §四 item 9(a), completed): once the
  // raw search exceeds budget they fall back to the symbolic
  // representation argument (`ua_section_proved`/`ua_retraction_proved`),
  // which decides the law directly without searching at all.
  inspect(ua_section_all(b16, b16) == LawHolds, content="true")
  inspect(ua_retraction_all(b16, b16) == LawHolds, content="true")
  // An 8-element type still fits the equivalence budget (8! = 40320).
  let b8 = TyProd(TyProd(TyBool, TyBool), TyBool)
  inspect(ua_section_all(b8, b8) == LawHolds, content="true")
  inspect(ua_retraction_all(b8, b8) == LawHolds, content="true")
  // The verdict constructor carries the counterexample when a law breaks.
  inspect(LawUndecided == LawUndecided, content="true")
  inspect(LawHolds == LawUndecided, content="false")
  // A failing law reports its counterexample table instead of passing.
  match exhaust_equiv(TyBool, TyBool, _ => false, law_enum_budget()) {
    LawFails(m) => {
      inspect(m.src == TyBool, content="true")
      inspect(m.dst == TyBool, content="true")
    }
    _ => inspect(false, content="true")
  }
  match exhaust_tables(TyBool, TyBool, _ => false, law_table_budget()) {
    LawFails(m) => inspect(m.table.length(), content="2")
    _ => inspect(false, content="true")
  }
}

///|
test "univalence: J on ua-paths and the aggregate battery" {
  inspect(j_rule_on_ua(fin_not_bool()), content="true")
  inspect(j_rule_on_ua(fin_swap_bool_pair()), content="true")
  inspect(univalence_compute_all(), content="true")
}

///|
test "univalence: codes decode identically in Int32 and BigNat" {
  let a = TyProd(TyBool, TyBool)
  let b = TyBool
  for code in 0..<16 {
    let small = fin_map_of_code(a, b, code)
    let big = fin_map_of_code_big(a, b, bignat_of_int(code))
    inspect(fin_map_table_eq(small, big), content="true")
  }
}

///|
test "univalence: paths form a groupoid (units, involution, anti-hom, assoc, coe)" {
  let n = fin_not_bool()
  let s = fin_swap_bool_pair()
  let np = cpath_ua(n)
  let sp = cpath_ua(s)
  // Units
  inspect(cpath_comp_left_unit(np), content="true")
  inspect(cpath_comp_right_unit(np), content="true")
  inspect(cpath_comp_left_unit(sp), content="true")
  inspect(cpath_comp_right_unit(sp), content="true")
  // Involution and reflection of refl
  inspect(cpath_sym_involutive(np), content="true")
  inspect(cpath_sym_involutive(sp), content="true")
  inspect(cpath_sym_refl(TyBool), content="true")
  inspect(cpath_sym_refl(TyProd(TyBool, TyBool)), content="true")
  // Anti-homomorphism and associativity
  inspect(cpath_sym_comp(np, np), content="true")
  inspect(cpath_sym_comp(sp, sp), content="true")
  inspect(cpath_comp_assoc(np, np, np), content="true")
  inspect(cpath_comp_assoc(sp, sp, sp), content="true")
  // Composite transport computes as composite of transports
  inspect(transport_comp_computes(np, np), content="true")
  inspect(transport_comp_computes(sp, sp), content="true")
  // Transport along refl is the identity
  inspect(transport_refl_identity(TyBool), content="true")
  inspect(transport_refl_identity(TyProd(TyBool, TyBool)), content="true")
  // Endpoint mismatch is refused, not guessed
  inspect(cpath_sym_comp(np, sp), content="false")
  inspect(cpath_comp_assoc(np, np, sp), content="false")
  inspect(transport_comp_computes(np, sp), content="false")
}

///|
test "univalence (9a): a symbolic identity layer decides section/retraction at any size" {
  // Cross-validate against the exhaustive decision at every size where
  // exhaustion still fits its budget: the two never disagree.
  let tys = [TyUnit, TyBool, TyProd(TyBool, TyBool)]
  for i in 0..<tys.length() {
    for j in 0..<tys.length() {
      inspect(
        ua_section_proved(tys[i], tys[j]) == ua_section_all(tys[i], tys[j]),
        content="true",
      )
      inspect(
        ua_retraction_proved(tys[i], tys[j]) ==
        ua_retraction_all(tys[i], tys[j]),
        content="true",
      )
    }
  }
  let b8 = TyProd(TyProd(TyBool, TyBool), TyBool)
  inspect(ua_section_proved(b8, b8) == ua_section_all(b8, b8), content="true")
  inspect(
    ua_retraction_proved(b8, b8) == ua_retraction_all(b8, b8),
    content="true",
  )
  // Beyond the exhaustive budget (16 elements): `ua_section_all`/
  // `ua_retraction_all` now fall back to the symbolic argument instead of
  // ever reporting `LawUndecided` for this law (item 9(a), completed) —
  // they agree with the dedicated `_proved` functions exactly.
  let b4 = TyProd(TyBool, TyBool)
  let b16 = TyProd(b4, b4)
  inspect(ua_section_all(b16, b16) == LawHolds, content="true")
  inspect(ua_retraction_all(b16, b16) == LawHolds, content="true")
  inspect(ua_section_proved(b16, b16) == LawHolds, content="true")
  inspect(ua_retraction_proved(b16, b16) == LawHolds, content="true")
  // Genuinely huge: two 16-element products, 256 elements — far beyond any
  // n! exhaustion, decided in O(n) by the same argument, through BOTH the
  // dedicated `_proved` functions and the now-complete `_all` functions.
  let b256 = TyProd(b16, b16)
  inspect(ua_section_proved(b256, b256) == LawHolds, content="true")
  inspect(ua_retraction_proved(b256, b256) == LawHolds, content="true")
  inspect(ua_section_all(b256, b256) == LawHolds, content="true")
  inspect(ua_retraction_all(b256, b256) == LawHolds, content="true")
  // Unequal sizes stay vacuously true, exactly as the exhaustive versions.
  inspect(ua_section_proved(TyBool, b4) == LawHolds, content="true")
  inspect(ua_retraction_proved(TyBool, b4) == LawHolds, content="true")
  // The computational core agrees with the single-equivalence checks for
  // actual equivalences, and extends them to arbitrary (non-equivalence)
  // tables and paths.
  inspect(fin_map_round_trip_identity(fin_not_bool()), content="true")
  inspect(fin_map_round_trip_identity(fin_swap_bool_pair()), content="true")
  inspect(
    fin_map_round_trip_identity(fin_map(TyBool, TyBool, [0, 0])),
    content="true",
  )
  inspect(cpath_round_trip_identity(cpath_ua(fin_not_bool())), content="true")
  inspect(
    cpath_round_trip_identity(cpath_ua(fin_map(TyBool, TyBool, [1, 1]))),
    content="true",
  )
}

///|
// `fin_ty` is now a public helper in univalence_compute.mbt (promoted so
// qpoly_univalence.mbt can reuse it); the private duplicate that used to
// live here has been removed.

///|
test "univalence (9b): enumeration threshold raised to the Int64-safe maximum (n=20)" {
  // 20! is the largest factorial that fits Int64; the DP enumeration and
  // the closed form must agree exactly at the new boundary and just past
  // it.
  inspect(bignat_to_string(fact(20)), content="2432902008176640000")
  inspect(bignat_to_string(fact(21)), content="51090942171709440000")
  // fin_equiv_count at n=19 and n=20 goes through the enumeration path
  // (n <= fin_equiv_enum_max()) and must match the closed form exactly.
  let ty19 = fin_ty(19)
  inspect(ty_card(ty19), content="19")
  inspect(
    bignat_to_string(fin_equiv_count(ty19, ty19)) == bignat_to_string(fact(19)),
    content="true",
  )
  let ty20 = fin_ty(20)
  inspect(ty_card(ty20), content="20")
  inspect(
    bignat_to_string(fin_equiv_count(ty20, ty20)) == bignat_to_string(fact(20)),
    content="true",
  )
  // n = 21 now falls past the enumeration boundary onto the closed form.
  let ty21 = fin_ty(21)
  inspect(ty_card(ty21), content="21")
  inspect(
    bignat_to_string(fin_equiv_count(ty21, ty21)) == bignat_to_string(fact(21)),
    content="true",
  )
}
