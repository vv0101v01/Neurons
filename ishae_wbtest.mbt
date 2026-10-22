///|
// Whitebox tests for ishae/biinv coherence and fiber contractibility
// (SPEC §四 item 3).

///|
test "ishae: fibers, contractibility and isEquiv-via-contractible-fibers" {
  // fin_not_bool is a genuine bijection: both fibers are singletons.
  let f = fin_not_bool()
  inspect(fin_fiber(f, 0).length(), content="1")
  inspect(fin_fiber(f, 1).length(), content="1")
  inspect(fin_is_contr_fiber(f, 0), content="true")
  inspect(fin_is_contr_fiber(f, 1), content="true")
  inspect(fin_is_equiv_via_contr(f), content="true")
  inspect(fin_is_equiv_via_contr(f) == fin_map_is_equiv(f), content="true")
  // A constant (non-injective, non-surjective) map Bool -> Bool: fiber
  // over the image point has size 2 (not contractible), the other is
  // empty (not contractible either).
  let const_map = fin_map(TyBool, TyBool, [0, 0])
  inspect(fin_fiber(const_map, 0).length(), content="2")
  inspect(fin_fiber(const_map, 1).length(), content="0")
  inspect(fin_is_contr_fiber(const_map, 0), content="false")
  inspect(fin_is_contr_fiber(const_map, 1), content="false")
  inspect(fin_is_equiv_via_contr(const_map), content="false")
  inspect(fin_map_is_equiv(const_map), content="false")
  // An injective-but-not-surjective map TyUnit -> TyBool: the hit fiber is
  // a singleton, the missed one is empty — contractible fibers fail only
  // at the missed point, exactly capturing "not surjective".
  let inj_map = fin_map(TyUnit, TyBool, [1])
  inspect(fin_is_contr_fiber(inj_map, 1), content="true")
  inspect(fin_is_contr_fiber(inj_map, 0), content="false")
  inspect(fin_is_equiv_via_contr(inj_map), content="false")
}

///|
test "ishae: the triangle identity is free once eta and epsilon hold" {
  let f = fin_swap_bool_pair()
  let g = f // self-inverse
  let h = Ishae::{ f, g, }
  inspect(ishae_eta_holds(h), content="true")
  inspect(ishae_eps_holds(h), content="true")
  inspect(ishae_triangle_holds(h), content="true")
  inspect(ishae_triangle_is_free(h), content="true")
  inspect(ishae_holds(h), content="true")
  // A broken "inverse" on the SAME type as f (TyProd(Bool,Bool), 4
  // elements): epsilon fails, the triangle also fails, and
  // ishae_triangle_is_free degenerates to vacuous truth (its antecedent
  // ishae_eps_holds is false), matching the implication's own statement.
  let b4 = TyProd(TyBool, TyBool)
  let bad_g = fin_map(b4, b4, [0, 0, 0, 0])
  let bad_h = Ishae::{ f, g: bad_g, }
  inspect(ishae_eps_holds(bad_h), content="false")
  inspect(ishae_triangle_holds(bad_h), content="false")
  inspect(ishae_triangle_is_free(bad_h), content="true") // vacuously
  inspect(ishae_holds(bad_h), content="false")
}

///|
test "ishae: biinv-to-ishae construction derives epsilon from a left inverse alone" {
  // fin_not_bool is self-inverse, so its left and right inverses coincide
  // trivially; the construction should still go through the general
  // chase, not special-case src==dst.
  let f = fin_not_bool()
  let l = fin_not_bool()
  let r = fin_not_bool()
  match biinv_to_ishae(f, l, r) {
    Some(h) => {
      inspect(h.g == l, content="true") // g is defined to be l, not r
      inspect(ishae_holds(h), content="true")
    }
    None => inspect("none", content="unreachable")
  }
  // A genuinely asymmetric case: f : TyBool -> TyBool x TyUnit (injective,
  // not surjective on its own, but biinv needs f itself to be an
  // equivalence; use a real bijection TyBool -> TyBool x TyUnit instead,
  // i.e. the canonical iso Bool ~ Bool*Unit).
  let bu = TyProd(TyBool, TyUnit)
  let f2 = fin_map(TyBool, bu, [0, 1]) // false |-> (false,*), true |-> (true,*)
  let l2 = fin_map(bu, TyBool, [0, 1]) // (false,*) |-> false, (true,*) |-> true
  let r2 = l2 // same table serves as both inverses here (f2 is a genuine bijection)
  inspect(fin_map_is_equiv(f2), content="true")
  match biinv_to_ishae(f2, l2, r2) {
    Some(h2) => inspect(ishae_holds(h2), content="true")
    None => inspect("none", content="unreachable")
  }
  // Malformed biinv data (l does not actually left-invert f): construction
  // reports None rather than returning a bogus package.
  let bad_l = fin_map(TyBool, TyBool, [0, 0])
  inspect(biinv_to_ishae(f, bad_l, r) is None, content="true")
  // Type-mismatched l/r: also None.
  inspect(biinv_to_ishae(f2, fin_not_bool(), r2) is None, content="true")
}

///|
// NOTE on reading these assertions: `fin_equiv_three_ways_agree(f)` is
// `true` exactly when the three notions of equivalence AGREE about `f` —
// which happens both when `f` genuinely is an equivalence (all three say
// "yes") and when `f` genuinely is not (all three say "no"). It is
// `false` only on a real three-way disagreement. So every entry below
// expects `true` except the two `*_mismatch_disagrees` cases, which
// demonstrate the exact scope boundary documented on the function.
test "ishae: the three equivalence notions agree, exhaustively" {
  // Bijections: all three predicates agree — `f` is an equivalence.
  inspect(fin_equiv_three_ways_agree(fin_not_bool()), content="true")
  inspect(fin_equiv_three_ways_agree(fin_swap_bool_pair()), content="true")
  inspect(fin_equiv_three_ways_agree(fin_map_id(TyBool)), content="true")
  inspect(
    fin_equiv_three_ways_agree(fin_map_id(TyProd(TyBool, TyBool))),
    content="true",
  )
  inspect(
    fin_equiv_three_ways_agree(fin_sum_swap(TyBool, TyUnit)),
    content="true",
  )
  // Non-equivalences between EQUAL-cardinality types: all three still
  // agree, now on "no" — `fin_map_is_equiv`'s injectivity check is already
  // a correct bijection test here, so there is no scope-boundary case to
  // expose.
  inspect(
    fin_equiv_three_ways_agree(fin_map(TyBool, TyBool, [0, 0])),
    content="true",
  )
  let b4 = TyProd(TyBool, TyBool)
  inspect(
    fin_equiv_three_ways_agree(fin_map(b4, b4, [0, 0, 1, 1])),
    content="true",
  )
  // Non-equivalences between MISMATCHED-cardinality types where the
  // smaller-to-larger table is still injective on its own (too few source
  // elements to be surjective, but nothing to witness non-injectivity
  // either): all three still agree on "no" once `via_table` carries the
  // cardinality check `fin_equiv_three_ways_agree` adds.
  inspect(
    fin_equiv_three_ways_agree(fin_map(TyUnit, TyBool, [1])),
    content="true",
  )
  inspect(
    fin_equiv_three_ways_agree(fin_map(TyBool, TyUnit, [0, 0])),
    content="true",
  )
  inspect(
    fin_equiv_three_ways_agree(fin_map(TyBool, b4, [0, 1])),
    content="true",
  )
}

///|
test "ishae: the raw fin_map_is_equiv injectivity-only scope boundary" {
  // The exact disagreement `fin_equiv_three_ways_agree` was written to
  // correct for: a well-formed, injective, but non-surjective table
  // (fewer source elements than destination elements) makes the RAW
  // `fin_map_is_equiv` say "equivalence", while `fin_is_equiv_via_contr`
  // (fiber-counting) correctly says "no" — `fin_map_is_equiv`'s own doc
  // comment already scopes it to equal-cardinality inputs, and every
  // other call site in the codebase enforces that precondition before
  // calling it; this test pins down the one place a bare call would be
  // unsound, so the gap stays documented instead of silently assumed.
  let b4 = TyProd(TyBool, TyBool)
  let f1 = fin_map(TyUnit, TyBool, [1])
  inspect(fin_map_is_equiv(f1), content="true") // wrong in isolation
  inspect(fin_is_equiv_via_contr(f1), content="false") // correct
  inspect(ty_card(f1.src) == ty_card(f1.dst), content="false")
  let f2 = fin_map(TyBool, b4, [0, 1])
  inspect(fin_map_is_equiv(f2), content="true") // wrong in isolation
  inspect(fin_is_equiv_via_contr(f2), content="false") // correct
  inspect(ty_card(f2.src) == ty_card(f2.dst), content="false")
  // The corrected three-way check does not inherit this gap.
  inspect(fin_equiv_three_ways_agree(f1), content="true")
  inspect(fin_equiv_three_ways_agree(f2), content="true")
}
