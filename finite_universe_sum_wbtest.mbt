///|
// Whitebox tests for the sum-type widening of the finite universe
// (SPEC §四 item 9(c)): `TySum` is supported throughout the
// computable-univalence layer (cardinality, elements, membership, search,
// counting, the univalence decision, and transport), without touching the
// Bool/Unit/Product-only wiring model or the Kan semantic embedding.

///|
test "finite universe (c): TySum cardinality and element order" {
  let s = TySum(TyBool, TyUnit)
  inspect(ty_card(s), content="3")
  let xs = elems_of(s)
  inspect(xs.length(), content="3")
  // Left-tagged elements of the first summand first, in their own order,
  // then right-tagged elements of the second.
  inspect(xs[0] == PVLeft(PVBool(false)), content="true")
  inspect(xs[1] == PVLeft(PVBool(true)), content="true")
  inspect(xs[2] == PVRight(PVUnit), content="true")
  // Membership respects the tag and the summand.
  inspect(in_ty(PVLeft(PVBool(true)), s), content="true")
  inspect(in_ty(PVRight(PVUnit), s), content="true")
  inspect(in_ty(PVLeft(PVUnit), s), content="false")
  inspect(in_ty(PVRight(PVBool(false)), s), content="false")
  inspect(in_ty(PVUnit, s), content="false")
  // Nested sums compose.
  let nested = TySum(TyBool, TySum(TyUnit, TyBool))
  inspect(ty_card(nested), content="5")
}

///|
test "finite universe (c): univalence decides across sum and product presentations of the same size" {
  // Bool + Bool and Bool x Unit x Bool x Unit... simplest: Bool+Bool has
  // card 4, same as Bool x Bool; univalence says they are equivalent and
  // there are exactly 4! equivalences between them, by cardinality alone.
  let sum4 = TySum(TyBool, TyBool)
  let prod4 = TyProd(TyBool, TyBool)
  inspect(ty_card(sum4), content="4")
  inspect(univalence_decides(sum4, prod4), content="true")
  inspect(bignat_to_string(fin_equiv_count(sum4, prod4)), content="24")
  inspect(bignat_to_string(fin_equiv_count(sum4, sum4)), content="24")
  match fin_equiv_search(sum4, prod4) {
    Some(m) => inspect(fin_map_is_equiv(m), content="true")
    None => inspect(false, content="true")
  }
  // Unequal sizes: `univalence_decides` is a self-consistency check of the
  // decision procedure (it also holds vacuously whenever existence and
  // cardinality agreement agree, i.e. both say "no equivalence" here) —
  // the actual non-existence fact is `fin_equiv_search is None` and
  // `fin_equiv_count == 0`.
  let sum3 = TySum(TyBool, TyUnit)
  inspect(univalence_decides(sum3, prod4), content="true")
  inspect(fin_equiv_search(sum3, prod4) is None, content="true")
  inspect(bignat_to_string(fin_equiv_count(sum3, prod4)), content="0")
}

///|
test "finite universe (c): a concrete sum-commutativity equivalence transports correctly" {
  // A+B ≃ B+A by swapping the tag: a manually built FinMap, checked to be
  // an equivalence, and its ua-path transports elements by the same swap.
  let ab = TySum(TyBool, TyUnit) // card 3: [L false, L true, R unit]
  let ba = TySum(TyUnit, TyBool) // card 3: [L unit, R false, R true]
  // index 0 (L false) -> index 1 (R false); 1 (L true) -> 2 (R true);
  // 2 (R unit) -> 0 (L unit)
  let swap = fin_map(ab, ba, [1, 2, 0])
  inspect(fin_map_is_equiv(swap), content="true")
  inspect(univalence_decides(ab, ba), content="true")
  let p = cpath_ua(swap)
  inspect(cpath_coe(p, 0, 1, PVLeft(PVBool(false))) == PVRight(PVBool(false)), content="true")
  inspect(cpath_coe(p, 0, 1, PVLeft(PVBool(true))) == PVRight(PVBool(true)), content="true")
  inspect(cpath_coe(p, 0, 1, PVRight(PVUnit)) == PVLeft(PVUnit), content="true")
  // Round trip back.
  inspect(cpath_coe(p, 1, 0, PVRight(PVBool(false))) == PVLeft(PVBool(false)), content="true")
  inspect(transport_roundtrip(swap), content="true")
  // The groupoid laws proved for the product fragment hold here too: they
  // never inspected the type former, only the table.
  inspect(ua_transport_computes(swap), content="true")
  inspect(ua_inverse(swap), content="true")
  inspect(cpath_comp_left_unit(p), content="true")
  inspect(cpath_comp_right_unit(p), content="true")
  inspect(cpath_sym_involutive(p), content="true")
  inspect(transport_refl_identity(ab), content="true")
}

///|
test "finite universe (c): fin_sum_swap is a generic A+B ≃ B+A equivalence" {
  let a = TyBool
  let b = TySum(TyUnit, TyBool) // card 3, heterogeneous nesting
  let swap = fin_sum_swap(a, b)
  inspect(swap.src == TySum(a, b), content="true")
  inspect(swap.dst == TySum(b, a), content="true")
  inspect(fin_map_is_equiv(swap), content="true")
  inspect(univalence_decides(swap.src, swap.dst), content="true")
  // Swapping twice (A+B ≃ B+A ≃ A+B) composes to a permutation that
  // round-trips every element back to itself.
  let back = fin_sum_swap(b, a)
  let roundtrip = fin_map_comp(back, swap)
  inspect(fin_map_is_equiv(roundtrip), content="true")
  for i in 0..<roundtrip.table.length() {
    inspect(roundtrip.table[i] == i, content="true")
  }
  // A degenerate summand (Unit) still swaps correctly.
  let deg = fin_sum_swap(TyUnit, TyBool)
  inspect(fin_map_is_equiv(deg), content="true")
  inspect(ty_card(deg.src), content="3")
}
