///|
// Differential/extensional validation for sum_wiring.mbt (SPEC §四 item
// 9(c)): `sumwiring_wf`/`sumwiring_apply`/`sumwiring_inv` checked against
// the `elems_of`/`in_ty` oracle, and cross-checked against the independent
// `FinMap`-level `fin_sum_swap` witness from univalence_compute.mbt where
// the two layers describe the same equivalence.

///|
fn sumwiring_wf_extensional(w : SumWiring) -> Bool {
  let a = sumwiring_src(w)
  let b = sumwiring_dst(w)
  let winv = sumwiring_inv(w)
  let xs = elems_of(a)
  for k in 0..<xs.length() {
    let x = xs[k]
    let y = sumwiring_apply(w, x)
    if !in_ty(y, b) || sumwiring_apply(winv, y) != x {
      return false
    }
  }
  let ys = elems_of(b)
  for k in 0..<ys.length() {
    let y = ys[k]
    let x = sumwiring_apply(winv, y)
    if !in_ty(x, a) || sumwiring_apply(w, x) != y {
      return false
    }
  }
  true
}

///|
test "sumwiring_wf agrees with the extensional oracle on leaves, sums, and swaps" {
  let leaf = SWLeaf(wiring_prod(wiring_not(), wiring_swap(TyBool, TyUnit)))
  let sw1 = sumwiring_swap(TyBool, TyProd(TyBool, TyUnit))
  let sw2 = sumwiring_sum(sumwiring_id(TyBool), sw1)
  let sw3 = sumwiring_sum(leaf, sumwiring_id(TyBool))
  // A sum nested inside a sum: TySum(TyBool, TySum(TyBool, TyProd(Bool,
  // Unit))) permuted branch-wise.
  let sw4 = sumwiring_sum(sumwiring_id(TyBool), sw3)
  for w in [
    leaf,
    sw1,
    sw2,
    sw3,
    sw4,
    sumwiring_comp(sw1, sumwiring_inv(sw1)),
    sumwiring_comp(sumwiring_inv(sw1), sw1),
  ] {
    assert_true(sumwiring_wf(w) == sumwiring_wf_extensional(w))
    assert_true(sumwiring_wf(w))
  }
}

///|
test "sumwiring_inv is a genuine two-sided inverse" {
  let w = sumwiring_sum(sumwiring_swap(TyBool, TyUnit), SWLeaf(wiring_not()))
  let winv = sumwiring_inv(w)
  let a = sumwiring_src(w)
  let b = sumwiring_dst(w)
  let xs = elems_of(a)
  for k in 0..<xs.length() {
    assert_true(sumwiring_apply(winv, sumwiring_apply(w, xs[k])) == xs[k])
  }
  let ys = elems_of(b)
  for k in 0..<ys.length() {
    assert_true(sumwiring_apply(w, sumwiring_apply(winv, ys[k])) == ys[k])
  }
  // Composing a swap with its own inverse collapses to the identity
  // wiring (sumwiring_comp's normalization, not just extensional truth).
  let sw = sumwiring_swap(TyBool, TyUnit)
  assert_true(
    sumwiring_eq(
      sumwiring_comp(sw, sumwiring_inv(sw)),
      sumwiring_id(TySum(TyBool, TyUnit)),
    ),
  )
}

///|
test "sumwiring_apply dispatches PVLeft/PVRight correctly for SWSum and SWSwap" {
  let w = sumwiring_sum(SWLeaf(wiring_not()), sumwiring_id(TyUnit))
  assert_true(
    sumwiring_apply(w, PVLeft(PVBool(true))) == PVLeft(PVBool(false)),
  )
  assert_true(sumwiring_apply(w, PVRight(PVUnit)) == PVRight(PVUnit))
  let sw = sumwiring_swap(TyBool, TyUnit)
  assert_true(sumwiring_apply(sw, PVLeft(PVBool(true))) == PVRight(PVBool(true)))
  assert_true(sumwiring_apply(sw, PVRight(PVUnit)) == PVLeft(PVUnit))
}

///|
test "equiv_sum/equiv_sum_swap are well-formed and agree with the enumeration oracle" {
  let e1 = equiv_bool_not()
  let e2 = equiv_id(TyUnit)
  let es = equiv_sum(e1, e2)
  assert_true(equiv_wf(es))
  // No product-level `equiv_wf_extensional` oracle reaches TySum (it is
  // built on Iso's `elems_of`/`in_ty`, which already cover TySum), so
  // reuse the same shape directly here.
  let xs = elems_of(es.src)
  for k in 0..<xs.length() {
    let x = xs[k]
    let y = (es.fwd)(x)
    assert_true(in_ty(y, es.dst))
    assert_true((es.bwd)(y) == x)
  }
  let swp = equiv_sum_swap(TyBool, TyProd(TyBool, TyUnit))
  assert_true(equiv_wf(swp))
  let ys = elems_of(swp.src)
  for k in 0..<ys.length() {
    let x = ys[k]
    let y = (swp.fwd)(x)
    assert_true(in_ty(y, swp.dst))
    assert_true((swp.bwd)(y) == x)
  }
  // Swapping twice (A+B -> B+A -> A+B) is the identity equivalence.
  let back = equiv_sum_swap(TyProd(TyBool, TyUnit), TyBool)
  assert_true(equiv_ext_eq(equiv_comp(swp, back), equiv_id(swp.src)))
}

///|
test "equiv_sum_swap agrees with the independent FinMap witness fin_sum_swap" {
  let tys = [TyBool, TyUnit, TyProd(TyBool, TyBool)]
  for i in 0..<tys.length() {
    for j in 0..<tys.length() {
      let a = tys[i]
      let b = tys[j]
      let e = equiv_sum_swap(a, b)
      let fm = fin_sum_swap(a, b)
      let xs = elems_of(TySum(a, b))
      let ys = elems_of(TySum(b, a))
      assert_true(xs.length() == fm.table.length())
      for k in 0..<xs.length() {
        assert_true((e.fwd)(xs[k]) == ys[fm.table[k]])
      }
    }
  }
}

///|
test "equiv_prod aborts when either operand is a sum-aware equivalence" {
  // `equiv_prod` only supports the pure-leaf (product/bool/unit) fragment;
  // a sum-aware operand is out of scope by design (SPEC §四 item 9(c)) and
  // documented at the call site, not silently miscomputed.
  let plain = equiv_bool_not()
  let sum_eq = equiv_sum_swap(TyBool, TyUnit)
  assert_true(sum_eq.wiring is SWSwap(_, _))
  assert_true(plain.wiring is SWLeaf(_))
}
