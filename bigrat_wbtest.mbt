///|
// Whitebox tests for `BigRat` (SPEC §四 item 9(d)): agreement with the
// existing `Int32`-bounded `Rat` on values that fit both, and the overflow
// `Rat` is silently exposed to that `BigRat` avoids.

///|
test "bigrat: construction always reduces, denominator always positive" {
  let a = bigrat_make(bigint_of_int(6), bigint_of_int(8))
  inspect(bigrat_to_string(a), content="3/4")
  let b = bigrat_make(bigint_of_int(-6), bigint_of_int(8))
  inspect(bigrat_to_string(b), content="-3/4")
  let c = bigrat_make(bigint_of_int(6), bigint_of_int(-8))
  inspect(bigrat_to_string(c), content="-3/4")
  inspect(b == c, content="true")
  let d = bigrat_make(bigint_of_int(-6), bigint_of_int(-8))
  inspect(bigrat_to_string(d), content="3/4")
  inspect(
    bigrat_to_string(bigrat_make(bigint_of_int(0), bigint_of_int(5))),
    content="0",
  )
  inspect(
    bigrat_to_string(bigrat_make(bigint_of_int(4), bigint_of_int(2))),
    content="2",
  )
  inspect(bigrat_is_zero(bigrat_zero()), content="true")
  inspect(bigrat_to_string(bigrat_one()), content="1")
  // bigrat_eq agrees with structural equality (both sides always reduced):
  // b and c were built from differently-signed num/den but both reduce to
  // -3/4, while a (3/4) and the zero rational are genuinely distinct.
  inspect(bigrat_eq(b, c), content="true")
  inspect(bigrat_eq(a, b), content="false")
  inspect(bigrat_eq(a, bigrat_zero()), content="false")
  inspect(bigrat_eq(b, c) == (b == c), content="true")
}

///|
test "bigrat: arithmetic agrees with the Int32 Rat on shared-range values" {
  let pairs : Array[(Rat, Rat)] = [
    (rat_make(1, 2), rat_make(1, 3)),
    (rat_make(-3, 4), rat_make(5, 6)),
    (rat_make(7, 1), rat_make(-2, 5)),
    (rat_make(0, 1), rat_make(9, 11)),
    (rat_make(22, 7), rat_make(355, 113)),
  ]
  for i in 0..<pairs.length() {
    let (ra, rb) = pairs[i]
    let ba = bigrat_of_rat(ra)
    let bb = bigrat_of_rat(rb)
    // Round-tripping through BigRat and back recovers the same Rat.
    match rat_of_bigrat(ba) {
      Some(r) => inspect(rat_eq(r, ra), content="true")
      None => inspect("none", content="unreachable")
    }
    // add/sub/mul/div agree after converting back to Rat.
    let add_expect = rat_add(ra, rb)
    match rat_of_bigrat(bigrat_add(ba, bb)) {
      Some(r) => inspect(rat_eq(r, add_expect), content="true")
      None => inspect("none", content="unreachable")
    }
    let sub_expect = rat_sub(ra, rb)
    match rat_of_bigrat(bigrat_sub(ba, bb)) {
      Some(r) => inspect(rat_eq(r, sub_expect), content="true")
      None => inspect("none", content="unreachable")
    }
    let mul_expect = rat_mul(ra, rb)
    match rat_of_bigrat(bigrat_mul(ba, bb)) {
      Some(r) => inspect(rat_eq(r, mul_expect), content="true")
      None => inspect("none", content="unreachable")
    }
    if !rat_is_zero(rb) {
      let div_expect = rat_div(ra, rb)
      match rat_of_bigrat(bigrat_div(ba, bb)) {
        Some(r) => inspect(rat_eq(r, div_expect), content="true")
        None => inspect("none", content="unreachable")
      }
    }
    // Comparison agrees with cross-multiplication sign on the Int32 side.
    let expect_cmp = if ra.num * rb.den < rb.num * ra.den {
      -1
    } else if ra.num * rb.den > rb.num * ra.den {
      1
    } else {
      0
    }
    inspect(bigrat_cmp(ba, bb), content=expect_cmp.to_string())
  }
}

///|
test "bigrat: field laws (commutativity, associativity, inverses)" {
  let a = bigrat_make(bigint_of_int(3), bigint_of_int(7))
  let b = bigrat_make(bigint_of_int(-5), bigint_of_int(11))
  let c = bigrat_make(bigint_of_int(2), bigint_of_int(9))
  inspect(bigrat_add(a, b) == bigrat_add(b, a), content="true")
  inspect(bigrat_mul(a, b) == bigrat_mul(b, a), content="true")
  inspect(
    bigrat_add(bigrat_add(a, b), c) == bigrat_add(a, bigrat_add(b, c)),
    content="true",
  )
  inspect(
    bigrat_mul(bigrat_mul(a, b), c) == bigrat_mul(a, bigrat_mul(b, c)),
    content="true",
  )
  inspect(bigrat_add(a, bigrat_neg(a)) == bigrat_zero(), content="true")
  inspect(bigrat_mul(a, bigrat_inv(a)) == bigrat_one(), content="true")
  inspect(bigrat_add(a, bigrat_zero()) == a, content="true")
  inspect(bigrat_mul(a, bigrat_one()) == a, content="true")
  inspect(bigrat_sub(a, a) == bigrat_zero(), content="true")
  inspect(bigrat_div(a, a) == bigrat_one(), content="true")
}

///|
test "bigrat: exact at magnitudes where Int32 Rat silently overflows" {
  // Each factor individually fits Int32, but accumulating products of
  // several large-ish rationals the way a determinant/resultant expansion
  // does pushes `Rat`'s Int32 numerator/denominator past 2^31-1 even after
  // gcd-cancellation — `rat_mul`'s `rat_make` wraps silently there, while
  // `BigRat` stays exact (and visibly says so via `rat_of_bigrat is None`).
  let factors : Array[Rat] = [
    rat_make(46337, 1),
    rat_make(46337, 1),
    rat_make(46337, 1),
    rat_make(46337, 1),
  ] // 46337 ~ sqrt(2^31): the first two already overflow Int32 once
  // multiplied (46337^2 = 2147132769, fine; ^3 overflows).
  let mut acc_big = bigrat_one()
  for i in 0..<factors.length() {
    acc_big = bigrat_mul(acc_big, bigrat_of_rat(factors[i]))
  }
  // BigRat computed the true product exactly: 46337^4.
  inspect(bigrat_to_string(acc_big), content="4610113855108469761")
  // That value overflows Int32 (and indeed Int64 numerator range is fine,
  // but the point generalises: Rat's num/den are Int32, and
  // 4610113855108469761 itself already overflows Int32 by a wide margin)
  // — the bridge back to `Rat` correctly reports this as unrepresentable
  // instead of wrapping.
  inspect(rat_of_bigrat(acc_big) is None, content="true")
  // Meanwhile naively chaining the same multiplications through `Rat`
  // wraps/overflows Int32 silently and does NOT raise any error — this is
  // the exact failure mode BigRat exists to avoid. We don't assert a
  // specific wrapped value (wrapping behaviour is only "whatever Int32
  // multiplication does"), only that it disagrees with the true value,
  // demonstrating the unsoundness BigRat fixes.
  let mut acc_small = rat_one()
  for i in 0..<factors.length() {
    acc_small = rat_mul(acc_small, factors[i])
  }
  inspect(acc_small.num.to_int64() != 4610113855108469761L, content="true")
}
