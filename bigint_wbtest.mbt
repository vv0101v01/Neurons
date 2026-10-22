///|
// Whitebox tests for exact signed integer arithmetic (sign-magnitude over
// `BigNat`), the signed layer under item 9(d)'s planned `BigRat`.

///|
test "bigint: construction, sign and decimal rendering" {
  inspect(bigint_to_string(bigint_zero()), content="0")
  inspect(bigint_is_zero(bigint_zero()), content="true")
  inspect(bigint_sign(bigint_zero()), content="0")
  inspect(bigint_to_string(bigint_of_int(42)), content="42")
  inspect(bigint_sign(bigint_of_int(42)), content="1")
  inspect(bigint_to_string(bigint_of_int(-42)), content="-42")
  inspect(bigint_sign(bigint_of_int(-42)), content="-1")
  // Negating zero stays zero (sign is canonically 0, not -0).
  inspect(bigint_neg(bigint_zero()) == bigint_zero(), content="true")
  inspect(bigint_of_int(5) == bigint_of_int(5), content="true")
  inspect(bigint_of_int(5) == bigint_of_int(-5), content="false")
  // Absolute value strips the sign down to the BigNat magnitude.
  inspect(bigint_abs(bigint_of_int(-7)) == bignat_of_int(7), content="true")
  inspect(bigint_abs(bigint_of_int(7)) == bignat_of_int(7), content="true")
  inspect(bigint_abs(bigint_zero()) == bignat_of_int(0), content="true")
}

///|
test "bigint: addition and subtraction match Int64 arithmetic" {
  let cases : Array[(Int64, Int64)] = [
    (5L, 3L),
    (3L, 5L),
    (-5L, 3L),
    (5L, -3L),
    (-5L, -3L),
    (0L, 7L),
    (7L, 0L),
    (0L, 0L),
    (1000000000000L, 999999999999L),
    (-1000000000000L, 999999999999L),
  ]
  for i in 0..<cases.length() {
    let (a, b) = cases[i]
    let bia = if a >= 0L {
      bigint_of_bignat(bignat_of_int64(a))
    } else {
      bigint_neg(bigint_of_bignat(bignat_of_int64(0L - a)))
    }
    let bib = if b >= 0L {
      bigint_of_bignat(bignat_of_int64(b))
    } else {
      bigint_neg(bigint_of_bignat(bignat_of_int64(0L - b)))
    }
    inspect(bigint_to_string(bigint_add(bia, bib)), content=(a + b).to_string())
    inspect(bigint_to_string(bigint_sub(bia, bib)), content=(a - b).to_string())
  }
}

///|
test "bigint: multiplication, comparison, gcd and divmod" {
  inspect(
    bigint_to_string(bigint_mul(bigint_of_int(-7), bigint_of_int(6))),
    content="-42",
  )
  inspect(
    bigint_to_string(bigint_mul(bigint_of_int(-7), bigint_of_int(-6))),
    content="42",
  )
  inspect(bigint_lt(bigint_of_int(-5), bigint_of_int(-3)), content="true")
  inspect(bigint_lt(bigint_of_int(-3), bigint_of_int(-5)), content="false")
  inspect(bigint_lt(bigint_of_int(-1), bigint_of_int(1)), content="true")
  inspect(bigint_cmp(bigint_of_int(0), bigint_of_int(0)), content="0")
  // gcd ignores sign.
  inspect(
    bigint_to_string(bigint_gcd(bigint_of_int(-48), bigint_of_int(18))),
    content="6",
  )
  // Truncating divmod: matches Int32's `/`/`%` sign convention.
  let (q1, r1) = bigint_divmod(bigint_of_int(7), bigint_of_int(2))
  inspect(bigint_to_string(q1), content="3")
  inspect(bigint_to_string(r1), content="1")
  let (q2, r2) = bigint_divmod(bigint_of_int(-7), bigint_of_int(2))
  inspect(bigint_to_string(q2), content="-3")
  inspect(bigint_to_string(r2), content="-1")
  let (q3, r3) = bigint_divmod(bigint_of_int(7), bigint_of_int(-2))
  inspect(bigint_to_string(q3), content="-3")
  inspect(bigint_to_string(r3), content="1")
  // x = q*y + r, for every sign combination above.
  inspect(
    bigint_add(bigint_mul(q1, bigint_of_int(2)), r1) == bigint_of_int(7),
    content="true",
  )
  inspect(
    bigint_add(bigint_mul(q2, bigint_of_int(2)), r2) == bigint_of_int(-7),
    content="true",
  )
  inspect(
    bigint_add(bigint_mul(q3, bigint_of_int(-2)), r3) == bigint_of_int(7),
    content="true",
  )
}

///|
test "bigint: values far beyond Int64 stay exact" {
  // 30! as a signed BigInt, negated, doubled back.
  let huge = bigint_of_bignat(bignat_fact(30))
  inspect(bigint_to_string(huge), content="265252859812191058636308480000000")
  let neg_huge = bigint_neg(huge)
  inspect(
    bigint_to_string(neg_huge),
    content="-265252859812191058636308480000000",
  )
  inspect(bigint_add(huge, neg_huge) == bigint_zero(), content="true")
  inspect(bigint_to_int64(huge) is None, content="true") // overflows Int64
  inspect(
    bigint_to_string(bigint_mul(neg_huge, bigint_of_int(-1))) ==
    bigint_to_string(huge),
    content="true",
  )
}
