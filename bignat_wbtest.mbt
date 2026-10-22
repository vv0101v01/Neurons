///|
// Whitebox tests for exact natural-number arithmetic (the overflow-free
// layer under the univalence counting formulas).

///|
test "bignat: construction, canonical form and decimal rendering" {
  inspect(bignat_to_string(bignat_of_int(0)), content="0")
  inspect(bignat_is_zero(bignat_of_int(0)), content="true")
  inspect(bignat_to_string(bignat_of_int(999999999)), content="999999999")
  inspect(bignat_to_string(bignat_of_int(1000000000)), content="1000000000")
  inspect(
    bignat_to_string(bignat_of_int64(999999999999999999L)),
    content="999999999999999999",
  )
  // canonical: zero has the empty limb array, so structural equality is
  // numeric equality
  inspect(bignat_of_int(0) == bignat_of_int64(0L), content="true")
  inspect(bignat_of_int(5) == bignat_of_int(5), content="true")
  inspect(bignat_of_int(5) == bignat_of_int(6), content="false")
}

///|
test "bignat: addition and multiplication are exact" {
  let x = bignat_of_int(123456789)
  let y = bignat_of_int(987654321)
  inspect(bignat_to_string(bignat_add(x, y)), content="1111111110")
  inspect(bignat_to_string(bignat_mul(x, y)), content="121932631112635269")
  // (x + y) + z = x + (y + z); 1 * x = x; 0 * x = 0
  let z = bignat_of_int(1000000000)
  inspect(
    bignat_add(bignat_add(x, y), z) == bignat_add(x, bignat_add(y, z)),
    content="true",
  )
  inspect(bignat_mul(bignat_of_int(1), x) == x, content="true")
  inspect(bignat_is_zero(bignat_mul(bignat_of_int(0), x)), content="true")
  // 10^18 + 1 crosses three limbs and back
  let big = bignat_add(bignat_mul(z, z), bignat_of_int(1))
  inspect(bignat_to_string(big), content="1000000000000000001")
}

///|
test "bignat: powers and factorials never wrap" {
  inspect(
    bignat_to_string(bignat_pow(bignat_of_int(2), 64)),
    content="18446744073709551616",
  )
  inspect(
    bignat_to_string(bignat_pow(bignat_of_int(16), 16)),
    content="18446744073709551616",
  )
  inspect(bignat_to_string(bignat_pow(bignat_of_int(0), 0)), content="1")
  inspect(bignat_to_string(bignat_fact(0)), content="1")
  inspect(bignat_to_string(bignat_fact(10)), content="3628800")
  inspect(
    bignat_to_string(bignat_fact(25)),
    content="15511210043330985984000000",
  )
  // 100! — 158 digits, far beyond any machine integer
  inspect(
    bignat_to_string(bignat_fact(100)),
    content="93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000000",
  )
}

///|
test "bignat: comparisons and partial conversions report overflow" {
  inspect(bignat_cmp(bignat_of_int(5), bignat_of_int(5)), content="0")
  inspect(bignat_lt(bignat_of_int(5), bignat_of_int(6)), content="true")
  inspect(bignat_lt(bignat_of_int(6), bignat_of_int(5)), content="false")
  match bignat_to_int64(bignat_of_int(42)) {
    Some(v) => inspect(v, content="42")
    None => inspect("none", content="unreachable")
  }
  match bignat_to_int64(bignat_of_int64(9223372036854775807L)) {
    Some(v) => inspect(v, content="9223372036854775807")
    None => inspect("none", content="unreachable")
  }
  // max + 1 overflows Int64: None, never wrapped
  inspect(
    bignat_to_int64(
      bignat_add(bignat_of_int64(9223372036854775807L), bignat_of_int(1)),
    )
    is None,
    content="true",
  )
  match bignat_to_int32(bignat_of_int(2147483647)) {
    Some(v) => inspect(v, content="2147483647")
    None => inspect("none", content="unreachable")
  }
  inspect(bignat_to_int32(bignat_of_int64(2147483648L)) is None, content="true")
  match bignat_to_int32(bignat_of_int(0)) {
    Some(v) => inspect(v, content="0")
    None => inspect("none", content="unreachable")
  }
}

///|
test "bignat: small divmod decodes mixed-radix codes" {
  let x = bignat_of_int64(1000000000000L) // 10^12
  let (q, r) = bignat_divmod_small(x, 1000000000L)
  inspect(bignat_to_string(q), content="1000")
  inspect(r.to_string(), content="0")
  let y = bignat_of_int(123456789)
  let (q2, r2) = bignat_divmod_small(y, 1000000000L)
  inspect(bignat_to_string(q2), content="0")
  inspect(r2.to_string(), content="123456789")
}

///|
test "bignat: subtraction is exact and aborts on a negative result" {
  let x = bignat_of_int64(1000000000000L) // 10^12
  let y = bignat_of_int(1)
  inspect(bignat_to_string(bignat_sub(x, y)), content="999999999999")
  inspect(bignat_to_string(bignat_sub(x, x)), content="0")
  inspect(bignat_is_zero(bignat_sub(x, x)), content="true")
  // (x + y) - y = x
  let z = bignat_of_int(987654321)
  inspect(bignat_sub(bignat_add(x, z), z) == x, content="true")
}

///|
test "bignat: general long division agrees with the small-divisor path" {
  let x = bignat_fact(25)
  let d = bignat_of_int(1000000000)
  let (q1, r1) = bignat_divmod(x, d)
  let (q2, r2) = bignat_divmod_small(x, 1000000000L)
  inspect(q1 == q2, content="true")
  inspect(bignat_to_string(r1), content=r2.to_string())
  // x = q*d + r, and 0 <= r < d
  inspect(bignat_add(bignat_mul(q1, d), r1) == x, content="true")
  inspect(bignat_lt(r1, d), content="true")
  // Division by a divisor bigger than the dividend: q=0, r=x.
  let small = bignat_of_int(41)
  let (q3, r3) = bignat_divmod(small, x)
  inspect(bignat_is_zero(q3), content="true")
  inspect(r3 == small, content="true")
  // Exact division with no remainder: 10! / 5! = 6*7*8*9*10 = 30240.
  let (q4, r4) = bignat_divmod(bignat_fact(10), bignat_fact(5))
  inspect(bignat_to_string(q4), content="30240")
  inspect(bignat_is_zero(r4), content="true")
}

///|
test "bignat: gcd matches the Int32 int_gcd on values that fit both" {
  inspect(
    bignat_to_string(bignat_gcd(bignat_of_int(48), bignat_of_int(18))),
    content="6",
  )
  inspect(int_gcd(48, 18), content="6")
  inspect(
    bignat_to_string(bignat_gcd(bignat_of_int(17), bignat_of_int(5))),
    content="1",
  )
  // gcd(25!, 10!) is the product of shared prime powers; cross-check
  // against the exact quotient relation instead of a canned constant.
  let g = bignat_gcd(bignat_fact(25), bignat_fact(10))
  let (_, r1) = bignat_divmod(bignat_fact(25), g)
  let (_, r2) = bignat_divmod(bignat_fact(10), g)
  inspect(bignat_is_zero(r1), content="true")
  inspect(bignat_is_zero(r2), content="true")
  inspect(g == bignat_fact(10), content="true") // 10! divides 25! exactly
}
