///|
// Whitebox tests for refactor certificates.

///|
test "refactor certificate: a move is an interface equivalence" {
  // the same names in a different order: a non-trivial permutation
  let plan = plan_of_ordered("reorder", ["b", "a", "c"], ["c", "b", "a"])
  inspect(plan is Some(_), content="true")
  match plan {
    None => inspect(false, content="true")
    Some(p) => {
      inspect(plan_preserves_symbol_set(p), content="true")
      inspect(refactor_is_equivalence(p), content="true")
      inspect(plan_agrees_with_univalence(p), content="true")
      inspect(certify(p) is Some(_), content="true")
    }
  }
}

///|
test "refactor certificate: loss and renaming are rejected" {
  inspect(plan_of_ordered("lossy", ["a", "b"], ["a"]) is None, content="true")
  inspect(plan_of_ordered("invent", ["a"], ["a", "b"]) is None, content="true")
  let mislabelled = refactor_plan(
    "mislabelled",
    ["a", "b"],
    ["b", "a"],
    index_table_identity(2),
  )
  inspect(refactor_is_equivalence(mislabelled), content="false")
  inspect(certify(mislabelled) is None, content="true")
  // a table that is not a permutation is rejected even when names line up
  let bad_table = refactor_plan(
    "dup",
    ["a", "b"],
    ["a", "b"],
    index_table([0, 0]),
  )
  inspect(refactor_is_equivalence(bad_table), content="false")
}

///|
test "refactor certificate: transport of verdicts round-trips" {
  let plan = plan_of_ordered("reorder", ["a", "b", "c", "d"], [
    "d", "c", "b", "a",
  ])
  match plan {
    None => inspect(false, content="true")
    Some(p) =>
      match certify(p) {
        None => inspect(false, content="true")
        Some(cert) => {
          // verdicts: specification-family ids per symbol
          let families = [7, 3, 9, 1]
          inspect(
            certificate_transport_roundtrip(cert, families),
            content="true",
          )
          // the transport really moves the entries (a != reverse(a) here)
          let fwd = certificate_transport_int(cert, families)
          inspect(fwd[0], content="1")
          inspect(fwd[3], content="7")
        }
      }
  }
}

///|
test "refactor certificate: identities, inverses and composition" {
  let id = refactor_plan("id", ["a", "b"], ["a", "b"], index_table_identity(2))
  match certify(id) {
    None => inspect(false, content="true")
    Some(c) => inspect(certificate_is_identity(c), content="true")
  }
  let p = plan_of_ordered("reorder", ["a", "b", "c"], ["c", "a", "b"])
  let q = plan_of_ordered("reorder2", ["c", "a", "b"], ["a", "b", "c"])
  match (p, q) {
    (Some(p1), Some(q1)) =>
      match (certify(p1), certify(q1)) {
        (Some(cp), Some(cq)) => {
          // p ; p⁻¹ = refl
          inspect(
            certificate_is_identity_option_for_test(cp, certificate_inverse(cp)),
            content="true",
          )
          // composition of the two reorderings is the identity
          match certificate_compose(cp, cq) {
            None => inspect(false, content="true")
            Some(cc) => inspect(certificate_is_identity(cc), content="true")
          }
        }
        _ => inspect(false, content="true")
      }
    _ => inspect(false, content="true")
  }
}

///|
fn certificate_is_identity_option_for_test(
  a : RefactorCertificate,
  b : RefactorCertificate?,
) -> Bool {
  match b {
    None => false
    Some(bb) =>
      match certificate_compose(a, bb) {
        None => false
        Some(c) => certificate_is_identity(c)
      }
  }
}

///|
test "refactor certificate: pulling back to the finite universe agrees with univalence" {
  // sizes 1..6 exercise the padding to the next power of two
  let pairs : Array[(Array[String], Array[String])] = [
    (["a"], ["a"]),
    (["a", "b"], ["b", "a"]),
    (["a", "b", "c"], ["c", "b", "a"]),
    (["a", "b", "c", "d"], ["d", "a", "c", "b"]),
    (["a", "b", "c", "d", "e"], ["e", "d", "c", "b", "a"]),
    (["a", "b", "c", "d", "e", "f"], ["f", "a", "e", "b", "d", "c"]),
  ]
  for i in 0..<pairs.length() {
    match plan_of_ordered("reorder", pairs[i].0, pairs[i].1) {
      None => inspect(false, content="true")
      Some(p) => {
        inspect(refactor_is_equivalence(p), content="true")
        // the bijection test agrees with fin_map_is_equiv on the padded type
        inspect(plan_agrees_with_univalence(p), content="true")
        match plan_to_fin_map(p) {
          None => inspect(false, content="true")
          Some(m) => inspect(fin_map_is_equiv(m), content="true")
        }
      }
    }
  }
  inspect(next_pow2(5), content="8")
  inspect(log2_int(8), content="3")
}

///|
test "refactor certificate: the decoupling surgery is certified" {
  inspect(decoupling_steps().length(), content="8")
  inspect(decoupling_certified(), content="true")
  inspect(decoupling_conserves_names(), content="true")
  inspect(refactor_certificates_sound(), content="true")
}
