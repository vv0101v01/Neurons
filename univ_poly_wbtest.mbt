///|
// Whitebox tests for first-class universe-polymorphic declarations and
// primitive mutual declarations (SPEC §四 item 1a/1b).

///|
test "univ poly: dlevel_var encodes body-level level slots" {
  inspect(dlevel_var(0), content="-1")
  inspect(dlevel_var(1), content="-2")
  match dlevel_unwrap(dlevel_var(3)) {
    Some(v) => inspect(v, content="3")
    None => inspect(false, content="true")
  }
  inspect(dlevel_unwrap(0) is None, content="true")
  inspect(dlevel_unwrap(7) is None, content="true")
}

///|
test "univ poly: ListU as abstract syntax agrees with the host-level scheme" {
  let decl = list_univ_poly_decl()
  inspect(duniv_poly_validate(decl), content="true")
  // the first-class declaration and the host closure describe the same
  // schema at every level — equality of the instantiated data
  for l in 0..<5 {
    inspect(
      duniv_poly_agrees_with_scheme(decl, list_level_scheme(), [l]),
      content="true",
    )
  }
  match duniv_poly_instantiate(decl, [1]) {
    Some(spec) => {
      inspect(spec.name, content="ListU")
      inspect(spec.level, content="1")
      inspect(spec.params.length(), content="1")
      inspect(spec.constructors.length(), content="2")
    }
    None => inspect(false, content="true")
  }
  // instantiating twice is deterministic (data, not a closure)
  inspect(
    duniv_poly_instantiate(decl, [2]) == duniv_poly_instantiate(decl, [2]),
    content="true",
  )
}

///|
test "univ poly: CircleU (HIT) agrees with the host-level scheme" {
  let decl = circle_univ_poly_decl()
  inspect(duniv_poly_hit_validate(decl), content="true")
  for l in 0..<3 {
    inspect(
      duniv_poly_hit_agrees_with_scheme(decl, circle_level_scheme(), [l]),
      content="true",
    )
  }
  // The explicit-pool constructor rebuilds the same declaration as data.
  let rebuilt = duniv_poly_hit_decl_with_levels(
    "CircleU",
    1,
    dlevel_identity_pool(1),
    DLevelVar(0),
    decl.template,
  )
  inspect(rebuilt == decl, content="true")
  inspect(
    duniv_poly_hit_agrees_with_scheme(rebuilt, circle_level_scheme(), [2]),
    content="true",
  )
}

///|
test "univ poly: declarations are comparable data (Eq is structural)" {
  inspect(list_univ_poly_decl() == list_univ_poly_decl(), content="true")
  // the HIT declaration is a different type of data, and different
  // names make different declarations
  let other = duniv_poly_decl(
    "OtherU",
    1,
    DLevelVar(0),
    dinductive_spec("OtherU", dlevel_var(0), [], [], [
      dconstructor_spec("mk", []),
    ]),
  )
  inspect(list_univ_poly_decl() == other, content="false")
  // a declaration at succ ℓ is a different declaration
  let succ_decl = duniv_poly_decl(
    "ListU",
    1,
    DLevelSucc(DLevelVar(0)),
    dinductive_spec("ListU", dlevel_var(0), [], [], [
      dconstructor_spec("nil", []),
    ]),
  )
  inspect(list_univ_poly_decl() == succ_decl, content="false")
}

///|
test "univ poly: ill-formed declarations and vectors are refused" {
  // wrong arity
  inspect(
    duniv_poly_instantiate(list_univ_poly_decl(), [0, 0]) is None,
    content="true",
  )
  // negative level
  inspect(
    duniv_poly_instantiate(list_univ_poly_decl(), [-1]) is None,
    content="true",
  )
  // template refers to a pool slot out of range
  let bad = duniv_poly_decl(
    "BadU",
    1,
    DLevelVar(0),
    dinductive_spec("BadU", dlevel_var(5), [], [], [dconstructor_spec("mk", [])]),
  )
  inspect(duniv_poly_validate(bad), content="false")
  inspect(duniv_poly_instantiate(bad, [0]) is None, content="true")
  // template name mismatch
  let renamed = duniv_poly_decl(
    "Other",
    1,
    DLevelVar(0),
    dinductive_spec("ListU", dlevel_var(0), [], [], [
      dconstructor_spec("mk", []),
    ]),
  )
  inspect(duniv_poly_validate(renamed), content="false")
  // result level uses a variable beyond the arity
  let bad_level = duniv_poly_decl(
    "BadL",
    1,
    DLevelVar(2),
    dinductive_spec("BadL", dlevel_var(0), [], [], [dconstructor_spec("mk", [])]),
  )
  inspect(duniv_poly_validate(bad_level), content="false")
  // a pool entry mentioning an out-of-range variable
  let bad_pool = duniv_poly_decl_with_levels(
    "BadP",
    1,
    [DLevelSucc(DLevelVar(3))],
    DLevelVar(0),
    dinductive_spec("BadP", dlevel_var(0), [], [], [dconstructor_spec("mk", [])]),
  )
  inspect(duniv_poly_validate(bad_pool), content="false")
}

///|
test "univ poly: compound levels in body positions (partial polymorphism)" {
  // A pool entry may be any level expression: the family lives at
  // max(1, ℓ), and body positions referencing slot 0 see exactly that.
  let pool = [DLevelMax(DLevelConst(1), DLevelVar(0))]
  let l0 = dlevel_var(0)
  let decl = duniv_poly_decl_with_levels(
    "BoundedU",
    1,
    pool,
    DLevelMax(DLevelConst(1), DLevelVar(0)),
    dinductive_spec("BoundedU", l0, [dtelescope_entry("A", DUniv(l0))], [], [
      dconstructor_spec("mk", [darg_external("x", DTVar(0))]),
    ]),
  )
  inspect(duniv_poly_validate(decl), content="true")
  match duniv_poly_instantiate(decl, [0]) {
    Some(spec) =>
      // max(1, 0) = 1 — the compound level computed into the body
      inspect(spec.level, content="1")
    None => inspect(false, content="true")
  }
  match duniv_poly_instantiate(decl, [3]) {
    Some(spec) => inspect(spec.level, content="3")
    None => inspect(false, content="true")
  }
}

///|
test "mutual decl: the primitive block compiles and matches its elaboration" {
  let decl = dmutual_decl("EvenOddS", even_odd_components())
  inspect(dmutual_decl_validate(decl), content="true")
  match dmutual_decl_compile(decl) {
    Some(fam) => {
      inspect(fam.name, content="EvenOddS")
      inspect(dmutual_decl_matches_family(decl, fam), content="true")
      // the same elaboration the direct compilation entry produces
      inspect(fam.combined.constructors.length(), content="3")
    }
    None => inspect(false, content="true")
  }
  let tf = dmutual_decl("TreeForestS", tree_forest_components())
  inspect(dmutual_decl_validate(tf), content="true")
  match dmutual_decl_compile(tf) {
    Some(fam) => inspect(dmutual_decl_matches_family(tf, fam), content="true")
    None => inspect(false, content="true")
  }
  // declaration equality is structural
  inspect(
    dmutual_decl("EvenOddS", even_odd_components()) == decl,
    content="true",
  )
}

///|
test "mutual decl: ill-formed blocks are refused at the declaration" {
  // empty block
  inspect(dmutual_decl_validate(dmutual_decl("Empty", [])), content="false")
  // duplicate component names
  let dup = dmutual_decl("Dup", [
    dinductive_spec("Same", 0, [], [], [dconstructor_spec("mk", [])]),
    dinductive_spec("Same", 0, [], [], [dconstructor_spec("mk2", [])]),
  ])
  inspect(dmutual_decl_validate(dup), content="false")
  // mismatched telescopes
  let mixed = dmutual_decl("Mixed", [
    dinductive_spec("A", 0, [dtelescope_entry("p", DUnitTy)], [], [
      dconstructor_spec("mk", []),
    ]),
    dinductive_spec("B", 0, [], [], [dconstructor_spec("mk", [])]),
  ])
  inspect(dmutual_decl_validate(mixed), content="false")
  // cross-reference outside the block
  let wild = dmutual_decl("Wild", [
    dinductive_spec("W", 0, [], [], [
      dconstructor_spec("mk", [
        DConstructorArg::{
          name: "x",
          kind: DArgRecursive,
          ty: DUnitTy,
          index: [],
          nested: DFunctorIdentity([]),
          target: 5,
        },
      ]),
    ]),
  ])
  inspect(dmutual_decl_validate(wild), content="false")
  // induction-recursive components are outside the mutual fragment
  let ir = dmutual_decl("IR", [
    dinductive_recursive_spec(
      "C",
      0,
      [],
      [],
      [dconstructor_spec("mk", [darg_decoded("d", 0)])],
      [DUnitTy],
    ),
  ])
  inspect(dmutual_decl_validate(ir), content="false")
}
