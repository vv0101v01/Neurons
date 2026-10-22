///|
// Propositional truncation `∥A∥`: the generic HIT schema generator
// applied to the `dhit_face_var` capability added in schema.mbt (SPEC §四
// item 3's propositional-truncation gap).
//
// `∥A∥` has two constructors: `point : A → ∥A∥` (written `∣_∣` in the
// HoTT book) and `squash : ∀ x y : ∥A∥. x ≡ y`.  The latter's two path
// endpoints are *squash's own two arguments*, not an instantiation of
// some other, already-defined cell — exactly the case the previous
// `DHitFaceExpr{cell,args,dims}` representation could not express (it
// could only say "this face is cell C instantiated at these arguments",
// never "this face is my own k-th argument").  `dhit_face_var` closes
// that gap by giving `cell` a reserved sentinel value meaning "evaluate
// this argument directly", so `squash`'s two faces are simply
// `dhit_face_var(0, 2)` and `dhit_face_var(1, 2)`.
//
// Scope: this is the structural shape of propositional truncation (two
// constructors, well-formed and type-checked, with the Kan/elimination
// machinery any generic HIT schema already gets — conversion, quoting,
// dependent elimination dispatch, hcomp). It does not separately prove
// `∥A∥` is itself a strict proposition in the ambient type theory (that
// `isProp(∥A∥)` would follow from `squash` definitionally, an
// extensional fact about *all* cubical fillers of `∥A∥`, not a single
// schema-level checkable predicate) — the generic HIT layer does not
// claim any such global coherence theorem for any of its other examples
// (Circle, Torus, Susp) either.

///|
fn ptrunc_schema_unchecked(name : String) -> DHitSpec {
  dhit_spec(name, 0, [dtelescope_entry("A", DUniv(0))], [], [
    dhit_cell_spec("point", 0, [darg_external("a", DTVar(0))], []),
    dhit_cell_spec("squash", 1, [darg_recursive("x"), darg_recursive("y")], [
      dhit_face_var(0, 2),
      dhit_face_var(1, 2),
    ]),
  ])
}

///|
/// The generated propositional truncation of a single `Type₀` parameter
/// `A`.  `None` only if `name` is empty or the generic HIT well-formedness
/// check somehow rejects the schema (it should not — this function exists
/// so a change elsewhere in the schema layer that silently broke this
/// shape would show up as a `None` here, not as a crash).
pub fn ptrunc_schema(name : String) -> DHitSpec? {
  if name.length() == 0 {
    return None
  }
  let out = ptrunc_schema_unchecked(name)
  if hit_schema_validate(out) {
    Some(out)
  } else {
    None
  }
}

///|
/// The canonical propositional truncation schema, named `"Squash"`.
pub fn squash_schema() -> DHitSpec {
  ptrunc_schema_unchecked("Squash")
}

///|
pub fn squash_type_term() -> DTerm {
  DHitType(squash_schema(), [DTVar(0)])
}

///|
pub fn squash_type_value(a_ty : DValue) -> DValue {
  DVHitType(squash_schema(), [a_ty], [])
}

///|
/// `∣ a ∣ : ∥A∥`, the point constructor (`a_ty` is the parameter `A`).
pub fn squash_point_value(a_ty : DValue, a : DValue) -> DValue {
  DVHitCell(squash_schema(), 0, [a_ty], [a], [])
}

///|
/// `squash x y @ dim : ∥A∥`, the path constructor: at `dim = 0` it
/// reduces (via the generic HIT cell smart constructor, exercising
/// `dhit_face_var`'s evaluation rule in `hit_face_instantiate`) to `x`
/// itself, and at `dim = 1` to `y` itself.
pub fn squash_path_value(
  a_ty : DValue,
  x : DValue,
  y : DValue,
  dim : Dim,
) -> DValue {
  hit_cell_value(squash_schema(), 1, [a_ty], [x, y], [dim])
}
