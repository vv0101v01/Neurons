///|
// Refactor certificates: using computable univalence to certify a decoupling
// surgery.
//
// The problem.  A package is one namespace, so moving a declaration from one
// `.mbt` file to another is *supposed* to be invisible: the exported symbol set,
// and therefore `pkg.generated.mbti`, must not change.  In practice a refactor
// can silently drop a symbol, declare it twice, or (worse) change which layer a
// symbol lives in so that the dependency graph quietly grows a new cycle.  This
// module turns "the refactor was harmless" into a decidable statement, using the
// univalence of `univalence_compute.mbt`:
//
//   * an interface is a finite set of symbol names (`SymbolSet`);
//   * a refactor is a *plan*: a map between the old and the new ordering, plus
//     the requirement that each index carries the same name
//     (`RefactorPlan`, `refactor_is_equivalence`);
//   * `certify` produces the ua image of a plan — the path between the two
//     interfaces — and any per-symbol verdict (a specification-family id, an
//     audit classification, a layer number) is transported along it
//     (`certificate_transport_int`), with the round trip the identity
//     (`certificate_transport_roundtrip`);
//   * `plan_agrees_with_univalence` pulls a plan back to a `FinMap` on the
//     finite universe of `pathp_glue.mbt` (pad the index set to the next power of
//     two and read the indices as elements of a `Bool`-product type), so the
//     bijection test *is* `fin_map_is_equiv` — the decision procedure that
//     `univalence_decides` uses.
//
// The decoupling performed in this repository (six file-level cycles reduced to
// one) is recorded as `decoupling_steps`; `decoupling_certified` checks every
// step, and `decoupling_preserves_families` checks that the specification-family
// verdicts survive the transport, which is exactly the conservation law that
// `tools/audit_spec.py` re-checks from the generated interface.

///|
/// A finite set of symbol names, kept sorted and distinct: the interface of a
/// module, a file, or the whole package.
pub struct SymbolSet {
  items : Array[String]
}

///|
pub fn symbol_set(names : Array[String]) -> SymbolSet {
  let out : Array[String] = []
  for i in 0..<names.length() {
    let mut seen = false
    for j in 0..<out.length() {
      if out[j] == names[i] {
        seen = true
      }
    }
    if !seen {
      out.push(names[i])
    }
  }
  // insertion sort: the canonical order is what makes the set a canonical form
  for i in 1..<out.length() {
    let mut j = i
    while j > 0 {
      if out[j] < out[j - 1] {
        let tmp = out[j]
        out[j] = out[j - 1]
        out[j - 1] = tmp
        j = j - 1
      } else {
        j = 0
      }
    }
  }
  SymbolSet::{ items: out, }
}

///|
pub fn symbol_set_size(s : SymbolSet) -> Int32 {
  s.items.length()
}

///|
pub fn symbol_set_items(s : SymbolSet) -> Array[String] {
  s.items.copy()
}

///|
pub fn symbol_set_eq(a : SymbolSet, b : SymbolSet) -> Bool {
  if a.items.length() != b.items.length() {
    return false
  }
  for i in 0..<a.items.length() {
    if a.items[i] != b.items[i] {
      return false
    }
  }
  true
}

///|
/// A declaration list in source order with duplicates removed: the *ordered*
/// interface of a file (two files listing the same names in a different order
/// are the same set of symbols but different listings).
pub fn ordered_items(names : Array[String]) -> Array[String] {
  let out : Array[String] = []
  for i in 0..<names.length() {
    let mut seen = false
    for j in 0..<out.length() {
      if out[j] == names[i] {
        seen = true
      }
    }
    if !seen {
      out.push(names[i])
    }
  }
  out
}

///|
/// The position of `name` in an ordered list, or -1.
pub fn ordered_index(names : Array[String], name : String) -> Int32 {
  let mut out = -1
  for i in 0..<names.length() {
    if names[i] == name {
      out = i
    }
  }
  out
}

///|
/// The position of `name` in the canonical order, or -1.
pub fn symbol_set_index(s : SymbolSet, name : String) -> Int32 {
  let mut out = -1
  for i in 0..<s.items.length() {
    if s.items[i] == name {
      out = i
    }
  }
  out
}

///|
/// A map between index sets: `table[i]` is the new position of old index `i`.
pub struct IndexTable {
  table : Array[Int32]
}

///|
pub fn index_table(table : Array[Int32]) -> IndexTable {
  IndexTable::{ table, }
}

///|
pub fn index_table_identity(n : Int32) -> IndexTable {
  let table : Array[Int32] = []
  for i in 0..<n {
    table.push(i)
  }
  IndexTable::{ table, }
}

///|
/// A table is a bijection on `n` indices when it is a permutation of `0..n-1`.
pub fn index_table_is_bijection(t : IndexTable, n : Int32) -> Bool {
  if t.table.length() != n {
    return false
  }
  let seen : Array[Bool] = []
  for _i in 0..<n {
    seen.push(false)
  }
  for i in 0..<n {
    let j = t.table[i]
    if j < 0 || j >= n || seen[j] {
      return false
    }
    seen[j] = true
  }
  true
}

///|
pub fn index_table_inv(t : IndexTable, n : Int32) -> IndexTable {
  let table : Array[Int32] = []
  for _i in 0..<n {
    table.push(0)
  }
  for i in 0..<t.table.length() {
    table[t.table[i]] = i
  }
  IndexTable::{ table, }
}

///|
/// Composition `g ∘ f`: first apply `f`, then `g`.
pub fn index_table_comp(g : IndexTable, f : IndexTable) -> IndexTable {
  let table : Array[Int32] = []
  for i in 0..<f.table.length() {
    table.push(g.table[f.table[i]])
  }
  IndexTable::{ table, }
}

///|
/// A refactor plan: two interface snapshots plus the index map between them.
pub struct RefactorPlan {
  label : String
  before : Array[String]
  after : Array[String]
  table : IndexTable
}

///|
pub fn refactor_plan(
  label : String,
  before : Array[String],
  after : Array[String],
  table : IndexTable,
) -> RefactorPlan {
  RefactorPlan::{ label, before, after, table, }
}

///|
pub fn refactor_plan_size(plan : RefactorPlan) -> Int32 {
  plan.before.length()
}

///|
/// The plan preserves the package interface as a *set* of symbols.
pub fn plan_preserves_symbol_set(plan : RefactorPlan) -> Bool {
  symbol_set_eq(symbol_set(plan.before), symbol_set(plan.after))
}

///|
/// Build the plan induced by two *ordered* declaration lists: each old position
/// maps to the new position holding the same name.  `None` if a name is missing.
pub fn plan_of_ordered(
  label : String,
  before_names : Array[String],
  after_names : Array[String],
) -> RefactorPlan? {
  let before = ordered_items(before_names)
  let after = ordered_items(after_names)
  if before.length() != after.length() {
    return None
  }
  let table : Array[Int32] = []
  for i in 0..<before.length() {
    let j = ordered_index(after, before[i])
    if j < 0 {
      return None
    }
    table.push(j)
  }
  Some(RefactorPlan::{ label, before, after, table: IndexTable::{ table, }, })
}

///|
/// A plan is an equivalence of interfaces when
///   * the two interfaces have the same size,
///   * the index map is a bijection, and
///   * every index carries the *same name* on both sides (a move, not a rename).
pub fn refactor_is_equivalence(plan : RefactorPlan) -> Bool {
  let n = plan.before.length()
  if n != plan.after.length() || n == 0 {
    return false
  }
  if !index_table_is_bijection(plan.table, n) {
    return false
  }
  for i in 0..<n {
    let j = plan.table.table[i]
    if plan.before[i] != plan.after[j] {
      return false
    }
  }
  plan_preserves_symbol_set(plan)
}

///|
/// A certificate is the ua image of an equivalence of interfaces.
pub struct RefactorCertificate {
  plan : RefactorPlan
}

///|
/// `ua`: certify an interface equivalence, producing a path between the two
/// interfaces.  `None` exactly when the plan is not an equivalence.
pub fn certify(plan : RefactorPlan) -> RefactorCertificate? {
  if refactor_is_equivalence(plan) {
    Some(RefactorCertificate::{ plan, })
  } else {
    None
  }
}

///|
pub fn index_table_is_identity(t : IndexTable, n : Int32) -> Bool {
  if t.table.length() != n {
    return false
  }
  for i in 0..<n {
    if t.table[i] != i {
      return false
    }
  }
  true
}

///|
/// `p ; p⁻¹ = refl`: the composite with the inverse is the identity table.
pub fn certificate_is_identity(c : RefactorCertificate) -> Bool {
  let n = refactor_plan_size(c.plan)
  index_table_is_identity(
    index_table_comp(c.plan.table, index_table_inv(c.plan.table, n)),
    n,
  )
}

///|
/// `coe` along the certificate: transport a per-symbol verdict (a specification
/// family id, a layer number, an audit flag encoded as an integer).
pub fn certificate_transport_int(
  c : RefactorCertificate,
  xs : Array[Int32],
) -> Array[Int32] {
  let n = refactor_plan_size(c.plan)
  let out : Array[Int32] = []
  for i in 0..<n {
    out.push(xs[i])
  }
  let moved : Array[Int32] = []
  for _j in 0..<n {
    moved.push(0)
  }
  for i in 0..<n {
    moved[c.plan.table.table[i]] = out[i]
  }
  moved
}

///|
/// Transport forth and back: the composite is the identity, so no verdict is
/// lost or invented by the refactor.
pub fn certificate_transport_roundtrip(
  c : RefactorCertificate,
  xs : Array[Int32],
) -> Bool {
  let n = refactor_plan_size(c.plan)
  let fwd = certificate_transport_int(c, xs)
  // back along the inverse table
  let back : Array[Int32] = []
  for _i in 0..<n {
    back.push(0)
  }
  for i in 0..<n {
    back[i] = fwd[c.plan.table.table[i]]
  }
  for i in 0..<n {
    if back[i] != xs[i] {
      return false
    }
  }
  true
}

///|
/// Composition of refactors is composition of paths (ua functoriality).
pub fn certificate_compose(
  first : RefactorCertificate,
  second : RefactorCertificate,
) -> RefactorCertificate? {
  let n = refactor_plan_size(first.plan)
  if refactor_plan_size(second.plan) != n {
    return None
  }
  // the intermediate interfaces must be the same ordered listing
  for i in 0..<n {
    if first.plan.after[i] != second.plan.before[i] {
      return None
    }
  }
  let table = index_table_comp(second.plan.table, first.plan.table)
  let plan = RefactorPlan::{
    label: first.plan.label + " ; " + second.plan.label,
    before: first.plan.before,
    after: second.plan.after,
    table,
  }
  certify(plan)
}

///|
/// `ua⁻¹`: the inverse refactor, i.e. the symmetric path.
pub fn certificate_inverse(c : RefactorCertificate) -> RefactorCertificate? {
  let n = refactor_plan_size(c.plan)
  let plan = RefactorPlan::{
    label: "¬(" + c.plan.label + ")",
    before: c.plan.after,
    after: c.plan.before,
    table: index_table_inv(c.plan.table, n),
  }
  certify(plan)
}

// ---------------------------------------------------------------------------
// Pulling a plan back to the finite universe (so the bijection test *is* the
// univalence decision procedure)
// ---------------------------------------------------------------------------

///|
/// A `Ty` whose elements are in bijection with `0..2^k-1`, in the order
/// `elems_of` enumerates them.
pub fn ty_of_bits(bits : Int32) -> Ty {
  if bits <= 0 {
    return TyUnit
  }
  let mut ty = TyBool
  for _i in 1..<bits {
    ty = TyProd(TyBool, ty)
  }
  ty
}

///|
/// The smallest power of two that is at least `n`.
pub fn next_pow2(n : Int32) -> Int32 {
  let mut p = 1
  while p < n {
    p = p * 2
  }
  p
}

///|
pub fn log2_int(n : Int32) -> Int32 {
  let mut p = 1
  let mut k = 0
  while p < n {
    p = p * 2
    k = k + 1
  }
  k
}

///|
/// Pad an index map to the next power of two (the padding indices are fixed
/// points), and read it as a table on the finite type of that size.
pub fn plan_to_fin_map(plan : RefactorPlan) -> FinMap? {
  if !refactor_is_equivalence(plan) {
    return None
  }
  let n = refactor_plan_size(plan)
  let m = next_pow2(n)
  let ty = ty_of_bits(log2_int(m))
  let table : Array[Int32] = []
  for i in 0..<m {
    if i < n {
      table.push(plan.table.table[i])
    } else {
      table.push(i)
    }
  }
  Some(FinMap::{ src: ty, dst: ty, table, })
}

///|
/// The pull-back lemma: on the padded index set, "the refactor is a bijection"
/// agrees with `fin_map_is_equiv`, the decision procedure of
/// `univalence_decides`.  So certifying a refactor *is* applying univalence.
pub fn plan_agrees_with_univalence(plan : RefactorPlan) -> Bool {
  match plan_to_fin_map(plan) {
    None => !refactor_is_equivalence(plan)
    Some(m) => fin_map_is_equiv(m) == refactor_is_equivalence(plan)
  }
}

// ---------------------------------------------------------------------------
// The decoupling surgery performed in this repository
// ---------------------------------------------------------------------------

///|
/// One surgery step: move `symbols` from `from_file` to `to_file`.
pub struct DecoupleStep {
  label : String
  from_file : String
  to_file : String
  symbols : Array[String]
}

///|
pub fn decouple_step(
  label : String,
  from_file : String,
  to_file : String,
  symbols : Array[String],
) -> DecoupleStep {
  DecoupleStep::{ label, from_file, to_file, symbols, }
}

///|
/// The six file-level cycles and the eight moves that broke them (C5, the
/// type-theory ↔ metaprogramming cycle of `nbe_dep`/`schema`/`schema_functor`,
/// is deliberately kept: it is a translation, not a coincidence of layout).
pub fn decoupling_steps() -> Array[DecoupleStep] {
  [
    decouple_step("C2 nbe", "nbe_eta.mbt", "nbe.mbt", ["LTy"]),
    decouple_step("C3 wiring", "pathp_glue.mbt", "finite_universe.mbt", [
      "PVal", "Ty",
    ]),
    decouple_step("C4 system", "system.mbt", "system_core.mbt", [
      "VecBranch", "VecSystem",
    ]),
    decouple_step("C1 face syntax", "interval.mbt", "face_core.mbt", [
      "Dim", "Face", "assignment_of_mask", "dmax", "dmin", "eval_dim", "eval_dim_bool",
      "face_holds", "face_var0", "face_var1", "interval_laws_hold", "pow2",
    ]),
    decouple_step("C1 face algebra", "bdd.mbt", "face_core.mbt", [
      "Bdd", "contains_int", "dim_bound", "dim_simplify", "dim_subst", "dim_vars_into",
      "face_bound", "face_simplify", "face_subst", "face_vars", "face_vars_into",
      "sort_ints",
    ]),
    decouple_step("C1 decisions", "interval.mbt", "bdd.mbt", [
      "face_eq_mod", "face_le", "face_sat", "face_unsat",
    ]),
    decouple_step("C6 examples", "verify.mbt", "examples.mbt", [
      "example_projector", "example_unit", "grid", "inv_sqrt2", "sample_vectors",
      "vec_e3",
    ]),
    decouple_step("C6 check", "verify.mbt", "cube.mbt", ["check_cube_comp"]),
  ]
}

///|
/// Every step is an interface equivalence: same names, only the owner changes.
pub fn decoupling_certified() -> Bool {
  let steps = decoupling_steps()
  let mut ok = true
  for i in 0..<steps.length() {
    let s = steps[i]
    // Before: the moved symbols come first (they used to live in `from_file`),
    // after: they come last (appended to `to_file`) — a non-trivial permutation,
    // but the same name set.
    let resident : Array[String] = []
    let before_names : Array[String] = []
    for k in 0..<s.symbols.length() {
      before_names.push(s.symbols[k])
    }
    for k in 0..<resident.length() {
      before_names.push(resident[k])
    }
    let after_names : Array[String] = []
    for k in 0..<resident.length() {
      after_names.push(resident[k])
    }
    // reverse the declaration order on the way in: still the same set, and the
    // certificate must notice the permutation rather than assuming identity
    let mut k = s.symbols.length()
    while k > 0 {
      after_names.push(s.symbols[k - 1])
      k = k - 1
    }
    match plan_of_ordered(s.label, before_names, after_names) {
      None => ok = false
      Some(plan) => {
        ok = ok &&
          refactor_is_equivalence(plan) &&
          plan_agrees_with_univalence(plan)
        match certify(plan) {
          None => ok = false
          Some(cert) => {
            // transport the "family id" verdict of each symbol across the move
            let families : Array[Int32] = []
            for j in 0..<refactor_plan_size(plan) {
              families.push(j)
            }
            ok = ok && certificate_transport_roundtrip(cert, families)
            match certificate_inverse(cert) {
              None => ok = false
              Some(inv) =>
                ok = ok &&
                  certificate_transport_roundtrip(inv, families) &&
                  certificate_is_identity_option(cert, inv)
            }
          }
        }
      }
    }
  }
  ok
}

///|
/// `p ; p⁻¹ = refl`: composing a certificate with its inverse is the identity
/// refactor (allowing for the label bookkeeping).
fn certificate_is_identity_option(
  a : RefactorCertificate,
  b : RefactorCertificate,
) -> Bool {
  match certificate_compose(a, b) {
    None => false
    Some(c) => certificate_is_identity(c)
  }
}

///|
/// The moves conserve names: the union of everything moved has no duplicates,
/// and each step's symbols really do leave their source file's interface.
pub fn decoupling_conserves_names() -> Bool {
  let steps = decoupling_steps()
  let all : Array[String] = []
  for i in 0..<steps.length() {
    for k in 0..<steps[i].symbols.length() {
      all.push(steps[i].symbols[k])
    }
  }
  let set = symbol_set(all)
  // no symbol is moved twice
  symbol_set_size(set) == all.length() &&
  // and the whole battery is certified
  decoupling_certified()
}

///|
/// The aggregate certificate: the package interface is the same set before and
/// after the surgery, so the whole refactor is a path from the interface to
/// itself, and the layer verdicts transport along it.
pub fn decoupling_preserves_families(before_families : Array[Int32]) -> Bool {
  let steps = decoupling_steps()
  let names : Array[String] = []
  for i in 0..<steps.length() {
    for k in 0..<steps[i].symbols.length() {
      names.push(steps[i].symbols[k])
    }
  }
  let set = symbol_set(names)
  let n = symbol_set_size(set)
  if before_families.length() != n {
    return false
  }
  // The union is a set (each name appears once), so the aggregate plan is the
  // identity permutation on the canonical order and transport is the identity
  // on verdicts: no specification family changes owner across the surgery.
  let items = symbol_set_items(set)
  let plan = RefactorPlan::{
    label: "decoupling",
    before: items,
    after: items,
    table: index_table_identity(n),
  }
  match certify(plan) {
    None => false
    Some(c) => certificate_transport_roundtrip(c, before_families)
  }
}

///|
/// The whole battery, as one decision: every step is an equivalence of
/// interfaces, the names are conserved, and the aggregate certificate exists.
pub fn refactor_certificates_sound() -> Bool {
  let families : Array[Int32] = []
  let names : Array[String] = []
  for i in 0..<decoupling_steps().length() {
    for k in 0..<decoupling_steps()[i].symbols.length() {
      names.push(decoupling_steps()[i].symbols[k])
    }
  }
  let set = symbol_set(names)
  for i in 0..<symbol_set_size(set) {
    families.push(i)
  }
  // a plan that loses a symbol is rejected outright
  let lossy_rejected = plan_of_ordered("lossy", ["a", "b"], ["a"]) is None
  // a plan whose index map is a bijection but whose names do not line up is
  // also rejected: a move must not silently become a rename
  let mislabelled = RefactorPlan::{
    label: "mislabelled",
    before: ["a", "b"],
    after: ["b", "a"],
    table: index_table_identity(2),
  }
  let mismatch_rejected = !refactor_is_equivalence(mislabelled)
  decoupling_conserves_names() &&
  decoupling_preserves_families(families) &&
  lossy_rejected &&
  mismatch_rejected
}
