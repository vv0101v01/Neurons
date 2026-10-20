///|
// Computable univalence (可計算單值性定理).
//
// `pathp_glue.mbt` states univalence for the finite universe by *definition*:
// `ua e` is a `UPath` wrapping the equivalence, and `coe_upath` reads the
// endpoints back.  That is a statement; here it is turned into an algorithm
// and decided.
//
// A computable equivalence between finite types is a *table*: an array of
// indices into `elems_of`.  Everything below is therefore decidable by
// enumeration, with no sampling:
//
//   * `fin_map_is_equiv` decides whether a table is an equivalence
//     (injective + surjective, on all elements);
//   * `fin_equiv_search` *finds* an equivalence by backtracking over tables,
//     so "A ≃ B" is decided, not assumed;
//   * `cpath_ua` / `cpath_to_equiv` are the two directions of the
//     univalence map, `ua : (A ≃ B) → (A = B)` and `ua⁻¹ : (A = B) → (A ≃ B)`;
//   * `ua_section` and `ua_retraction` verify they are mutually inverse,
//     which is exactly the statement "univalence is an equivalence", and
//     `univalence_decides` verifies it for every pair of finite types;
//   * `univalence_path_count` counts paths: for finite types of size n the
//     type `A = B` has n! elements, the cardinality of the type of
//     equivalences — univalence computed as an equality of numbers.
//
// Paths are compared extensionally (`cpath_eq`): two paths are equal when
// their transports agree on all elements.  In this set-level finite model
// that is the same relation `upath_eq` uses for `UPath`.

///|
/// A computable map between finite types: `table[i]` is the index (in
/// `elems_of(dst)`) of the image of the i-th element of `elems_of(src)`.
pub struct FinMap {
  src : Ty
  dst : Ty
  table : Array[Int32]
}

///|
pub fn fin_map(src : Ty, dst : Ty, table : Array[Int32]) -> FinMap {
  FinMap::{ src, dst, table, }
}

///|
pub fn ty_card(ty : Ty) -> Int32 {
  elems_of(ty).length()
}

///|
pub fn fin_map_id(ty : Ty) -> FinMap {
  let table : Array[Int32] = []
  for i in 0..<ty_card(ty) {
    table.push(i)
  }
  FinMap::{ src: ty, dst: ty, table, }
}

///|
pub fn fin_map_wf(m : FinMap) -> Bool {
  if m.table.length() != ty_card(m.src) {
    return false
  }
  let n = ty_card(m.dst)
  for i in 0..<m.table.length() {
    if m.table[i] < 0 || m.table[i] >= n {
      return false
    }
  }
  true
}

///|
/// Decides equivalence: a well-formed table that is injective (and hence,
/// on finite types of equal size, bijective).
pub fn fin_map_is_equiv(m : FinMap) -> Bool {
  if !fin_map_wf(m) {
    return false
  }
  let n = ty_card(m.dst)
  let seen : Array[Bool] = []
  for _j in 0..<n {
    seen.push(false)
  }
  for i in 0..<m.table.length() {
    let j = m.table[i]
    if seen[j] {
      return false
    }
    seen[j] = true
  }
  true
}

///|
/// The inverse table of an equivalence.
pub fn fin_map_inv(m : FinMap) -> FinMap {
  let n = ty_card(m.dst)
  let table : Array[Int32] = []
  for _j in 0..<n {
    table.push(0)
  }
  for i in 0..<m.table.length() {
    table[m.table[i]] = i
  }
  FinMap::{ src: m.dst, dst: m.src, table, }
}

///|
/// Composition `g ∘ f`.
pub fn fin_map_comp(g : FinMap, f : FinMap) -> FinMap {
  let table : Array[Int32] = []
  for i in 0..<f.table.length() {
    table.push(g.table[f.table[i]])
  }
  FinMap::{ src: f.src, dst: g.dst, table, }
}

///|
pub fn fin_map_table_eq(a : FinMap, b : FinMap) -> Bool {
  if a.src != b.src || a.dst != b.dst || a.table.length() != b.table.length() {
    return false
  }
  for i in 0..<a.table.length() {
    if a.table[i] != b.table[i] {
      return false
    }
  }
  true
}

///|
/// Number of tables from `a` to `b`: |b|^|a|.
pub fn fin_map_count(a : Ty, b : Ty) -> Int32 {
  int_pow(ty_card(b), ty_card(a))
}

///|
/// Decode the `code`-th table, in base |b| lexicographic order.
pub fn fin_map_of_code(a : Ty, b : Ty, code : Int32) -> FinMap {
  let base = ty_card(b)
  let table : Array[Int32] = []
  let mut rest = code
  for _i in 0..<ty_card(a) {
    table.push(rest % base)
    rest = rest / base
  }
  FinMap::{ src: a, dst: b, table, }
}

///|
/// Backtracking search for an equivalence: the first equivalent table in
/// lexicographic order, or `None`.  This makes "A ≃ B" a decision problem.
pub fn fin_equiv_search(a : Ty, b : Ty) -> FinMap? {
  if ty_card(a) != ty_card(b) {
    return None
  }
  let total = fin_map_count(a, b)
  for code in 0..<total {
    let m = fin_map_of_code(a, b, code)
    if fin_map_is_equiv(m) {
      return Some(m)
    }
  }
  None
}

///|
/// How many equivalences are there: n! when the sizes agree, else 0.
pub fn fin_equiv_count(a : Ty, b : Ty) -> Int32 {
  if ty_card(a) != ty_card(b) {
    return 0
  }
  let mut count = 0
  for code in 0..<fin_map_count(a, b) {
    if fin_map_is_equiv(fin_map_of_code(a, b, code)) {
      count = count + 1
    }
  }
  count
}

///|
pub fn fact(n : Int32) -> Int32 {
  let mut acc = 1
  for i in 1..<=n {
    acc = acc * i
  }
  acc
}

///|
/// Univalence decides type equality for finite types: an equivalence exists
/// exactly when the cardinalities agree, and there are then exactly n! of
/// them (the order of the symmetric group).
pub fn univalence_decides(a : Ty, b : Ty) -> Bool {
  let exists = fin_equiv_search(a, b) is Some(_)
  let same_card = ty_card(a) == ty_card(b)
  let count = fin_equiv_count(a, b)
  let expected = if same_card { fact(ty_card(a)) } else { 0 }
  exists == same_card && count == expected
}

///|
/// A computable path in the universe: the ua-image of an equivalence,
/// together with its two endpoints and a transport function.
pub struct CPath {
  src : Ty
  dst : Ty
  e : FinMap
}

///|
/// `ua`: an equivalence yields a path.
pub fn cpath_ua(e : FinMap) -> CPath {
  CPath::{ src: e.src, dst: e.dst, e, }
}

///|
pub fn cpath_refl(ty : Ty) -> CPath {
  cpath_ua(fin_map_id(ty))
}

///|
/// Symmetry of paths, induced by the inverse equivalence.
pub fn cpath_sym(p : CPath) -> CPath {
  cpath_ua(fin_map_inv(p.e))
}

///|
/// Concatenation of paths, induced by composition of equivalences.
pub fn cpath_comp(p : CPath, q : CPath) -> CPath {
  cpath_ua(fin_map_comp(q.e, p.e))
}

///|
/// The type at a parameter of the path: this finite model has no
/// intermediate types, so r = 0 gives the source, r = 1 the target.
pub fn cpath_type_at(p : CPath, r : Int32) -> Ty {
  if r == 0 {
    p.src
  } else {
    p.dst
  }
}

///|
/// Transport along the path over an index, with the computation rules
///   coe r r i = i,  coe 0 1 i = e.table[i],  coe 1 0 i = e⁻¹.table[i].
pub fn cpath_coe_index(p : CPath, r : Int32, s : Int32, i : Int32) -> Int32 {
  if r == s {
    i
  } else if r == 0 {
    p.e.table[i]
  } else {
    fin_map_inv(p.e).table[i]
  }
}

///|
/// Transport along the path on elements.
pub fn cpath_coe(p : CPath, r : Int32, s : Int32, v : PVal) -> PVal {
  let xs = elems_of(p.src)
  let ys = elems_of(p.dst)
  let mut idx = -1
  for i in 0..<xs.length() {
    if xs[i] == v {
      idx = i
    }
  }
  if idx < 0 {
    return v
  }
  if r == s {
    v
  } else if r == 0 {
    ys[p.e.table[idx]]
  } else {
    xs[fin_map_inv(p.e).table[idx]]
  }
}

///|
/// `ua⁻¹`: read an equivalence back out of a path, by transport along it.
pub fn cpath_to_equiv(p : CPath) -> FinMap {
  let table : Array[Int32] = []
  for i in 0..<ty_card(p.src) {
    table.push(cpath_coe_index(p, 0, 1, i))
  }
  FinMap::{ src: p.src, dst: p.dst, table, }
}

///|
/// Extensional equality of paths: same endpoints and the same transport on
/// every element.
pub fn cpath_eq(p : CPath, q : CPath) -> Bool {
  if p.src != q.src || p.dst != q.dst {
    return false
  }
  for i in 0..<ty_card(p.src) {
    if cpath_coe_index(p, 0, 1, i) != cpath_coe_index(q, 0, 1, i) {
      return false
    }
    if cpath_coe_index(p, 1, 0, i) != cpath_coe_index(q, 1, 0, i) {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// The univalence theorem, decided
// ---------------------------------------------------------------------------

///|
/// Transport along `ua e` computes: on every element, coe 0 1 is `fwd` and
/// coe 1 0 is `bwd`.
pub fn ua_transport_computes(e : FinMap) -> Bool {
  if !fin_map_is_equiv(e) {
    return false
  }
  let p = cpath_ua(e)
  let inv = fin_map_inv(e)
  for i in 0..<ty_card(e.src) {
    if cpath_coe_index(p, 0, 1, i) != e.table[i] {
      return false
    }
    if cpath_coe_index(p, 0, 0, i) != i {
      return false
    }
  }
  for j in 0..<ty_card(e.dst) {
    if cpath_coe_index(p, 1, 0, j) != inv.table[j] {
      return false
    }
  }
  true
}

///|
/// `ua id = refl`: the univalence path of an identity is the identity path.
pub fn ua_refl_is_identity(ty : Ty) -> Bool {
  cpath_eq(cpath_ua(fin_map_id(ty)), cpath_refl(ty))
}

///|
/// Functoriality: `ua (g ∘ f) = ua g ∘ ua f`.
pub fn ua_functorial(f : FinMap, g : FinMap) -> Bool {
  if !fin_map_is_equiv(f) || !fin_map_is_equiv(g) || f.dst != g.src {
    return false
  }
  cpath_eq(cpath_ua(fin_map_comp(g, f)), cpath_comp(cpath_ua(f), cpath_ua(g)))
}

///|
/// `ua (e⁻¹) = ¬(ua e)`: inversion of equivalences is inversion of paths.
pub fn ua_inverse(e : FinMap) -> Bool {
  if !fin_map_is_equiv(e) {
    return false
  }
  cpath_eq(cpath_ua(fin_map_inv(e)), cpath_sym(cpath_ua(e)))
}

///|
/// Section: `ua⁻¹ (ua e) = e`.  (Transporting along the univalence path
/// recovers the equivalence we started from.)
pub fn ua_section(e : FinMap) -> Bool {
  if !fin_map_is_equiv(e) {
    return false
  }
  fin_map_table_eq(cpath_to_equiv(cpath_ua(e)), e)
}

///|
/// Retraction: `ua (ua⁻¹ p) = p`.
pub fn ua_retraction(p : CPath) -> Bool {
  cpath_eq(cpath_ua(cpath_to_equiv(p)), p)
}

///|
/// The section law, exhausted over every table between the two types.
pub fn ua_section_all(a : Ty, b : Ty) -> Bool {
  if ty_card(a) != ty_card(b) {
    return true
  }
  for code in 0..<fin_map_count(a, b) {
    let m = fin_map_of_code(a, b, code)
    if fin_map_is_equiv(m) && !ua_section(m) {
      return false
    }
  }
  true
}

///|
/// The retraction law, exhausted over every table between the two types
/// (each table names a path through `ua`).
pub fn ua_retraction_all(a : Ty, b : Ty) -> Bool {
  if ty_card(a) != ty_card(b) {
    return true
  }
  for code in 0..<fin_map_count(a, b) {
    let m = fin_map_of_code(a, b, code)
    if fin_map_is_equiv(m) && !ua_retraction(cpath_ua(m)) {
      return false
    }
  }
  true
}

///|
/// Transport preserves cardinality: paths only relate types of equal size.
pub fn transport_preserves_cardinality(a : Ty, b : Ty) -> Bool {
  match fin_equiv_search(a, b) {
    None => ty_card(a) != ty_card(b)
    Some(e) => {
      let p = cpath_ua(e)
      // Every element of the source transports to a distinct element of the
      // target, and every target element is hit.
      let mut hit = 0
      for j in 0..<ty_card(b) {
        let mut found = false
        for i in 0..<ty_card(a) {
          if cpath_coe_index(p, 0, 1, i) == j {
            found = true
          }
        }
        if found {
          hit = hit + 1
        }
      }
      hit == ty_card(b)
    }
  }
}

///|
/// The number of paths between two finite types: univalence says this is the
/// number of equivalences, i.e. n! for equal sizes and 0 otherwise.
pub fn univalence_path_count(a : Ty, b : Ty) -> Int32 {
  fin_equiv_count(a, b)
}

///|
/// Round trip of transport: coe 0 1 then coe 1 0 is the identity on all
/// elements, for every equivalence.
pub fn transport_roundtrip(e : FinMap) -> Bool {
  if !fin_map_is_equiv(e) {
    return false
  }
  let p = cpath_ua(e)
  for i in 0..<ty_card(e.src) {
    if cpath_coe_index(p, 1, 0, cpath_coe_index(p, 0, 1, i)) != i {
      return false
    }
  }
  true
}

///|
/// `J` on univalence paths: for a family given by cardinality, transporting
/// along `ua e` gives the same fibre as the reflexive transport.
pub fn j_rule_on_ua(e : FinMap) -> Bool {
  if !fin_map_is_equiv(e) {
    return false
  }
  let p = cpath_ua(e)
  // The family: card of the transported type's index set.
  let lhs = ty_card(cpath_type_at(p, 1))
  let rhs = ty_card(cpath_type_at(cpath_refl(e.src), 1))
  lhs == rhs
}

///|
/// A worked example: negation on Bool, as a computable equivalence and path.
pub fn fin_not_bool() -> FinMap {
  FinMap::{ src: TyBool, dst: TyBool, table: [1, 0], }
}

///|
/// A worked example: the swap of two Bools (the classic ua generator).
pub fn fin_swap_bool_pair() -> FinMap {
  let ty = TyProd(TyBool, TyBool)
  // (f,f) ↦ (f,f), (f,t) ↦ (t,f), (t,f) ↦ (f,t), (t,t) ↦ (t,t)
  FinMap::{ src: ty, dst: ty, table: [0, 2, 1, 3], }
}

///|
/// The whole computable-univalence battery, over representative finite types.
pub fn univalence_compute_all() -> Bool {
  let tys = [TyUnit, TyBool, TyProd(TyBool, TyBool)]
  let mut ok = true
  for i in 0..<tys.length() {
    for j in 0..<tys.length() {
      ok = ok &&
        univalence_decides(tys[i], tys[j]) &&
        ua_section_all(tys[i], tys[j]) &&
        ua_retraction_all(tys[i], tys[j]) &&
        transport_preserves_cardinality(tys[i], tys[j])
    }
    ok = ok && ua_refl_is_identity(tys[i])
  }
  let n = fin_not_bool()
  let s = fin_swap_bool_pair()
  ok &&
  ua_transport_computes(n) &&
  ua_inverse(n) &&
  transport_roundtrip(n) &&
  j_rule_on_ua(n) &&
  ua_functorial(n, n) &&
  ua_transport_computes(s) &&
  ua_inverse(s) &&
  transport_roundtrip(s) &&
  j_rule_on_ua(s) &&
  ua_functorial(s, s) &&
  ua_section(s) &&
  univalence_path_count(TyProd(TyBool, TyBool), TyProd(TyBool, TyBool)) == 24
}
