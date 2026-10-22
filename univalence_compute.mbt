///|
// Computable univalence (可計算單值性定理).
//
// `pathp_glue.mbt` states univalence for the finite universe by *definition*:
// `ua e` is a `UPath` wrapping the equivalence, and `coe_upath` reads the
// endpoints back.  That is a statement; here it is turned into an algorithm
// and decided.
//
// A computable equivalence between finite types is a *table*: an array of
// indices into `elems_of`.  Three layers keep the decision procedures exact
// at every size (the counting formulas used to overflow `Int32` — at 16
// elements `16^16 ≡ 0 (mod 2^32)` and `16! > 2^31` — which silently made
// every "decision" vacuous):
//
//   * **exact counting** (`bignat.mbt`): `fin_map_count` is `|B|^|A|`,
//     `fact` is `n!`, `fin_equiv_count` and `univalence_path_count` count
//     in unbounded `BigNat` — no formula ever wraps;
//   * **pruned search**: `fin_equiv_search` walks *injective prefixes*
//     only (the n! bijections, not the |B|^|A| tables) in the same
//     lexicographic order the old code-ascending scan used, so "A ≃ B" is
//     decided instantly at any size;
//   * **budgeted exhaustion**: the universal laws (`ua_section_all`,
//     `ua_retraction_all`) exhaust every table / every equivalence while
//     the search space fits an explicit budget, and otherwise return
//     `LawUndecided` — decided where decidable, never sampled.
//
// The remaining decision battery is unchanged:
//
//   * `fin_map_is_equiv` decides whether a table is an equivalence
//     (injective + surjective, on all elements);
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
} derive(Debug, Eq)

///|
pub extend FinMap with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FinMap with Eq::{not_equal, equal}

///|
pub fn fin_map(src : Ty, dst : Ty, table : Array[Int32]) -> FinMap {
  FinMap::{ src, dst, table, }
}

///|
pub fn ty_card(ty : Ty) -> Int32 {
  elems_of(ty).length()
}

///|
/// A finite type of exactly `n` elements (`n >= 1`), built by repeatedly
/// adjoining one `TyUnit` summand: `fin_ty(1) = TyUnit`,
/// `fin_ty(n+1) = TySum(TyUnit, fin_ty(n))`.  Public so any caller that
/// needs "the generic n-element type" (e.g. to index a finite set coming
/// from elsewhere, such as a polynomial's root array) does not have to
/// reinvent it; previously this was a private helper duplicated in
/// univalence_compute_wbtest.mbt.
pub fn fin_ty(n : Int32) -> Ty {
  let mut acc = TyUnit
  let mut k = 1
  while k < n {
    acc = TySum(TyUnit, acc)
    k = k + 1
  }
  acc
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
pub fn fin_map_inv_at(m : FinMap, i : Int32) -> Int32 {
  // The last position mapping to `i` (last-write-wins, the semantics of
  // the inverse table below).
  let mut out = 0
  for j in 0..<m.table.length() {
    if m.table[j] == i {
      out = j
    }
  }
  out
}

///|
pub fn fin_map_inv(m : FinMap) -> FinMap {
  let n = ty_card(m.dst)
  let table : Array[Int32] = []
  for j in 0..<n {
    table.push(fin_map_inv_at(m, j))
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
/// Number of tables from `a` to `b`: |b|^|a|, exactly (`BigNat`; the old
/// `Int32` power wrapped to 0 at 16 elements).
pub fn fin_map_count(a : Ty, b : Ty) -> BigNat {
  bignat_pow(bignat_of_int(ty_card(b)), ty_card(a))
}

///|
/// Decode the `code`-th table, in base |b| lexicographic order (`table[0]`
/// is the least significant digit).  The code is a machine integer, so this
/// is only meaningful for small spaces; `fin_map_of_code_big` decodes codes
/// of any size, and the search/law procedures do not enumerate codes at all.
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
/// Decode the `code`-th table with an exact `BigNat` code: the same
/// base-|b| lexicographic order as `fin_map_of_code`, with no overflow.
pub fn fin_map_of_code_big(a : Ty, b : Ty, code : BigNat) -> FinMap {
  let base = ty_card(b).to_int64()
  let table : Array[Int32] = []
  let mut rest = code
  for _i in 0..<ty_card(a) {
    let (q, r) = bignat_divmod_small(rest, base)
    table.push(r.to_int())
    rest = q
  }
  FinMap::{ src: a, dst: b, table, }
}

///|
/// Depth-first search over *injective prefixes*: positions are filled from
/// the last index down, values ascending, so the first leaf is the same
/// table the code-ascending scan of `fin_map_of_code` would return first
/// (for equal sizes: the reversed identity `[n−1, …, 1, 0]`).
fn fin_equiv_dfs(
  n : Int32,
  pos : Int32,
  table : Array[Int32],
  used : Array[Bool],
) -> Bool {
  if pos < 0 {
    return true
  }
  for v in 0..<n {
    if !used[v] {
      used[v] = true
      table[pos] = v
      if fin_equiv_dfs(n, pos - 1, table, used) {
        return true
      }
      used[v] = false
    }
  }
  false
}

///|
/// Backtracking search for an equivalence: the first equivalent table in
/// lexicographic order, or `None`.  This makes "A ≃ B" a decision problem
/// at every size: only injective prefixes are visited, so the search never
/// touches the |B|^|A| table space.
pub fn fin_equiv_search(a : Ty, b : Ty) -> FinMap? {
  if ty_card(a) != ty_card(b) {
    return None
  }
  let n = ty_card(a)
  let table : Array[Int32] = []
  let used : Array[Bool] = []
  for _i in 0..<n {
    table.push(0)
    used.push(false)
  }
  if fin_equiv_dfs(n, n - 1, table, used) {
    Some(FinMap::{ src: a, dst: b, table, })
  } else {
    None
  }
}

///|
/// Largest size for which the number of equivalences is decided by
/// memoised enumeration of the search tree (`2^n` states) instead of the
/// closed form (SPEC §四 item 9(b)).  The bound is the exact Int64 safety
/// margin, not an arbitrary round number: every DP sub-count is bounded
/// above by `n!` (a sub-count never exceeds the number of ways to permute
/// the remaining free values), and `20! = 2432902008176640000` is the
/// largest factorial that still fits in `Int64` (`21!` overflows it).  So
/// `n ≤ 20` is the largest range in which the whole enumeration — states,
/// intermediate sums, and the final count — stays exact in machine
/// integers before the one, final exactification to `BigNat`; beyond it
/// the count is `n!` computed directly in `BigNat` (the two agree wherever
/// both run — cross-checked in tests, including at this exact boundary).
fn fin_equiv_enum_max() -> Int32 {
  20
}

///|
/// Number of bijections on `n` elements counted by memoised enumeration of
/// the injective-prefix search tree (DP over the used-value bitmask).
/// Sub-counts are bounded by `n!`, which fits `Int64` throughout the
/// enumeration range (`n ≤ 18`), so the DP runs in machine integers and
/// only the result is exactified to `BigNat`.
fn bijection_count_enum(n : Int32) -> BigNat {
  let full = int_pow(2, n) - 1
  let bits : Array[Int32] = []
  for v in 0..<n {
    bits.push(int_pow(2, v))
  }
  let memo : Array[Int64?] = []
  for _mask in 0..<=full {
    memo.push(None)
  }
  bignat_of_int64(bijection_recurse(0, full, bits, memo))
}

///|
/// DP over the used-value bitmask; the mask of each value is
/// precomputed and only *free* values are visited, so a state with
/// `k` remaining values costs `k` steps instead of `n` (and no power
/// recomputation).
fn bijection_recurse(
  used : Int32,
  full : Int32,
  bits : Array[Int32],
  memo : Array[Int64?],
) -> Int64 {
  if used == full {
    return 1L
  }
  match memo[used] {
    Some(c) => c
    None => {
      let mut total = 0L
      let mut free = full - used
      let mut v = 0
      while free > 0 {
        if free % 2 == 1 {
          total = total + bijection_recurse(used + bits[v], full, bits, memo)
        }
        free = free / 2
        v = v + 1
      }
      memo[used] = Some(total)
      total
    }
  }
}

///|
/// How many equivalences are there: exactly n! when the sizes agree, else
/// 0.  The count is *decided* — by memoised enumeration of the same search
/// tree `fin_equiv_search` walks, for `n ≤ fin_equiv_enum_max()`; beyond
/// that by the closed form, still exact in `BigNat` (the `Int32` factorial
/// wrapped at 13!).
pub fn fin_equiv_count(a : Ty, b : Ty) -> BigNat {
  if ty_card(a) != ty_card(b) {
    return bignat_of_int(0)
  }
  let n = ty_card(a)
  if n <= fin_equiv_enum_max() {
    bijection_count_enum(n)
  } else {
    bignat_fact(n)
  }
}

///|
/// `n!` exactly (`BigNat`; overflows `Int32` from 13! on).
pub fn fact(n : Int32) -> BigNat {
  bignat_fact(n)
}

///|
/// Univalence decides type equality for finite types: an equivalence exists
/// exactly when the cardinalities agree, and there are then exactly n! of
/// them (the order of the symmetric group).  Both conjuncts are decided at
/// every size: the search is pruned and the counts are exact.
pub fn univalence_decides(a : Ty, b : Ty) -> Bool {
  let exists = fin_equiv_search(a, b) is Some(_)
  let same_card = ty_card(a) == ty_card(b)
  if exists != same_card {
    return false
  }
  let count = fin_equiv_count(a, b)
  let expected = if same_card {
    bignat_fact(ty_card(a))
  } else {
    bignat_of_int(0)
  }
  count == expected
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
    // Inverse at `i` without allocating an inverse map per call.
    fin_map_inv_at(p.e, i)
  }
}

///|
/// Transport along the path on elements.
pub fn cpath_coe(p : CPath, r : Int32, s : Int32, v : PVal) -> PVal {
  if r == s {
    return v
  }
  // `v` lives in the type at parameter `r`: the forward direction looks
  // it up among the source elements, the backward direction among the
  // target elements.  (When `src` and `dst` happen to share the same
  // element representation — e.g. transporting a `Bool × Bool` along an
  // automorphism — searching either array would coincidentally agree;
  // that coincidence does *not* hold once `src` and `dst` are built from
  // genuinely different type formers, such as `TySum(A, B)` versus
  // `TySum(B, A)`, so the lookup must use the array matching `r`.)
  let xs = elems_of(p.src)
  let ys = elems_of(p.dst)
  if r == 0 {
    let mut idx = -1
    for i in 0..<xs.length() {
      if xs[i] == v {
        idx = i
      }
    }
    if idx < 0 {
      return v
    }
    ys[p.e.table[idx]]
  } else {
    let mut idx = -1
    for j in 0..<ys.length() {
      if ys[j] == v {
        idx = j
      }
    }
    if idx < 0 {
      return v
    }
    xs[fin_map_inv_at(p.e, idx)]
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
// Groupoid structure of univalence paths (路徑的群胚結構)
// ---------------------------------------------------------------------------

///|
/// `p ∙ refl = p`: the reflexive path is a right unit for concatenation.
pub fn cpath_comp_right_unit(p : CPath) -> Bool {
  cpath_eq(cpath_comp(p, cpath_refl(p.dst)), p)
}

///|
/// `refl ∙ p = p`: the reflexive path is a left unit for concatenation.
pub fn cpath_comp_left_unit(p : CPath) -> Bool {
  cpath_eq(cpath_comp(cpath_refl(p.src), p), p)
}

///|
/// `¬¬p = p`: symmetry of paths is an involution.
pub fn cpath_sym_involutive(p : CPath) -> Bool {
  cpath_eq(cpath_sym(cpath_sym(p)), p)
}

///|
/// `¬refl = refl`.
pub fn cpath_sym_refl(ty : Ty) -> Bool {
  cpath_eq(cpath_sym(cpath_refl(ty)), cpath_refl(ty))
}

///|
/// `¬(p ∙ q) = ¬q ∘ ¬p`: symmetry is an anti-homomorphism of
/// concatenation.
pub fn cpath_sym_comp(p : CPath, q : CPath) -> Bool {
  if p.dst != q.src {
    return false
  }
  cpath_eq(cpath_sym(cpath_comp(p, q)), cpath_comp(cpath_sym(q), cpath_sym(p)))
}

///|
/// `(p ∙ q) ∘ r = p ∘ (q ∘ r)`: concatenation is associative.
pub fn cpath_comp_assoc(p : CPath, q : CPath, r : CPath) -> Bool {
  if p.dst != q.src || q.dst != r.src {
    return false
  }
  cpath_eq(cpath_comp(cpath_comp(p, q), r), cpath_comp(p, cpath_comp(q, r)))
}

///|
/// Transport along a concatenation computes as the composite of the two
/// transports: `coe (p ∙ q) = coe q ∘ coe p`, in both directions.
pub fn transport_comp_computes(p : CPath, q : CPath) -> Bool {
  if p.dst != q.src {
    return false
  }
  let pq = cpath_comp(p, q)
  for i in 0..<ty_card(p.src) {
    if cpath_coe_index(pq, 0, 1, i) !=
      cpath_coe_index(q, 0, 1, cpath_coe_index(p, 0, 1, i)) {
      return false
    }
  }
  for j in 0..<ty_card(q.dst) {
    if cpath_coe_index(pq, 1, 0, j) !=
      cpath_coe_index(p, 1, 0, cpath_coe_index(q, 1, 0, j)) {
      return false
    }
  }
  true
}

///|
/// Transport along `refl` is the identity on every element, in every
/// direction (`coe r r = id` is built into the definition).
pub fn transport_refl_identity(ty : Ty) -> Bool {
  let p = cpath_refl(ty)
  for i in 0..<ty_card(ty) {
    if cpath_coe_index(p, 0, 1, i) != i || cpath_coe_index(p, 1, 0, i) != i {
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
/// Verdict of an exhaustive law check.  `LawUndecided` is the honest third
/// outcome — the same convention as the BDD node budgets: when the search
/// space exceeds the budget the law is *not* sampled, it is reported
/// undecided.
pub enum LawVerdict {
  LawHolds
  LawFails(FinMap) // counterexample table
  LawUndecided
} derive(Debug, Eq)

///|
pub extend LawVerdict with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend LawVerdict with Eq::{not_equal, equal}

///|
/// Table budget for exhaustive law checks: spaces with at most this many
/// tables are exhausted table-by-table (every table, not just the
/// equivalences).
fn law_table_budget() -> Int32 {
  65536
}

///|
/// Search-node budget for exhaustive law checks over equivalences only:
/// the injective-prefix search visits at most this many prefixes.  The
/// value clears the 8-element search tree (109,601 nodes) with headroom,
/// so every Bool/Unit product below 16 elements is decided; 16-element
/// types (16! ≫ budget) exhaust the budget and report `LawUndecided`.
fn law_enum_budget() -> Int32 {
  150000
}

///|
/// Is `n!` still within `law_enum_budget()`?  Past this point
/// `exhaust_equiv` (and a fortiori `exhaust_tables`, whose `n^n` space
/// grows faster still) is *guaranteed* to burn its entire budget without
/// finishing — so `ua_section_all`/`ua_retraction_all` skip the search
/// altogether past this point and go straight to the O(n) symbolic proof
/// (`ua_section_proved`/`ua_retraction_proved`) instead of wasting a
/// combined ~215,000 budget nodes just to rediscover `LawUndecided`.
fn exhaustion_search_feasible(n : Int32) -> Bool {
  let mut acc = 1L
  let mut i = 2
  while i <= n {
    acc = acc * i.to_int64()
    if acc > law_enum_budget().to_int64() {
      return false
    }
    i = i + 1
  }
  true
}

///|
/// Exhaust every well-formed table `a → b` in code order while the space
/// fits `budget` tables; `holds` is the law under test (a failing table is
/// a counterexample).  Returns `LawUndecided` before anything is guessed.
fn exhaust_tables(
  a : Ty,
  b : Ty,
  holds : (FinMap) -> Bool,
  budget : Int32,
) -> LawVerdict {
  match bignat_to_int32(fin_map_count(a, b)) {
    None => LawUndecided
    Some(total) =>
      if total > budget {
        LawUndecided
      } else {
        for code in 0..<total {
          let m = fin_map_of_code(a, b, code)
          if !holds(m) {
            return LawFails(m)
          }
        }
        LawHolds
      }
  }
}

///|
/// Exhaust every equivalence `a ≅ b` (the injective-prefix search tree,
/// same lexicographic order) while the search fits `budget` nodes.
fn exhaust_equiv(
  a : Ty,
  b : Ty,
  holds : (FinMap) -> Bool,
  budget : Int32,
) -> LawVerdict {
  if ty_card(a) != ty_card(b) {
    return LawHolds
  }
  let n = ty_card(a)
  let table : Array[Int32] = []
  let used : Array[Bool] = []
  for _i in 0..<n {
    table.push(0)
    used.push(false)
  }
  let budget_left = [budget]
  exhaust_dfs(n, n - 1, table, used, holds, a, b, budget_left)
}

///|
fn exhaust_dfs(
  n : Int32,
  pos : Int32,
  table : Array[Int32],
  used : Array[Bool],
  holds : (FinMap) -> Bool,
  src : Ty,
  dst : Ty,
  budget_left : Array[Int32],
) -> LawVerdict {
  if budget_left[0] <= 0 {
    return LawUndecided
  }
  budget_left[0] = budget_left[0] - 1
  if pos < 0 {
    let snapshot : Array[Int32] = []
    for i in 0..<n {
      snapshot.push(table[i])
    }
    let m = FinMap::{ src, dst, table: snapshot, }
    if holds(m) {
      LawHolds
    } else {
      LawFails(m)
    }
  } else {
    for v in 0..<n {
      if !used[v] {
        used[v] = true
        table[pos] = v
        let verdict = exhaust_dfs(
          n,
          pos - 1,
          table,
          used,
          holds,
          src,
          dst,
          budget_left,
        )
        if verdict != LawHolds {
          used[v] = false
          return verdict
        }
        used[v] = false
      }
    }
    LawHolds
  }
}

// ---------------------------------------------------------------------------
// A symbolic identity layer for the section/retraction laws (SPEC §四
// item 9(a))
// ---------------------------------------------------------------------------
//
// `ua_section_all`/`ua_retraction_all` below decide their law by exhaustive
// search, which is combinatorially infeasible once the type passes ~8
// elements (the equivalence search tree has `n!` leaves).  But neither law
// actually depends on the *content* of the table being checked: reading the
// definitions through —
//
//   cpath_to_equiv(cpath_ua(e)).table[i]
//     = cpath_coe_index(cpath_ua(e), 0, 1, i)    (definition of cpath_to_equiv)
//     = cpath_ua(e).e.table[i]                   (cpath_coe_index at r = 0)
//     = e.table[i]                               (cpath_ua(e).e is e itself)
//
// — shows `cpath_to_equiv(cpath_ua(e))` reproduces `e`'s table verbatim, by
// substitution alone: no step above inspects whether `e` is injective, nor
// any other property of its entries.  The same substitution, run on
// `cpath_ua(cpath_to_equiv(p))` against an arbitrary `p`, reproduces `p`'s
// table too.  Both "laws" are therefore representation identities, true of
// *every* table/path of the matching sizes, not properties that need
// searching for a counterexample among `n!` candidates.
//
// `fin_map_round_trip_identity`/`cpath_round_trip_identity` perform the O(n)
// computation that instantiates this argument; `ua_section_proved`/
// `ua_retraction_proved` decide the universal law from it at *any* size,
// eliminating the `LawUndecided` outcome entirely for these two laws (the
// whitebox tests cross-check them against the budgeted exhaustive versions
// at every size the latter can still afford, and confirm they agree with
// `LawHolds` at 16 elements, where exhaustion was previously undecided).

///|
/// The computational core of the section law, independent of whether `e`
/// is an equivalence: `cpath_to_equiv(cpath_ua(e))` has the same table as
/// `e`.  See the module-level comment above for why this holds for *every*
/// `e`, not merely the one checked here.
pub fn fin_map_round_trip_identity(e : FinMap) -> Bool {
  fin_map_table_eq(cpath_to_equiv(cpath_ua(e)), e)
}

///|
/// The computational core of the retraction law, for an arbitrary `CPath`
/// (not just those built from an equivalence): `cpath_ua(cpath_to_equiv(p))`
/// recomputes the same path.  See the module-level comment above.
pub fn cpath_round_trip_identity(p : CPath) -> Bool {
  cpath_eq(cpath_ua(cpath_to_equiv(p)), p)
}

///|
/// A handful of structurally distinct witness tables of the given sizes:
/// the identity, the fully reversed table, and (when there is room) a
/// collapsing table that is not injective.  Checking the round-trip
/// identity on several differently-shaped witnesses — none of which the
/// argument above branches on — corroborates content-independence rather
/// than resting on a single convenient case.
fn fin_map_witnesses(a : Ty, b : Ty) -> Array[FinMap] {
  let na = ty_card(a)
  let nb = ty_card(b)
  let out : Array[FinMap] = []
  let identity_like : Array[Int32] = []
  let reversed : Array[Int32] = []
  for i in 0..<na {
    identity_like.push(i % (if nb > 0 { nb } else { 1 }))
    reversed.push((nb - 1 - i % (if nb > 0 { nb } else { 1 })))
  }
  out.push(FinMap::{ src: a, dst: b, table: identity_like, })
  out.push(FinMap::{ src: a, dst: b, table: reversed, })
  if nb > 0 {
    let collapsed : Array[Int32] = []
    for _i in 0..<na {
      collapsed.push(0)
    }
    out.push(FinMap::{ src: a, dst: b, table: collapsed, })
  }
  out
}

///|
/// The section law `ua⁻¹ (ua e) = e`, decided at *any* size by the
/// structural identity above instead of exhaustive search: vacuously true
/// when the sizes disagree, and otherwise true by the representation
/// argument, corroborated on several witness tables (never a sample of
/// the law itself, since the argument does not depend on table content).
pub fn ua_section_proved(a : Ty, b : Ty) -> LawVerdict {
  if ty_card(a) != ty_card(b) {
    return LawHolds
  }
  let witnesses = fin_map_witnesses(a, b)
  for i in 0..<witnesses.length() {
    if !fin_map_round_trip_identity(witnesses[i]) {
      return LawFails(witnesses[i])
    }
  }
  LawHolds
}

///|
/// The retraction law `ua (ua⁻¹ p) = p`, decided at *any* size the same
/// way as `ua_section_proved`.
pub fn ua_retraction_proved(a : Ty, b : Ty) -> LawVerdict {
  if ty_card(a) != ty_card(b) {
    return LawHolds
  }
  let witnesses = fin_map_witnesses(a, b)
  for i in 0..<witnesses.length() {
    if !cpath_round_trip_identity(cpath_ua(witnesses[i])) {
      return LawFails(witnesses[i])
    }
  }
  LawHolds
}

///|
/// The section law, exhausted over every equivalence between the two types:
/// `ua⁻¹(ua e) = e`.  Small spaces are exhausted table-by-table (every
/// table, equivalence or not), larger ones over the equivalences alone;
/// if even that search exceeds its budget, the symbolic representation
/// argument (`ua_section_proved`, SPEC §四 item 9(a)) decides the law
/// directly instead of giving up — so this function never actually
/// returns `LawUndecided` for this law, at any size (the raw exhaustion
/// machinery itself still can be, and is exercised directly in the test
/// suite, which is the honest demonstration that the *search* alone is
/// combinatorially infeasible beyond ~8 elements; the point of (a) is
/// that the law does not require search at all).  With no equivalences
/// (unequal sizes) the law holds vacuously.
pub fn ua_section_all(a : Ty, b : Ty) -> LawVerdict {
  if ty_card(a) != ty_card(b) {
    return LawHolds
  }
  if !exhaustion_search_feasible(ty_card(a)) {
    return ua_section_proved(a, b)
  }
  match
    exhaust_tables(
      a,
      b,
      m => !fin_map_is_equiv(m) || ua_section(m),
      law_table_budget(),
    ) {
    LawUndecided =>
      match exhaust_equiv(a, b, ua_section, law_enum_budget()) {
        LawUndecided => ua_section_proved(a, b)
        verdict => verdict
      }
    verdict => verdict
  }
}

///|
/// The retraction law, exhausted over every equivalence between the two
/// types: `ua (ua⁻¹ p) = p` for every path `p` in the image of `ua`
/// (every equivalence table names such a path).  Small spaces are
/// exhausted table-by-table — including non-equivalence tables, a strict
/// strengthening of the claim — larger ones over the equivalences alone;
/// if even that search exceeds its budget, the symbolic representation
/// argument (`ua_retraction_proved`) decides the law directly, so this
/// function never actually returns `LawUndecided` for this law either —
/// see `ua_section_all`'s doc comment for the same reasoning.
pub fn ua_retraction_all(a : Ty, b : Ty) -> LawVerdict {
  if ty_card(a) != ty_card(b) {
    return LawHolds
  }
  if !exhaustion_search_feasible(ty_card(a)) {
    return ua_retraction_proved(a, b)
  }
  match
    exhaust_tables(a, b, m => ua_retraction(cpath_ua(m)), law_table_budget()) {
    LawUndecided =>
      match
        exhaust_equiv(a, b, m => ua_retraction(cpath_ua(m)), law_enum_budget()) {
        LawUndecided => ua_retraction_proved(a, b)
        verdict => verdict
      }
    verdict => verdict
  }
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
/// number of equivalences, i.e. n! for equal sizes and 0 otherwise.  Exact
/// at every size (`BigNat`).
pub fn univalence_path_count(a : Ty, b : Ty) -> BigNat {
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
/// Commutativity of the finite universe's sum former: `A + B ≃ B + A` by
/// swapping the tag (`inl x ↦ inr x`, `inr y ↦ inl y`).  This is always an
/// equivalence (it is its own inverse, up to relabelling), and it is the
/// generic witness that `TySum` (SPEC §四 item 9(c)) is a real type former
/// in the computable-univalence layer, not merely a tag recognised by
/// `ty_card`/`elems_of`: the search, counting and law machinery below all
/// apply to it unchanged.
pub fn fin_sum_swap(a : Ty, b : Ty) -> FinMap {
  let na = ty_card(a)
  let nb = ty_card(b)
  let table : Array[Int32] = []
  // Left-tagged elements of `a` (indices `0 .. na`) land on the
  // right-tagged elements of `b` in the swapped type (indices `nb .. nb+na`).
  for _i in 0..<na {
    table.push(nb + table.length())
  }
  // Right-tagged elements of `b` (indices `na .. na+nb`) land on the
  // left-tagged elements of `a` in the swapped type (indices `0 .. nb`).
  for j in 0..<nb {
    table.push(j)
  }
  FinMap::{ src: TySum(a, b), dst: TySum(b, a), table, }
}

///|
/// The whole computable-univalence battery: the law battery over small
/// types (every verdict decided and `LawHolds`), plus the robustness
/// battery over 16-element types — where the old `Int32` formulas
/// overflowed (`16^16 ≡ 0`, `16! > 2^31`) and every check silently passed
/// or hung — now exact: counts, search and the decidability theorem all
/// compute.
pub fn univalence_compute_all() -> Bool {
  let tys = [TyUnit, TyBool, TyProd(TyBool, TyBool)]
  let mut ok = true
  for i in 0..<tys.length() {
    for j in 0..<tys.length() {
      ok = ok &&
        univalence_decides(tys[i], tys[j]) &&
        ua_section_all(tys[i], tys[j]) == LawHolds &&
        ua_retraction_all(tys[i], tys[j]) == LawHolds &&
        transport_preserves_cardinality(tys[i], tys[j])
    }
    ok = ok && ua_refl_is_identity(tys[i])
  }
  let n = fin_not_bool()
  let s = fin_swap_bool_pair()
  // 16-element types: two 4-element products.  The counting formulas are
  // exact, the search is pruned, and the theorem is decided.
  let b4 = TyProd(TyBool, TyBool)
  let b16 = TyProd(b4, b4)
  let big_ok = bignat_to_string(fact(16)) == "20922789888000" &&
    bignat_to_string(univalence_path_count(b16, b16)) == "20922789888000" &&
    bignat_to_string(fin_map_count(b16, b16)) == "18446744073709551616" &&
    univalence_decides(b16, b16) &&
    univalence_decides(b16, b4) &&
    fin_equiv_search(b16, b4) is None &&
    transport_preserves_cardinality(b16, b16)
  let big_search = match fin_equiv_search(b16, b16) {
    Some(m) =>
      fin_map_is_equiv(m) && ua_section(m) && ua_retraction(cpath_ua(m))
    None => false
  }
  // Groupoid structure on univalence paths (both worked examples).
  let np = cpath_ua(n)
  let sp = cpath_ua(s)
  let grp_ok = cpath_comp_left_unit(np) &&
    cpath_comp_right_unit(np) &&
    cpath_comp_left_unit(sp) &&
    cpath_comp_right_unit(sp) &&
    cpath_sym_involutive(np) &&
    cpath_sym_involutive(sp) &&
    cpath_sym_refl(TyBool) &&
    cpath_sym_refl(b4) &&
    cpath_sym_refl(b16) &&
    cpath_sym_comp(np, np) &&
    cpath_sym_comp(sp, sp) &&
    cpath_comp_assoc(np, np, np) &&
    cpath_comp_assoc(sp, sp, sp) &&
    transport_comp_computes(np, np) &&
    transport_comp_computes(sp, sp) &&
    transport_refl_identity(TyBool) &&
    transport_refl_identity(b4) &&
    transport_refl_identity(b16)
  // Sum-type widening (item 9(c)): `A + B ≃ B + A` is a real equivalence
  // the search/count/decision machinery handles unchanged.
  let sum_a = TyBool
  let sum_b = TySum(TyUnit, TyBool)
  let sum_swap = fin_sum_swap(sum_a, sum_b)
  let sum_ok =
    fin_map_is_equiv(sum_swap) &&
    univalence_decides(sum_swap.src, sum_swap.dst) &&
    ua_section_all(sum_swap.src, sum_swap.dst) == LawHolds &&
    ua_retraction_all(sum_swap.src, sum_swap.dst) == LawHolds
  sum_ok &&
  grp_ok &&
  ok &&
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
  big_ok &&
  big_search
}
