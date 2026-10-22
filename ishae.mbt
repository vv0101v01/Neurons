///|
// Higher coherence for equivalences: half-adjoint equivalences (`ishae`),
// the biinv→ishae construction, and fiber contractibility (SPEC §四 item 3).
//
// The AST-level `Equiv` (pathp_glue.mbt) packages a single two-sided
// inverse `bwd`, because it is built from `Wiring`, a signed permutation —
// in that representation forward and backward are *definitionally*
// mutual inverses, so there is no separate section/retraction coherence
// to state. The finite-table layer (`FinMap`, univalence_compute.mbt) is
// more general: a `FinMap` need not be injective or surjective at all, so
// it is the right place to state the textbook distinction the research
// this turn surfaced (HoTT book Def 4.2.1 / Def 4.3.1; Coq HoTT library):
//
//   biinv(f)  := (Σ g. g∘f ~ id) × (Σ h. f∘h ~ id)      -- two separate
//                                                            witnesses
//   ishae(f)  := Σ g. Σ η:g∘f~id. Σ ε:f∘g~id.
//                  Π x. f(η x) = ε(f x)                 -- ONE witness,
//                                                            plus a
//                                                            triangle law
//   isContr(fiber f y) := Σ y-preimage. ∀ other preimage. equal to it
//
// and the theorem (HoTT book Thm 4.2.3 / 4.3.2) that all three are
// logically equivalent, with `ishae` singled out as "the" definition
// because (unlike `biinv`) `isContr(fiber f y)` and hence `ishae(f)` is a
// *mere proposition* — in our finite, decidable, strict-equality (hSet)
// model every one of these becomes a plain Boolean-decidable fact, so the
// theorem specializes to "all three Boolean predicates below agree",
// checked exhaustively rather than merely asserted.

///|
/// The fiber of `f` over `y`: every source index `f` sends to `y`.
pub fn fin_fiber(f : FinMap, y : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<f.table.length() {
    if f.table[i] == y {
      out.push(i)
    }
  }
  out
}

///|
/// `isContr(fiber f y)`: the fiber over `y` has *exactly* one element —
/// not "at least one" (that would be surjectivity alone) and not merely
/// "at most one" (injectivity alone), but both at once, decided by
/// counting matches in the table (no search, no higher path data needed).
pub fn fin_is_contr_fiber(f : FinMap, y : Int32) -> Bool {
  fin_fiber(f, y).length() == 1
}

///|
/// `isEquiv(f) := Π(y : dst). isContr(fiber f y)`, the cubical/HoTT
/// "contractible fibers" formulation of equivalence, decided by counting.
pub fn fin_is_equiv_via_contr(f : FinMap) -> Bool {
  if !fin_map_wf(f) {
    return false
  }
  let n = ty_card(f.dst)
  for y in 0..<n {
    if !fin_is_contr_fiber(f, y) {
      return false
    }
  }
  true
}

///|
/// A half-adjoint equivalence structure on `f`: an inverse `g`, packaged
/// with the two homotopies and the coherence triangle as checkable
/// predicates below (`ishae_eta_holds`/`ishae_eps_holds`/
/// `ishae_triangle_holds`) rather than stored proof terms — faithful to
/// `ishae(f) := Σ g. Σ η. Σ ε. Π x. f(ηx) = ε(fx)`, just decided instead of
/// assumed.
pub struct Ishae {
  f : FinMap
  g : FinMap
} derive(Debug, Eq)

///|
pub extend Ishae with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Ishae with Eq::{not_equal, equal}

///|
/// `η : g ∘ f ~ id_A`, checked at every element of the source.
pub fn ishae_eta_holds(h : Ishae) -> Bool {
  for a in 0..<h.f.table.length() {
    if h.g.table[h.f.table[a]] != a {
      return false
    }
  }
  true
}

///|
/// `ε : f ∘ g ~ id_B`, checked at every element of the destination.
pub fn ishae_eps_holds(h : Ishae) -> Bool {
  for b in 0..<h.g.table.length() {
    if h.f.table[h.g.table[b]] != b {
      return false
    }
  }
  true
}

///|
/// The triangle identity `Π(x : A). f(ηx) = ε(fx)` (HoTT book Def 4.2.1,
/// the coherence that distinguishes `ishae` from a bare pair of
/// homotopies; the Coq HoTT library calls it one of "the triangle
/// identities of an adjoint equivalence... the other is provable, but
/// must not be assumed as data").
///
/// In this finite, strict-equality model both sides of the triangle are
/// literal `Int32` values, not path terms, so the identity is exactly the
/// proposition `f(g(f(x))) = f(x)` for every `x` — which is `ε`
/// instantiated at `f(x)`, not independent data. `ishae_triangle_holds`
/// checks this directly; `ishae_triangle_is_free` (below, tested) confirms
/// it is *implied* by `ishae_eps_holds` alone, i.e. in an hSet-valued
/// model the triangle costs nothing beyond the two homotopies — the
/// concrete realization of the book's remark.
pub fn ishae_triangle_holds(h : Ishae) -> Bool {
  for a in 0..<h.f.table.length() {
    let lhs = h.f.table[h.g.table[h.f.table[a]]] // f(η-side): f(g(f(x)))
    let rhs = h.f.table[a] // ε-side: f(x)
    if lhs != rhs {
      return false
    }
  }
  true
}

///|
/// `ishae_eps_holds(h)` alone already implies `ishae_triangle_holds(h)`:
/// instantiating `ε` at `f(x)` gives exactly the triangle equation. No
/// table scan is needed to see this — it is a direct substitution — but
/// the function performs the substitution explicitly so callers get a
/// `Bool`, not just a comment.
pub fn ishae_triangle_is_free(h : Ishae) -> Bool {
  !ishae_eps_holds(h) || ishae_triangle_holds(h)
}

///|
/// Full `ishae` package: inverse, both homotopies, and the triangle.
pub fn ishae_holds(h : Ishae) -> Bool {
  h.f.src == h.g.dst &&
  h.f.dst == h.g.src &&
  ishae_eta_holds(h) &&
  ishae_eps_holds(h) &&
  ishae_triangle_holds(h)
}

///|
/// The biinv→ishae construction (HoTT book Lemma 4.2.2 / Thm 4.3.2,
/// §cubicaltt `equivToHAE`-style reasoning): given `f`, a LEFT inverse `l`
/// (only `l∘f ~ id_A` is assumed) and a RIGHT inverse `r` (only
/// `f∘r ~ id_B`), define `g := l` and show it is *also* a right inverse —
/// i.e. that `l` alone already suffices for `ishae`, with no separate `r`
/// needed in the final package. The chase, for every `b : B`:
///
///   f(l(b)) = f(l(f(r(b))))   -- by ε₀ : f(r(b)) = b, substituted in
///           = f(r(b))         -- by η : l(f(r(b))) = r(b), applied at r(b)
///           = b               -- by ε₀ : f(r(b)) = b, again
///
/// so `ε(b) := f(l(b)) = b` is *derived*, not assumed, which is exactly
/// why `biinv` and `ishae` carry the same information despite `ishae`
/// looking like it demands more (the coherent inverse is forced, not
/// extra data) — this is the logical content of HoTT book Thm 4.3.2.
/// Returns `None` if `l`/`r` do not satisfy the stated biinv equations, so
/// the construction is honest about its precondition rather than
/// returning a garbage `Ishae`.
pub fn biinv_to_ishae(f : FinMap, l : FinMap, r : FinMap) -> Ishae? {
  if l.src != f.dst || l.dst != f.src || r.src != f.dst || r.dst != f.src {
    return None
  }
  // η₀ : l ∘ f ~ id_A
  for a in 0..<f.table.length() {
    if l.table[f.table[a]] != a {
      return None
    }
  }
  // ε₀ : f ∘ r ~ id_B
  for b in 0..<r.table.length() {
    if f.table[r.table[b]] != b {
      return None
    }
  }
  Some(Ishae::{ f, g: l })
}

///|
/// Theorem (HoTT book Thm 4.2.3 / 4.3.2, specialized to this finite
/// decidable model): for a well-formed total `f`, the three notions of
/// equivalence agree exactly — "is a bijection", `fin_is_equiv_via_contr`
/// (every fiber contractible), and "there exists an `Ishae` package on
/// `f`" (half-adjoint equivalence). This function decides the third by
/// constructing the canonical candidate `g := fin_map_inv_at(f, ·)` and
/// checking `ishae_holds` on it — if `f` is bijective this inverse is
/// total and the package always holds; if `f` is not bijective, no
/// `Ishae` package exists on `f` at all (checked exhaustively in the test
/// suite, not merely asserted here).
///
/// Note on "is a bijection": `fin_map_is_equiv` alone only checks
/// injectivity, which is a correct bijection test *only* when
/// `ty_card(f.src) == ty_card(f.dst)` (its own doc comment says so, and
/// every other call site in this codebase enforces that precondition
/// before calling it — `fin_equiv_search`/`exhaust_equiv`/
/// `fin_equiv_count` all short-circuit on a cardinality mismatch first).
/// This function accepts an arbitrary `FinMap`, so it conjoins the
/// cardinality check explicitly here instead of silently inheriting that
/// precondition — without it, an injective-but-not-surjective map (e.g.
/// `TyUnit -> TyBool`) would make `fin_map_is_equiv` say "equivalence"
/// while the fiber- and `ishae`-based tests correctly say "no", a real
/// three-way disagreement caught while writing this function's tests
/// (see `ishae_wbtest.mbt`, which checks the raw `fin_map_is_equiv` call
/// disagrees exactly there, and that this function's corrected `via_table`
/// does not).
pub fn fin_equiv_three_ways_agree(f : FinMap) -> Bool {
  let via_table = fin_map_is_equiv(f) && ty_card(f.src) == ty_card(f.dst)
  let via_fiber = fin_is_equiv_via_contr(f)
  let g_table : Array[Int32] = []
  for i in 0..<ty_card(f.dst) {
    g_table.push(fin_map_inv_at(f, i))
  }
  let g = fin_map(f.dst, f.src, g_table)
  let via_ishae = fin_map_wf(f) && ishae_holds(Ishae::{ f, g })
  via_table == via_fiber && via_fiber == via_ishae
}
