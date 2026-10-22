///|
// A sum-aware extension of the wiring DSL (SPEC §四 item 9(c), wiring
// layer).
//
// `Wiring` (wiring.mbt) models equivalences as per-leaf signed
// permutations, which only makes sense for the Bool/Unit/Product fragment
// — a `TySum` element picks *one* branch, so it has no fixed leaf count to
// assign, and `leaves_of_ty`/`wiring_apply` correctly `abort` on it.
//
// `SumWiring` adds exactly the combinators a coproduct needs, in the same
// constructive-DSL spirit as `Wiring` itself (`wiring_id`/`wiring_not`/
// `wiring_swap`/`wiring_prod`/`wiring_comp`/`wiring_inv` are a handful of
// named constructors, not "every possible equivalence"):
//
//   SWLeaf(w)        -- the existing product/bool/unit fragment, unchanged
//   SWSum(w1, w2)    -- A+C ≃ B+D, tag-preserving: w1 on the left branch,
//                       w2 on the right
//   SWSwap(a, b)     -- A+B ≃ B+A, the branch swap (the `SumWiring`
//                       counterpart of `fin_sum_swap` in the
//                       univalence_compute.mbt FinMap layer)
//   SWComp(w1,w2)    -- composition, `w2` after `w1`, matching
//                       `wiring_comp`'s convention; `sumwiring_inv` closes
//                       the DSL under inverse by pushing the inverse down
//                       to the leaves instead of adding a fifth
//                       constructor
//
// Scope: a `TySum` may itself nest further `TySum`s (`SWSum`/`SWSwap`
// recurse), and each summand may be any type `Wiring` already supports
// (Bool/Unit/Product). What is *not* supported is a `TySum` nested
// strictly inside a `TyProd` (e.g. `TyProd(TySum(Bool,Unit), Bool)`) —
// `Wiring`'s leaf flattening cannot see across the sum boundary there,
// and extending it to do so is a larger change than this item asks for;
// `sumwiring_of_ty_id`, used by `sumwiring_id`, makes this restriction an
// explicit `abort` rather than a silent miscount, exactly mirroring
// `wiring.mbt`'s own convention for its own fragment boundary.

///|
pub enum SumWiring {
  SWLeaf(Wiring)
  SWSum(SumWiring, SumWiring)
  SWSwap(Ty, Ty)
  SWComp(SumWiring, SumWiring)
}

///|
/// The source type of a `SumWiring`.
pub fn sumwiring_src(w : SumWiring) -> Ty {
  match w {
    SWLeaf(wr) => wr.src
    SWSum(w1, w2) => TySum(sumwiring_src(w1), sumwiring_src(w2))
    SWSwap(a, b) => TySum(a, b)
    SWComp(w1, _) => sumwiring_src(w1)
  }
}

///|
/// The destination type of a `SumWiring`.
pub fn sumwiring_dst(w : SumWiring) -> Ty {
  match w {
    SWLeaf(wr) => wr.dst
    SWSum(w1, w2) => TySum(sumwiring_dst(w1), sumwiring_dst(w2))
    SWSwap(a, b) => TySum(b, a)
    SWComp(_, w2) => sumwiring_dst(w2)
  }
}

///|
/// The identity `SumWiring` on `ty`: recurses into `SWSum` at every
/// `TySum` node, and falls back to the plain `Wiring` identity on the
/// pure product/bool/unit fragment (see the module comment for the
/// nesting restriction this inherits from `wiring_id`/`leaves_of_ty`).
pub fn sumwiring_id(ty : Ty) -> SumWiring {
  match ty {
    TySum(a, b) => SWSum(sumwiring_id(a), sumwiring_id(b))
    other => SWLeaf(wiring_id(other))
  }
}

///|
/// Tag-preserving sum of two `SumWiring`s: `w1 ⊕ w2 : A+C ≃ B+D` applies
/// `w1 : A ≃ B` on the left branch and `w2 : C ≃ D` on the right branch,
/// never crossing tags.
pub fn sumwiring_sum(w1 : SumWiring, w2 : SumWiring) -> SumWiring {
  SWSum(w1, w2)
}

///|
/// The branch swap `A+B ≃ B+A` — the `SumWiring` counterpart of
/// `fin_sum_swap` in the univalence_compute.mbt `FinMap` layer.
pub fn sumwiring_swap(a : Ty, b : Ty) -> SumWiring {
  SWSwap(a, b)
}

///|
/// Composition, `w2` after `w1`, matching `wiring_comp`'s convention.
/// Normalizes wherever the sub-structure lets it, instead of always
/// wrapping in `SWComp`:
///   * two leaves compose to a single flattened leaf via `wiring_comp`
///     (this is the case *every* pre-existing, product-only caller hits —
///     preserving it is what keeps `equiv_comp`/`equiv_inv`'s results in
///     the same normal form `wiring_comp`/`wiring_inv` always produced, so
///     structural-equality law checks elsewhere are unaffected by this
///     extension);
///   * two tag-preserving sums compose branchwise;
///   * a swap followed by the matching reverse swap is the identity.
/// Anything else (e.g. composing with an un-normalized `SWComp`) falls
/// back to the literal `SWComp` wrapper.
pub fn sumwiring_comp(w1 : SumWiring, w2 : SumWiring) -> SumWiring {
  match (w1, w2) {
    (SWLeaf(a), SWLeaf(b)) => SWLeaf(wiring_comp(a, b))
    (SWSum(a1, a2), SWSum(b1, b2)) =>
      SWSum(sumwiring_comp(a1, b1), sumwiring_comp(a2, b2))
    (SWSwap(a, b), SWSwap(b2, a2)) =>
      if a == a2 && b == b2 {
        SWSum(sumwiring_id(a), sumwiring_id(b))
      } else {
        SWComp(w1, w2)
      }
    _ => SWComp(w1, w2)
  }
}

///|
/// Inverse, pushed down to the leaves and to `SWSwap` (self-inverse up to
/// swapping its two type arguments) and composed through `SWComp` via the
/// same normalizing `sumwiring_comp`, rather than represented as an
/// opaque wrapper — so `sumwiring_wf`/`sumwiring_apply` never need to
/// unwind one, and the leaf case stays in exactly the normal form
/// `wiring_inv` always produced.
pub fn sumwiring_inv(w : SumWiring) -> SumWiring {
  match w {
    SWLeaf(wr) => SWLeaf(wiring_inv(wr))
    SWSum(w1, w2) => SWSum(sumwiring_inv(w1), sumwiring_inv(w2))
    SWSwap(a, b) => SWSwap(b, a)
    SWComp(w1, w2) => sumwiring_comp(sumwiring_inv(w2), sumwiring_inv(w1))
  }
}

///|
/// Symbolic well-formedness, recursively: every leaf wiring is a signed
/// permutation, every `SWSum` combines two well-formed pieces, every
/// `SWComp` lines up source/destination at the splice point, `SWSwap` is
/// always well-formed (it is total and bijective by construction).
pub fn sumwiring_wf(w : SumWiring) -> Bool {
  match w {
    SWLeaf(wr) => wiring_wf(wr)
    SWSum(w1, w2) => sumwiring_wf(w1) && sumwiring_wf(w2)
    SWSwap(_, _) => true
    SWComp(w1, w2) =>
      sumwiring_wf(w1) &&
      sumwiring_wf(w2) &&
      sumwiring_dst(w1) == sumwiring_src(w2)
  }
}

///|
/// Structural (canonical-form) equality — like `wiring_eq`, this compares
/// the DSL term itself, not a normal form, so e.g. `SWComp(id, w)` and `w`
/// are not identified (consistent with `wiring_eq`'s own granularity).
pub fn sumwiring_eq(a : SumWiring, b : SumWiring) -> Bool {
  match (a, b) {
    (SWLeaf(wa), SWLeaf(wb)) => wiring_eq(wa, wb)
    (SWSum(a1, a2), SWSum(b1, b2)) =>
      sumwiring_eq(a1, b1) && sumwiring_eq(a2, b2)
    (SWSwap(a1, a2), SWSwap(b1, b2)) => a1 == b1 && a2 == b2
    (SWComp(a1, a2), SWComp(b1, b2)) =>
      sumwiring_eq(a1, b1) && sumwiring_eq(a2, b2)
    _ => false
  }
}

///|
/// Evaluate a `SumWiring` on a value: `SWLeaf` delegates to
/// `wiring_apply`; `SWSum` dispatches on the tag and recurses into the
/// matching branch's sub-wiring, preserving the tag; `SWSwap` flips the
/// tag; `SWComp`/`SWInv` thread through as expected.
pub fn sumwiring_apply(w : SumWiring, v : PVal) -> PVal {
  match w {
    SWLeaf(wr) => wiring_apply(wr, v)
    SWSum(w1, w2) =>
      match v {
        PVLeft(x) => PVLeft(sumwiring_apply(w1, x))
        PVRight(y) => PVRight(sumwiring_apply(w2, y))
        other => other
      }
    SWSwap(_, _) =>
      match v {
        PVLeft(x) => PVRight(x)
        PVRight(y) => PVLeft(y)
        other => other
      }
    SWComp(w1, w2) => sumwiring_apply(w2, sumwiring_apply(w1, v))
  }
}
