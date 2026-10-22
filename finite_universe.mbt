///|
// The finite universe: types built from Bool and Unit by products and
// sums, their elements, and the two trait extensions used across the
// package.
//
// Extracted from pathp_glue.mbt so that the wiring layer (which only needs
// these two types) no longer has to reach into the ua/Glue layer, and the
// ua/Glue layer no longer has to own them.  Declarations moved between files
// of one package do not change the package interface.
//
// `TySum` widens the universe beyond the Bool/Unit/Product fragment (SPEC
// §四 item 9(c)): it is supported throughout the computable-univalence
// layer (`ty_card`, `elems_of`, `in_ty`, and hence `FinMap`/`CPath`/
// `fin_equiv_search`/`fin_equiv_count`/`univalence_decides` all work on it
// unchanged, since they are generic over any `Ty`).  It is deliberately
// *not* supported by the leaf-permutation wiring model (`wiring.mbt`,
// which represents every equivalence as a per-leaf assignment and so only
// ever models the product fragment) or by the Kan semantic embedding
// (`kan_dep.mbt`'s `dvalue_of_ty`/`dline_of_ty`, which would need a
// coproduct Kan structure that does not exist yet); those two call `abort`
// on `TySum` rather than silently mis-modelling it.

///|
pub enum Ty {
  TyBool
  TyUnit
  TyProd(Ty, Ty)
  TySum(Ty, Ty)
} derive(Debug, Eq)

///|
pub extend PVal with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend PVal with Eq::{not_equal, equal}

///|
pub extend Ty with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Ty with Eq::{not_equal, equal}

///|
pub enum PVal {
  PVUnit
  PVBool(Bool)
  PVPair(PVal, PVal)
  PVLeft(PVal)
  PVRight(PVal)
} derive(Debug, Eq)
