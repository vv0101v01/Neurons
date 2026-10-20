///|
// The finite universe: types built from Bool and Unit by products, their
// elements, and the two trait extensions used across the package.
//
// Extracted from pathp_glue.mbt so that the wiring layer (which only needs
// these two types) no longer has to reach into the ua/Glue layer, and the
// ua/Glue layer no longer has to own them.  Declarations moved between files
// of one package do not change the package interface.

///|
pub enum Ty {
  TyBool
  TyUnit
  TyProd(Ty, Ty)
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
} derive(Debug, Eq)
