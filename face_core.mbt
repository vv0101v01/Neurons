///|
// Shared face algebra: the face lattice syntax, the structural operations on
// it (variables, simplification, substitution, bounding) and the tree-shaped
// BDD declaration.
//
// This file is the floor that `interval.mbt` (De Morgan evaluation) and
// `bdd.mbt`/`bdd_dag.mbt` (decisions) both build on.  Before the split those
// three files formed a cycle: the interval called the BDD decisions while the
// BDDs needed the interval syntax.  Extracting the syntax breaks it into a
// chain  face_core <- bdd_dag <- bdd <- {interval, system}.

///|
pub extend Face with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Face with Eq::{not_equal, equal}

///|
pub enum Face {
  FTop
  FBot
  FEq0(Dim)
  FEq1(Dim)
  FAnd(Face, Face)
  FOr(Face, Face)
} derive(Debug, Eq)

///|
/// Does the face hold at this endpoint assignment?
pub fn face_holds(f : Face, env : Array[Bool]) -> Bool {
  match f {
    FTop => true
    FBot => false
    FEq0(r) => !eval_dim_bool(r, env)
    FEq1(r) => eval_dim_bool(r, env)
    FAnd(a, b) => face_holds(a, env) && face_holds(b, env)
    FOr(a, b) => face_holds(a, env) || face_holds(b, env)
  }
}

///|
pub fn pow2(n : Int32) -> Int32 {
  let mut acc = 1
  for _i in 0..<n {
    acc = acc * 2
  }
  acc
}

///|
/// The `mask`-th endpoint assignment of `n` dimension variables.
pub fn assignment_of_mask(mask : Int32, n : Int32) -> Array[Bool] {
  let env : Array[Bool] = []
  for k in 0..<n {
    env.push(((mask >> k) & 1) == 1)
  }
  env
}

///|
/// The face (i = 0) for the i-th dimension variable.
pub fn face_var0(i : Int32) -> Face {
  FEq0(DVar(i))
}

///|
/// The face (i = 1) for the i-th dimension variable.
pub fn face_var1(i : Int32) -> Face {
  FEq1(DVar(i))
}

///|
pub enum Bdd {
  BddZero
  BddOne
  BddNode(Int32, Bdd, Bdd) // variable, low (x=0), high (x=1)
} derive(Debug, Eq)

///|
pub extend Bdd with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Bdd with Eq::{not_equal, equal}

///|
pub fn sort_ints(xs : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<xs.length() {
    out.push(xs[i])
  }
  for _pass in 0..<out.length() {
    for j in 0..<(out.length() - 1) {
      if out[j] > out[j + 1] {
        let tmp = out[j]
        out[j] = out[j + 1]
        out[j + 1] = tmp
      }
    }
  }
  out
}

///|
pub fn contains_int(xs : Array[Int32], x : Int32) -> Bool {
  for i in 0..<xs.length() {
    if xs[i] == x {
      return true
    }
  }
  false
}

///|
fn dim_vars_into(r : Dim, acc : Array[Int32]) -> Unit {
  match r {
    DZero | DOne => ()
    DVar(i) => if !contains_int(acc, i) { acc.push(i) }
    DNeg(a) => dim_vars_into(a, acc)
    DAnd(a, b) => {
      dim_vars_into(a, acc)
      dim_vars_into(b, acc)
    }
    DOr(a, b) => {
      dim_vars_into(a, acc)
      dim_vars_into(b, acc)
    }
  }
}

///|
fn face_vars_into(f : Face, acc : Array[Int32]) -> Unit {
  match f {
    FTop | FBot => ()
    FEq0(r) | FEq1(r) => dim_vars_into(r, acc)
    FAnd(a, b) => {
      face_vars_into(a, acc)
      face_vars_into(b, acc)
    }
    FOr(a, b) => {
      face_vars_into(a, acc)
      face_vars_into(b, acc)
    }
  }
}

///|
/// Variables occurring in a face, sorted increasingly (the BDD order).
pub fn face_vars(f : Face) -> Array[Int32] {
  let acc : Array[Int32] = []
  face_vars_into(f, acc)
  sort_ints(acc)
}

///|
/// Constant simplification of dimension expressions (the endpoint
/// Boolean algebra): this rewriting is what prunes the BDD construction.
pub fn dim_simplify(r : Dim) -> Dim {
  match r {
    DNeg(a) =>
      match dim_simplify(a) {
        DZero => DOne
        DOne => DZero
        DNeg(x) => x
        x => DNeg(x)
      }
    DAnd(a, b) =>
      match (dim_simplify(a), dim_simplify(b)) {
        (DZero, _) | (_, DZero) => DZero
        (DOne, x) => x
        (x, DOne) => x
        (x, y) => if x == y { x } else { DAnd(x, y) }
      }
    DOr(a, b) =>
      match (dim_simplify(a), dim_simplify(b)) {
        (DOne, _) | (_, DOne) => DOne
        (DZero, x) => x
        (x, DZero) => x
        (x, y) => if x == y { x } else { DOr(x, y) }
      }
    other => other
  }
}

///|
pub fn dim_subst(r : Dim, vidx : Int32, val : Bool) -> Dim {
  match r {
    DVar(i) => if i == vidx { if val { DOne } else { DZero } } else { r }
    DNeg(a) => dim_simplify(DNeg(dim_subst(a, vidx, val)))
    DAnd(a, b) =>
      dim_simplify(DAnd(dim_subst(a, vidx, val), dim_subst(b, vidx, val)))
    DOr(a, b) =>
      dim_simplify(DOr(dim_subst(a, vidx, val), dim_subst(b, vidx, val)))
    other => other
  }
}

///|
pub fn face_simplify(f : Face) -> Face {
  match f {
    FEq0(r) =>
      match dim_simplify(r) {
        DZero => FTop
        DOne => FBot
        x => FEq0(x)
      }
    FEq1(r) =>
      match dim_simplify(r) {
        DZero => FBot
        DOne => FTop
        x => FEq1(x)
      }
    FAnd(a, b) =>
      match (face_simplify(a), face_simplify(b)) {
        (FBot, _) | (_, FBot) => FBot
        (FTop, x) => x
        (x, FTop) => x
        (x, y) => if x == y { x } else { FAnd(x, y) }
      }
    FOr(a, b) =>
      match (face_simplify(a), face_simplify(b)) {
        (FTop, _) | (_, FTop) => FTop
        (FBot, x) => x
        (x, FBot) => x
        (x, y) => if x == y { x } else { FOr(x, y) }
      }
    other => other
  }
}

///|
pub fn face_subst(f : Face, vidx : Int32, val : Bool) -> Face {
  match f {
    FEq0(r) => face_simplify(FEq0(dim_subst(r, vidx, val)))
    FEq1(r) => face_simplify(FEq1(dim_subst(r, vidx, val)))
    FAnd(a, b) =>
      face_simplify(FAnd(face_subst(a, vidx, val), face_subst(b, vidx, val)))
    FOr(a, b) =>
      face_simplify(FOr(face_subst(a, vidx, val), face_subst(b, vidx, val)))
    other => other
  }
}

///|
fn dim_bound(r : Dim, n : Int32) -> Dim {
  match r {
    DVar(i) => if i < 0 || i >= n { DZero } else { r }
    DNeg(a) => dim_simplify(DNeg(dim_bound(a, n)))
    DAnd(a, b) => dim_simplify(DAnd(dim_bound(a, n), dim_bound(b, n)))
    DOr(a, b) => dim_simplify(DOr(dim_bound(a, n), dim_bound(b, n)))
    other => other
  }
}

///|
/// Variable indices outside [0, n) denote 0, matching eval_dim_bool.
pub fn face_bound(f : Face, n : Int32) -> Face {
  match f {
    FEq0(r) => face_simplify(FEq0(dim_bound(r, n)))
    FEq1(r) => face_simplify(FEq1(dim_bound(r, n)))
    FAnd(a, b) => face_simplify(FAnd(face_bound(a, n), face_bound(b, n)))
    FOr(a, b) => face_simplify(FOr(face_bound(a, n), face_bound(b, n)))
    other => other
  }
}
