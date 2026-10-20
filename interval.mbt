///|
// The cubical interval and face (cofibration) formulas.
//
// The interval I is a De Morgan algebra: dimension expressions are built
// from 0, 1, variables, ¬ (1−x), ∧ (min), ∨ (max).  Semantically a
// dimension expression denotes a function Iⁿ → I; at the endpoints it
// denotes a boolean function, which is what face formulas test.
//
// A face formula φ (cofibration) is built from equations (r = 0), (r = 1)
// by ∧ and ∨.  Because the endpoint semantics is finite (2ⁿ assignments),
// satisfiability, entailment φ ≤ ψ and equality of faces are decidable by
// exhaustive enumeration.  The quotient of systems by face equality — and
// pruning of unsatisfiable / subsumed branches — rests on these decisions.

///|
pub enum Dim {
  DZero
  DOne
  DVar(Int32)
  DNeg(Dim)
  DAnd(Dim, Dim)
  DOr(Dim, Dim)
} derive(Debug, Eq)

///|
pub extend Dim with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Dim with Eq::{not_equal, equal}

///|
pub fn dmin(a : Double, b : Double) -> Double {
  if a < b {
    a
  } else {
    b
  }
}

///|
pub fn dmax(a : Double, b : Double) -> Double {
  if a > b {
    a
  } else {
    b
  }
}

///|
/// Interval semantics: env assigns each dimension variable a point of I.
pub fn eval_dim(r : Dim, env : Array[Double]) -> Double {
  match r {
    DZero => 0.0
    DOne => 1.0
    DVar(i) => if i >= 0 && i < env.length() { env[i] } else { 0.0 }
    DNeg(a) => 1.0 - eval_dim(a, env)
    DAnd(a, b) => dmin(eval_dim(a, env), eval_dim(b, env))
    DOr(a, b) => dmax(eval_dim(a, env), eval_dim(b, env))
  }
}

///|
/// Endpoint (boolean) semantics of a dimension expression.
pub fn eval_dim_bool(r : Dim, env : Array[Bool]) -> Bool {
  match r {
    DZero => false
    DOne => true
    DVar(i) => if i >= 0 && i < env.length() { env[i] } else { false }
    DNeg(a) => !eval_dim_bool(a, env)
    DAnd(a, b) => eval_dim_bool(a, env) && eval_dim_bool(b, env)
    DOr(a, b) => eval_dim_bool(a, env) || eval_dim_bool(b, env)
  }
}

///|
/// De Morgan / lattice laws of I hold definitionally in the semantics.
/// Spot-check the characteristic ones on sample points: ¬¬r = r,
/// r ∧ ¬r and r ∨ ¬r are the *non-boolean* middle values min(x,1−x) /
/// max(x,1−x), and De Morgan duality ¬(a∧b) = ¬a ∨ ¬b.
pub fn interval_laws_hold(samples : Array[Double]) -> Bool {
  for s in 0..<samples.length() {
    let x = samples[s]
    let env : Array[Double] = [x]
    let r = DVar(0)
    if (eval_dim(DNeg(DNeg(r)), env) - x).abs() >= eps {
      return false
    }
    let meet_self = eval_dim(DAnd(r, DNeg(r)), env)
    if (meet_self - dmin(x, 1.0 - x)).abs() >= eps {
      return false
    }
    let join_self = eval_dim(DOr(r, DNeg(r)), env)
    if (join_self - dmax(x, 1.0 - x)).abs() >= eps {
      return false
    }
    let lhs = eval_dim(DNeg(DAnd(r, DOne)), env)
    let rhs = eval_dim(DOr(DNeg(r), DNeg(DOne)), env)
    if (lhs - rhs).abs() >= eps {
      return false
    }
  }
  true
}
