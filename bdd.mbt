///|
// Symbolic decision for face formulas via reduced ordered BDDs.
//
// The first version decided face satisfiability / entailment / equality
// by enumerating all 2ⁿ endpoint assignments.  This module replaces that
// with a symbolic normal form: every face formula compiles to a reduced
// ordered binary decision diagram (variables in increasing order, nodes
// with equal children eliminated).  Two faces are equal in the quotient
// iff their BDDs are *structurally identical* — the BDD is the canonical
// representative of the quotient class.  Satisfiability is "BDD ≠ ⊥",
// entailment is "bdd(f ∧ ¬g) = ⊥", and a satisfying assignment can be
// read off a root-to-⊤ path (witness), all without enumerating the cube.
//
// Categorically, faces modulo BDD equality form a bounded distributive
// lattice, i.e. a poset category with ∧ as product, ∨ as coproduct,
// ⊤ terminal and ⊥ initial; face_le is its (unique) morphism existence.
//
// The brute-force enumerator survives only in the whitebox tests, as an
// independent oracle that the symbolic decisions are differentially
// checked against; library decision paths never call it.

///|
fn bdd_node(vidx : Int32, lo : Bdd, hi : Bdd) -> Bdd {
  if lo == hi {
    lo // reduction rule: a test with equal outcomes is no test
  } else {
    BddNode(vidx, lo, hi)
  }
}

///|
/// The canonical form of a face over variables [0, n): its ROBDD.
pub fn bdd_of_face(f : Face, n : Int32) -> Bdd {
  // Built in the interned DAG manager (bdd_dag.mbt), then expanded
  // once to the legacy tree type with shared subdiagrams shared.
  let manager = bdd_manager_new(n)
  let root = bdd_dag_build_face(manager, face_bound(f, n))
  bdd_tree_of_dag(manager, root)
}

///|
pub fn bdd_not(b : Bdd) -> Bdd {
  match b {
    BddZero => BddOne
    BddOne => BddZero
    BddNode(v, lo, hi) => bdd_node(v, bdd_not(lo), bdd_not(hi))
  }
}

///|
pub fn bdd_and(a : Bdd, b : Bdd) -> Bdd {
  match (a, b) {
    (BddZero, _) | (_, BddZero) => BddZero
    (BddOne, x) => x
    (x, BddOne) => x
    (BddNode(v, alo, ahi), BddNode(w, blo, bhi)) =>
      if v == w {
        bdd_node(v, bdd_and(alo, blo), bdd_and(ahi, bhi))
      } else if v < w {
        bdd_node(v, bdd_and(alo, b), bdd_and(ahi, b))
      } else {
        bdd_node(w, bdd_and(a, blo), bdd_and(a, bhi))
      }
  }
}

///|
pub fn bdd_or(a : Bdd, b : Bdd) -> Bdd {
  match (a, b) {
    (BddOne, _) | (_, BddOne) => BddOne
    (BddZero, x) => x
    (x, BddZero) => x
    (BddNode(v, alo, ahi), BddNode(w, blo, bhi)) =>
      if v == w {
        bdd_node(v, bdd_or(alo, blo), bdd_or(ahi, bhi))
      } else if v < w {
        bdd_node(v, bdd_or(alo, b), bdd_or(ahi, b))
      } else {
        bdd_node(w, bdd_or(a, blo), bdd_or(a, bhi))
      }
  }
}

///|
/// Symbolic satisfiability.
pub fn bdd_sat_face(f : Face, n : Int32) -> Bool {
  bdd_dag_sat_face(f, n)
}

///|
/// Symbolic entailment: f ≤ g iff f ∧ ¬g is unsatisfiable.
pub fn bdd_face_le(f : Face, g : Face, n : Int32) -> Bool {
  bdd_dag_face_le(f, g, n)
}

///|
/// Symbolic quotient equality: identical canonical forms.
pub fn bdd_face_eq(f : Face, g : Face, n : Int32) -> Bool {
  bdd_dag_face_eq(f, g, n)
}

///|
/// A satisfying endpoint assignment read off the BDD, if one exists.
pub fn face_witness(f : Face, n : Int32) -> Array[Bool]? {
  let manager = bdd_manager_new(n)
  let root = bdd_dag_build_face(manager, f)
  bdd_dag_witness(manager, root)
}

///|
/// Canonical-form spot laws: duplicates and units vanish in the BDD,
/// De Morgan-shaped rewrites coincide, and witnesses satisfy the face.
pub fn check_bdd_canonical() -> Bool {
  let i0 = face_var0(0)
  let j1 = face_var1(1)
  let f = FOr(i0, j1)
  if bdd_of_face(FOr(f, f), 2) != bdd_of_face(f, 2) {
    return false
  }
  if bdd_of_face(FAnd(FTop, f), 2) != bdd_of_face(f, 2) {
    return false
  }
  if bdd_of_face(FAnd(i0, face_var1(0)), 2) != BddZero {
    return false
  }
  // (i=0) as a face is the constant-true under (¬i=1): FEq1(DNeg i) ≡ FEq0(i)
  if !bdd_face_eq(FEq1(DNeg(DVar(0))), i0, 2) {
    return false
  }
  match face_witness(FAnd(i0, j1), 2) {
    Some(env) => face_holds(FAnd(i0, j1), env) && !env[0] && env[1]
    None => false
  }
}

///|
/// Satisfiability of a face over n variables, decided symbolically (ROBDD ≠ ⊥; see bdd.mbt).
pub fn face_sat(f : Face, n : Int32) -> Bool {
  bdd_sat_face(f, n)
}

///|
pub fn face_unsat(f : Face, n : Int32) -> Bool {
  !face_sat(f, n)
}

///|
/// Entailment of faces: φ ≤ ψ iff every endpoint satisfying φ satisfies ψ.
pub fn face_le(f : Face, g : Face, n : Int32) -> Bool {
  bdd_face_le(f, g, n)
}

///|
/// Equality in the quotient of face formulas by semantic equivalence:
/// decided by structural equality of canonical ROBDDs (bdd.mbt).  Syntactically different formulas
/// (e.g. φ ∨ φ and φ) become *equal* here — the quotient that system
/// pruning and system equivalence are taken modulo.
pub fn face_eq_mod(f : Face, g : Face, n : Int32) -> Bool {
  bdd_face_eq(f, g, n)
}
