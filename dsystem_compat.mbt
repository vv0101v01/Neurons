///|
// Compatibility decisions and first-match normal forms for raw
// semantic tube systems.
//
// A host program can build a `DSystem` directly from arbitrary tube
// branches.  Such a system need not be compatible: branches can
// disagree on overlaps, or disagree with a proposed composition base
// at dimension 0.  This file provides the missing checked boundary:
//
//   * `conv_at_under_face` decides conversion relative to a face by
//     decomposing the face BDD into satisfying cubes, restricting
//     the quoted values to each cube, and re-checking conversion;
//   * `dsystem_compatibility_report` / `dsystem_checked` decide and
//     package composition compatibility with a base;
//   * `dsystem_first_match_normal_form` gives every raw tube system
//     a BDD effective-region normal form (previously only partial
//     values had one), and `dsystem_first_match_system` turns it
//     back into a pairwise-disjoint composition system.

///|
fn bdd_cubes_into(
  b : Bdd,
  assignment : Array[Int32],
  out : Array[Array[Int32]],
) -> Unit {
  match b {
    BddZero => ()
    BddOne => out.push(assignment)
    BddNode(v, lo, hi) =>
      if v >= 0 && v < assignment.length() {
        let lo_assignment : Array[Int32] = []
        let hi_assignment : Array[Int32] = []
        for i in 0..<assignment.length() {
          lo_assignment.push(assignment[i])
          hi_assignment.push(assignment[i])
        }
        lo_assignment[v] = 0
        hi_assignment[v] = 1
        bdd_cubes_into(lo, lo_assignment, out)
        bdd_cubes_into(hi, hi_assignment, out)
      }
  }
}

///|
/// The satisfying cubes of a BDD over variables `[0, n)`.  Each cube
/// is a partial assignment: 0, 1, or -1 for an unconstrained variable.
pub fn bdd_satisfying_cubes(b : Bdd, n : Int32) -> Array[Array[Int32]] {
  let assignment : Array[Int32] = []
  for _i in 0..<n {
    assignment.push(-1)
  }
  let out : Array[Array[Int32]] = []
  bdd_cubes_into(b, assignment, out)
  out
}

///|
/// A Face formula for a BDD region, in disjunctive normal form over
/// literal faces `(i = 0)` and `(i = 1)`.
pub fn face_of_bdd(b : Bdd) -> Face {
  match b {
    BddZero => FBot
    BddOne => FTop
    BddNode(v, lo, hi) =>
      face_simplify(
        FOr(
          FAnd(FEq0(DVar(v)), face_of_bdd(lo)),
          FAnd(FEq1(DVar(v)), face_of_bdd(hi)),
        ),
      )
  }
}

///|
fn fresh_term_env(level : Int32) -> DEnv {
  let values : Array[DValue] = []
  for i in 0..<level {
    values.push(DVNeutral(DNVar(level - 1 - i)))
  }
  denv_from_array(values)
}

///|
fn cube_dim_env(assignment : Array[Int32]) -> DDimEnv {
  let n = assignment.length()
  let values : Array[Dim] = []
  for i in 0..<n {
    let level = n - 1 - i
    values.push(
      if assignment[level] == 0 {
        DZero
      } else if assignment[level] == 1 {
        DOne
      } else {
        DVar(level)
      },
    )
  }
  ddim_from_array(values)
}

///|
/// Conversion under the assumption that `face` holds.  Globally
/// convertible values pass immediately; otherwise both values are
/// restricted to every satisfying cube of the face.  For example, a
/// loop at dimension `i` and its base point are convertible under
/// `(i = 0)` but not globally.
pub fn conv_at_under_face(
  level : Int32,
  dlevel : Int32,
  face : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Bool {
  if face_is_bot_sem(face) {
    return true
  }
  if conv_at(level, dlevel, ty, a, b) {
    return true
  }
  let face_vars = face_nvars_sem(face)
  let dl = if dlevel > face_vars { dlevel } else { face_vars }
  let cubes = bdd_satisfying_cubes(bdd_of_face(face, dl), dl)
  if cubes.length() == 0 {
    return true
  }
  let ty_term = quote_ty(level, dl, ty)
  let a_term = quote_at(level, dl, ty, a)
  let b_term = quote_at(level, dl, ty, b)
  let term_env = fresh_term_env(level)
  for i in 0..<cubes.length() {
    let denv = cube_dim_env(cubes[i])
    let ty_value = deval_dim(ty_term, term_env, denv)
    let a_value = deval_dim(a_term, term_env, denv)
    let b_value = deval_dim(b_term, term_env, denv)
    if !conv_at(level, dl, ty_value, a_value, b_value) {
      return false
    }
  }
  true
}

///|
/// Tube-path conversion under a face, at both endpoints and at a
/// fresh generic composition dimension.
pub fn tube_paths_conv_under_face(
  level : Int32,
  dlevel : Int32,
  face : Face,
  line : (Dim) -> DValue,
  p : (Dim) -> DValue,
  q : (Dim) -> DValue,
) -> Bool {
  let fresh = DVar(dlevel)
  conv_at_under_face(level, dlevel, face, line(DZero), p(DZero), q(DZero)) &&
  conv_at_under_face(level, dlevel + 1, face, line(fresh), p(fresh), q(fresh)) &&
  conv_at_under_face(level, dlevel, face, line(DOne), p(DOne), q(DOne))
}

///|
pub enum DSystemIncompatibility {
  DSystemOk
  DSystemBaseIncompatible
  DSystemBranchesIncompatible
} derive(Debug, Eq)

///|
pub extend DSystemIncompatibility with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DSystemIncompatibility with Eq::{not_equal, equal}

///|
pub struct DSystemCompatibility {
  compatible : Bool
  reason : DSystemIncompatibility
  branch : Int32
  other_branch : Int32
} derive(Debug, Eq)

///|
pub extend DSystemCompatibility with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DSystemCompatibility with Eq::{not_equal, equal}

///|
/// Decide whether branches agree pairwise on every satisfiable
/// overlap.  Bottom branches are ignored.
pub fn dsystem_pairwise_compatible(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
) -> Bool {
  dsystem_compatibility_report(level, dlevel, line, system, None).compatible
}

///|
/// Full composition compatibility: pairwise agreement on overlaps
/// and agreement of every branch with `base` at dimension 0 on its
/// face.
pub fn dsystem_compatible_with_base(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
) -> Bool {
  dsystem_compatibility_report(level, dlevel, line, system, Some(base)).compatible
}

///|
/// Compatibility decision with the first mismatching branch (or pair
/// of branches) as a witness.
pub fn dsystem_compatibility_report(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue?,
) -> DSystemCompatibility {
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    if face_is_bot_sem(br.face) {
      continue
    }
    match base {
      Some(base_value) =>
        if !conv_at_under_face(
            level,
            dlevel,
            br.face,
            line(DZero),
            (br.path)(DZero),
            base_value,
          ) {
          return DSystemCompatibility::{
            compatible: false,
            reason: DSystemBaseIncompatible,
            branch: i,
            other_branch: -1,
          }
        }
      None => ()
    }
    for j in (i + 1)..<system.branches.length() {
      let other = system.branches[j]
      if face_is_bot_sem(other.face) {
        continue
      }
      let overlap = face_simplify(FAnd(br.face, other.face))
      if face_is_sat_sem(overlap) &&
        !tube_paths_conv_under_face(
          level,
          dlevel,
          overlap,
          line,
          br.path,
          other.path,
        ) {
        return DSystemCompatibility::{
          compatible: false,
          reason: DSystemBranchesIncompatible,
          branch: i,
          other_branch: j,
        }
      }
    }
  }
  DSystemCompatibility::{
    compatible: true,
    reason: DSystemOk,
    branch: -1,
    other_branch: -1,
  }
}

///|
/// The checked composition-system constructor: Some(canonical
/// system) for a compatible raw system, None for an incompatible one.
pub fn dsystem_checked(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
) -> DSystem? {
  if dsystem_compatible_with_base(level, dlevel, line, system, base) {
    Some(dsystem_canonical(level, dlevel, line, system))
  } else {
    None
  }
}

///|
/// Checked constructor from raw branches.
pub fn dsystem_checked_of(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  branches : Array[DTubeBranch],
  base : DValue,
) -> DSystem? {
  dsystem_checked(level, dlevel, line, dsystem_of(branches), base)
}

// ---------------------------------------------------------------------------
// First-match normal form for tube systems
// ---------------------------------------------------------------------------

///|
pub struct DTubeNFClass {
  region : Bdd
  path : (Dim) -> DValue
}

///|
pub struct DTubeNF {
  classes : Array[DTubeNFClass]
  undefined : Bdd
}

///|
fn dsystem_nvars(system : DSystem, dlevel : Int32) -> Int32 {
  let mut n = dlevel
  for i in 0..<system.branches.length() {
    let m = face_nvars_sem(system.branches[i].face)
    if m > n {
      n = m
    }
  }
  n
}

///|
/// First-match BDD normal form of a raw tube system.  The effective
/// region of a branch is its face minus all earlier faces;
/// convertible paths merge and classes are sorted by quoted path.
/// No compatibility assumption is made.
pub fn dsystem_first_match_normal_form(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system0 : DSystem,
) -> DTubeNF {
  let system = dsystem_of(system0.branches)
  let nvars = dsystem_nvars(system, dlevel)
  let regions : Array[Bdd] = []
  let paths : Array[(Dim) -> DValue] = []
  let mut covered = BddZero
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    let all = bdd_of_face(br.face, nvars)
    let effective = bdd_and(all, bdd_not(covered))
    covered = bdd_or(covered, all)
    if effective == BddZero {
      continue
    }
    let mut merged = false
    for k in 0..<paths.length() {
      if tube_paths_conv(level, dlevel, line, paths[k], br.path) {
        regions[k] = bdd_or(regions[k], effective)
        merged = true
        break
      }
    }
    if !merged {
      regions.push(effective)
      paths.push(br.path)
    }
  }
  let body_keys : Array[String] = []
  let region_keys : Array[String] = []
  for i in 0..<paths.length() {
    body_keys.push(
      dsystem_body_key(level, dlevel, line, tube_branch(FTop, paths[i])),
    )
    region_keys.push(Repr(regions[i]).to_string())
  }
  for _pass in 0..<paths.length() {
    for j in 0..<(paths.length() - 1) {
      let swap = body_keys[j + 1] < body_keys[j] ||
        (
          body_keys[j + 1] == body_keys[j] &&
          region_keys[j + 1] < region_keys[j]
        )
      if swap {
        let tmp_region = regions[j]
        regions[j] = regions[j + 1]
        regions[j + 1] = tmp_region
        let tmp_path = paths[j]
        paths[j] = paths[j + 1]
        paths[j + 1] = tmp_path
        let tmp_body = body_keys[j]
        body_keys[j] = body_keys[j + 1]
        body_keys[j + 1] = tmp_body
        let tmp_region_key = region_keys[j]
        region_keys[j] = region_keys[j + 1]
        region_keys[j + 1] = tmp_region_key
      }
    }
  }
  let classes : Array[DTubeNFClass] = []
  for i in 0..<paths.length() {
    classes.push(DTubeNFClass::{ region: regions[i], path: paths[i], })
  }
  DTubeNF::{ classes, undefined: bdd_not(covered), }
}

///|
/// The pairwise-disjoint composition system represented by a
/// first-match normal form.  Regions are converted back to DNF faces.
pub fn dsystem_of_first_match_nf(nf : DTubeNF) -> DSystem {
  let out : Array[DTubeBranch] = []
  for i in 0..<nf.classes.length() {
    out.push(tube_branch(face_of_bdd(nf.classes[i].region), nf.classes[i].path))
  }
  DSystem::{ branches: out, }
}

///|
/// Disjointify a raw system under first-match semantics.  The result
/// is pairwise compatible by construction (its regions are disjoint),
/// regardless of whether the raw branches agreed on their overlaps.
pub fn dsystem_first_match_system(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
) -> DSystem {
  dsystem_of_first_match_nf(
    dsystem_first_match_normal_form(level, dlevel, line, system),
  )
}

///|
/// First-match disjointification followed by the base-compatibility
/// check: shadowed branches no longer need to agree with the base.
pub fn dsystem_first_match_checked(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
) -> DSystem? {
  let disjoint = dsystem_first_match_system(level, dlevel, line, system)
  if dsystem_compatible_with_base(level, dlevel, line, disjoint, base) {
    Some(disjoint)
  } else {
    None
  }
}

///|
/// Equality of raw tube systems under first-match semantics.
pub fn dsystem_first_match_eq(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  a : DSystem,
  b : DSystem,
) -> Bool {
  let na = dsystem_first_match_normal_form(level, dlevel, line, a)
  let nb = dsystem_first_match_normal_form(level, dlevel, line, b)
  if na.undefined != nb.undefined || na.classes.length() != nb.classes.length() {
    return false
  }
  for i in 0..<na.classes.length() {
    if na.classes[i].region != nb.classes[i].region ||
      !tube_paths_conv(
        level,
        dlevel,
        line,
        na.classes[i].path,
        nb.classes[i].path,
      ) {
      return false
    }
  }
  true
}
