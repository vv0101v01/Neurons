///|
// Type-directed Kan operations for the dependent AST.
//
// This file gives the computational content of the cubical term
// constructors DCoe / DComp / DHComp / DHFill.  A line is a semantic
// Dim -> DValue type function (usually the evaluation of a line body
// under a fresh dimension), and a tube is a finite list of face-
// guarded paths over that line.  comp dispatches on the shape of the
// line sampled at a fresh generic dimension:
//
//   Pi      : contravariant on the domain; the argument travels along
//             the reversed domain fill before codomain composition.
//   Sigma   : compose the first component, take its fill, then compose
//             the second component over that fill.
//   PathP   : compose at each point of the path dimension, adding the
//             two endpoint branches of the moving path type.
//   Universe: hcomp produces a Glue type; coe along a constant
//   universe line is the identity on types.
//   Glue    : compose in the base and partial types, then correct the
//             base component by the hcomp path from the partial fill
//             (the same Kan-5 repair as the finite Glue layer).
//   Data    : Bool/Unit/Nat/List recurse on matching constructors.
//   HITs    : all-base systems over Circle/Torus reduce to the base
//             point; nontrivial compositions remain as formal hcomp
//             points (the standard stuck HIT compositions).
//   Neutral : stuck compositions are kept as DNComp neutrals.
//
// fill is the usual restriction of comp to an initial segment
// (j <= r); coe between arbitrary endpoints is reduced to fills and
// segment compositions.  hcomp is comp along a constant line and
// hfill is its filler.

// ---------------------------------------------------------------------------
// Semantic dimension / face predicates
// ---------------------------------------------------------------------------

///|
pub fn dim_vars_of(r : Dim) -> Array[Int32] {
  match r {
    DVar(i) => [i]
    DNeg(a) => dim_vars_of(a)
    DAnd(a, b) => {
      let out = dim_vars_of(a)
      let bs = dim_vars_of(b)
      for i in 0..<bs.length() {
        out.push(bs[i])
      }
      out
    }
    DOr(a, b) => {
      let out = dim_vars_of(a)
      let bs = dim_vars_of(b)
      for i in 0..<bs.length() {
        out.push(bs[i])
      }
      out
    }
    _ => []
  }
}

///|
pub fn dim_nvars_sem(r : Dim) -> Int32 {
  let vars = dim_vars_of(r)
  let mut n = 0
  for i in 0..<vars.length() {
    if vars[i] + 1 > n {
      n = vars[i] + 1
    }
  }
  n
}

///|
pub fn dim_eq_sem(r : Dim, s : Dim) -> Bool {
  let n1 = dim_nvars_sem(r)
  let n2 = dim_nvars_sem(s)
  let n = if n1 > n2 { n1 } else { n2 }
  face_eq_mod(FEq0(r), FEq0(s), n)
}

///|
pub fn face_nvars_sem(f : Face) -> Int32 {
  let vars = face_vars(f)
  let mut n = 0
  for i in 0..<vars.length() {
    if vars[i] + 1 > n {
      n = vars[i] + 1
    }
  }
  n
}

///|
pub fn face_is_top_sem(f : Face) -> Bool {
  face_le(FTop, f, face_nvars_sem(f))
}

///|
pub fn face_is_bot_sem(f : Face) -> Bool {
  face_le(f, FBot, face_nvars_sem(f))
}

///|
pub fn face_is_sat_sem(f : Face) -> Bool {
  !face_is_bot_sem(f)
}

///|
fn dim_is_zero(r : Dim) -> Bool {
  dim_eq_sem(r, DZero)
}

///|
fn dim_is_one(r : Dim) -> Bool {
  dim_eq_sem(r, DOne)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

///|
fn top_branch(system : DSystem) -> DTubeBranch? {
  for i in 0..<system.branches.length() {
    if face_is_top_sem(system.branches[i].face) {
      return Some(system.branches[i])
    }
  }
  None
}

///|
pub fn map_branches(
  branches : DSystem,
  f : ((Dim) -> DValue) -> (Dim) -> DValue,
) -> DSystem {
  dsystem_map(branches, f)
}

///|
fn line_pi_at(line : (Dim) -> DValue, d : Dim) -> DFamilyParts {
  match as_pi(line(d)) {
    Some(p) => p
    None => DFamilyParts::{ dom: DVUnitTy, fam: _ => DVUnitTy, }
  }
}

///|
fn line_sigma_at(line : (Dim) -> DValue, d : Dim) -> DFamilyParts {
  match as_sigma(line(d)) {
    Some(p) => p
    None => DFamilyParts::{ dom: DVUnitTy, fam: _ => DVUnitTy, }
  }
}

///|
fn path_at(line : (Dim) -> DValue, d : Dim) -> DPathParts {
  match as_path(line(d)) {
    Some(p) => p
    None => DPathParts::{ line: _ => DVUnitTy, left: DVUnit, right: DVUnit, }
  }
}

///|
fn glue_at(line : (Dim) -> DValue, d : Dim) -> DGlueParts {
  let ty = line(d)
  match as_glue(ty) {
    Some(g) => g
    None =>
      DGlueParts::{
        system: dsystem_empty(),
        face: FBot,
        line: _ => ty,
        base: ty,
        level: 0,
      }
  }
}

///|
fn list_elem_at(line : (Dim) -> DValue, d : Dim) -> DValue {
  match as_list_elem(line(d)) {
    Some(a) => a
    None => DVUnitTy
  }
}

// ---------------------------------------------------------------------------
// fill / coe (defined from comp)
// ---------------------------------------------------------------------------

///|
pub fn fill_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> (Dim) -> DValue {
  r => {
    if dim_is_zero(r) {
      base
    } else {
      let subline = (j : Dim) => line(dim_simplify(DAnd(j, r)))
      let mapped = map_branches(branches, p => {
        (j : Dim) => p(dim_simplify(DAnd(j, r)))
      })
      mapped.branches.push(tube_branch(face_simplify(FEq0(r)), _ => base))
      comp_value(subline, mapped, base, dlevel + 1)
    }
  }
}

///|
pub fn hfill_value(
  ty : DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> (Dim) -> DValue {
  fill_value(_ => ty, branches, base, dlevel)
}

///|
pub fn coe_value(
  line : (Dim) -> DValue,
  r : Dim,
  s : Dim,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  if dim_eq_sem(r, s) {
    v
  } else if dim_is_zero(r) && dim_is_one(s) {
    comp_value(line, dsystem_empty(), v, dlevel)
  } else if dim_is_one(r) && dim_is_zero(s) {
    comp_value(j => line(DNeg(j)), dsystem_empty(), v, dlevel)
  } else if dim_is_zero(r) {
    fill_value(line, dsystem_empty(), v, dlevel)(s)
  } else if dim_is_one(s) {
    comp_value(j => line(DOr(r, j)), dsystem_empty(), v, dlevel)
  } else if dim_is_one(r) {
    comp_value(j => line(DOr(s, DNeg(j))), dsystem_empty(), v, dlevel)
  } else if dim_is_zero(s) {
    coe_value(j => line(DNeg(j)), DNeg(r), DOne, v, dlevel)
  } else {
    let mid = coe_value(line, r, DOne, v, dlevel)
    coe_value(line, DOne, s, mid, dlevel)
  }
}

// ---------------------------------------------------------------------------
// comp: the type-directed recursion
// ---------------------------------------------------------------------------

///|
pub fn comp_value(
  line : (Dim) -> DValue,
  branches0 : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let branches = dsystem_of(branches0.branches)
  match top_branch(branches) {
    Some(br) => return (br.path)(DOne)
    None => ()
  }
  let generic = DVar(dlevel)
  match force_value(line(generic)) {
    DVPi(_, _) => comp_pi_value(line, branches, base, dlevel)
    DVSigma(_, _) => comp_sigma_value(line, branches, base, dlevel)
    DVPathTy(_, _, _) => comp_path_value(line, branches, base, dlevel)
    DVUniv(_) => comp_univ_value(line, branches, base, dlevel)
    DVGlue(_, _, _) => comp_glue_value(line, branches, base, dlevel)
    DVEquivTy(_, _, _) => comp_equiv_value(line, branches, base, dlevel)
    DVGlueEquiv(_, _, _) => comp_glue_equiv_value(line, branches, base, dlevel)
    DVInductive(_, _, _) => comp_inductive_value(line, branches, base, dlevel)
    DVHitType(_, _, _) => comp_hit_value(line, branches, base, dlevel)
    DVBoolTy => comp_bool_value(line, branches, base, dlevel)
    DVUnitTy => DVUnit
    DVNatTy => comp_nat_value(line, branches, base, dlevel)
    DVListTy(_) => comp_list_value(line, branches, base, dlevel)
    DVCircleTy => comp_circle_value(line, branches, base, dlevel)
    DVTorusTy => comp_torus_value(line, branches, base, dlevel)
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

///|
pub fn hcomp_value(
  ty : DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  match comp_value(_ => ty, branches, base, dlevel) {
    DVNeutral(DNComp(_, bs, b)) => DVNeutral(DNHComp(ty, bs, b))
    other => other
  }
}

///|
pub fn comp_pi_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  DVLam(y => {
    let a_line = (j : Dim) => line_pi_at(line, j).dom
    let rev_fill = fill_value(j => a_line(DNeg(j)), dsystem_empty(), y, dlevel)
    let x_path = (j : Dim) => rev_fill(dim_simplify(DNeg(j)))
    let b_line = (j : Dim) => (line_pi_at(line, j).fam)(x_path(j))
    let b_branches = map_branches(branches, p => {
      (j : Dim) => dapp_typed(p(j), x_path(j), a_line(j))
    })
    comp_value(
      b_line,
      b_branches,
      dapp_typed(base, x_path(DZero), a_line(DZero)),
      dlevel,
    )
  })
}

///|
pub fn comp_sigma_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let a_line = (j : Dim) => line_sigma_at(line, j).dom
  let fam_at = (j : Dim) => line_sigma_at(line, j).fam
  let fst_branches = map_branches(branches, p => {
    (j : Dim) => dfst_typed(p(j), fam_at(j))
  })
  let a_fill = fill_value(
    a_line,
    fst_branches,
    dfst_typed(base, fam_at(DZero)),
    dlevel,
  )
  let b_line = (j : Dim) => fam_at(j)(a_fill(j))
  let snd_branches = map_branches(branches, p => {
    (j : Dim) => dsnd_typed(p(j), a_line(j), fam_at(j))
  })
  DVPair(
    a_fill(DOne),
    comp_value(
      b_line,
      snd_branches,
      dsnd_typed(base, a_line(DZero), fam_at(DZero)),
      dlevel,
    ),
  )
}

///|
pub fn comp_path_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  DVPathLam(k => {
    let a_line = (j : Dim) => (path_at(line, j).line)(k)
    let mapped = map_branches(branches, p => (j : Dim) => dapp_dim(p(j), k))
    mapped.branches.push(
      tube_branch(face_simplify(FEq0(k)), j => path_at(line, j).left),
    )
    mapped.branches.push(
      tube_branch(face_simplify(FEq1(k)), j => path_at(line, j).right),
    )
    comp_value(a_line, mapped, dapp_dim(base, k), dlevel + 1)
  })
}

///|
/// hcomp in a universe.  The resulting semantic Glue retains the
/// entire partial type system; elements carry matching partial values.
pub fn comp_univ_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  _dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    base
  } else {
    let lvl = match as_univ_level(line(DOne)) {
      Some(l) => l
      None => 0
    }
    DVGlue(branches, base, lvl)
  }
}

///|
fn glue_branch_path_at(
  line : (Dim) -> DValue,
  j : Dim,
  idx : Int32,
) -> (Dim) -> DValue {
  let g = glue_at(line, j)
  if idx >= 0 && idx < g.system.branches.length() {
    g.system.branches[idx].path
  } else {
    _ => g.base
  }
}

///|
fn glue_branch_cap_line(line : (Dim) -> DValue, idx : Int32) -> (Dim) -> DValue {
  (j : Dim) => glue_branch_path_at(line, j, idx)(DOne)
}

///|
fn glue_partial_at(
  line : (Dim) -> DValue,
  j : Dim,
  packed : DValue,
  idx : Int32,
) -> DValue {
  let g = glue_at(line, j)
  let values = glue_partial_values(g, dfst_typed(packed, _ => g.base))
  if idx >= 0 && idx < values.length() {
    values[idx]
  } else {
    DVUnit
  }
}

///|
/// Pack an endpoint value into Glue pair form when the Glue face is
/// decided there (an unglued value under bot, a partial value under
/// top).  Generic Glue values are already pairs.  Multi-branch systems
/// pack one partial value for every type branch.
fn glue_pack_at(
  line : (Dim) -> DValue,
  d : Dim,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(v) {
    DVPair(_, _) => v
    _ => {
      let g = glue_at(line, d)
      if g.system.branches.length() == 0 {
        // The endpoint Glue may have collapsed to its base type (for
        // example hcompU at a decided face).  Probe the generic point
        // of the line so the base value is still packed against the
        // partial system used by the composition algorithm.
        let generic = glue_at(line, DVar(dlevel))
        if generic.system.branches.length() == 0 {
          v
        } else {
          let values : Array[DValue] = []
          for i in 0..<generic.system.branches.length() {
            values.push(
              coe_value(generic.system.branches[i].path, DZero, DOne, v, dlevel),
            )
          }
          DVPair(glue_store_partial(generic, values), v)
        }
      } else if face_is_bot_sem(g.face) {
        let values : Array[DValue] = []
        for i in 0..<g.system.branches.length() {
          values.push(
            coe_value(g.system.branches[i].path, DZero, DOne, v, dlevel),
          )
        }
        DVPair(glue_store_partial(g, values), v)
      } else if face_is_top_sem(g.face) {
        let values = glue_partial_values(g, v)
        let first = if values.length() > 0 { values[0] } else { DVUnit }
        DVPair(v, coe_value(g.line, DOne, DZero, first, dlevel))
      } else {
        v
      }
    }
  }
}

///|
pub fn comp_glue_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let a_line = (j : Dim) => glue_at(line, j).base
  let packed_base = glue_pack_at(line, DZero, base, dlevel)
  let src = glue_at(line, DZero)
  let tgt = glue_at(line, DOne)
  let first_cap = glue_branch_cap_line(line, 0)
  let snd_branches = map_branches(branches, p => {
    (j : Dim) => {
      dsnd_typed(glue_pack_at(line, j, p(j), dlevel), first_cap(j), _ => {
        a_line(j)
      })
    }
  })
  let base0 = dsnd_typed(packed_base, first_cap(DZero), _ => a_line(DZero))
  let a_raw = comp_value(a_line, snd_branches, base0, dlevel)
  let count = tgt.system.branches.length()
  let partial0 = glue_partial_values(
    src,
    dfst_typed(packed_base, _ => a_line(DZero)),
  )
  let fills : Array[(Dim) -> DValue] = []
  let t_outs : Array[DValue] = []
  for idx in 0..<count {
    let t_line = glue_branch_cap_line(line, idx)
    let t_branches = map_branches(branches, p => {
      (j : Dim) => {
        glue_partial_at(line, j, glue_pack_at(line, j, p(j), dlevel), idx)
      }
    })
    let t_base = if idx < partial0.length() {
      partial0[idx]
    } else {
      coe_value(
        glue_branch_path_at(line, DZero, idx),
        DZero,
        DOne,
        base0,
        dlevel,
      )
    }
    let t_fill = fill_value(t_line, t_branches, t_base, dlevel)
    fills.push(t_fill)
    if idx >= src.system.branches.length() {
      t_outs.push(
        coe_value(
          glue_branch_path_at(line, DOne, idx),
          DZero,
          DOne,
          a_raw,
          dlevel,
        ),
      )
    } else {
      t_outs.push(t_fill(DOne))
    }
  }
  let a_out = if count == 0 {
    a_raw
  } else {
    let correction_branches : Array[DTubeBranch] = []
    for idx in 0..<count {
      let face = tgt.system.branches[idx].face
      let t_fill = fills[idx]
      let correction = (k : Dim) => {
        let down = coe_value(
          glue_branch_path_at(line, k, idx),
          DOne,
          DZero,
          t_fill(k),
          dlevel,
        )
        coe_value(a_line, k, DOne, down, dlevel)
      }
      correction_branches.push(tube_branch(face, correction))
    }
    hcomp_value(a_line(DOne), dsystem_of(correction_branches), a_raw, dlevel)
  }
  if count == 0 {
    a_out
  } else if count == 1 && face_is_top_sem(tgt.face) {
    t_outs[0]
  } else {
    DVPair(glue_store_partial(tgt, t_outs), a_out)
  }
}

///|
/// hcomp in a universe, named explicitly: a partial type over a base
/// type composes to the Glue type.
pub fn hcomp_univ_value(
  level : Int32,
  branches : DSystem,
  base_ty : DValue,
  dlevel : Int32,
) -> DValue {
  hcomp_value(DVUniv(level), branches, base_ty, dlevel)
}

// ---------------------------------------------------------------------------
// Data-type compositions (constructor recursion)
// ---------------------------------------------------------------------------

///|
pub fn comp_bool_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    return base
  }
  match base {
    DVBool(bb) => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        match (branches.branches[i].path)(DVar(dlevel)) {
          DVBool(x) => if x != bb { ok = false }
          _ => ok = false
        }
      }
      if ok {
        DVBool(bb)
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

///|
fn pred_of(v : DValue) -> DValue? {
  match v {
    DVSucc(n) => Some(n)
    _ => None
  }
}

///|
fn pred_or_zero(v : DValue) -> DValue {
  match pred_of(v) {
    Some(n) => n
    None => DVZeroNat
  }
}

///|
fn head_or_unit(v : DValue) -> DValue {
  match cons_head(v) {
    Some(h) => h
    None => DVUnit
  }
}

///|
fn tail_or_nil(v : DValue) -> DValue {
  match cons_tail(v) {
    Some(t) => t
    None => DVNil
  }
}

///|
pub fn comp_nat_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    return base
  }
  match base {
    DVZeroNat => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        match (branches.branches[i].path)(DVar(dlevel)) {
          DVZeroNat => ()
          _ => ok = false
        }
      }
      if ok {
        DVZeroNat
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    DVSucc(n) => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        match pred_of((branches.branches[i].path)(DVar(dlevel))) {
          Some(_) => ()
          None => ok = false
        }
      }
      if ok {
        let pred_branches = map_branches(branches, p => {
          (j : Dim) => pred_or_zero(p(j))
        })
        DVSucc(comp_value(line, pred_branches, n, dlevel))
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

///|
fn cons_head(v : DValue) -> DValue? {
  match v {
    DVCons(x, _) => Some(x)
    _ => None
  }
}

///|
fn cons_tail(v : DValue) -> DValue? {
  match v {
    DVCons(_, xs) => Some(xs)
    _ => None
  }
}

///|
pub fn comp_list_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    return base
  }
  match base {
    DVNil => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        match (branches.branches[i].path)(DVar(dlevel)) {
          DVNil => ()
          _ => ok = false
        }
      }
      if ok {
        DVNil
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    DVCons(x, xs) => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        match cons_head((branches.branches[i].path)(DVar(dlevel))) {
          Some(_) => ()
          None => ok = false
        }
      }
      if ok {
        let elem_line = (j : Dim) => list_elem_at(line, j)
        let head_branches = map_branches(branches, p => {
          (j : Dim) => head_or_unit(p(j))
        })
        let tail_branches = map_branches(branches, p => {
          (j : Dim) => tail_or_nil(p(j))
        })
        DVCons(
          comp_value(elem_line, head_branches, x, dlevel),
          comp_value(line, tail_branches, xs, dlevel),
        )
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

// ---------------------------------------------------------------------------
// HIT compositions: all-base reduction, otherwise formal hcomp points
// ---------------------------------------------------------------------------

///|
fn is_circle_base(v : DValue) -> Bool {
  match v {
    DVCirclePoint(r) => dim_is_zero(r) || dim_is_one(r)
    _ => false
  }
}

///|
pub fn comp_circle_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    return base
  }
  let mut ok = is_circle_base(base)
  for i in 0..<branches.branches.length() {
    if !is_circle_base((branches.branches[i].path)(DVar(dlevel))) {
      ok = false
    }
  }
  if ok {
    DVCirclePoint(DZero)
  } else {
    DVNeutral(DNComp(line, branches, base))
  }
}

///|
fn is_torus_base(v : DValue) -> Bool {
  match v {
    DVTorusPoint(a, b) =>
      (dim_is_zero(a) || dim_is_one(a)) && (dim_is_zero(b) || dim_is_one(b))
    _ => false
  }
}

///|
pub fn comp_torus_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    return base
  }
  let mut ok = is_torus_base(base)
  for i in 0..<branches.branches.length() {
    if !is_torus_base((branches.branches[i].path)(DVar(dlevel))) {
      ok = false
    }
  }
  if ok {
    DVTorusPoint(DZero, DZero)
  } else {
    DVNeutral(DNComp(line, branches, base))
  }
}
