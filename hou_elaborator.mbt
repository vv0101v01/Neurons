///|
// Pattern higher-order unification and a bidirectional elaborator.
//
// Full higher-order unification is undecidable, so the unifier here
// implements the useful Miller pattern fragment: a flexible head
// `?F x1 ... xn`, where the xi are distinct bound variables, is
// solved by abstracting exactly those variables.  Rigid/rigid
// decomposition, beta/eta/projection reduction, occurs and scope
// checks, closed non-pattern assignment, and flex-headed applications
// are also handled.  This is the fragment needed by elaborators for
// implicit arguments and dependent motives.
//
// The bidirectional elaborator consumes a named surface syntax,
// inserts implicit arguments as metavariables, infers/checks against
// UTerm types, solves the resulting HOU constraints, beta/eta
// optimizes the zonked core term, and finally translates it to the
// project's DTerm.  The laws validate those DTerms with the ordinary
// dependent checker.

///|
pub enum UTerm {
  UVar(Int32)
  UMeta(Int32, Array[UTerm])
  UConst(String)
  UType(Int32)
  ULam(UTerm, UTerm)
  UApp(UTerm, UTerm)
  UPi(UTerm, UTerm)
  UImplicitPi(UTerm, UTerm)
  USigma(UTerm, UTerm)
  UPair(UTerm, UTerm)
  UFst(UTerm)
  USnd(UTerm)
  UBoolLit(Bool)
  UNatZero
  USucc(UTerm)
  UNatElim(UTerm, UTerm, UTerm, UTerm)
} derive(Debug, Eq)

///|
pub extend UTerm with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend UTerm with Eq::{not_equal, equal}

///|
pub fn uty_bool() -> UTerm {
  UConst("Bool")
}

///|
pub fn uty_nat() -> UTerm {
  UConst("Nat")
}

///|
pub fn uty_unit() -> UTerm {
  UConst("Unit")
}

///|
pub fn uty_arrow(a : UTerm, b : UTerm) -> UTerm {
  UPi(a, uterm_shift(b, 1, 0))
}

///|
pub struct UMetaInfo {
  context_depth : Int32
  mut solution : UTerm?
} derive(Debug, Eq)

///|
pub extend UMetaInfo with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend UMetaInfo with Eq::{not_equal, equal}

///|
pub struct Unifier {
  metas : Array[UMetaInfo]
  mut solved_count : Int32
} derive(Debug, Eq)

///|
pub extend Unifier with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Unifier with Eq::{not_equal, equal}

///|
pub fn unifier_new() -> Unifier {
  Unifier::{ metas: [], solved_count: 0, }
}

///|
fn uterm_shift(t : UTerm, amount : Int32, cutoff : Int32) -> UTerm {
  match t {
    UVar(i) => if i >= cutoff { UVar(i + amount) } else { UVar(i) }
    UMeta(id, args) => {
      let out : Array[UTerm] = []
      for i in 0..<args.length() {
        out.push(uterm_shift(args[i], amount, cutoff))
      }
      UMeta(id, out)
    }
    UConst(_) | UType(_) | UBoolLit(_) | UNatZero => t
    ULam(dom, body) =>
      ULam(
        uterm_shift(dom, amount, cutoff),
        uterm_shift(body, amount, cutoff + 1),
      )
    UApp(f, x) =>
      UApp(uterm_shift(f, amount, cutoff), uterm_shift(x, amount, cutoff))
    UPi(a, b) =>
      UPi(uterm_shift(a, amount, cutoff), uterm_shift(b, amount, cutoff + 1))
    UImplicitPi(a, b) =>
      UImplicitPi(
        uterm_shift(a, amount, cutoff),
        uterm_shift(b, amount, cutoff + 1),
      )
    USigma(a, b) =>
      USigma(uterm_shift(a, amount, cutoff), uterm_shift(b, amount, cutoff + 1))
    UPair(a, b) =>
      UPair(uterm_shift(a, amount, cutoff), uterm_shift(b, amount, cutoff))
    UFst(x) => UFst(uterm_shift(x, amount, cutoff))
    USnd(x) => USnd(uterm_shift(x, amount, cutoff))
    USucc(x) => USucc(uterm_shift(x, amount, cutoff))
    UNatElim(m, z, s, scrut) =>
      UNatElim(
        uterm_shift(m, amount, cutoff),
        uterm_shift(z, amount, cutoff),
        uterm_shift(s, amount, cutoff),
        uterm_shift(scrut, amount, cutoff),
      )
  }
}

///|
/// Beta substitution: replace de Bruijn index `index + binder_depth`
/// by the (suitably shifted) replacement and lower higher indices.
fn uterm_subst(
  t : UTerm,
  replacement : UTerm,
  index : Int32,
  binder_depth : Int32,
) -> UTerm {
  match t {
    UVar(i) =>
      if i == index + binder_depth {
        uterm_shift(replacement, binder_depth, 0)
      } else if i > index + binder_depth {
        UVar(i - 1)
      } else {
        UVar(i)
      }
    UMeta(id, args) => {
      let out : Array[UTerm] = []
      for i in 0..<args.length() {
        out.push(uterm_subst(args[i], replacement, index, binder_depth))
      }
      UMeta(id, out)
    }
    UConst(_) | UType(_) | UBoolLit(_) | UNatZero => t
    ULam(dom, body) =>
      ULam(
        uterm_subst(dom, replacement, index, binder_depth),
        uterm_subst(body, replacement, index, binder_depth + 1),
      )
    UApp(f, x) =>
      UApp(
        uterm_subst(f, replacement, index, binder_depth),
        uterm_subst(x, replacement, index, binder_depth),
      )
    UPi(a, b) =>
      UPi(
        uterm_subst(a, replacement, index, binder_depth),
        uterm_subst(b, replacement, index, binder_depth + 1),
      )
    UImplicitPi(a, b) =>
      UImplicitPi(
        uterm_subst(a, replacement, index, binder_depth),
        uterm_subst(b, replacement, index, binder_depth + 1),
      )
    USigma(a, b) =>
      USigma(
        uterm_subst(a, replacement, index, binder_depth),
        uterm_subst(b, replacement, index, binder_depth + 1),
      )
    UPair(a, b) =>
      UPair(
        uterm_subst(a, replacement, index, binder_depth),
        uterm_subst(b, replacement, index, binder_depth),
      )
    UFst(x) => UFst(uterm_subst(x, replacement, index, binder_depth))
    USnd(x) => USnd(uterm_subst(x, replacement, index, binder_depth))
    USucc(x) => USucc(uterm_subst(x, replacement, index, binder_depth))
    UNatElim(m, z, s, scrut) =>
      UNatElim(
        uterm_subst(m, replacement, index, binder_depth),
        uterm_subst(z, replacement, index, binder_depth),
        uterm_subst(s, replacement, index, binder_depth),
        uterm_subst(scrut, replacement, index, binder_depth),
      )
  }
}

///|
fn uterm_instantiate(body : UTerm, arg : UTerm) -> UTerm {
  uterm_subst(body, arg, 0, 0)
}

///|
fn uterm_apply_many(f : UTerm, args : Array[UTerm]) -> UTerm {
  let mut out = f
  for i in 0..<args.length() {
    out = UApp(out, args[i])
  }
  out
}

///|
pub fn uterm_whnf(t : UTerm, unifier : Unifier) -> UTerm {
  match t {
    UMeta(id, args) =>
      if id >= 0 && id < unifier.metas.length() {
        match unifier.metas[id].solution {
          Some(solution) =>
            uterm_whnf(uterm_apply_many(solution, args), unifier)
          None => t
        }
      } else {
        t
      }
    UApp(f, x) =>
      match uterm_whnf(f, unifier) {
        ULam(_, body) => uterm_whnf(uterm_instantiate(body, x), unifier)
        f2 => UApp(f2, x)
      }
    UFst(x) =>
      match uterm_whnf(x, unifier) {
        UPair(a, _) => uterm_whnf(a, unifier)
        x2 => UFst(x2)
      }
    USnd(x) =>
      match uterm_whnf(x, unifier) {
        UPair(_, b) => uterm_whnf(b, unifier)
        x2 => USnd(x2)
      }
    UNatElim(m, z, s, scrut) =>
      match uterm_whnf(scrut, unifier) {
        UNatZero => uterm_whnf(z, unifier)
        USucc(pred) =>
          uterm_whnf(UApp(UApp(s, pred), UNatElim(m, z, s, pred)), unifier)
        scrut2 => UNatElim(m, z, s, scrut2)
      }
    _ => t
  }
}

///|
/// Substitute solved metavariables and beta/projection/Nat-reduce
/// recursively.  This is the semantic optimization pass run before
/// translation to DTerm.
pub fn hou_semantic_optimize(t : UTerm, unifier : Unifier) -> UTerm {
  match uterm_whnf(t, unifier) {
    ULam(dom, body) =>
      ULam(
        hou_semantic_optimize(dom, unifier),
        hou_semantic_optimize(body, unifier),
      )
    UApp(f, x) =>
      UApp(hou_semantic_optimize(f, unifier), hou_semantic_optimize(x, unifier))
    UPi(a, b) =>
      UPi(hou_semantic_optimize(a, unifier), hou_semantic_optimize(b, unifier))
    UImplicitPi(a, b) =>
      UImplicitPi(
        hou_semantic_optimize(a, unifier),
        hou_semantic_optimize(b, unifier),
      )
    USigma(a, b) =>
      USigma(
        hou_semantic_optimize(a, unifier),
        hou_semantic_optimize(b, unifier),
      )
    UPair(a, b) =>
      UPair(
        hou_semantic_optimize(a, unifier),
        hou_semantic_optimize(b, unifier),
      )
    UFst(x) => UFst(hou_semantic_optimize(x, unifier))
    USnd(x) => USnd(hou_semantic_optimize(x, unifier))
    USucc(x) => USucc(hou_semantic_optimize(x, unifier))
    UNatElim(m, z, s, scrut) =>
      UNatElim(
        hou_semantic_optimize(m, unifier),
        hou_semantic_optimize(z, unifier),
        hou_semantic_optimize(s, unifier),
        hou_semantic_optimize(scrut, unifier),
      )
    UVar(i) => UVar(i)
    UMeta(id, args) => {
      let out : Array[UTerm] = []
      for i in 0..<args.length() {
        out.push(hou_semantic_optimize(args[i], unifier))
      }
      UMeta(id, out)
    }
    UConst(name) => UConst(name)
    UType(level) => UType(level)
    UBoolLit(value) => UBoolLit(value)
    UNatZero => UNatZero
  }
}

///|
pub fn uterm_contains_unsolved_meta(t : UTerm, unifier : Unifier) -> Bool {
  match uterm_whnf(t, unifier) {
    UMeta(_, _) => true
    UVar(_) | UConst(_) | UType(_) | UBoolLit(_) | UNatZero => false
    ULam(a, b)
    | UApp(a, b)
    | UPi(a, b)
    | UImplicitPi(a, b)
    | USigma(a, b)
    | UPair(a, b) =>
      uterm_contains_unsolved_meta(a, unifier) ||
      uterm_contains_unsolved_meta(b, unifier)
    UFst(x) | USnd(x) | USucc(x) => uterm_contains_unsolved_meta(x, unifier)
    UNatElim(a, b, c, d) =>
      uterm_contains_unsolved_meta(a, unifier) ||
      uterm_contains_unsolved_meta(b, unifier) ||
      uterm_contains_unsolved_meta(c, unifier) ||
      uterm_contains_unsolved_meta(d, unifier)
  }
}

///|
fn uterm_occurs_meta(t : UTerm, id : Int32, unifier : Unifier) -> Bool {
  match t {
    UMeta(other, args) => {
      if other == id {
        return true
      }
      let other_solution = if other >= 0 && other < unifier.metas.length() {
        unifier.metas[other].solution
      } else {
        None
      }
      match other_solution {
        Some(solution) =>
          uterm_occurs_meta(uterm_apply_many(solution, args), id, unifier)
        None => {
          for i in 0..<args.length() {
            if uterm_occurs_meta(args[i], id, unifier) {
              return true
            }
          }
          false
        }
      }
    }
    UVar(_) | UConst(_) | UType(_) | UBoolLit(_) | UNatZero => false
    ULam(a, b)
    | UApp(a, b)
    | UPi(a, b)
    | UImplicitPi(a, b)
    | USigma(a, b)
    | UPair(a, b) =>
      uterm_occurs_meta(a, id, unifier) || uterm_occurs_meta(b, id, unifier)
    UFst(x) | USnd(x) | USucc(x) => uterm_occurs_meta(x, id, unifier)
    UNatElim(a, b, c, d) =>
      uterm_occurs_meta(a, id, unifier) ||
      uterm_occurs_meta(b, id, unifier) ||
      uterm_occurs_meta(c, id, unifier) ||
      uterm_occurs_meta(d, id, unifier)
  }
}

///|
fn pattern_level_position(levels : Array[Int32], level : Int32) -> Int32 {
  for i in 0..<levels.length() {
    if levels[i] == level {
      return i
    }
  }
  -1
}

///|
fn abstract_pattern_go(
  t : UTerm,
  root_depth : Int32,
  binder_depth : Int32,
  meta_depth : Int32,
  levels : Array[Int32],
) -> UTerm? {
  match t {
    UVar(i) => {
      if i < binder_depth {
        return Some(t)
      }
      let level = root_depth + binder_depth - 1 - i
      if level < 0 {
        return None
      }
      let pos = pattern_level_position(levels, level)
      if pos >= 0 {
        Some(UVar(binder_depth + levels.length() - 1 - pos))
      } else if level < meta_depth {
        Some(UVar(meta_depth + levels.length() + binder_depth - 1 - level))
      } else {
        None
      }
    }
    UMeta(id, args) => {
      let out : Array[UTerm] = []
      for i in 0..<args.length() {
        match
          abstract_pattern_go(
            args[i],
            root_depth,
            binder_depth,
            meta_depth,
            levels,
          ) {
          Some(x) => out.push(x)
          None => return None
        }
      }
      Some(UMeta(id, out))
    }
    UConst(_) | UType(_) | UBoolLit(_) | UNatZero => Some(t)
    ULam(dom, body) => {
      let d = match
        abstract_pattern_go(dom, root_depth, binder_depth, meta_depth, levels) {
        Some(x) => x
        None => return None
      }
      let b = match
        abstract_pattern_go(
          body,
          root_depth,
          binder_depth + 1,
          meta_depth,
          levels,
        ) {
        Some(x) => x
        None => return None
      }
      Some(ULam(d, b))
    }
    UApp(f, x) => {
      let f2 = match
        abstract_pattern_go(f, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      let x2 = match
        abstract_pattern_go(x, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      Some(UApp(f2, x2))
    }
    UPi(a, b) => {
      let a2 = match
        abstract_pattern_go(a, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      let b2 = match
        abstract_pattern_go(b, root_depth, binder_depth + 1, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      Some(UPi(a2, b2))
    }
    UImplicitPi(a, b) => {
      let a2 = match
        abstract_pattern_go(a, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      let b2 = match
        abstract_pattern_go(b, root_depth, binder_depth + 1, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      Some(UImplicitPi(a2, b2))
    }
    USigma(a, b) => {
      let a2 = match
        abstract_pattern_go(a, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      let b2 = match
        abstract_pattern_go(b, root_depth, binder_depth + 1, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      Some(USigma(a2, b2))
    }
    UPair(a, b) => {
      let a2 = match
        abstract_pattern_go(a, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      let b2 = match
        abstract_pattern_go(b, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      Some(UPair(a2, b2))
    }
    UFst(x) =>
      match
        abstract_pattern_go(x, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => Some(UFst(v))
        None => None
      }
    USnd(x) =>
      match
        abstract_pattern_go(x, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => Some(USnd(v))
        None => None
      }
    USucc(x) =>
      match
        abstract_pattern_go(x, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => Some(USucc(v))
        None => None
      }
    UNatElim(a, b, c, d) => {
      let a2 = match
        abstract_pattern_go(a, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      let b2 = match
        abstract_pattern_go(b, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      let c2 = match
        abstract_pattern_go(c, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      let d2 = match
        abstract_pattern_go(d, root_depth, binder_depth, meta_depth, levels) {
        Some(v) => v
        None => return None
      }
      Some(UNatElim(a2, b2, c2, d2))
    }
  }
}

///|
fn pattern_solution(
  rhs : UTerm,
  args : Array[UTerm],
  depth : Int32,
  meta_depth : Int32,
  unifier : Unifier,
) -> UTerm? {
  let levels : Array[Int32] = []
  let mut is_pattern = true
  for i in 0..<args.length() {
    match uterm_whnf(args[i], unifier) {
      UVar(index) => {
        let level = depth - 1 - index
        if level < meta_depth || pattern_level_position(levels, level) >= 0 {
          is_pattern = false
        } else {
          levels.push(level)
        }
      }
      _ => is_pattern = false
    }
  }
  let body = if is_pattern {
    abstract_pattern_go(rhs, depth, 0, meta_depth, levels)
  } else {
    // A sound non-pattern fallback: a constant solution is allowed
    // when rhs only uses variables from the metavariable context.
    abstract_pattern_go(rhs, depth, 0, meta_depth, [])
  }
  match body {
    Some(body0) => {
      let mut out = body0
      let n = if is_pattern { levels.length() } else { args.length() }
      for _i in 0..<n {
        out = ULam(UConst("PatternDomain"), out)
      }
      Some(out)
    }
    None => None
  }
}

///|
fn assign_meta(
  unifier : Unifier,
  id : Int32,
  args : Array[UTerm],
  rhs_in : UTerm,
  depth : Int32,
) -> Bool {
  if id < 0 || id >= unifier.metas.length() {
    return false
  }
  match unifier.metas[id].solution {
    Some(_) => hou_unify(UMeta(id, args), rhs_in, depth, unifier)
    None => {
      let rhs = uterm_whnf(rhs_in, unifier)
      if uterm_occurs_meta(rhs, id, unifier) {
        return false
      }
      match
        pattern_solution(
          rhs,
          args,
          depth,
          unifier.metas[id].context_depth,
          unifier,
        ) {
        Some(solution) => {
          unifier.metas[id].solution = Some(solution)
          unifier.solved_count = unifier.solved_count + 1
          true
        }
        None => false
      }
    }
  }
}

///|
fn meta_head_spine(t : UTerm, unifier : Unifier) -> (Int32, Array[UTerm])? {
  match uterm_whnf(t, unifier) {
    UMeta(id, args) => Some((id, args))
    UApp(f, x) =>
      match meta_head_spine(f, unifier) {
        Some((id, args)) => {
          let out : Array[UTerm] = []
          for i in 0..<args.length() {
            out.push(args[i])
          }
          out.push(x)
          Some((id, out))
        }
        None => None
      }
    _ => None
  }
}

///|
/// Higher-order unification in the Miller pattern fragment.
/// `depth` is the number of variables in scope.  It beta/eta reduces,
/// decomposes rigid heads, and solves pattern-flexible heads.
pub fn hou_unify(
  a_in : UTerm,
  b_in : UTerm,
  depth : Int32,
  unifier : Unifier,
) -> Bool {
  let a = uterm_whnf(a_in, unifier)
  let b = uterm_whnf(b_in, unifier)
  if a == b {
    return true
  }
  match meta_head_spine(a, unifier) {
    Some((id, args)) => return assign_meta(unifier, id, args, b, depth)
    None => ()
  }
  match meta_head_spine(b, unifier) {
    Some((id, args)) => return assign_meta(unifier, id, args, a, depth)
    None => ()
  }
  match (a, b) {
    (ULam(ad, ab), ULam(bd, bb)) =>
      hou_unify(ad, bd, depth, unifier) && hou_unify(ab, bb, depth + 1, unifier)
    (ULam(_, body), other) =>
      hou_unify(
        body,
        UApp(uterm_shift(other, 1, 0), UVar(0)),
        depth + 1,
        unifier,
      )
    (other, ULam(_, body)) =>
      hou_unify(
        UApp(uterm_shift(other, 1, 0), UVar(0)),
        body,
        depth + 1,
        unifier,
      )
    (UPi(x1, y1), UPi(x2, y2))
    | (UImplicitPi(x1, y1), UImplicitPi(x2, y2))
    | (USigma(x1, y1), USigma(x2, y2))
    | (UPair(x1, y1), UPair(x2, y2))
    | (UApp(x1, y1), UApp(x2, y2)) =>
      hou_unify(x1, x2, depth, unifier) && hou_unify(y1, y2, depth, unifier)
    (UFst(x), UFst(y)) | (USnd(x), USnd(y)) | (USucc(x), USucc(y)) =>
      hou_unify(x, y, depth, unifier)
    (UNatElim(a1, b1, c1, d1), UNatElim(a2, b2, c2, d2)) =>
      hou_unify(a1, a2, depth, unifier) &&
      hou_unify(b1, b2, depth, unifier) &&
      hou_unify(c1, c2, depth, unifier) &&
      hou_unify(d1, d2, depth, unifier)
    _ => false
  }
}

///|
/// Create a fresh pattern metavariable over every variable in scope.
pub fn hou_fresh_meta(unifier : Unifier, depth : Int32) -> UTerm {
  let id = unifier.metas.length()
  unifier.metas.push(UMetaInfo::{ context_depth: 0, solution: None, })
  let args : Array[UTerm] = []
  for level in 0..<depth {
    args.push(UVar(depth - 1 - level))
  }
  UMeta(id, args)
}

///|
pub enum STerm {
  SVar(String)
  SLam(String, UTerm?, STerm)
  SApp(STerm, STerm)
  SPair(STerm, STerm)
  SFst(STerm)
  SSnd(STerm)
  SBoolLit(Bool)
  SUnitLit
  SNatZero
  SSucc(STerm)
  SNatElim(STerm, STerm, STerm, STerm)
  SAnn(STerm, UTerm)
  SHole
} derive(Debug, Eq)

///|
pub extend STerm with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend STerm with Eq::{not_equal, equal}

///|
pub struct ElabVar {
  name : String
  ty : UTerm
} derive(Debug, Eq)

///|
pub extend ElabVar with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ElabVar with Eq::{not_equal, equal}

///|
pub struct Elaborator {
  unifier : Unifier
  vars : Array[ElabVar]
} derive(Debug, Eq)

///|
pub extend Elaborator with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Elaborator with Eq::{not_equal, equal}

///|
pub struct ElabResult {
  term : UTerm
  ty : UTerm
} derive(Debug, Eq)

///|
pub extend ElabResult with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ElabResult with Eq::{not_equal, equal}

///|
pub fn elaborator_new() -> Elaborator {
  Elaborator::{ unifier: unifier_new(), vars: [], }
}

///|
fn elab_depth(e : Elaborator) -> Int32 {
  e.vars.length()
}

///|
fn elab_fresh(e : Elaborator) -> UTerm {
  hou_fresh_meta(e.unifier, elab_depth(e))
}

///|
fn elab_fresh_at(e : Elaborator, depth : Int32) -> UTerm {
  hou_fresh_meta(e.unifier, depth)
}

///|
fn elab_lookup(e : Elaborator, name : String) -> ElabResult? {
  let depth = elab_depth(e)
  for i in 0..<depth {
    let index = depth - 1 - i
    if e.vars[index].name == name {
      let ty = uterm_shift(e.vars[index].ty, depth - index - 1, 0)
      return Some(ElabResult::{ term: UVar(depth - 1 - index), ty, })
    }
  }
  None
}

///|
fn elab_push(e : Elaborator, name : String, ty : UTerm) -> Unit {
  e.vars.push(ElabVar::{ name, ty, })
}

///|
fn elab_truncate(e : Elaborator, depth : Int32) -> Unit {
  while e.vars.length() > depth {
    match e.vars.pop() {
      Some(_) => ()
      None => break
    }
  }
}

///|
pub fn elab_check(
  e : Elaborator,
  term : STerm,
  expected : UTerm,
) -> ElabResult? {
  let depth = elab_depth(e)
  match term {
    SHole => Some(ElabResult::{ term: elab_fresh(e), ty: expected, })
    SLam(name, annotation, body) => {
      let expected2 = uterm_whnf(expected, e.unifier)
      let (dom, cod) = match expected2 {
        UPi(a, b) | UImplicitPi(a, b) => (a, b)
        UMeta(_, _) => {
          let dom = elab_fresh(e)
          let cod = elab_fresh_at(e, depth + 1)
          if !hou_unify(expected2, UPi(dom, cod), depth, e.unifier) {
            return None
          }
          (dom, cod)
        }
        _ => return None
      }
      match annotation {
        Some(ann) => if !hou_unify(ann, dom, depth, e.unifier) { return None }
        None => ()
      }
      elab_push(e, name, dom)
      let body_result = elab_check(e, body, cod)
      elab_truncate(e, depth)
      match body_result {
        Some(r) =>
          Some(ElabResult::{ term: ULam(dom, r.term), ty: UPi(dom, cod), })
        None => None
      }
    }
    SPair(first, second) => {
      let expected2 = uterm_whnf(expected, e.unifier)
      let (dom, cod) = match expected2 {
        USigma(a, b) => (a, b)
        UMeta(_, _) => {
          let dom = elab_fresh(e)
          let cod = elab_fresh_at(e, depth + 1)
          if !hou_unify(expected2, USigma(dom, cod), depth, e.unifier) {
            return None
          }
          (dom, cod)
        }
        _ => return None
      }
      let first_r = match elab_check(e, first, dom) {
        Some(r) => r
        None => return None
      }
      let second_ty = uterm_instantiate(cod, first_r.term)
      let second_r = match elab_check(e, second, second_ty) {
        Some(r) => r
        None => return None
      }
      Some(ElabResult::{
        term: UPair(first_r.term, second_r.term),
        ty: USigma(dom, cod),
      })
    }
    _ => {
      let inferred = match elab_infer(e, term) {
        Some(r) => r
        None => return None
      }
      if hou_unify(inferred.ty, expected, depth, e.unifier) {
        Some(ElabResult::{ term: inferred.term, ty: expected, })
      } else {
        None
      }
    }
  }
}

///|
pub fn elab_infer(e : Elaborator, term : STerm) -> ElabResult? {
  let depth = elab_depth(e)
  match term {
    SVar(name) => elab_lookup(e, name)
    SHole => {
      let ty = elab_fresh(e)
      Some(ElabResult::{ term: elab_fresh(e), ty, })
    }
    SBoolLit(value) =>
      Some(ElabResult::{ term: UBoolLit(value), ty: uty_bool(), })
    SUnitLit => Some(ElabResult::{ term: UConst("UnitLit"), ty: uty_unit(), })
    SNatZero => Some(ElabResult::{ term: UNatZero, ty: uty_nat(), })
    SSucc(x) => {
      let r = match elab_check(e, x, uty_nat()) {
        Some(v) => v
        None => return None
      }
      Some(ElabResult::{ term: USucc(r.term), ty: uty_nat(), })
    }
    SAnn(inner, ty) => elab_check(e, inner, ty)
    SLam(name, annotation, body) => {
      let dom = match annotation {
        Some(ann) => ann
        None => elab_fresh(e)
      }
      elab_push(e, name, dom)
      let body_r = elab_infer(e, body)
      elab_truncate(e, depth)
      match body_r {
        Some(r) =>
          Some(ElabResult::{ term: ULam(dom, r.term), ty: UPi(dom, r.ty), })
        None => None
      }
    }
    SPair(first, second) => {
      let first_r = match elab_infer(e, first) {
        Some(r) => r
        None => return None
      }
      let second_r = match elab_infer(e, second) {
        Some(r) => r
        None => return None
      }
      Some(ElabResult::{
        term: UPair(first_r.term, second_r.term),
        ty: USigma(first_r.ty, uterm_shift(second_r.ty, 1, 0)),
      })
    }
    SFst(pair) => {
      let r = match elab_infer(e, pair) {
        Some(v) => v
        None => return None
      }
      let dom = elab_fresh(e)
      let cod = elab_fresh_at(e, depth + 1)
      if !hou_unify(r.ty, USigma(dom, cod), depth, e.unifier) {
        return None
      }
      Some(ElabResult::{ term: UFst(r.term), ty: dom, })
    }
    SSnd(pair) => {
      let r = match elab_infer(e, pair) {
        Some(v) => v
        None => return None
      }
      let dom = elab_fresh(e)
      let cod = elab_fresh_at(e, depth + 1)
      if !hou_unify(r.ty, USigma(dom, cod), depth, e.unifier) {
        return None
      }
      Some(ElabResult::{
        term: USnd(r.term),
        ty: uterm_instantiate(cod, UFst(r.term)),
      })
    }
    SApp(fn_term, arg_term) => {
      let fn_r0 = match elab_infer(e, fn_term) {
        Some(r) => r
        None => return None
      }
      let mut fn_r = fn_r0
      // Insert implicit arguments until an explicit Pi (or a
      // metavariable that can be forced to one) is exposed.
      for _i in 0..<16 {
        match uterm_whnf(fn_r.ty, e.unifier) {
          UImplicitPi(_dom, cod) => {
            let inserted = elab_fresh(e)
            // The inserted hole must itself inhabit dom; recording
            // that fact is the job of cross-checking the zonked
            // DTerm.  HOU normally solves it from the explicit
            // argument below (for example the A in id {A}).
            fn_r = ElabResult::{
              term: UApp(fn_r.term, inserted),
              ty: uterm_instantiate(cod, inserted),
            }
          }
          _ => break
        }
      }
      let (dom, cod) = match uterm_whnf(fn_r.ty, e.unifier) {
        UPi(a, b) => (a, b)
        UMeta(_, _) => {
          let dom = elab_fresh(e)
          let cod = elab_fresh_at(e, depth + 1)
          if !hou_unify(fn_r.ty, UPi(dom, cod), depth, e.unifier) {
            return None
          }
          (dom, cod)
        }
        _ => return None
      }
      let arg_r = match elab_check(e, arg_term, dom) {
        Some(r) => r
        None => return None
      }
      Some(ElabResult::{
        term: UApp(fn_r.term, arg_r.term),
        ty: uterm_instantiate(cod, arg_r.term),
      })
    }
    SNatElim(motive_s, zero_s, succ_s, scrut_s) => {
      let scrut = match elab_check(e, scrut_s, uty_nat()) {
        Some(r) => r
        None => return None
      }
      let motive_ty = UPi(uty_nat(), UType(0))
      let motive = match elab_check(e, motive_s, motive_ty) {
        Some(r) => r
        None => return None
      }
      let zero_ty = UApp(motive.term, UNatZero)
      let zero = match elab_check(e, zero_s, zero_ty) {
        Some(r) => r
        None => return None
      }
      let motive1 = uterm_shift(motive.term, 1, 0)
      let motive2 = uterm_shift(motive.term, 2, 0)
      let succ_ty = UPi(
        uty_nat(),
        UPi(UApp(motive1, UVar(0)), UApp(motive2, USucc(UVar(1)))),
      )
      let succ = match elab_check(e, succ_s, succ_ty) {
        Some(r) => r
        None => return None
      }
      Some(ElabResult::{
        term: UNatElim(motive.term, zero.term, succ.term, scrut.term),
        ty: UApp(motive.term, scrut.term),
      })
    }
  }
}

///|
fn uterm_to_dterm_depth(
  t_in : UTerm,
  depth : Int32,
  unifier : Unifier,
) -> DTerm? {
  let t = uterm_whnf(t_in, unifier)
  match t {
    UVar(i) => if i < depth { Some(DTVar(i)) } else { None }
    UMeta(_, _) => None
    UConst(name) =>
      if name == "Bool" {
        Some(DBoolTy)
      } else if name == "Nat" {
        Some(DNatTy)
      } else if name == "Unit" {
        Some(DUnitTy)
      } else if name == "UnitLit" {
        Some(DUnitLit)
      } else {
        None
      }
    UType(level) => Some(DUniv(level))
    ULam(dom, body) => {
      let d = match uterm_to_dterm_depth(dom, depth, unifier) {
        Some(x) => x
        None => return None
      }
      let b = match uterm_to_dterm_depth(body, depth + 1, unifier) {
        Some(x) => x
        None => return None
      }
      Some(DLam(d, b))
    }
    UApp(f, x) => {
      let f2 = match uterm_to_dterm_depth(f, depth, unifier) {
        Some(v) => v
        None => return None
      }
      let x2 = match uterm_to_dterm_depth(x, depth, unifier) {
        Some(v) => v
        None => return None
      }
      Some(DApp(f2, x2))
    }
    UPi(a, b) | UImplicitPi(a, b) => {
      let a2 = match uterm_to_dterm_depth(a, depth, unifier) {
        Some(v) => v
        None => return None
      }
      let b2 = match uterm_to_dterm_depth(b, depth + 1, unifier) {
        Some(v) => v
        None => return None
      }
      Some(DPi(a2, b2))
    }
    USigma(a, b) => {
      let a2 = match uterm_to_dterm_depth(a, depth, unifier) {
        Some(v) => v
        None => return None
      }
      let b2 = match uterm_to_dterm_depth(b, depth + 1, unifier) {
        Some(v) => v
        None => return None
      }
      Some(DSigma(a2, b2))
    }
    UPair(a, b) => {
      let a2 = match uterm_to_dterm_depth(a, depth, unifier) {
        Some(v) => v
        None => return None
      }
      let b2 = match uterm_to_dterm_depth(b, depth, unifier) {
        Some(v) => v
        None => return None
      }
      Some(DPair(a2, b2))
    }
    UFst(x) =>
      match uterm_to_dterm_depth(x, depth, unifier) {
        Some(v) => Some(DFst(v))
        None => None
      }
    USnd(x) =>
      match uterm_to_dterm_depth(x, depth, unifier) {
        Some(v) => Some(DSnd(v))
        None => None
      }
    UBoolLit(value) => Some(DBoolLit(value))
    UNatZero => Some(DNatZero)
    USucc(x) =>
      match uterm_to_dterm_depth(x, depth, unifier) {
        Some(v) => Some(DSucc(v))
        None => None
      }
    UNatElim(m, z, s, scrut) => {
      // DTerm's DNatElim stores the motive *body* under its Nat
      // binder, not a lambda.  A UTerm lambda therefore contributes
      // its body; any other motive is eta-expanded under the binder.
      let motive = match uterm_whnf(m, unifier) {
        ULam(_, body) =>
          match uterm_to_dterm_depth(body, depth + 1, unifier) {
            Some(body2) => body2
            None => return None
          }
        _ =>
          match uterm_to_dterm_depth(uterm_shift(m, 1, 0), depth + 1, unifier) {
            Some(v) => DApp(v, DTVar(0))
            None => return None
          }
      }
      let z2 = match uterm_to_dterm_depth(z, depth, unifier) {
        Some(v) => v
        None => return None
      }
      let s2 = match uterm_to_dterm_depth(s, depth, unifier) {
        Some(v) => v
        None => return None
      }
      let scrut2 = match uterm_to_dterm_depth(scrut, depth, unifier) {
        Some(v) => v
        None => return None
      }
      Some(DNatElim(motive, z2, s2, scrut2))
    }
  }
}

///|
/// Optimize and translate a closed elaborated term to DTerm.  Fails
/// if a metavariable remains unsolved.
pub fn elab_result_to_dterm(e : Elaborator, result : ElabResult) -> DTerm? {
  let term = hou_semantic_optimize(result.term, e.unifier)
  if uterm_contains_unsolved_meta(term, e.unifier) {
    None
  } else {
    uterm_to_dterm_depth(term, 0, e.unifier)
  }
}

///|
pub fn elab_type_to_dterm(e : Elaborator, result : ElabResult) -> DTerm? {
  let ty = hou_semantic_optimize(result.ty, e.unifier)
  if uterm_contains_unsolved_meta(ty, e.unifier) {
    None
  } else {
    uterm_to_dterm_depth(ty, 0, e.unifier)
  }
}

///|
pub fn check_hou_elaborator() -> Bool {
  // Direct Miller pattern problem at depth 2.  Levels are x=0, y=1,
  // hence de Bruijn indices are y=0 and x=1: solve ?F x y = (y, x).
  let u = unifier_new()
  let f = hou_fresh_meta(u, 2)
  if !hou_unify(f, UPair(UVar(0), UVar(1)), 2, u) {
    return false
  }
  let instantiated = hou_semantic_optimize(
    UApp(UApp(ULam(uty_nat(), ULam(uty_nat(), f)), UNatZero), USucc(UNatZero)),
    u,
  )
  if instantiated != UPair(USucc(UNatZero), UNatZero) {
    return false
  }
  // Scope failure: a pattern over the first variable alone cannot
  // be solved by a body mentioning the second variable.
  let u2 = unifier_new()
  let only_x = uterm_shift(hou_fresh_meta(u2, 1), 1, 0)
  if hou_unify(only_x, UVar(0), 2, u2) {
    return false
  }
  // Implicit identity in a one-variable context.  Elaborating
  // `id true` inserts a type metavariable and HOU solves it as Bool.
  let id_ty = UImplicitPi(UType(0), UPi(UVar(0), UVar(1)))
  let e2 = elaborator_new()
  elab_push(e2, "id", id_ty)
  let id_result = elab_infer(e2, SApp(SVar("id"), SBoolLit(true)))
  elab_truncate(e2, 0)
  let id_ok = match id_result {
    Some(result) => {
      let opt_ty = hou_semantic_optimize(result.ty, e2.unifier)
      let opt_term = hou_semantic_optimize(result.term, e2.unifier)
      let term_ok = match opt_term {
        UApp(UApp(UVar(0), UConst(name)), UBoolLit(true)) => name == "Bool"
        _ => false
      }
      opt_ty == uty_bool() && term_ok
    }
    None => false
  }
  if !id_ok {
    return false
  }
  // Dependent motive inference: checking a Nat eliminator against
  // Nat -> Nat solves its motive as a constant family.  The core is
  // translated to DTerm, accepted by the dependent checker, and
  // computes on a literal.
  let e3 = elaborator_new()
  let surface3 = SLam(
    "n",
    Some(uty_nat()),
    SNatElim(
      SHole,
      SNatZero,
      SLam("k", None, SLam("ih", None, SVar("ih"))),
      SVar("n"),
    ),
  )
  let result3 = match
    elab_check(e3, surface3, uty_arrow(uty_nat(), uty_nat())) {
    Some(r) => r
    None => return false
  }
  let core = match elab_result_to_dterm(e3, result3) {
    Some(t) => t
    None => return false
  }
  let core_ty = match elab_type_to_dterm(e3, result3) {
    Some(t) => t
    None => return false
  }
  if !dep_check_closed(core, core_ty) ||
    dep_nf_closed(DApp(core, d_nat_lit(3)), DNatTy) != Some(DNatZero) {
    return false
  }
  // The remaining surface forms elaborate through the same
  // bidirectional rules, with projections reduced by the semantic
  // optimizer.
  let e4 = elaborator_new()
  let pair_surface = SPair(SAnn(SBoolLit(true), uty_bool()), SSucc(SNatZero))
  let fst_ok = match elab_infer(e4, SFst(pair_surface)) {
    Some(r) =>
      hou_semantic_optimize(r.term, e4.unifier) == UBoolLit(true) &&
      hou_semantic_optimize(r.ty, e4.unifier) == uty_bool()
    None => false
  }
  let snd_ok = match elab_infer(e4, SSnd(pair_surface)) {
    Some(r) =>
      hou_semantic_optimize(r.term, e4.unifier) == USucc(UNatZero) &&
      hou_semantic_optimize(r.ty, e4.unifier) == uty_nat()
    None => false
  }
  let unit_ok = match elab_infer(e4, SUnitLit) {
    Some(r) => r.ty == uty_unit()
    None => false
  }
  fst_ok && snd_ok && unit_ok
}
