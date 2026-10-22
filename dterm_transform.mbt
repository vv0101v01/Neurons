///|
// Capture-avoiding variable maps for the dependent cubical AST.
//
// The map below is the single place which knows the term-binder
// structure of every AST constructor.  Dimension binders do not bind
// term variables.  The motives of the primitive Bool/Nat/List/Circle/
// Torus eliminators are bodies under one term binder; the motives of
// generated eliminators are ordinary function terms.  Embedded
// schema descriptors are closed schema-local data and are not
// traversed as ambient terms.

///|
fn dterm_map_vars_list(
  terms : Array[DTerm],
  depth : Int32,
  f : (Int32, Int32) -> DTerm,
) -> Array[DTerm] {
  let out : Array[DTerm] = []
  for i in 0..<terms.length() {
    out.push(dterm_map_vars_at(terms[i], depth, f))
  }
  out
}

///|
fn dterm_map_vars_at(
  t : DTerm,
  depth : Int32,
  f : (Int32, Int32) -> DTerm,
) -> DTerm {
  match t {
    DTVar(i) => f(i, depth)
    DPi(a, b) =>
      DPi(dterm_map_vars_at(a, depth, f), dterm_map_vars_at(b, depth + 1, f))
    DSigma(a, b) =>
      DSigma(dterm_map_vars_at(a, depth, f), dterm_map_vars_at(b, depth + 1, f))
    DLam(a, b) =>
      DLam(dterm_map_vars_at(a, depth, f), dterm_map_vars_at(b, depth + 1, f))
    DApp(x, y) =>
      DApp(dterm_map_vars_at(x, depth, f), dterm_map_vars_at(y, depth, f))
    DPair(x, y) =>
      DPair(dterm_map_vars_at(x, depth, f), dterm_map_vars_at(y, depth, f))
    DFst(x) => DFst(dterm_map_vars_at(x, depth, f))
    DSnd(x) => DSnd(dterm_map_vars_at(x, depth, f))
    DBoolElim(m, x, y, z) =>
      DBoolElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(y, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DAnn(x, y) =>
      DAnn(dterm_map_vars_at(x, depth, f), dterm_map_vars_at(y, depth, f))
    DPartial(branches) => {
      let out : Array[DFaceTerm] = []
      for i in 0..<branches.length() {
        out.push(
          d_face_term(
            branches[i].face,
            dterm_map_vars_at(branches[i].body, depth, f),
          ),
        )
      }
      DPartial(out)
    }
    DPathP(line, l, r) =>
      DPathP(
        dterm_map_vars_at(line, depth, f),
        dterm_map_vars_at(l, depth, f),
        dterm_map_vars_at(r, depth, f),
      )
    DPath(a, l, r) =>
      DPath(
        dterm_map_vars_at(a, depth, f),
        dterm_map_vars_at(l, depth, f),
        dterm_map_vars_at(r, depth, f),
      )
    DLamDim(body) => DLamDim(dterm_map_vars_at(body, depth, f))
    DAppDim(x, r) => DAppDim(dterm_map_vars_at(x, depth, f), r)
    DCoe(line, r, s, v) =>
      DCoe(
        dterm_map_vars_at(line, depth, f),
        r,
        s,
        dterm_map_vars_at(v, depth, f),
      )
    DComp(line, tubes, base) =>
      DComp(
        dterm_map_vars_at(line, depth, f),
        dterm_map_tubes(tubes, depth, f),
        dterm_map_vars_at(base, depth, f),
      )
    DHComp(a, tubes, base) =>
      DHComp(
        dterm_map_vars_at(a, depth, f),
        dterm_map_tubes(tubes, depth, f),
        dterm_map_vars_at(base, depth, f),
      )
    DHFill(a, tubes, base, r) =>
      DHFill(
        dterm_map_vars_at(a, depth, f),
        dterm_map_tubes(tubes, depth, f),
        dterm_map_vars_at(base, depth, f),
        r,
      )
    DSucc(x) => DSucc(dterm_map_vars_at(x, depth, f))
    DNatElim(m, x, y, z) =>
      DNatElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(y, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DListTy(a) => DListTy(dterm_map_vars_at(a, depth, f))
    DCons(x, y) =>
      DCons(dterm_map_vars_at(x, depth, f), dterm_map_vars_at(y, depth, f))
    DListElim(m, x, y, z) =>
      DListElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(y, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DCircleElim(m, x, y, z) =>
      DCircleElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(y, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DTorusElim(m, x, z) =>
      DTorusElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DInductive(spec, args) =>
      DInductive(spec, dterm_map_vars_list(args, depth, f))
    DIntro(spec, ctor, params, args) =>
      DIntro(
        spec,
        ctor,
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(args, depth, f),
      )
    DInductiveElim(spec, m, cases, params, indices, scrut) =>
      DInductiveElim(
        spec,
        dterm_map_vars_at(m, depth, f),
        dterm_map_vars_list(cases, depth, f),
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(indices, depth, f),
        dterm_map_vars_at(scrut, depth, f),
      )
    DHitType(spec, args) => DHitType(spec, dterm_map_vars_list(args, depth, f))
    DHitIntro(spec, cell, params, args, dims) =>
      DHitIntro(
        spec,
        cell,
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(args, depth, f),
        dims,
      )
    DHitElim(spec, m, cases, params, indices, scrut) =>
      DHitElim(
        spec,
        dterm_map_vars_at(m, depth, f),
        dterm_map_vars_list(cases, depth, f),
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(indices, depth, f),
        dterm_map_vars_at(scrut, depth, f),
      )
    DDecode(spec, params, indices, code) =>
      DDecode(
        spec,
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(indices, depth, f),
        dterm_map_vars_at(code, depth, f),
      )
    DEquivTy(a, b) =>
      DEquivTy(dterm_map_vars_at(a, depth, f), dterm_map_vars_at(b, depth, f))
    DMkEquiv(a, b, fwd, bwd, sect, retr) =>
      DMkEquiv(
        dterm_map_vars_at(a, depth, f),
        dterm_map_vars_at(b, depth, f),
        dterm_map_vars_at(fwd, depth, f),
        dterm_map_vars_at(bwd, depth, f),
        dterm_map_vars_at(sect, depth, f),
        dterm_map_vars_at(retr, depth, f),
      )
    DEquivFwd(e) => DEquivFwd(dterm_map_vars_at(e, depth, f))
    DEquivBwd(e) => DEquivBwd(dterm_map_vars_at(e, depth, f))
    DEquivSect(e) => DEquivSect(dterm_map_vars_at(e, depth, f))
    DEquivRetr(e) => DEquivRetr(dterm_map_vars_at(e, depth, f))
    DGlueEquiv(base, branches) => {
      let out : Array[DEquivBranch] = []
      for i in 0..<branches.length() {
        out.push(
          d_equiv_branch(
            branches[i].face,
            dterm_map_vars_at(branches[i].ty, depth, f),
            dterm_map_vars_at(branches[i].equiv, depth, f),
          ),
        )
      }
      DGlueEquiv(dterm_map_vars_at(base, depth, f), out)
    }
    DUa(e) => DUa(dterm_map_vars_at(e, depth, f))
    other => other
  }
}

///|
fn dterm_map_tubes(
  tubes : Array[DTubeTerm],
  depth : Int32,
  f : (Int32, Int32) -> DTerm,
) -> Array[DTubeTerm] {
  let out : Array[DTubeTerm] = []
  for i in 0..<tubes.length() {
    out.push(d_tube(tubes[i].face, dterm_map_vars_at(tubes[i].body, depth, f)))
  }
  out
}

///|
/// Shift free variables at or above `cutoff` by `delta`.
pub fn dterm_shift(t : DTerm, cutoff : Int32, delta : Int32) -> DTerm {
  dterm_map_vars_at(t, 0, (i, depth) => {
    if i >= cutoff + depth {
      DTVar(i + delta)
    } else {
      DTVar(i)
    }
  })
}

///|
/// Capture-avoiding substitution of one de Bruijn variable.
pub fn dterm_substitute(t : DTerm, index : Int32, replacement : DTerm) -> DTerm {
  dterm_map_vars_at(t, 0, (i, depth) => {
    if i == index + depth {
      dterm_shift(replacement, 0, depth)
    } else if i > index + depth {
      DTVar(i - 1)
    } else {
      DTVar(i)
    }
  })
}

///|
/// Immediate ambient subterms of an AST node.  Embedded schema
/// descriptors are not expanded: their internal terms have
/// schema-local scopes.
pub fn dterm_children(t : DTerm) -> Array[DTerm] {
  match t {
    DPi(a, b)
    | DSigma(a, b)
    | DLam(a, b)
    | DApp(a, b)
    | DPair(a, b)
    | DAnn(a, b)
    | DCons(a, b) => [a, b]
    DFst(a) | DSnd(a) | DLamDim(a) | DSucc(a) | DListTy(a) => [a]
    DBoolElim(a, b, c, d)
    | DNatElim(a, b, c, d)
    | DListElim(a, b, c, d)
    | DCircleElim(a, b, c, d) => [a, b, c, d]
    DPartial(branches) => {
      let out : Array[DTerm] = []
      for i in 0..<branches.length() {
        out.push(branches[i].body)
      }
      out
    }
    DPathP(a, b, c) | DPath(a, b, c) => [a, b, c]
    DAppDim(a, _) => [a]
    DCoe(a, _, _, b) => [a, b]
    DComp(a, tubes, b) | DHComp(a, tubes, b) => {
      let out = [a, b]
      for i in 0..<tubes.length() {
        out.push(tubes[i].body)
      }
      out
    }
    DHFill(a, tubes, b, _) => {
      let out = [a, b]
      for i in 0..<tubes.length() {
        out.push(tubes[i].body)
      }
      out
    }
    DTorusElim(a, b, c) => [a, b, c]
    DInductive(_, args) | DHitType(_, args) => args
    DIntro(_, _, params, args) | DHitIntro(_, _, params, args, _) => {
      let out : Array[DTerm] = []
      for i in 0..<params.length() {
        out.push(params[i])
      }
      for i in 0..<args.length() {
        out.push(args[i])
      }
      out
    }
    DInductiveElim(_, m, cases, params, indices, scrut)
    | DHitElim(_, m, cases, params, indices, scrut) => {
      let out = [m, scrut]
      for i in 0..<cases.length() {
        out.push(cases[i])
      }
      for i in 0..<params.length() {
        out.push(params[i])
      }
      for i in 0..<indices.length() {
        out.push(indices[i])
      }
      out
    }
    DEquivTy(a, b) => [a, b]
    DMkEquiv(a, b, f, g, sect, retr) => [a, b, f, g, sect, retr]
    DEquivFwd(e) | DEquivBwd(e) | DEquivSect(e) | DEquivRetr(e) | DUa(e) => [e]
    DGlueEquiv(base, branches) => {
      let out = [base]
      for i in 0..<branches.length() {
        out.push(branches[i].ty)
        out.push(branches[i].equiv)
      }
      out
    }
    DDecode(_, params, indices, code) => {
      let out = [code]
      for i in 0..<params.length() {
        out.push(params[i])
      }
      for i in 0..<indices.length() {
        out.push(indices[i])
      }
      out
    }
    _ => []
  }
}

///|
// Level-position maps (層級位置映射).
//
// Levels live in: `DUniv(l)` nodes, the `level`/`decode_level` fields of
// embedded schema descriptors, and the telescope, constructor-argument,
// result-index, constraint and decode-case terms of those descriptors.
// Levels are *not* bound by term or dimension binders, so the map needs
// no depth.  Unlike the variable map, embedded schema descriptors *are*
// traversed here: a level-abstracted schema template embeds its nested
// generated types at the same level variables.
//
// `f` maps one raw level position to its replacement.  Positions are
// ordinary non-negative levels plus — inside universe-polymorphic
// templates — `dlevel_var(i) = -1 - i` encodings; the caller decides
// their meaning.  `f` must be total on the positions of its input:
// the universe-polymorphic entry points establish this by validating
// the template first, so these helpers stay package-private.

///|
fn dterm_map_levels_list(
  terms : Array[DTerm],
  f : (Int32) -> Int32,
) -> Array[DTerm] {
  let out : Array[DTerm] = []
  for i in 0..<terms.length() {
    out.push(dterm_map_levels(terms[i], f))
  }
  out
}

///|
fn dterm_map_levels(t : DTerm, f : (Int32) -> Int32) -> DTerm {
  match t {
    DUniv(l) => DUniv(f(l))
    DPi(a, b) => DPi(dterm_map_levels(a, f), dterm_map_levels(b, f))
    DSigma(a, b) => DSigma(dterm_map_levels(a, f), dterm_map_levels(b, f))
    DLam(a, b) => DLam(dterm_map_levels(a, f), dterm_map_levels(b, f))
    DApp(x, y) => DApp(dterm_map_levels(x, f), dterm_map_levels(y, f))
    DPair(x, y) => DPair(dterm_map_levels(x, f), dterm_map_levels(y, f))
    DFst(x) => DFst(dterm_map_levels(x, f))
    DSnd(x) => DSnd(dterm_map_levels(x, f))
    DBoolElim(m, x, y, z) =>
      DBoolElim(
        dterm_map_levels(m, f),
        dterm_map_levels(x, f),
        dterm_map_levels(y, f),
        dterm_map_levels(z, f),
      )
    DAnn(x, y) => DAnn(dterm_map_levels(x, f), dterm_map_levels(y, f))
    DPartial(branches) => {
      let out : Array[DFaceTerm] = []
      for i in 0..<branches.length() {
        out.push(
          d_face_term(branches[i].face, dterm_map_levels(branches[i].body, f)),
        )
      }
      DPartial(out)
    }
    DPathP(line, l, r) =>
      DPathP(
        dterm_map_levels(line, f),
        dterm_map_levels(l, f),
        dterm_map_levels(r, f),
      )
    DPath(a, l, r) =>
      DPath(
        dterm_map_levels(a, f),
        dterm_map_levels(l, f),
        dterm_map_levels(r, f),
      )
    DLamDim(body) => DLamDim(dterm_map_levels(body, f))
    DAppDim(x, r) => DAppDim(dterm_map_levels(x, f), r)
    DCoe(line, r, s, v) =>
      DCoe(dterm_map_levels(line, f), r, s, dterm_map_levels(v, f))
    DComp(line, tubes, base) =>
      DComp(
        dterm_map_levels(line, f),
        dterm_map_levels_tubes(tubes, f),
        dterm_map_levels(base, f),
      )
    DHComp(a, tubes, base) =>
      DHComp(
        dterm_map_levels(a, f),
        dterm_map_levels_tubes(tubes, f),
        dterm_map_levels(base, f),
      )
    DHFill(a, tubes, base, r) =>
      DHFill(
        dterm_map_levels(a, f),
        dterm_map_levels_tubes(tubes, f),
        dterm_map_levels(base, f),
        r,
      )
    DSucc(x) => DSucc(dterm_map_levels(x, f))
    DNatElim(m, x, y, z) =>
      DNatElim(
        dterm_map_levels(m, f),
        dterm_map_levels(x, f),
        dterm_map_levels(y, f),
        dterm_map_levels(z, f),
      )
    DListTy(a) => DListTy(dterm_map_levels(a, f))
    DCons(x, y) => DCons(dterm_map_levels(x, f), dterm_map_levels(y, f))
    DListElim(m, x, y, z) =>
      DListElim(
        dterm_map_levels(m, f),
        dterm_map_levels(x, f),
        dterm_map_levels(y, f),
        dterm_map_levels(z, f),
      )
    DCircleElim(m, x, y, z) =>
      DCircleElim(
        dterm_map_levels(m, f),
        dterm_map_levels(x, f),
        dterm_map_levels(y, f),
        dterm_map_levels(z, f),
      )
    DTorusElim(m, x, z) =>
      DTorusElim(
        dterm_map_levels(m, f),
        dterm_map_levels(x, f),
        dterm_map_levels(z, f),
      )
    DInductive(spec, args) =>
      DInductive(
        dinductive_spec_map_levels(spec, f),
        dterm_map_levels_list(args, f),
      )
    DIntro(spec, ctor, params, args) =>
      DIntro(
        dinductive_spec_map_levels(spec, f),
        ctor,
        dterm_map_levels_list(params, f),
        dterm_map_levels_list(args, f),
      )
    DInductiveElim(spec, m, cases, params, indices, scrut) =>
      DInductiveElim(
        dinductive_spec_map_levels(spec, f),
        dterm_map_levels(m, f),
        dterm_map_levels_list(cases, f),
        dterm_map_levels_list(params, f),
        dterm_map_levels_list(indices, f),
        dterm_map_levels(scrut, f),
      )
    DHitType(spec, args) =>
      DHitType(dhit_spec_map_levels(spec, f), dterm_map_levels_list(args, f))
    DHitIntro(spec, cell, params, args, dims) =>
      DHitIntro(
        dhit_spec_map_levels(spec, f),
        cell,
        dterm_map_levels_list(params, f),
        dterm_map_levels_list(args, f),
        dims,
      )
    DHitElim(spec, m, cases, params, indices, scrut) =>
      DHitElim(
        dhit_spec_map_levels(spec, f),
        dterm_map_levels(m, f),
        dterm_map_levels_list(cases, f),
        dterm_map_levels_list(params, f),
        dterm_map_levels_list(indices, f),
        dterm_map_levels(scrut, f),
      )
    DDecode(spec, params, indices, code) =>
      DDecode(
        dinductive_spec_map_levels(spec, f),
        dterm_map_levels_list(params, f),
        dterm_map_levels_list(indices, f),
        dterm_map_levels(code, f),
      )
    DEquivTy(a, b) => DEquivTy(dterm_map_levels(a, f), dterm_map_levels(b, f))
    DMkEquiv(a, b, fwd, bwd, sect, retr) =>
      DMkEquiv(
        dterm_map_levels(a, f),
        dterm_map_levels(b, f),
        dterm_map_levels(fwd, f),
        dterm_map_levels(bwd, f),
        dterm_map_levels(sect, f),
        dterm_map_levels(retr, f),
      )
    DEquivFwd(e) => DEquivFwd(dterm_map_levels(e, f))
    DEquivBwd(e) => DEquivBwd(dterm_map_levels(e, f))
    DEquivSect(e) => DEquivSect(dterm_map_levels(e, f))
    DEquivRetr(e) => DEquivRetr(dterm_map_levels(e, f))
    DGlueEquiv(base, branches) => {
      let out : Array[DEquivBranch] = []
      for i in 0..<branches.length() {
        out.push(
          d_equiv_branch(
            branches[i].face,
            dterm_map_levels(branches[i].ty, f),
            dterm_map_levels(branches[i].equiv, f),
          ),
        )
      }
      DGlueEquiv(dterm_map_levels(base, f), out)
    }
    DUa(e) => DUa(dterm_map_levels(e, f))
    other => other
  }
}

///|
fn dterm_map_levels_tubes(
  tubes : Array[DTubeTerm],
  f : (Int32) -> Int32,
) -> Array[DTubeTerm] {
  let out : Array[DTubeTerm] = []
  for i in 0..<tubes.length() {
    out.push(d_tube(tubes[i].face, dterm_map_levels(tubes[i].body, f)))
  }
  out
}

///|
fn dfunctor_map_levels(
  fa : DPositiveFunctor,
  f : (Int32) -> Int32,
) -> DPositiveFunctor {
  match fa {
    DFunctorIdentity(index) => DFunctorIdentity(dterm_map_levels_list(index, f))
    DFunctorConst(ty) => DFunctorConst(dterm_map_levels(ty, f))
    DFunctorProduct(a, b) =>
      DFunctorProduct(dfunctor_map_levels(a, f), dfunctor_map_levels(b, f))
    DFunctorSum(a, b) =>
      DFunctorSum(dfunctor_map_levels(a, f), dfunctor_map_levels(b, f))
    DFunctorList(inner) => DFunctorList(dfunctor_map_levels(inner, f))
    DFunctorPi(dom, inner) =>
      DFunctorPi(dterm_map_levels(dom, f), dfunctor_map_levels(inner, f))
    DFunctorContainer(shape, positions, index) =>
      DFunctorContainer(
        dterm_map_levels(shape, f),
        dterm_map_levels(positions, f),
        dterm_map_levels_list(index, f),
      )
  }
}

///|
fn darg_map_levels(
  arg : DConstructorArg,
  f : (Int32) -> Int32,
) -> DConstructorArg {
  DConstructorArg::{
    name: arg.name,
    kind: arg.kind,
    ty: dterm_map_levels(arg.ty, f),
    index: dterm_map_levels_list(arg.index, f),
    nested: dfunctor_map_levels(arg.nested, f),
    target: arg.target,
  }
}

///|
fn dconstraint_map_levels(
  c : DConstructorConstraint,
  f : (Int32) -> Int32,
) -> DConstructorConstraint {
  DConstructorConstraint::{
    ty: dterm_map_levels(c.ty, f),
    lhs: dterm_map_levels(c.lhs, f),
    rhs: dterm_map_levels(c.rhs, f),
  }
}

///|
fn dctor_map_levels(
  ctor : DConstructorSpec,
  f : (Int32) -> Int32,
) -> DConstructorSpec {
  let args : Array[DConstructorArg] = []
  for i in 0..<ctor.args.length() {
    args.push(darg_map_levels(ctor.args[i], f))
  }
  let constraints : Array[DConstructorConstraint] = []
  for i in 0..<ctor.constraints.length() {
    constraints.push(dconstraint_map_levels(ctor.constraints[i], f))
  }
  DConstructorSpec::{
    name: ctor.name,
    args,
    result_index: dterm_map_levels_list(ctor.result_index, f),
    constraints,
  }
}

///|
fn dtelescope_map_levels(
  entries : Array[DTelescopeEntry],
  f : (Int32) -> Int32,
) -> Array[DTelescopeEntry] {
  let out : Array[DTelescopeEntry] = []
  for i in 0..<entries.length() {
    out.push(
      dtelescope_entry(entries[i].name, dterm_map_levels(entries[i].ty, f)),
    )
  }
  out
}

///|
fn dinductive_spec_map_levels(
  spec : DInductiveSpec,
  f : (Int32) -> Int32,
) -> DInductiveSpec {
  let constructors : Array[DConstructorSpec] = []
  for i in 0..<spec.constructors.length() {
    constructors.push(dctor_map_levels(spec.constructors[i], f))
  }
  DInductiveSpec::{
    name: spec.name,
    level: f(spec.level),
    params: dtelescope_map_levels(spec.params, f),
    indices: dtelescope_map_levels(spec.indices, f),
    constructors,
    decode_cases: dterm_map_levels_list(spec.decode_cases, f),
    decode_level: f(spec.decode_level),
  }
}

///|
fn dhit_spec_map_levels(spec : DHitSpec, f : (Int32) -> Int32) -> DHitSpec {
  let cells : Array[DHitCellSpec] = []
  for i in 0..<spec.cells.length() {
    let cell = spec.cells[i]
    let args : Array[DConstructorArg] = []
    for j in 0..<cell.args.length() {
      args.push(darg_map_levels(cell.args[j], f))
    }
    let faces : Array[DHitFaceExpr] = []
    for j in 0..<cell.faces.length() {
      faces.push(
        dhit_face(
          cell.faces[j].cell,
          dterm_map_levels_list(cell.faces[j].args, f),
          cell.faces[j].dims,
        ),
      )
    }
    let constraints : Array[DConstructorConstraint] = []
    for j in 0..<cell.constraints.length() {
      constraints.push(dconstraint_map_levels(cell.constraints[j], f))
    }
    cells.push(
      dhit_cell_spec(
        cell.name,
        cell.dim_count,
        args,
        faces,
        result_index=dterm_map_levels_list(cell.result_index, f),
        constraints~,
      ),
    )
  }
  DHitSpec::{
    name: spec.name,
    level: f(spec.level),
    params: dtelescope_map_levels(spec.params, f),
    indices: dtelescope_map_levels(spec.indices, f),
    cells,
  }
}
