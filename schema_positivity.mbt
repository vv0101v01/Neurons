///|
// Structural strict-positivity analysis for generated families.
//
// This replaces the original Debug-string name scan.  The analysis
// walks type syntax with polarity and a strictness context,
// beta-reduces aliases (with fuel, so ill-typed self-applications
// cannot make validation loop), and understands indirect occurrences
// through previously generated families whose parameters have been
// certified positive by analysing their own constructor telescopes.
//
// A report distinguishes:
//   * no occurrence;
//   * a strictly positive occurrence;
//   * a merely positive-polarity but non-strict occurrence (for
//     example under a double negation); and
//   * negative or unknown occurrences.
//
// The schema validator remains sound in a deliberately simple way:
// external arguments and function domains must have *no* occurrence,
// while genuinely recursive occurrences are admitted only through
// the recursive/function/nested/decoded descriptors for which the
// generator knows how to synthesize induction hypotheses.

///|
pub struct DPositivityReport {
  occurs : Bool
  strictly_positive : Bool
  positive_polarity : Bool
  negative_polarity : Bool
  unknown : Bool
} derive(Debug, Eq)

///|
pub extend DPositivityReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DPositivityReport with Eq::{not_equal, equal}

///|
pub fn dpositivity_report(
  occurs : Bool,
  strictly_positive : Bool,
  positive_polarity : Bool,
  negative_polarity : Bool,
  unknown : Bool,
) -> DPositivityReport {
  DPositivityReport::{
    occurs,
    strictly_positive,
    positive_polarity,
    negative_polarity,
    unknown,
  }
}

///|
fn positivity_absent() -> DPositivityReport {
  DPositivityReport::{
    occurs: false,
    strictly_positive: true,
    positive_polarity: false,
    negative_polarity: false,
    unknown: false,
  }
}

///|
fn positivity_occurrence(
  positive : Bool,
  strict_allowed : Bool,
) -> DPositivityReport {
  DPositivityReport::{
    occurs: true,
    strictly_positive: strict_allowed && positive,
    positive_polarity: positive,
    negative_polarity: !positive,
    unknown: false,
  }
}

///|
fn positivity_unknown() -> DPositivityReport {
  DPositivityReport::{
    occurs: true,
    strictly_positive: false,
    positive_polarity: false,
    negative_polarity: false,
    unknown: true,
  }
}

///|
fn positivity_combine(
  a : DPositivityReport,
  b : DPositivityReport,
) -> DPositivityReport {
  DPositivityReport::{
    occurs: a.occurs || b.occurs,
    strictly_positive: a.strictly_positive && b.strictly_positive,
    positive_polarity: a.positive_polarity || b.positive_polarity,
    negative_polarity: a.negative_polarity || b.negative_polarity,
    unknown: a.unknown || b.unknown,
  }
}

///|
fn positivity_flip(r : DPositivityReport) -> DPositivityReport {
  if r.occurs {
    DPositivityReport::{
      occurs: true,
      strictly_positive: false,
      positive_polarity: r.negative_polarity,
      negative_polarity: r.positive_polarity,
      unknown: r.unknown,
    }
  } else {
    r
  }
}

///|
fn positivity_mark_unknown(r : DPositivityReport) -> DPositivityReport {
  if r.occurs {
    DPositivityReport::{
      occurs: true,
      strictly_positive: false,
      positive_polarity: r.positive_polarity,
      negative_polarity: r.negative_polarity,
      unknown: true,
    }
  } else {
    r
  }
}

///|
fn positivity_non_strict(r : DPositivityReport) -> DPositivityReport {
  DPositivityReport::{
    occurs: r.occurs,
    strictly_positive: r.strictly_positive && !r.occurs,
    positive_polarity: r.positive_polarity,
    negative_polarity: r.negative_polarity,
    unknown: r.unknown,
  }
}

///|
fn positivity_of_children_term(
  t : DTerm,
  name : String,
  fuel : Int32,
) -> DPositivityReport {
  let children = dterm_children(t)
  let mut out = positivity_absent()
  for i in 0..<children.length() {
    out = positivity_combine(
      out,
      dterm_family_positivity_term(children[i], name, fuel),
    )
  }
  out
}

///|
fn dterm_family_positivity_term(
  t : DTerm,
  name : String,
  fuel : Int32,
) -> DPositivityReport {
  let self_report = match t {
    DInductive(spec, _) =>
      if spec.name == name {
        positivity_unknown()
      } else {
        positivity_absent()
      }
    DHitType(spec, _) =>
      if spec.name == name {
        positivity_unknown()
      } else {
        positivity_absent()
      }
    DDecode(spec, _, _, _) =>
      if spec.name == name {
        positivity_unknown()
      } else {
        positivity_absent()
      }
    _ => positivity_absent()
  }
  positivity_mark_unknown(
    positivity_combine(self_report, positivity_of_children_term(t, name, fuel)),
  )
}

///|
fn positivity_split_terms(
  terms : Array[DTerm],
  n : Int32,
) -> (Array[DTerm], Array[DTerm]) {
  let a : Array[DTerm] = []
  let b : Array[DTerm] = []
  for i in 0..<terms.length() {
    if i < n {
      a.push(terms[i])
    } else {
      b.push(terms[i])
    }
  }
  (a, b)
}

///|
fn positivity_through_parameter(
  report : DPositivityReport,
  arg : DTerm,
  name : String,
  positive : Bool,
  strict_allowed : Bool,
  fuel : Int32,
) -> DPositivityReport {
  if report.strictly_positive &&
    report.occurs &&
    !report.unknown &&
    !report.negative_polarity {
    dterm_family_positivity_type(arg, name, positive, strict_allowed, fuel)
  } else if report.occurs &&
    report.positive_polarity &&
    !report.negative_polarity &&
    !report.unknown {
    positivity_non_strict(
      dterm_family_positivity_type(arg, name, positive, false, fuel),
    )
  } else if report.occurs &&
    report.negative_polarity &&
    !report.positive_polarity &&
    !report.unknown {
    positivity_non_strict(
      dterm_family_positivity_type(arg, name, !positive, false, fuel),
    )
  } else {
    dterm_family_positivity_term(arg, name, fuel)
  }
}

///|
fn dterm_family_positivity_type(
  t : DTerm,
  name : String,
  positive : Bool,
  strict_allowed : Bool,
  fuel : Int32,
) -> DPositivityReport {
  match t {
    DPi(a, b) =>
      positivity_combine(
        positivity_flip(
          dterm_family_positivity_type(a, name, positive, false, fuel),
        ),
        dterm_family_positivity_type(b, name, positive, strict_allowed, fuel),
      )
    DSigma(a, b) =>
      positivity_combine(
        dterm_family_positivity_type(a, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(b, name, positive, strict_allowed, fuel),
      )
    DListTy(a) =>
      dterm_family_positivity_type(a, name, positive, strict_allowed, fuel)
    DPathP(line, l, r) =>
      positivity_combine(
        dterm_family_positivity_type(line, name, positive, strict_allowed, fuel),
        positivity_combine(
          dterm_family_positivity_term(l, name, fuel),
          dterm_family_positivity_term(r, name, fuel),
        ),
      )
    DPath(a, l, r) =>
      positivity_combine(
        dterm_family_positivity_type(a, name, positive, strict_allowed, fuel),
        positivity_combine(
          dterm_family_positivity_term(l, name, fuel),
          dterm_family_positivity_term(r, name, fuel),
        ),
      )
    DInductive(spec, args) =>
      if spec.name == name {
        let mut out = positivity_occurrence(positive, strict_allowed)
        for i in 0..<args.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(args[i], name, fuel),
          )
        }
        out
      } else {
        let (params, indices) = positivity_split_terms(
          args,
          spec.params.length(),
        )
        let mut out = positivity_absent()
        for i in 0..<params.length() {
          out = positivity_combine(
            out,
            positivity_through_parameter(
              inductive_parameter_positivity(spec, i),
              params[i],
              name,
              positive,
              strict_allowed,
              fuel,
            ),
          )
        }
        for i in 0..<indices.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(indices[i], name, fuel),
          )
        }
        out
      }
    DHitType(spec, args) =>
      if spec.name == name {
        let mut out = positivity_occurrence(positive, strict_allowed)
        for i in 0..<args.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(args[i], name, fuel),
          )
        }
        out
      } else {
        let (params, indices) = positivity_split_terms(
          args,
          spec.params.length(),
        )
        let mut out = positivity_absent()
        for i in 0..<params.length() {
          out = positivity_combine(
            out,
            positivity_through_parameter(
              hit_parameter_positivity(spec, i),
              params[i],
              name,
              positive,
              strict_allowed,
              fuel,
            ),
          )
        }
        for i in 0..<indices.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(indices[i], name, fuel),
          )
        }
        out
      }
    DApp(DLam(_, body), arg) =>
      if fuel <= 0 {
        positivity_unknown()
      } else {
        dterm_family_positivity_type(
          dterm_substitute(body, 0, arg),
          name,
          positive,
          strict_allowed,
          fuel - 1,
        )
      }
    DLam(a, b) =>
      positivity_combine(
        positivity_flip(
          dterm_family_positivity_type(a, name, positive, false, fuel),
        ),
        dterm_family_positivity_type(b, name, positive, strict_allowed, fuel),
      )
    DAnn(x, y) =>
      positivity_combine(
        dterm_family_positivity_type(x, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(y, name, positive, strict_allowed, fuel),
      )
    DLamDim(body) =>
      dterm_family_positivity_type(body, name, positive, strict_allowed, fuel)
    DAppDim(x, _) =>
      dterm_family_positivity_type(x, name, positive, strict_allowed, fuel)
    DPartial(branches) => {
      let mut out = positivity_absent()
      for i in 0..<branches.length() {
        out = positivity_combine(
          out,
          dterm_family_positivity_type(
            branches[i].body,
            name,
            positive,
            strict_allowed,
            fuel,
          ),
        )
      }
      out
    }
    DCoe(line, _, _, v) =>
      positivity_combine(
        dterm_family_positivity_type(line, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(v, name, positive, strict_allowed, fuel),
      )
    DComp(line, tubes, base) | DHComp(line, tubes, base) => {
      let mut out = positivity_combine(
        dterm_family_positivity_type(line, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(base, name, positive, strict_allowed, fuel),
      )
      for i in 0..<tubes.length() {
        out = positivity_combine(
          out,
          dterm_family_positivity_type(
            tubes[i].body,
            name,
            positive,
            strict_allowed,
            fuel,
          ),
        )
      }
      out
    }
    DHFill(a, tubes, base, _) => {
      let mut out = positivity_combine(
        dterm_family_positivity_type(a, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(base, name, positive, strict_allowed, fuel),
      )
      for i in 0..<tubes.length() {
        out = positivity_combine(
          out,
          dterm_family_positivity_type(
            tubes[i].body,
            name,
            positive,
            strict_allowed,
            fuel,
          ),
        )
      }
      out
    }
    DDecode(spec, _, _, _) =>
      if spec.name == name {
        positivity_combine(
          positivity_unknown(),
          positivity_of_children_term(t, name, fuel),
        )
      } else {
        dterm_family_positivity_term(t, name, fuel)
      }
    _ => dterm_family_positivity_term(t, name, fuel)
  }
}

///|
/// Structural positivity report for a named generated family in a
/// type term.
pub fn dterm_family_positivity(t : DTerm, name : String) -> DPositivityReport {
  dterm_family_positivity_type(t, name, true, true, 64)
}

///|
pub fn dterm_family_occurs(t : DTerm, name : String) -> Bool {
  dterm_family_positivity(t, name).occurs
}

///|
pub fn dterm_family_strictly_positive(t : DTerm, name : String) -> Bool {
  let r = dterm_family_positivity(t, name)
  !r.occurs || (r.strictly_positive && !r.unknown && !r.negative_polarity)
}

///|
fn positivity_probe_name() -> String {
  "__PositivityProbe"
}

///|
fn positivity_probe_term() -> DTerm {
  DInductive(dinductive_spec(positivity_probe_name(), 0, [], [], []), [])
}

///|
fn positivity_substitute_param(
  t : DTerm,
  scope : Int32,
  param_index : Int32,
) -> DTerm {
  let variable = scope - 1 - param_index
  if variable < 0 {
    t
  } else {
    dterm_substitute(t, variable, positivity_probe_term())
  }
}

///|
fn positivity_param_in_type(
  t : DTerm,
  scope : Int32,
  param_index : Int32,
  strict_allowed : Bool,
) -> DPositivityReport {
  dterm_family_positivity_type(
    positivity_substitute_param(t, scope, param_index),
    positivity_probe_name(),
    true,
    strict_allowed,
    64,
  )
}

///|
fn positivity_param_in_term(
  t : DTerm,
  scope : Int32,
  param_index : Int32,
) -> DPositivityReport {
  dterm_family_positivity_term(
    positivity_substitute_param(t, scope, param_index),
    positivity_probe_name(),
    64,
  )
}

///|
fn positivity_param_in_terms(
  terms : Array[DTerm],
  scope : Int32,
  param_index : Int32,
) -> DPositivityReport {
  let mut out = positivity_absent()
  for i in 0..<terms.length() {
    out = positivity_combine(
      out,
      positivity_param_in_term(terms[i], scope, param_index),
    )
  }
  out
}

///|
fn positivity_param_in_functor(
  functor : DPositiveFunctor,
  scope : Int32,
  param_index : Int32,
) -> DPositivityReport {
  match functor {
    DFunctorIdentity(index) =>
      positivity_param_in_terms(index, scope, param_index)
    DFunctorConst(ty) => positivity_param_in_type(ty, scope, param_index, true)
    DFunctorProduct(a, b) | DFunctorSum(a, b) =>
      positivity_combine(
        positivity_param_in_functor(a, scope, param_index),
        positivity_param_in_functor(b, scope, param_index),
      )
    DFunctorList(inner) =>
      positivity_param_in_functor(inner, scope, param_index)
    DFunctorPi(dom, inner) =>
      positivity_combine(
        positivity_non_strict(
          positivity_param_in_type(dom, scope, param_index, false),
        ),
        positivity_param_in_functor(inner, scope + 1, param_index),
      )
    DFunctorContainer(shape, positions, index) =>
      positivity_combine(
        positivity_non_strict(
          positivity_param_in_type(shape, scope, param_index, false),
        ),
        positivity_combine(
          positivity_non_strict(
            positivity_param_in_type(positions, scope + 1, param_index, false),
          ),
          positivity_param_in_terms(index, scope + 2, param_index),
        ),
      )
  }
}

///|
fn positivity_param_in_arg(
  arg : DConstructorArg,
  scope : Int32,
  param_index : Int32,
  has_decode : Bool,
) -> DPositivityReport {
  match arg.kind {
    DArgExternal => positivity_param_in_type(arg.ty, scope, param_index, true)
    DArgRecursive => positivity_param_in_terms(arg.index, scope, param_index)
    DArgFunction =>
      positivity_combine(
        positivity_non_strict(
          positivity_param_in_type(arg.ty, scope, param_index, false),
        ),
        positivity_param_in_terms(arg.index, scope + 1, param_index),
      )
    DArgNested => positivity_param_in_functor(arg.nested, scope, param_index)
    DArgDecoded =>
      if has_decode {
        positivity_unknown()
      } else {
        positivity_absent()
      }
    DArgDecodedFunction =>
      positivity_combine(
        if has_decode {
          positivity_unknown()
        } else {
          positivity_absent()
        },
        positivity_param_in_terms(arg.index, scope + 1, param_index),
      )
  }
}

///|
fn positivity_param_in_telescope(
  entries : Array[DTelescopeEntry],
  start_scope : Int32,
  param_index : Int32,
) -> DPositivityReport {
  let mut out = positivity_absent()
  for i in 0..<entries.length() {
    out = positivity_combine(
      out,
      positivity_param_in_term(entries[i].ty, start_scope + i, param_index),
    )
  }
  out
}

///|
fn positivity_decode_case_scope(
  ctor : DConstructorSpec,
  params : Int32,
) -> Int32 {
  let mut scope = params
  for i in 0..<ctor.args.length() {
    scope = scope + 1
    match ctor.args[i].kind {
      DArgRecursive | DArgFunction | DArgNested | DArgDecodedFunction =>
        scope = scope + 1
      _ => ()
    }
  }
  scope + ctor.constraints.length()
}

///|
/// Certify how one parameter of a generated inductive family is used
/// by its constructors.  A strictly positive report is what permits
/// an indirect recursive occurrence through this family in the
/// structural positivity checker.
pub fn inductive_parameter_positivity(
  spec : DInductiveSpec,
  param_index : Int32,
) -> DPositivityReport {
  if param_index < 0 || param_index >= spec.params.length() {
    return positivity_absent()
  }
  let mut out = positivity_param_in_telescope(spec.params, 0, param_index)
  out = positivity_combine(
    out,
    positivity_param_in_telescope(
      spec.indices,
      spec.params.length(),
      param_index,
    ),
  )
  let has_decode = spec.decode_cases.length() > 0
  for c in 0..<spec.constructors.length() {
    let ctor = spec.constructors[c]
    for i in 0..<ctor.args.length() {
      out = positivity_combine(
        out,
        positivity_param_in_arg(
          ctor.args[i],
          spec.params.length() + i,
          param_index,
          has_decode,
        ),
      )
    }
    out = positivity_combine(
      out,
      positivity_param_in_terms(
        ctor.result_index,
        spec.params.length() + ctor.args.length(),
        param_index,
      ),
    )
    for i in 0..<ctor.constraints.length() {
      let scope = spec.params.length() + ctor.args.length()
      out = positivity_combine(
        out,
        positivity_param_in_term(ctor.constraints[i].ty, scope, param_index),
      )
      out = positivity_combine(
        out,
        positivity_param_in_term(ctor.constraints[i].lhs, scope, param_index),
      )
      out = positivity_combine(
        out,
        positivity_param_in_term(ctor.constraints[i].rhs, scope, param_index),
      )
    }
    if c < spec.decode_cases.length() {
      out = positivity_combine(
        out,
        positivity_param_in_term(
          spec.decode_cases[c],
          positivity_decode_case_scope(ctor, spec.params.length()),
          param_index,
        ),
      )
    }
  }
  out
}

///|
/// Parameter-use certification for generated HITs.
pub fn hit_parameter_positivity(
  spec : DHitSpec,
  param_index : Int32,
) -> DPositivityReport {
  if param_index < 0 || param_index >= spec.params.length() {
    return positivity_absent()
  }
  let mut out = positivity_param_in_telescope(spec.params, 0, param_index)
  out = positivity_combine(
    out,
    positivity_param_in_telescope(
      spec.indices,
      spec.params.length(),
      param_index,
    ),
  )
  for c in 0..<spec.cells.length() {
    let cell = spec.cells[c]
    for i in 0..<cell.args.length() {
      out = positivity_combine(
        out,
        positivity_param_in_arg(
          cell.args[i],
          spec.params.length() + i,
          param_index,
          false,
        ),
      )
    }
    let scope = spec.params.length() + cell.args.length()
    out = positivity_combine(
      out,
      positivity_param_in_terms(cell.result_index, scope, param_index),
    )
    for i in 0..<cell.constraints.length() {
      out = positivity_combine(
        out,
        positivity_param_in_term(cell.constraints[i].ty, scope, param_index),
      )
      out = positivity_combine(
        out,
        positivity_param_in_term(cell.constraints[i].lhs, scope, param_index),
      )
      out = positivity_combine(
        out,
        positivity_param_in_term(cell.constraints[i].rhs, scope, param_index),
      )
    }
    for f in 0..<cell.faces.length() {
      out = positivity_combine(
        out,
        positivity_param_in_terms(cell.faces[f].args, scope, param_index),
      )
    }
  }
  out
}

///|
pub fn schema_telescope_family_occurs(
  entries : Array[DTelescopeEntry],
  name : String,
) -> Bool {
  for i in 0..<entries.length() {
    if dterm_family_occurs(entries[i].ty, name) {
      return true
    }
  }
  false
}
