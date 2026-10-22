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
/// Certified variance of one argument position of an opaque neutral
/// type operator.  A registered certificate asserts how occurrences of
/// a family inside that argument position translate: strictly
/// (polarity and strictness preserved), positively (polarity kept,
/// strictness lost), or negatively (polarity flipped, strictness
/// lost).  Certificates are an explicit trust boundary: they cannot be
/// derived from the operator, which is opaque to the checker.
pub enum DVariance {
  VarianceStrict
  VariancePositive
  VarianceNegative
} derive(Debug, Eq)

///|
pub extend DVariance with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DVariance with Eq::{not_equal, equal}

///|
/// Variance certificate for one neutral type operator: one certified
/// variance per argument position, left to right.  An application with
/// no more arguments than certified positions is analysed positionally;
/// any longer application stays conservative.
pub struct DPositivityCert {
  operator : String
  variances : Array[DVariance]
} derive(Debug, Eq)

///|
pub extend DPositivityCert with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DPositivityCert with Eq::{not_equal, equal}

///|
/// Registry of variance certificates.  The value is explicit data
/// passed by the caller (never global state), so validation caches can
/// key on it and two registries never interfere.
pub struct DPositivityCerts {
  certs : Array[DPositivityCert]
} derive(Debug, Eq)

///|
pub extend DPositivityCerts with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DPositivityCerts with Eq::{not_equal, equal}

///|
pub fn dpositivity_cert(
  operator : String,
  variances : Array[DVariance],
) -> DPositivityCert {
  DPositivityCert::{ operator, variances, }
}

///|
/// Certificate with a single certified argument position: strictly
/// positive (polarity and strictness preserved).
pub fn dpositivity_cert_strict(operator : String) -> DPositivityCert {
  DPositivityCert::{ operator, variances: [VarianceStrict], }
}

///|
/// Single-position certificate: positive (polarity kept, strictness
/// lost).
pub fn dpositivity_cert_positive(operator : String) -> DPositivityCert {
  DPositivityCert::{ operator, variances: [VariancePositive], }
}

///|
/// Single-position certificate: negative (polarity flipped, strictness
/// lost).
pub fn dpositivity_cert_negative(operator : String) -> DPositivityCert {
  DPositivityCert::{ operator, variances: [VarianceNegative], }
}

///|
/// Empty registry: the conservative baseline.
pub fn dpositivity_certs_empty() -> DPositivityCerts {
  DPositivityCerts::{ certs: [], }
}

///|
/// Registry size (number of certified operators).
pub fn dpositivity_certs_size(certs : DPositivityCerts) -> Int32 {
  certs.certs.length()
}

///|
/// Registry with `cert` added or replacing the same operator.  Returns
/// a fresh registry; the input is unchanged.
pub fn dpositivity_certs_add(
  certs : DPositivityCerts,
  cert : DPositivityCert,
) -> DPositivityCerts {
  let out : Array[DPositivityCert] = []
  let mut replaced = false
  for i in 0..<certs.certs.length() {
    if certs.certs[i].operator == cert.operator {
      out.push(cert)
      replaced = true
    } else {
      out.push(certs.certs[i])
    }
  }
  if !replaced {
    out.push(cert)
  }
  DPositivityCerts::{ certs: out, }
}

///|
/// Look up the certificate of `operator`.  The empty name never
/// matches, so anonymous binders cannot pick up a certificate.
pub fn dpositivity_certs_lookup(
  certs : DPositivityCerts,
  operator : String,
) -> DPositivityCert? {
  if operator.length() == 0 {
    return None
  }
  for i in 0..<certs.certs.length() {
    if certs.certs[i].operator == operator {
      return Some(certs.certs[i])
    }
  }
  None
}

///|
/// Flatten an application spine into its root and arguments (left to
/// right).
fn app_spine_collect(t : DTerm, acc : Array[DTerm]) -> (DTerm, Array[DTerm]) {
  match t {
    DApp(h, a) => {
      acc.push(a)
      app_spine_collect(h, acc)
    }
    _ => {
      let args : Array[DTerm] = []
      let mut i = acc.length() - 1
      while i >= 0 {
        args.push(acc[i])
        i = i - 1
      }
      (t, args)
    }
  }
}

///|
fn app_spine(t : DTerm) -> (DTerm, Array[DTerm]) {
  app_spine_collect(t, [])
}

///|
fn positivity_of_children_term(
  t : DTerm,
  name : String,
  fuel : Int32,
  names : Array[String],
  depth : Int32,
  certs : DPositivityCerts,
) -> DPositivityReport {
  let children = dterm_children(t)
  let mut out = positivity_absent()
  for i in 0..<children.length() {
    out = positivity_combine(
      out,
      dterm_family_positivity_term(children[i], name, fuel, names, depth, certs),
    )
  }
  out
}

///|
fn dterm_family_positivity_term(
  t : DTerm,
  name : String,
  fuel : Int32,
  names : Array[String],
  depth : Int32,
  certs : DPositivityCerts,
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
    positivity_combine(
      self_report,
      positivity_of_children_term(t, name, fuel, names, depth, certs),
    ),
  )
}

///|
fn positivity_through_parameter(
  report : DPositivityReport,
  arg : DTerm,
  name : String,
  positive : Bool,
  strict_allowed : Bool,
  fuel : Int32,
  names : Array[String],
  depth : Int32,
  certs : DPositivityCerts,
) -> DPositivityReport {
  if report.strictly_positive &&
    report.occurs &&
    !report.unknown &&
    !report.negative_polarity {
    dterm_family_positivity_type(
      arg, name, positive, strict_allowed, fuel, names, depth, certs,
    )
  } else if report.occurs &&
    report.positive_polarity &&
    !report.negative_polarity &&
    !report.unknown {
    positivity_non_strict(
      dterm_family_positivity_type(
        arg, name, positive, false, fuel, names, depth, certs,
      ),
    )
  } else if report.occurs &&
    report.negative_polarity &&
    !report.positive_polarity &&
    !report.unknown {
    positivity_non_strict(
      dterm_family_positivity_type(
        arg,
        name,
        !positive,
        false,
        fuel,
        names,
        depth,
        certs,
      ),
    )
  } else {
    dterm_family_positivity_term(arg, name, fuel, names, depth, certs)
  }
}

///|
fn positivity_variance_walk(
  variance : DVariance,
  arg : DTerm,
  name : String,
  positive : Bool,
  strict_allowed : Bool,
  fuel : Int32,
  names : Array[String],
  depth : Int32,
  certs : DPositivityCerts,
) -> DPositivityReport {
  match variance {
    VarianceStrict =>
      dterm_family_positivity_type(
        arg, name, positive, strict_allowed, fuel, names, depth, certs,
      )
    VariancePositive =>
      positivity_non_strict(
        dterm_family_positivity_type(
          arg, name, positive, false, fuel, names, depth, certs,
        ),
      )
    VarianceNegative =>
      positivity_non_strict(
        dterm_family_positivity_type(
          arg,
          name,
          !positive,
          false,
          fuel,
          names,
          depth,
          certs,
        ),
      )
  }
}

///|
fn dterm_family_positivity_type(
  t : DTerm,
  name : String,
  positive : Bool,
  strict_allowed : Bool,
  fuel : Int32,
  names : Array[String],
  depth : Int32,
  certs : DPositivityCerts,
) -> DPositivityReport {
  match t {
    DPi(a, b) =>
      positivity_combine(
        positivity_flip(
          dterm_family_positivity_type(
            a, name, positive, false, fuel, names, depth, certs,
          ),
        ),
        dterm_family_positivity_type(
          b,
          name,
          positive,
          strict_allowed,
          fuel,
          names,
          depth + 1,
          certs,
        ),
      )
    DSigma(a, b) =>
      positivity_combine(
        dterm_family_positivity_type(
          a, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
        dterm_family_positivity_type(
          b,
          name,
          positive,
          strict_allowed,
          fuel,
          names,
          depth + 1,
          certs,
        ),
      )
    DListTy(a) =>
      dterm_family_positivity_type(
        a, name, positive, strict_allowed, fuel, names, depth, certs,
      )
    DPathP(line, l, r) =>
      positivity_combine(
        dterm_family_positivity_type(
          line, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
        positivity_combine(
          dterm_family_positivity_term(l, name, fuel, names, depth, certs),
          dterm_family_positivity_term(r, name, fuel, names, depth, certs),
        ),
      )
    DPath(a, l, r) =>
      positivity_combine(
        dterm_family_positivity_type(
          a, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
        positivity_combine(
          dterm_family_positivity_term(l, name, fuel, names, depth, certs),
          dterm_family_positivity_term(r, name, fuel, names, depth, certs),
        ),
      )
    DInductive(spec, args) =>
      if spec.name == name {
        let mut out = positivity_occurrence(positive, strict_allowed)
        for i in 0..<args.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(
              args[i],
              name,
              fuel,
              names,
              depth,
              certs,
            ),
          )
        }
        out
      } else {
        let (params, indices) = split_terms_at(args, spec.params.length())
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
              names,
              depth,
              certs,
            ),
          )
        }
        for i in 0..<indices.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(
              indices[i],
              name,
              fuel,
              names,
              depth,
              certs,
            ),
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
            dterm_family_positivity_term(
              args[i],
              name,
              fuel,
              names,
              depth,
              certs,
            ),
          )
        }
        out
      } else {
        let (params, indices) = split_terms_at(args, spec.params.length())
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
              names,
              depth,
              certs,
            ),
          )
        }
        for i in 0..<indices.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(
              indices[i],
              name,
              fuel,
              names,
              depth,
              certs,
            ),
          )
        }
        out
      }
    DApp(_, _) => {
      let (root, args) = app_spine(t)
      match root {
        DLam(_, body) =>
          // Transparent alias applied to arguments: beta-reduce one
          // step and continue with the remaining arguments.
          if fuel <= 0 {
            positivity_unknown()
          } else {
            let mut cur = dterm_substitute(body, 0, args[0])
            let mut i = 1
            while i < args.length() {
              cur = DApp(cur, args[i])
              i = i + 1
            }
            dterm_family_positivity_type(
              cur,
              name,
              positive,
              strict_allowed,
              fuel - 1,
              names,
              depth,
              certs,
            )
          }
        DTVar(k) => {
          // Certified neutral type-operator application: analyse each
          // argument position by its certified variance; unregistered
          // operators and arity overflows stay conservative.
          let idx = k - depth
          if idx < 0 || idx >= names.length() {
            dterm_family_positivity_term(t, name, fuel, names, depth, certs)
          } else {
            match dpositivity_certs_lookup(certs, names[idx]) {
              Some(cert) =>
                if args.length() <= cert.variances.length() {
                  let mut out = positivity_absent()
                  for i in 0..<args.length() {
                    out = positivity_combine(
                      out,
                      positivity_variance_walk(
                        cert.variances[i],
                        args[i],
                        name,
                        positive,
                        strict_allowed,
                        fuel,
                        names,
                        depth,
                        certs,
                      ),
                    )
                  }
                  out
                } else {
                  dterm_family_positivity_term(
                    t, name, fuel, names, depth, certs,
                  )
                }
              None =>
                dterm_family_positivity_term(t, name, fuel, names, depth, certs)
            }
          }
        }
        DInductive(_, _)
        | DHitType(_, _)
        // The family (or another generated family) applied as an
        // operator: occurrence at the head, extra arguments walked
        // conservatively.
        | DDecode(_, _, _, _) => {
          let mut out = dterm_family_positivity_type(
            root, name, positive, strict_allowed, fuel, names, depth, certs,
          )
          for i in 0..<args.length() {
            out = positivity_combine(
              out,
              dterm_family_positivity_term(
                args[i],
                name,
                fuel,
                names,
                depth,
                certs,
              ),
            )
          }
          out
        }
        _ => dterm_family_positivity_term(t, name, fuel, names, depth, certs)
      }
    }
    DLam(a, b) =>
      positivity_combine(
        positivity_flip(
          dterm_family_positivity_type(
            a, name, positive, false, fuel, names, depth, certs,
          ),
        ),
        dterm_family_positivity_type(
          b,
          name,
          positive,
          strict_allowed,
          fuel,
          names,
          depth + 1,
          certs,
        ),
      )
    DAnn(x, y) =>
      positivity_combine(
        dterm_family_positivity_type(
          x, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
        dterm_family_positivity_type(
          y, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
      )
    DLamDim(body) =>
      dterm_family_positivity_type(
        body, name, positive, strict_allowed, fuel, names, depth, certs,
      )
    DAppDim(x, _) =>
      dterm_family_positivity_type(
        x, name, positive, strict_allowed, fuel, names, depth, certs,
      )
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
            names,
            depth,
            certs,
          ),
        )
      }
      out
    }
    DCoe(line, _, _, v) =>
      positivity_combine(
        dterm_family_positivity_type(
          line, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
        dterm_family_positivity_type(
          v, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
      )
    DComp(line, tubes, base) | DHComp(line, tubes, base) => {
      let mut out = positivity_combine(
        dterm_family_positivity_type(
          line, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
        dterm_family_positivity_type(
          base, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
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
            names,
            depth,
            certs,
          ),
        )
      }
      out
    }
    DHFill(a, tubes, base, _) => {
      let mut out = positivity_combine(
        dterm_family_positivity_type(
          a, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
        dterm_family_positivity_type(
          base, name, positive, strict_allowed, fuel, names, depth, certs,
        ),
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
            names,
            depth,
            certs,
          ),
        )
      }
      out
    }
    DDecode(spec, _, _, _) =>
      if spec.name == name {
        positivity_combine(
          positivity_unknown(),
          positivity_of_children_term(t, name, fuel, names, depth, certs),
        )
      } else {
        dterm_family_positivity_term(t, name, fuel, names, depth, certs)
      }
    _ => dterm_family_positivity_term(t, name, fuel, names, depth, certs)
  }
}

///|
/// Structural positivity report for a named generated family in a
/// type term.
pub fn dterm_family_positivity(t : DTerm, name : String) -> DPositivityReport {
  dterm_family_positivity_with(t, name, [], dpositivity_certs_empty())
}

///|
/// Positivity report under a telescope naming context and a registry
/// of variance certificates for neutral type operators.  `names` is in
/// de Bruijn order (index 0 = the innermost binder of the context); a
/// `DTVar(k)` at binder depth `depth` resolves to `names[k - depth]`
/// when that entry exists.  Registered operator applications are
/// analysed by their certified per-argument variance instead of the
/// conservative unknown verdict.
pub fn dterm_family_positivity_with(
  t : DTerm,
  name : String,
  names : Array[String],
  certs : DPositivityCerts,
) -> DPositivityReport {
  dterm_family_positivity_type(t, name, true, true, 64, names, 0, certs)
}

///|
pub fn dterm_family_occurs(t : DTerm, name : String) -> Bool {
  dterm_family_positivity(t, name).occurs
}

///|
/// The certified acceptance rule: an occurrence is admitted exactly
/// when every occurrence is strictly positive (no unknown, no negative
/// polarity).  Non-occurrence is always accepted.
fn schema_positivity_accepts(r : DPositivityReport) -> Bool {
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
    [],
    0,
    dpositivity_certs_empty(),
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
    [],
    0,
    dpositivity_certs_empty(),
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
