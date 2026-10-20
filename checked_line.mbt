///|
// Checked, substitutable semantic type lines.
//
// A raw semantic type line is a host function `Dim -> DValue`; such a
// function could in principle inspect dimension syntax in a way that
// does not respect dimension substitution.  A `DCheckedTypeLine`
// instead stores a DTerm body, checked as a type under one fresh
// dimension binder, together with the persistent environments in
// which that body is to be read.  Evaluating the stored body at a
// dimension is exactly dimension substitution, so every checked line
// is natural by construction.  The semantic function is memoized on
// simplified dimensions.
//
// The body follows the same dimension convention as the line argument
// of `DCoe`/`DComp`: `DVar(0)` is the line dimension and ambient
// dimensions are shifted by one.  A constant line stores an ambient
// type term instead and ignores the line dimension.

///|
pub struct DCheckedTypeLine {
  body : DTerm
  ctx : DEnv
  env : DEnv
  denv : DDimEnv
  level : Int32
  constant : Bool
  line : (Dim) -> DValue
}

///|
/// Validate `body` as a type under one fresh dimension and package it
/// as a substitutable type line.  The body is checked at a generic
/// dimension and at both endpoints.
pub fn checked_type_line(
  body : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DCheckedTypeLine? {
  let fresh = fresh_dim(denv)
  match d_as_type(body, ctx, env, ddim_cons(fresh, denv)) {
    Some(tv) => {
      let at_zero = d_as_type(body, ctx, env, ddim_cons(DZero, denv))
      let at_one = d_as_type(body, ctx, env, ddim_cons(DOne, denv))
      match (at_zero, at_one) {
        (Some(z), Some(o)) => {
          let mut level = tv.level
          if z.level > level {
            level = z.level
          }
          if o.level > level {
            level = o.level
          }
          Some(DCheckedTypeLine::{
            body,
            ctx,
            env,
            denv,
            level,
            constant: false,
            line: memo_dim_line(d => dtype_of_line(body, ctx, env, denv, d)),
          })
        }
        _ => None
      }
    }
    None => None
  }
}

///|
pub fn checked_type_line_closed(body : DTerm) -> DCheckedTypeLine? {
  checked_type_line(body, denv_empty(), denv_empty(), ddim_empty())
}

///|
/// A checked constant type line from an ambient type term.
pub fn checked_constant_type_line(
  ty : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DCheckedTypeLine? {
  match d_as_type(ty, ctx, env, denv) {
    Some(tv) =>
      Some(DCheckedTypeLine::{
        body: ty,
        ctx,
        env,
        denv,
        level: tv.level,
        constant: true,
        line: _ => tv.value,
      })
    None => None
  }
}

///|
pub fn checked_constant_type_line_closed(ty : DTerm) -> DCheckedTypeLine? {
  checked_constant_type_line(ty, denv_empty(), denv_empty(), ddim_empty())
}

///|
/// The checked line underlying a PathP type term.
pub fn checked_line_of_pathp_term(
  t : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DCheckedTypeLine? {
  match t {
    DPathP(line, _, _) => checked_type_line(line, ctx, env, denv)
    DPath(a, _, _) => checked_constant_type_line(a, ctx, env, denv)
    _ => None
  }
}

///|
/// The ua line of an equivalence term, as a checked line.  The
/// equivalence term is read with ambient dimensions shifted by the
/// line binder, exactly as in a `DCoe` line body; closed equivalence
/// terms need no adjustment.
pub fn checked_ua_line(
  equiv : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DCheckedTypeLine? {
  checked_type_line(DAppDim(DUa(equiv), DVar(0)), ctx, env, denv)
}

///|
pub fn checked_line_at(line : DCheckedTypeLine, d : Dim) -> DValue {
  (line.line)(d)
}

///|
pub fn checked_line_is_constant(line : DCheckedTypeLine) -> Bool {
  line.constant
}

///|
pub fn checked_line_endpoints(line : DCheckedTypeLine) -> (DValue, DValue) {
  ((line.line)(DZero), (line.line)(DOne))
}

///|
/// Pointwise conversion of checked lines at a generic dimension and
/// at both endpoints.
pub fn checked_line_conv(
  level : Int32,
  dlevel : Int32,
  a : DCheckedTypeLine,
  b : DCheckedTypeLine,
) -> Bool {
  let fresh = DVar(dlevel)
  conv_ty(level, dlevel + 1, (a.line)(fresh), (b.line)(fresh)) &&
  conv_ty(level, dlevel, (a.line)(DZero), (b.line)(DZero)) &&
  conv_ty(level, dlevel, (a.line)(DOne), (b.line)(DOne))
}

///|
/// Quote the body of a checked line under its dimension binder (or
/// the ambient body of a constant line).
pub fn checked_line_quote_body(
  level : Int32,
  dlevel : Int32,
  line : DCheckedTypeLine,
) -> DTerm {
  if line.constant {
    quote_ty(level, dlevel, (line.line)(DZero))
  } else {
    quote_ty(level, dlevel + 1, (line.line)(DVar(dlevel)))
  }
}

///|
/// The PathP type over a checked line.
pub fn checked_pathp_type(
  line : DCheckedTypeLine,
  left : DValue,
  right : DValue,
) -> DValue {
  DVPathTy(line.line, left, right)
}

///|
pub fn checked_coe_value(
  line : DCheckedTypeLine,
  r : Dim,
  s : Dim,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  coe_value(line.line, r, s, v, dlevel)
}

///|
pub fn checked_comp_value(
  line : DCheckedTypeLine,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  comp_value(line.line, branches, base, dlevel)
}

///|
/// Pack a raw semantic line only after reifying and rechecking it at
/// a generic dimension.  The quoted body is read in the empty
/// context, so this succeeds precisely for lines whose generic fibre
/// quotes to a closed, well-formed type line that also validates at
/// the endpoints; the endpoints of the result are then required to
/// be convertible to the raw line's endpoints.
pub fn checked_line_reify_closed(raw : (Dim) -> DValue) -> DCheckedTypeLine? {
  let body = quote_ty(0, 1, raw(DVar(0)))
  match checked_type_line_closed(body) {
    Some(line) =>
      if conv_ty(0, 0, (line.line)(DZero), raw(DZero)) &&
        conv_ty(0, 0, (line.line)(DOne), raw(DOne)) &&
        conv_ty(0, 1, (line.line)(DVar(0)), raw(DVar(0))) {
        Some(line)
      } else {
        None
      }
    None => None
  }
}
