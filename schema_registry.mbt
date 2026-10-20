///|
// Schema registration, validation caching, and telescope-elaboration
// caching.
//
// A registry interns inductive and HIT descriptors as *plans*: the
// descriptor is validated once, its parameter/index telescopes are
// elaborated once at generic values, and later registrations of a
// structurally equal descriptor return the existing plan.  Concrete
// telescope elaborations are cached semantically: a cached request
// is reused when prefix types, prefix values, and telescope values
// are convertible stepwise, so no telescope type is recomputed on a
// hit.  The public `inductive_schema_validate` /
// `hit_schema_validate` entry points go through a shared default
// registry, which removes the repeated validation that AST
// evaluation/inference would otherwise perform for every embedded
// descriptor occurrence.

///|
pub struct DInductivePlan {
  id : Int32
  key : String
  spec : DInductiveSpec
  valid : Bool
  generic_param_types : Array[DValue]
  generic_index_types : Array[DValue]
}

///|
pub struct DHitPlan {
  id : Int32
  key : String
  spec : DHitSpec
  valid : Bool
  generic_param_types : Array[DValue]
  generic_index_types : Array[DValue]
}

///|
pub struct DTelescopeCacheEntry {
  entries : Array[DTelescopeEntry]
  prefix_types : Array[DValue]
  prefix_values : Array[DValue]
  values : Array[DValue]
  types : Array[DValue]
}

///|
pub struct DSchemaRegistry {
  inductives : Array[DInductivePlan]
  hits : Array[DHitPlan]
  telescopes : Array[DTelescopeCacheEntry]
  mut validation_hits : Int32
  mut validation_misses : Int32
  mut telescope_hits : Int32
  mut telescope_misses : Int32
}

///|
pub fn schema_registry_new() -> DSchemaRegistry {
  DSchemaRegistry::{
    inductives: [],
    hits: [],
    telescopes: [],
    validation_hits: 0,
    validation_misses: 0,
    telescope_hits: 0,
    telescope_misses: 0,
  }
}

///|
/// The shared registry used by the descriptor-embedding AST forms.
pub let default_schema_registry : DSchemaRegistry = schema_registry_new()

///|
pub fn inductive_schema_key(spec : DInductiveSpec) -> String {
  Repr(spec).to_string()
}

///|
pub fn hit_schema_key(spec : DHitSpec) -> String {
  Repr(spec).to_string()
}

///|
fn copy_values(values : Array[DValue]) -> Array[DValue] {
  schema_concat_values([], values)
}

///|
pub fn schema_registry_register_inductive(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
) -> DInductivePlan {
  for i in 0..<registry.inductives.length() {
    if registry.inductives[i].spec == spec {
      registry.validation_hits = registry.validation_hits + 1
      return registry.inductives[i]
    }
  }
  registry.validation_misses = registry.validation_misses + 1
  let valid = inductive_schema_validate_uncached(spec)
  let pv = schema_fresh_values(spec.params.length(), 8200)
  let param_types = if valid {
    telescope_type_values(spec.params, [], [], pv)
  } else {
    []
  }
  let iv = schema_fresh_values(spec.indices.length(), 8300)
  let index_types = if valid {
    telescope_type_values(spec.indices, param_types, pv, iv)
  } else {
    []
  }
  let plan = DInductivePlan::{
    id: registry.inductives.length(),
    key: inductive_schema_key(spec),
    spec,
    valid,
    generic_param_types: param_types,
    generic_index_types: index_types,
  }
  registry.inductives.push(plan)
  plan
}

///|
pub fn schema_registry_register_hit(
  registry : DSchemaRegistry,
  spec : DHitSpec,
) -> DHitPlan {
  for i in 0..<registry.hits.length() {
    if registry.hits[i].spec == spec {
      registry.validation_hits = registry.validation_hits + 1
      return registry.hits[i]
    }
  }
  registry.validation_misses = registry.validation_misses + 1
  let valid = hit_schema_validate_uncached(spec)
  let pv = schema_fresh_values(spec.params.length(), 8200)
  let param_types = if valid {
    telescope_type_values(spec.params, [], [], pv)
  } else {
    []
  }
  let iv = schema_fresh_values(spec.indices.length(), 8300)
  let index_types = if valid {
    telescope_type_values(spec.indices, param_types, pv, iv)
  } else {
    []
  }
  let plan = DHitPlan::{
    id: registry.hits.length(),
    key: hit_schema_key(spec),
    spec,
    valid,
    generic_param_types: param_types,
    generic_index_types: index_types,
  }
  registry.hits.push(plan)
  plan
}

///|
pub fn schema_registry_hit_by_id(
  registry : DSchemaRegistry,
  id : Int32,
) -> DHitPlan? {
  if id >= 0 && id < registry.hits.length() {
    Some(registry.hits[id])
  } else {
    None
  }
}

///|
pub fn schema_registry_inductive_by_name(
  registry : DSchemaRegistry,
  name : String,
) -> DInductivePlan? {
  for i in 0..<registry.inductives.length() {
    if registry.inductives[i].spec.name == name {
      return Some(registry.inductives[i])
    }
  }
  None
}

///|
pub fn schema_registry_validate_inductive(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
) -> Bool {
  schema_registry_register_inductive(registry, spec).valid
}

///|
pub fn schema_registry_validate_hit(
  registry : DSchemaRegistry,
  spec : DHitSpec,
) -> Bool {
  schema_registry_register_hit(registry, spec).valid
}

///|
/// Validate an inductive descriptor through the shared registry:
/// each structurally distinct descriptor is validated once.
pub fn inductive_schema_validate(spec : DInductiveSpec) -> Bool {
  schema_registry_validate_inductive(default_schema_registry, spec)
}

///|
pub fn hit_schema_validate(spec : DHitSpec) -> Bool {
  schema_registry_validate_hit(default_schema_registry, spec)
}

///|
fn telescope_cache_matches(
  entry : DTelescopeCacheEntry,
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  values : Array[DValue],
) -> Bool {
  if entry.prefix_types.length() != prefix_types.length() ||
    entry.values.length() != values.length() {
    return false
  }
  for i in 0..<prefix_types.length() {
    if !conv_ty(10000, 0, entry.prefix_types[i], prefix_types[i]) ||
      !conv_at(
        10000,
        0,
        entry.prefix_types[i],
        entry.prefix_values[i],
        prefix_values[i],
      ) {
      return false
    }
  }
  for i in 0..<values.length() {
    if i >= entry.types.length() ||
      !conv_at(10000, 0, entry.types[i], entry.values[i], values[i]) {
      return false
    }
  }
  true
}

///|
/// `telescope_type_values` with semantic caching in a registry.
pub fn telescope_type_values_cached(
  registry : DSchemaRegistry,
  entries : Array[DTelescopeEntry],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  values : Array[DValue],
) -> Array[DValue] {
  for i in 0..<registry.telescopes.length() {
    let entry = registry.telescopes[i]
    if entry.entries == entries &&
      telescope_cache_matches(entry, prefix_types, prefix_values, values) {
      registry.telescope_hits = registry.telescope_hits + 1
      return copy_values(entry.types)
    }
  }
  registry.telescope_misses = registry.telescope_misses + 1
  let types = telescope_type_values(
    entries, prefix_types, prefix_values, values,
  )
  registry.telescopes.push(DTelescopeCacheEntry::{
    entries,
    prefix_types: copy_values(prefix_types),
    prefix_values: copy_values(prefix_values),
    values: copy_values(values),
    types: copy_values(types),
  })
  types
}

///|
pub fn inductive_param_types_cached(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
  params : Array[DValue],
) -> Array[DValue] {
  telescope_type_values_cached(registry, spec.params, [], [], params)
}

///|
pub fn inductive_index_types_cached(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> Array[DValue] {
  telescope_type_values_cached(
    registry,
    spec.indices,
    inductive_param_types_cached(registry, spec, params),
    params,
    indices,
  )
}

///|
pub fn hit_param_types_cached(
  registry : DSchemaRegistry,
  spec : DHitSpec,
  params : Array[DValue],
) -> Array[DValue] {
  telescope_type_values_cached(registry, spec.params, [], [], params)
}

///|
pub fn hit_index_types_cached(
  registry : DSchemaRegistry,
  spec : DHitSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> Array[DValue] {
  telescope_type_values_cached(
    registry,
    spec.indices,
    hit_param_types_cached(registry, spec, params),
    params,
    indices,
  )
}

///|
/// AST terms built from a registered plan share the plan's one
/// descriptor rather than reconstructing it at each use.
pub fn inductive_plan_type_term(
  plan : DInductivePlan,
  args : Array[DTerm],
) -> DTerm {
  DInductive(plan.spec, args)
}
