///|
test "generated inductive schemas" {
  inspect(check_generated_inductive_schemas(), content="true")
}

///|
test "generated HIT schemas" {
  inspect(check_generated_hit_schemas(), content="true")
}

///|
test "phase-5 semantic systems, environments and laziness" {
  inspect(check_phase5_semantic_systems(), content="true")
}

///|
test "extended schemas: positivity, nesting, mutual, IR, constraints, quotients, 3-cells" {
  inspect(check_schema_extensions(), content="true")
}
