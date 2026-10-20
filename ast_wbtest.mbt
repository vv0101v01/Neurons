///|
test "cubical AST paths" {
  inspect(check_ast_paths(), content="true")
}

///|
test "cubical AST data" {
  inspect(check_ast_data(), content="true")
}

///|
test "cubical AST HITs" {
  inspect(check_ast_hits(), content="true")
}

///|
test "cubical AST Kan terms" {
  inspect(check_ast_kan_terms(), content="true")
}

///|
test "cubical AST Kan by type" {
  inspect(check_ast_kan_types(), content="true")
}
