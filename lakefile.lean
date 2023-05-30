import Lake
open Lake DSL

package «lean4sexp» {
  -- add package configuration options here
  moreLeanArgs := #["-DautoImplicit=false"]
}

lean_lib Sexp {
  -- add library configuration options here
}

lean_lib Export {
  -- add library configuration options here
}

lean_lib Test {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4sexp» {
  root := `Main
  supportInterpreter := true
}
