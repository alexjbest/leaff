import Lake

open Lake DSL

require Cli from git "https://github.com/leanprover/lean4-cli.git" @ "main"
require std from git "https://github.com/leanprover/std4.git" @ "main"
meta if get_config? mathlib = some "on" then
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "30d39f9a058b13ec1786a90af4c051d650762951"
meta if get_config? mathlib = some "on" then
require mathlib2 from git "https://github.com/leanprover-community/mathlib4" @ "d9ba3f07499769fc5730aea4be84298a2c13ff61"

package «leaff» {
  -- add package configuration options here
}

lean_lib «test» {
  globs := #[.submodules `test]
  -- add library configuration options here
}

lean_lib «Leaff» {
  -- add library configuration options here
}

@[default_target]
lean_exe «leaff» {
  root := `Main
  supportInterpreter := true
}
