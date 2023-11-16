import Lake

open Lake DSL

require Cli from git "https://github.com/leanprover/lean4-cli.git" @ "main"
require std from git "https://github.com/leanprover/std4.git" @ "main"

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
}


meta if get_config? mathlib = some "on" then
require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "master"
