import Lake

open Lake DSL

require Cli from git "https://github.com/leanprover/lean4-cli.git" @ "main"
require Std from git "https://github.com/leanprover/std4.git" @ "main"

package «leaff» {
  -- add package configuration options here
}

lean_lib «Leaff» {
  -- add library configuration options here
}

@[default_target]
lean_exe «leaff» {
  root := `Main
}
