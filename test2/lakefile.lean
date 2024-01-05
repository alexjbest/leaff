import Lake
open Lake DSL

package «test» where
  -- add package configuration options here

lean_lib «Test» where
  globs := #[.submodules `Test]
  -- add library configuration options here
