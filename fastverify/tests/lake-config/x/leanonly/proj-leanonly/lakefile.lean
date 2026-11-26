import Lake
open Lake DSL

package mini where
  srcDir := "src"

@[default_target]
lean_lib Main where
  roots := #[`Main]
