import Lake
open Lake DSL

-- Lake 4.33.1 uses lakefile.lean when both lakefile.lean and lakefile.toml exist (Lake/Load/Package.lean:110-116)
package mini where
  srcDir := "src"

@[default_target]
lean_lib Main where
  srcDir := "real"
  roots := #[`Main]
