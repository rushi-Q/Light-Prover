import Lean
open Lean Elab Term

/-- The package this module is compiled in, as Lean records it in the module's environment / .olean
(`Lean.Environment.getModulePackage?`, public API; set from the build system's setup, e.g. Lake's `--setup`). -/
elab "thisPackage" : term => return mkStrLit (toString ((← getEnv).getModulePackage?))

def pkg : String := thisPackage
