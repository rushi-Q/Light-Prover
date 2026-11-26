import LA
open Lean Elab Command in
run_cmd liftCoreM <| modifyEnv fun env => myExt.addEntry env 1
