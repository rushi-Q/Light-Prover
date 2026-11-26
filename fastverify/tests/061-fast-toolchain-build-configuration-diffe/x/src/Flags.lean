import Lean
#eval IO.println (Lean.Compiler.FFI.getLinkerFlags "/SYSROOT" false)
#eval IO.println (Lean.Compiler.FFI.getInternalLinkerFlags "/SYSROOT")
