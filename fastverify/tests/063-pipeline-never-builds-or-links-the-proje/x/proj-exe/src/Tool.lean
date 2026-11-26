-- the tool calls a C function that the project never provides: `lake build` cannot link the executable
@[extern "mini_missing_c_function"] opaque missingFn : UInt32 → UInt32
def main : IO Unit := IO.println (missingFn 1)
