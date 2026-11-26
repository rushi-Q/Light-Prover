unsafe def cntImpl : IO.Ref Nat := unsafeBaseIO (IO.mkRef 0)
@[implemented_by cntImpl] opaque cnt : IO.Ref Nat
