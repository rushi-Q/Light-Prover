import Tiny.A
theorem tinyB : (2 : Nat) + 2 + 0 = 4 := by
  rw [tinyA]
-- kernel-invalid but accepted by a build with -Ddebug.skipKernelTC=true (the build-time kernel check is skipped):
theorem v05bad : (2 : Nat) + 2 = 5 := by decide +kernel
