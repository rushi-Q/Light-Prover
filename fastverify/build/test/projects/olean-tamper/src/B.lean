import A
import Lean
run_cmd do
  let h ← IO.FS.Handle.mk ".lake/build/lib/lean/A.olean" .append
  h.write (ByteArray.mk #[0])
theorem b : True := a
