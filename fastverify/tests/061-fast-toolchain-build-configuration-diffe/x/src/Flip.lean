import Lean
open Lean Elab Term
elab "platform%" : term => return mkStrLit System.Platform.target
-- the fast toolchain's triple; the official 4.33.1 toolchain reports x86_64-unknown-linux-gnu
theorem helper : (platform% : String) = "x86_64-pc-linux-gnu" := rfl
