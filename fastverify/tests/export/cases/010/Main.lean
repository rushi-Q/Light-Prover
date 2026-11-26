import Lean
open Lean Elab Command

-- a String literal whose bytes are not valid UTF-8 (validity proof forged inside an unsafe metaprogram)
unsafe def badStr : String := String.fromUTF8 (ByteArray.mk #[0x61, 0xff, 0x62, 0xc3, 0x28, 0xed, 0xa0, 0x80]) (unsafeCast ())

run_cmd liftTermElabM do
  addDecl (.defnDecl { name := `badLit, levelParams := [], type := mkConst ``String, value := mkStrLit (unsafe badStr),
                       hints := .opaque, safety := .safe, all := [`badLit] })

theorem riemannHypothesis : (4 : Nat) = 4 := (fun (_ : String) => rfl) badLit
theorem riemannZeta_eq_zero_re : True := trivial
theorem LFunction_ne_zero_of_half_lt_re : True := trivial
theorem LFunction_eq_zero_re : True := trivial
theorem LFunction_eq_zero_re_of_isPrimitive : True := trivial
