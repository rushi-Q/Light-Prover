def sieveAux : Nat → List Nat → List Nat
  | 0, l => l
  | _+1, [] => []
  | fuel+1, p :: xs => p :: sieveAux fuel (xs.filter (fun x => x % p != 0))
def primesUpTo (n : Nat) : List Nat := sieveAux n ((List.range (n+1)).drop 2)
def primeSum (n : Nat) : Nat := (primesUpTo n).foldl (· + ·) 0
set_option maxHeartbeats 0 in
theorem heavy : primeSum 8000 = 3738566 := by decide +kernel
theorem main_thm : True := (fun (_ : primeSum 8000 = 3738566) => trivial) heavy
