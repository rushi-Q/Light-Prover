mutual
  theorem left (n : Nat) : True :=
    match n with
    | 0 => True.intro
    | k+1 => right k
  theorem right (n : Nat) : True :=
    match n with
    | 0 => True.intro
    | k+1 => left k
end
