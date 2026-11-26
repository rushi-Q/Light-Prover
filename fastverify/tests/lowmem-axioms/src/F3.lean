import Std.Data.HashMap
import Std.Data.TreeMap
theorem hm1 : ((∅ : Std.HashMap Nat Nat).insert 1 2)[1]? = some 2 := by simp
theorem hm2 (m : Std.HashMap Nat Nat) (k v : Nat) : (m.insert k v).contains k = true := by simp
theorem tm1 (m : Std.TreeMap Nat Nat) (k v : Nat) : (m.insert k v).contains k = true := by simp
theorem arr2 (a : Array Nat) (x : Nat) : (a.push x).size = a.size + 1 := by simp
theorem lst3 (l : List Nat) : l.reverse.reverse = l := by simp
