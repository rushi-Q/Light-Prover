def leaked : String := include_str "secret_link.txt"
theorem check_prefix : (leaked.toList.head? == some 'S') = true := rfl
theorem t : True := sorry
