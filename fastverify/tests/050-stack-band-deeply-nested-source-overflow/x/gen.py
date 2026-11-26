# gen.py N -> a Lean module whose single definition has N nested parentheses (ordinary source, no metaprogramming)
import sys
n = int(sys.argv[1])
print('set_option maxRecDepth 100000000')
print('def x : Nat := ' + '(' * n + '1' + ')' * n)
