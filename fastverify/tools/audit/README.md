# Statement audit (`tools/audit/`, advisory)

An advisor for challenge authors and for readers who check statements. It never changes a verdict: the judge does not call it, and
its output carries `advisory: true`. `fv audit` is the front end.

```bash
python3 -I fastverify/tools/audit/audit.py CHALLENGE --base-index MATHLIB.baseidx --probe --reading-set reading-set.lean --json audit.json
python3 -I fastverify/tools/audit/audit.py Subgoal.lean --packages WS --probe --conjecture-mode      # a standalone file
python3 -I fastverify/tools/audit/audit.py solution.export --config comparator.json --solution-mode   # after a proof
python3 -I fastverify/tools/audit/audit.py CHALLENGE --fail-on HIGH --json out.json                    # CI intake: exit 1 at HIGH
fastverify/tools/audit/bin/expaudit index-base -j 16 -o mathlib.baseidx mathlib.export                 # one-time Mathlib index
```

It extracts the minimal set of non-Mathlib definitions a reader must check to understand the statements, runs static lints
on the statements' kernel terms (rules `F01`-`F11`: missing or non-theorem targets, non-standard axioms, `sorry` or
`opaque` in the statement closure, definition holes, modified base declarations, trivial conclusions or contradictory
premises, unconstrained implicit parameters, existentials over implications, uninhabited premises, truncating `Nat`
arithmetic, and, with `--solution-mode`, targets proved without any project lemma), and with `--probe` sandboxed
dynamic probes of the statements. Exit 0 no finding, 1 a finding at or above
`--fail-on`, 2 the audit could not run. Measured precision and recall are small-sample figures
([limitations](../../../docs/limitations.md#what-a-verdict-does-not-tell-you)). The `expaudit` binary:
[PROVENANCE.md](../../PROVENANCE.md).
