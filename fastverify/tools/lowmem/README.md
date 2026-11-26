# Low-memory end-to-end verifier (`tools/lowmem/`)

`fv_lowmem.py` runs a whole verification within a memory budget: it detects the cgroup or host budget, builds the
challenge officially if needed, builds the project with the number of parallel `lean` jobs capped to the budget, exports
with the low-memory exporter (falling back to the official one) and judges with the
[low-memory judge](../../check/lowmem/README.md).

```
python3 -I fastverify/tools/lowmem/fv_lowmem.py PROJECT CHALLENGE OUT --challenge-sha256 HEX --comparator-sha256 HEX \
    [--mem-budget-mb MB] [--threads N] [--packages WS] [--pins 437]
python3 -I fastverify/tools/lowmem/fv_lowmem.py - CHALLENGE OUT --from-export SOL.export --challenge-sha256 HEX --comparator-sha256 HEX
```

`fv check --low-mem` and `--preset sound-auto` (which switches to the low-memory judge when the estimated peak exceeds the
budget) cover most uses. Measured memory floors: [benchmarks](../../../docs/benchmarks.md#judging-an-export-by-machine-budget).
