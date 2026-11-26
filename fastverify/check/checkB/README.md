# Legacy research checks C3 / C4 (`check/checkB/`)

Legacy research checks, kept for comparison runs. A run that selects C3 or C4 carries trust `UNSAFE`, which `fv`, the
services and CI never count; no trusted preset uses them, and they are refused on Lean 4.37+ challenges.

```
check/checkB/check-b.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--dual | --single] ...
```

- **C3** (`--dual`, default): `kcompare` (a re-implementation of the comparator's `compareAt` and `checkAxioms`), two
  independent kernels (`gruszka` and `nano-lean`), the official `nanoda_bin` when the configuration names it, and the
  pre-check `check/prechk/` in mode `checkB`, which declines exports on which the official comparator could fail for
  reasons of its own tools (parser limits, replay order, stack depth). ACCEPTED only if every leg accepts and the pre-check
  is clean.
- **C4** (`--single`): one independent kernel and `kcompare`.

Exit 0 ACCEPTED, 1 REJECTED, 2 DECLINED. Binaries are pinned in `components.json` and built by `build.sh DIR` from
`sources/{gruszka,nano-lean,kcompare}` and `patches/`; `prechk` is built by `check/prechk/build.sh` (fully static). Tests:
`test/run.sh`, `regress/regress.sh GENDIR [--official]` and `regress/defs/run.sh`.
