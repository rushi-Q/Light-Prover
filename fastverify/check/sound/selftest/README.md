# check/sound/selftest — the judges' self-test inputs

Every judge script (`check/sound/check-sound.sh`, `check-sound-svc.sh`, `check/lowmem/check-sound-lowmem.sh`,
`check-sound-ultralowmem.sh`, `check/notary/check-notary.sh`) checks these self-test inputs before each run. They are
pinned by sha256 in every `pins*.env` (`PIN selftest_comparator`, `selftest_challenge`, `selftest_good`,
`selftest_bad`; `selftest_kbad` in `check/sound/pins.env` and `pins-437.env`). The judge hashes each file before every
run and DECLINES if a file is missing or its sha256 differs from the pin ("pinned file missing" / "sha256 mismatch").

| file | content |
|---|---|
| `comparator.json` | the self-test comparator configuration: theorem `fvSelfTest`, no definitions, permitted axioms `propext`, `Quot.sound`, `Classical.choice`; lists `nanoda` as an external kernel |
| `challenge.export` | the self-test challenge (theorem `fvSelfTest`), exported by the official lean4export of Lean 4.33.1 |
| `good.export` | a valid solution: `fvSelfTest : 2 + 2 = 4 := rfl` |
| `bad.export` | a solution that uses a custom axiom (`fvCheat`) |
| `selftest-kbad.export` | `good.export` with the proof of `fvSelfTest` made kernel-invalid; used only when an extra kernel (`PIN con_leche` / `PIN nanoda`) is enabled |

`SHA256SUMS` lists the five files; the hashes equal the PIN lines.

## Install

The pins name fixed paths. Copy the files there (read-only), from the repository root:

```
install -D -m 444 fastverify/check/sound/selftest/{comparator.json,challenge.export,good.export,bad.export} -t /scratch/fastverify-next/selftest/
install -D -m 444 fastverify/check/sound/selftest/selftest-kbad.export /scratch/fastverify-next/selftest/selftest-kbad.export
```

If you install the pinned components under another prefix, use the paths in your edited `pins*.env` files instead.
