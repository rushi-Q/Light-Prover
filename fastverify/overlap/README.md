# Overlap of the kernel leg with the build (`overlap/`)

Opt-in and untrusted scheduling for very large proofs: parts of the official-kernel leg run while the build is still
running, on snapshot exports of the modules that have finished. No preset enables it; `bin/fastverify --preset sound
--overlap-targets FILE` turns on the targeted mode. The plain judge path (`check-sound.sh` without `--incr-dir`) uses
none of this.

## How it works

`lib/fastverify.py` starts a kernel server (`incr-server.sh`: the pinned `pleanchecker_incr` in a bubblewrap sandbox like
the judge's kernels) and an untrusted snapshot driver (`snapdriver.py`) before the build. When modules finish, the driver
exports the closure of not yet checked target names with the pinned `snapshot_exporter` and hands the snapshot to the
server over a FIFO (`snap PATH`). In the targeted mode the server kernel-checks only the listed declarations (the long
kernel jobs of the hint list), each on an environment of the snapshot's constants. When the build returns, the driver
is stopped, the final export is written, and the judge runs with `--incr-dir`: its kernel leg attaches to the server,
which replays the final export from an empty environment with the unchanged replay and skips a target's kernel call only
if the final export holds the same constant, every constant it reaches is present and equal in both, and the
kernel-implicit constants agree. ACCEPTED also requires every skipped check to have succeeded; otherwise the final export
is replayed without skips. The full mode (`--overlap`) checks every snapshot declaration; it is reviewed and gated but
pays only where the build leaves CPUs idle.

## Soundness relevance

The server and the replay are part of the trusted kernel leg; the driver, the snapshot exporter, the target list and the
hint lists are untrusted inputs that can only change which work is done early. Why a targeted skip is safe: the
skipped job checked the same constant against an environment in which every constant it reaches, and every constant the
kernel looks up without a syntactic reference, is equal to the final export's; the kernel's answer therefore cannot
differ, and the final replay still replays every other declaration in Lean's order. Records of inductive blocks are
compared with the kernel's own constants, as in the sound judge.

## Pinned binaries (`check/sound/pins.env`)

| pin | sha256 | sources | rebuild |
|---|---|---|---|
| `pleanchecker_incr` | `6a9092380325cc6f6ae94234e671aa67ba6a5daf163e642611d01c0762b91b7f` | `check/sound/src` with `overlap/src/r9d/{Main.lean,PChk/Par.lean,PChk/Incr.lean}` | as the 4.36 `pleanchecker` ([`check/sound/`](../check/sound/README.md#rebuilding)): objects with `lake build`, PGO + ThinLTO link with the build bundle |
| `snapshot_exporter` | `4ac1016d928ccec86869d392ab6f3485fa139bd361ba484154f80126af4bd9cd` | the native exporter E1 plus the snapshot mode (`overlap/src/e1-snap.diff`, `native/fast_export.cpp` only) | as E1 ([`export/`](../export/README.md#pinned-binaries)) with the diff applied |

## Files

| file | trusted? | role |
|---|---|---|
| `incr-server.sh` | wiring | starts the pinned `pleanchecker_incr --incremental=OUT/incr` in a bwrap sandbox like the comparator's kernels (no network, read-only `/`, `/home` `/tmp` `/run` hidden, clean env; nice 19, targeted mode `incr-server.sh DIR PLC T TARGETS`: `--targeted=DIR/targets.txt`, nice 0 (`INCR_NICE`), THP kept only if `/proc/vmstat` `compact_stall` is 0 (`INCR_THP=1/0` forces), `PCHK_PRIO_FILE` = targets + `check/sound/hints/default.txt` + `hints-next.txt`) |
| `snapdriver.py` | **no** | follows `LOG/build-fast/sched.out`; when the build drains (>= 12 % of the CPU idle or nice) exports the constants of finished modules with the pinned `snapshot_exporter` (bwrap, nice 19, `OUT/incr` hidden) and sends `snap PATH`. Roots are passed in the solution module's import order (duplicate theorems resolve like in the final export); hand-written duplicate theorem names (static source scan) are deferred until the module whose version the final export keeps is built; constants the server left out (`leftout-K.txt`) are exported again later; at most 8 % of the modules per snapshot, two snapshots in flight. `--targets FILE` = targeted mode (see below) |
| `hints-next.txt` | no (order only) | the 723 RH kernel jobs >= 10 s that are not in the CS hint list: once the targets are skipped they are the longest jobs of the final replay, so the targeted server serves them first |
| `hints-next-merged.txt` | no (order only; NOT used by default) | refresh for merged builds (908 = `hints-next.txt` + 185 names >= 10 s from merged builds; merge renames `_private.<module>.0` prefixes, so private hints from unmerged runs miss). Unmeasured: to use it, copy it over `hints-next.txt`. Rule: regenerate hints from a check log of the SAME build configuration |
| `targets-ranked.txt`, `targets-top40.txt`, `targets-top80.txt` | no (selection only) | the 279 CS hint names ranked by their kernel time on server A (longest first; `check/sound/hints/default.txt` itself is alphabetical) and its first 40 (the preset's `--overlap-targets overlap/targets-top40.txt`: ~8k CPU-s of target checks instead of ~24k, by a cost model over K) / first 80 (a candidate) |
| `test/` | — | `incr_cases.sh` (rh-mid adversarial, stdin protocol), `arena_incr.sh` (arena 225 in 3 protocols), `incr_gates.sh` + `cases-mid.tsv` (full wiring: server + check-sound.sh `--incr-dir`), `targeted_e2e.sh` + `fakebuild.py` + `targets-mid.txt` (targeted mode end to end on rh-mid: emulated build-fast records, driver `--targets`, server, check-sound; honest -> ACCEPT with the targets skipped, mutant -> REJECT); inputs from `FV_BENCH_INPUTS` / `OVERLAP_INPUTS` (script headers) |

## Measured

On server A (384 threads) the targeted mode with the top 40 targets shortened the Riemann Hypothesis kernel
leg from about 402 s to 370 s and the whole `--preset sound` run from 1,789 s to 1,766 s (one run each, earlier pins).
Outside that proof it gives no gain ([limitations](../../docs/limitations.md#performance)).
