# Output formats

Once a run of `fastverify/bin/fastverify` has initialized `OUT`, it records its progress in `OUT/result.json`
(argument refusals and an unusable `OUT` exit 2 before that; read stderr and the exit status). The front ends (`bin/fv`,
the MCP and HTTP servers, `fv watch` and the CI action) report results in a versioned API envelope; `bin/fv` can also
write SARIF and LSP diagnostics on the subcommands that produce verdicts, and the HTTP batch and Kimina-compatible
endpoints package the envelope in their own response shapes. The standalone judges print their own JSON object.

## API envelope (`result-v1`)

Schema: [`fastverify/schemas/result-v1.schema.json`](../../fastverify/schemas/result-v1.schema.json), validator
`fastverify/schemas/fv_schema.py` (`validate_v1`). Required fields: `api_version`, `mode`, `verdict`, `accepted`,
`reward`, `exit_code`, `trust`, `verdict_basis`, `timing`, `diagnostics`; further fields (`reason`, `target`,
`soundness`, `frontier`, `warnings`, `raw`, ...) depend on the operation.

**Trust rule.** Only a sound-family verdict counts: `accepted` is true if and only if `verdict == "ACCEPTED"` **and**
`trust` is `sound`, `sound-conditional` or `notary`. An ACCEPTED with any other trust - `official` (the unmodified
`lake comparator` decided, for example `--preset reference`; it trusts the configuration's permitted axioms as given),
`UNSAFE`, `exact-by-design (unofficial)`, `conditional` or `none` - keeps its `verdict` but has `accepted: false`,
`reward: 0.0`, `exit_code: 2` and a warning. Consumers (rewards, merge gates, CI) must gate on `accepted` or
`exit_code`, never on `verdict` alone.

Invariants (enforced by `validate_v1`):

- `reward == 1.0` if and only if `accepted`; every other envelope has `reward == 0.0`.
- `exit_code` is a function of `verdict` and `trust`, and it is the exit status of `bin/fv verify`, `check`, `attempt`
  and `watch`:

  | `verdict` | `trust` | `accepted` | `reward` | `exit_code` |
  |---|---|---|---:|---:|
  | `ACCEPTED` | `sound`, `sound-conditional`, `notary` | true | 1.0 | 0 |
  | `ACCEPTED` | `official`, `UNSAFE`, `exact-by-design (unofficial)`, `conditional`, `none` | false | 0.0 | 2 |
  | `REJECTED` | any | false | 0.0 | 1 |
  | `CONDITIONAL` | any (`sound-conditional` from the frontier check) | false | 0.0 | 3 |
  | `DECLINED`, `NO-VERDICT`, `ERROR`, `PENDING` | any | false | 0.0 | 2 |

  So a reference run whose official comparator says ACCEPTED (raw `result.json` verdict ACCEPTED, raw exit 0) is
  reported by `fv` as `verdict: "ACCEPTED"`, `trust: "official"`, `accepted: false`, `reward: 0.0`, and `fv` exits 2.
- CONDITIONAL is the literal `"CONDITIONAL"`, so a prefix test for `ACCEPTED` cannot misread it.

## Diagnostics: SARIF and LSP

Diagnostics are emitted as LSP 3.17 (`--lsp-out FILE`) and SARIF 2.1.0 (`--sarif FILE`) with these rule ids:

| rule | meaning |
|---|---|
| `FV001` | build error |
| `FV002` | statement drift |
| `FV003` | illegal axiom |
| `FV004` | kernel rejection |
| `FV005` | open `sorry` frontier |
| `FV006` | no verdict |
| `FV007` | statement audit finding |

## `result.json`

Rewritten atomically after every stage (`updated` is the time of the last write). Until the run is final - after the
end-of-run integrity check - a decided verdict is written as `"PENDING"` with the decision under `verdict_pending`, so an
interrupted run never shows a verdict.

```
{ "fastverify": {"version", "root", "argv"}, "host", "started", "updated", "finished", "threads",
  "mode": {"preset", "build", "unsafe", "export", "check", "export_given", "fast_policy", "sound"},
  "inputs": {"project", "challenge", "comparator_config": {"path","sha256","content","pinned_sha256"}, "toolchain", "export_targets",
             "solution_module", "challenge_module", "packages_workspace", "dependencies",
             "project_tree": {"sha256","files"},                 # digest of the judged sources (PROJECT minus .lake)
             "host_limits": {"vm.max_map_count","necessary","project_modules"},
             "challenge_export": {"path","source","sha256","size"}},
  "components": {"<name>": {"path","sha256", ...}},          # every pinned binary and stage script actually used
  "preflight": {"<stage>": "ok" | "preflight failed: ..."},
  "build":  {"exit", "option": "B0".."B3", "mode": "fast"|"official", "seconds",
             "attempts": [{"option","mode","exit","seconds","stage": {...}}]},
  "export": {"exit", "option": "E0"|"E1"|"E1-lowmem", "mode", "path", "sha256", "size", "seconds", "attempts": [...],
             "reference": {"sha256","identical"}},                 # a caller-supplied export: "mode": "given", other fields
  "checks": {"<name>": {"option", "exit", "raw_exit",
                        "verdict": "ACCEPTED"|"REJECTED"|"CONDITIONAL"|"DECLINED"|"ERROR"|"NOT_RUN",
                        "seconds", "stage": {...}}},
  "stage_seconds": {"preflight","prepare","build","export","sha256_export","check_<name>","checks_total"},
  "verdict": "ACCEPTED"|"REJECTED"|"CONDITIONAL"|"DECLINED"|"ERROR"|"PENDING"|"PREFLIGHT_OK"|"PREFLIGHT_INCOMPLETE",
  "verdict_pending", "verdict_basis", "official_comparator": {"challenge_release","comparator_toolchain","tool"},
  "verdict_official", "verdict_fast", "verdict_fast_basis": {"policy","accepted_by","rejected_by","declined_or_not_run"},
  "trust": "sound"|"sound-conditional"|"notary"|"official"|"exact-by-design (unofficial)"|"UNSAFE", "unsafe_reasons": [...],
  "soundness": {"claim", "trusted": {"challenge_export","check"}, "untrusted": {"build","export"}},
  "autotune": {"build","unsafe","options","threads","check_threads","check_plan","reasons","dropped","features","host"},
  "frontier": {"mode","verdict","frontier":[{name,type,type_sha256,source}],"frontier_size","blockers","claim",...},
  "overlap": {"dir","snapshots","mode"},
  "check_pins": {"path","sha256","selected_by","hide":{"path","sha256"}},
  "check_pins_missing": {"path","missing"},
  "confirm_reject": {...}, "require_sorried_holes", "extra_kernels",
  "interrupted": ...,
  "agreement", "warnings": [...], "exit" }
```

Notes on the fields:

| field | notes |
|---|---|
| `verdict` | the decision ([soundness.md](../concepts/soundness.md#verdicts)). `PENDING`: the run is not final yet (the decision is in `verdict_pending`), or C0 is selected without CS/CN (for example `--check C3,C0`), the other checks have finished and the official comparator still runs. `PREFLIGHT_OK` / `PREFLIGHT_INCOMPLETE`: a `--preflight-only` run (exit 0 / 2). A refusal (unsupported toolchain, unpinned binary, inconsistent challenge, dependency mismatch, host limit, a component changed during the run, internal error) is `ERROR` with the reason in `verdict_basis`. |
| `trust` | the basis of the verdict; `sound` when the sound judge decided. Only `sound`, `sound-conditional` and `notary` count as accepted in the API envelope ([trust rule](#api-envelope-result-v1)); a raw ACCEPTED with `official` or `UNSAFE` trust exits 0 from `bin/fastverify` but never counts. |
| `official_comparator` | when C0 decided: the challenge's release and the comparator toolchain that judged it (they can differ: releases before 4.37 are judged by the pinned 4.36.0 comparator) |
| `require_sorried_holes` | CS / CN: whether the sorried-hole switch was on |
| `verdict_basis` | the trusted components that decided, or the reason for no verdict |
| `soundness` | sound mode: the challenge export sha256 and whether it equals `--challenge-sha256`, the judge's pinned binaries, the untrusted build option and its transforms with the reason each one is sound, the export sha256 |
| `checks` | one entry per selected check: `sound` (CS; with `--modulo-frontier` its stage is the frontier judge's), `notary` (CN), `official` (C0), and the legacy `checkB` (C3), `checkB_single` (C4) (results of pre-release package versions can also hold `checkA` (C1) and `checkA_patched` (C2), the retired check A). The CS stage object includes per-leg status (`legs`), leg times, inputs and the sha256 of the binaries. |
| `build.confirmed_by`, `build.failed_modules` | not written in v0.1 (a failed transformed build is always confirmed by the full exact build) |
| `export.option`, `export.attempts[].option` | the final and each attempted exporter; `E1-lowmem` marks the low-memory exporter. A caller-supplied export (`--from-export`) records `mode: "given"` without `option` or `attempts` |
| `export.reference.identical` | with `--reference-export`: byte identity with a reference export (information only in sound mode) |
| `autotune` | `sound-auto`: every choice and its reason (`check_plan.con_leche`: whether `con-leche` would fit the memory budget if enabled) |
| `extra_kernels` | sound mode: a human-readable summary string with one part per veto-only extra kernel of the judge, for example `con-leche: off (opt-in: ...); nanoda: off (...)` (the default), `con-leche: accepted`, `con-leche: not decided (declined (unsupported feature): ...)` or `con-leche: skipped (memory) ...`; the full per-kernel record is `checks.sound.stage.extra_kernels` (also `soundness.trusted.check.extra_kernels`) |
| `frontier` | `--modulo-frontier`: each open lemma with its name, statement and statement hash, and source candidates when a matching declaration is found; `blockers` explains a REJECTED |
| `check_pins`, `check_pins_missing` | the judge's pins file when one was selected; the missing judge when `sound-auto` refused |
| `confirm_reject` | both rounds of `--confirm-reject` |
| `interrupted` | the run received SIGTERM, SIGINT or SIGHUP; never a verdict (exit 2), whatever `verdict` says |
| `warnings`, `agreement` | research presets: disagreements between checks; `ALARM` if a fast check accepted what the official comparator rejected |
| `exit` | the process exit status of `bin/fastverify` (raw: 0 also for an ACCEPTED with `official` or `UNSAFE` trust, and for `PREFLIGHT_OK`) |

To print the essentials of a run:

```bash
python3 -c 'import json,sys; r=json.load(open(sys.argv[1])); e=r.get("export") or {}; print(r.get("verdict"),
  r.get("verdict_official"), r.get("verdict_fast"), r.get("trust"), e.get("sha256"),
  (e.get("reference") or {}).get("identical"), r.get("stage_seconds"))' OUT/result.json
```

(Preflight-only and early-failure results lack later fields, and `export` can be null.)

## Standalone judge output

`check/sound/check-sound.sh` and the other standalone judges print one JSON object on their last stdout line (or write
it with `--json FILE`). Main fields: `verdict`, `exit`, `reason` (the judge's first error, for example
`Illegal axiom detected: 'sorryAx'`), `basis`, `binaries_sha256`, and per leg (`legs.lean`, `legs.k2`) the exit status,
time and first message; for the official-kernel leg, the first refused declaration. A deciding leg killed by the OOM killer
shows `rc = 137`: no verdict, never a rejection (an optional extra kernel killed that way is recorded as "not decided"
and leaves the verdict; a `--require-kernel` kernel then means no verdict). The frontier judge reports its two checks
under `checks`, with its frontier and claim. `check-sound.sh` (v2.3-H) adds `extra_kernels`: per extra kernel `mode`
(`off`, `auto` = default-on via the default switch, `optional` = `--kernel`, `required`), `status` (`accepted`, `rejected`, `not decided`,
`skipped (memory)`, `not configured`, `not consulted` = the two-kernel verdict was not ACCEPTED, `off`, and in
`--preflight` output `self-test ok` / `self-test failed`), `reason`, `rc`,
`wall_s`, `max_rss_kb`, `message` (the deciding line) and `sha256`; `extra_kernels_summary` (one line),
`two_kernel_wall_s` (when the two-kernel verdict was ready) and `kernel_grace_s`.

Only the judge scripts give verdicts. The leg binaries started directly are not judges: an exit status 0 of `ccmp` or
`pleanchecker` is not a verdict. They take trust-relevant settings from the environment (`ccmp` the binary of its Lean
kernel leg from `CCMP_LEANCHECKER`, the 4.37 `pleanchecker` its hide list from `PCHK_HIDE_FILE`); the judge scripts
re-execute under `env -i` and set these themselves.
