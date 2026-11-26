# User guide

This guide covers the daily workflows: verifying a project or an export, sound feedback while a development still has
`sorry` lemmas, a per-edit daemon, an attempt service for provers and RL pipelines, a CI gate, and choosing a
configuration for your hardware. Installation is in [getting-started.md](getting-started.md); every option is in the
[reference](reference/cli.md); measured costs are in [benchmarks.md](benchmarks.md).

Paths are relative to the repository root. Placeholders:

| placeholder | meaning |
|---|---|
| `PROJECT`, `CHALLENGE`, `OUT` | the Lean project; the clean challenge directory (`comparator.json` and the official `challenge.export`); a fresh output directory |
| `$PIN`, `$CFG_PIN` | sha256 of the official `challenge.export` (printed by `fv init-challenge`) and of `comparator.json` |
| `$WS` | a trusted Lake workspace whose `.lake/packages` holds the project's dependencies |
| `$ST` | a private state directory for a daemon, on a local disk |

## Verdicts in one paragraph

A verdict is ACCEPTED (exit 0) only when the target statements equal the pinned challenge's, only permitted axioms are
used, and every declaration in the targets' closure is accepted by an independent second kernel and (except `unsafe` and
`partial` records, which the official replay skips) by the official Lean kernel. REJECTED is exit 1, no verdict (DECLINED or ERROR) exit 2, and CONDITIONAL (opt-in) exit 3. For rewards and merge
gates use the envelope's `accepted` field or `fv`'s exit status: only an ACCEPTED with trust `sound`, `sound-conditional`
or `notary` counts (exit 0); an ACCEPTED of the official comparator (`--preset reference`, trust `official`) is reported
but exits 2 ([trust rule](reference/result-json.md#api-envelope-result-v1)). Count no verdict as a failure, because
hostile code can steer a run there. The challenge identity (the sha256 of `challenge.export` and of `comparator.json`) is
always configured by you or on the server side, and both pins are required together: the comparator configuration decides which statements and axioms are checked, so it
is pinned like the challenge. With a fixed challenge identity, services accept solutions only (the MCP server can also
be configured to take caller challenge directories, and then requires both pins). Details:
[soundness model](concepts/soundness.md).

## Prepare a challenge

```bash
fastverify/bin/fv doctor --project PROJECT              # bwrap, cgroup RAM, /dev/shm, pins, the plan sound-auto would pick
python3 -I fastverify/lib/autotune.py PROJECT --json    # what --preset sound-auto would choose here, and why

fastverify/bin/fv init-challenge CHALLENGE_SRC CHALLENGE --packages "$WS" -j 16     # official build + export; prints sha256
fastverify/bin/fv audit CHALLENGE --challenge-sha256 "$PIN" --probe --reading-set reading-set.lean    # advisory; runs no sound check, so no comparator pin
```

`CHALLENGE_SRC` is a challenge source directory: the statements with `sorry` proofs, a lakefile, `lean-toolchain` and
`comparator.json` (see the example in [getting started](getting-started.md#6-first-verification)). `fv init-challenge`
builds and exports it with the official tools and prints the pin. `fv audit` is advisory: it flags statement hazards and
writes the minimal set of non-library statements a reader must check ([helpers](#advisory-helpers)).

## Verify a project

```bash
fastverify/bin/fv verify PROJECT -c CHALLENGE --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
    --packages "$WS" -j 16 --json --sarif out.sarif
fastverify/bin/fastverify PROJECT CHALLENGE OUT --preset sound-auto --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
    --packages "$WS"
```

- `fv verify` defaults to `--preset sound-auto`, which tunes the untrusted build to the project and the host and records
  every choice in `result.json` under `autotune`. Use `--preset sound` only for very large projects on large nodes
  ([presets](reference/options.md#presets)).
- `--guard mem=16G,wall=600` adds resource limits ([limits and isolation](#share-one-verifier-limits-and-isolation)).
- `--incr-base OUT` is accepted but, in v0.1, takes the cold sound path: the project is verified from scratch, and the
  result says so (`verdict_basis` and `warnings`: "incremental mode is experimental in v0.1 and was not used"). The
  incremental machinery is EXPERIMENTAL and not reachable from `fv`.
- A failed transformed build is always confirmed by the full exact build B1 (or B0) before REJECTED; read
  `build.attempts`, the build log and `verdict_basis`.
- Several claims in one repository: `fastverify/tools/claims.py verify PROJECT GIVEN_ROOT WS OUT` builds once and judges
  each claim against its own pinned challenge (`claims.py pin` produces the official challenge exports first).

## Judge an existing export

When a publisher or a prover ships the export, skip the build:

```bash
fastverify/bin/fv check solution.export -c CHALLENGE --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
    [--low-mem | --experimental --notary | --pins 437 | --frontier]
fastverify/bin/fastverify - CHALLENGE OUT --preset sound-auto --from-export solution.export --challenge-sha256 "$PIN" \
    --comparator-sha256 "$CFG_PIN"
fastverify/check/sound/check-sound.sh solution.export CHALLENGE/challenge.export CHALLENGE/comparator.json \
    --threads 32 [--private-inputs] [--json res.json]
```

- The judges copy every input first (a reflink where possible), so the kernel legs judge a file nobody else can write.
  `--private-inputs` hard-links exports larger than 4 GiB instead; use it only for a file you produced.
- The judge's JSON (last stdout line, or `--json`) has `verdict`, `exit`, `reason` (the first error, for example
  `Illegal axiom detected: 'sorryAx'`) and per leg the exit status, time and first message
  ([output formats](reference/result-json.md#standalone-judge-output)). A leg killed by the OOM killer shows `rc = 137`:
  no verdict, never a rejection.
- The sound judge can add two veto-only extra kernels bundled with the official Lean 4.37.0-rc1 release, both off by
  default: `con-leche` and `nanoda` (`check-sound.sh --kernel NAME`, `bin/fastverify --extra-kernel NAME`; `fv check` has
  no option for them). An extra kernel's own rejection turns ACCEPTED into REJECTED; anything it cannot decide (custom
  axioms, format limits, memory, stack, timeout) is reported as `not decided (<reason>)` in `extra_kernels` and does not
  change the verdict; `--require-kernel NAME` (both tools) makes one mandatory (then "not decided" is no verdict).
  Both have known false rejects and costs ([limitations](limitations.md#assurance)).
- Pick the judge variant by available memory and the assurance you need
  ([choose a judge](#choose-a-preset-and-judge-for-your-hardware)): `--low-mem` for tight RAM, `--notary` (EXPERIMENTAL in v0.1) for
  archival sign-off with the unmodified official kernel libraries (its independent kernels with `--notary-kernels`; `gruszka`
always runs), `--pins 437` for Lean
  4.37.0-rc1 challenges.

## Conditional verdicts while proving

While a `sorry` is used in the targets' closure, every sound preset answers REJECTED (`sorryAx`). `--modulo-frontier`
answers instead:
*are the challenge's theorems proved from exactly these open lemmas, with everything else kernel-checked and no other
axiom?* Opt-in.

```bash
fastverify/bin/fv verify PROJECT -c CHALLENGE --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --modulo-frontier auto \
    --frontier-base prev/result.json
fastverify/bin/fastverify PROJECT CHALLENGE OUT --preset sound-auto --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
    --modulo-frontier [ALLOWED.txt] [--frontier-pin PINDIR]
fastverify/check/frontier/check-frontier.sh EXPORT CHALLENGE/challenge.export CHALLENGE/comparator.json --threads 16 \
    [--allowed FILE] [--pinned PINDIR] [--base BASE.json] [--axioms FILE] [--pins FILE]
python3 -I fastverify/tools/frontier/frontier.py pin EXPORT CHALLENGE/challenge.export CHALLENGE/comparator.json PINDIR
python3 -I fastverify/tools/frontier/ledger.py gate BASE.json CURRENT.json [--allow-new] [--require-progress] [--block-dropped]
```

`ALLOWED.txt` lists the lemmas that may stay open; a pin (`frontier.py pin`) also fixes their statements. The result's
`frontier` lists each open lemma with its statement, hash and users, and source candidates when a matching declaration
is found; `blockers` explains a REJECTED.

**What CONDITIONAL guarantees.** Every official target, with its official statement, is derivable from the permitted
axioms plus exactly the listed open lemmas (their statements are recorded in a minted frontier challenge whose sha256 is
in the result), and both kernels accepted every declaration. Two runs of the unchanged judge decide; the preparation is
untrusted ([argument](../fastverify/check/frontier/README.md)). **Not claimed:** that the open lemmas are true
or non-vacuous (an open lemma `False` implies every target; triage them), that the work is finished, or anything outside
the targets' closure.

| development state | verdict |
|---|---|
| `theorem L : P := by sorry` used below a target | CONDITIONAL; the frontier is the sorried lemmas actually used |
| a sketch inside a target (`have h : A := by sorry; ...`), a Prop `sorry` in a definition's proof position | CONDITIONAL with generated lemmas `T._fv_sorry_k` (the goal closed over its local context) |
| a data `sorry` (`def f : ℕ := sorry`), a `sorry` inside a statement, a target whose whole proof is `sorry` | REJECTED |
| `native_decide`, a project `axiom` (unless declared with `--axioms FILE`), a changed target statement | REJECTED |
| with an allowed list or pin: a new open lemma outside it, a restated pinned lemma | REJECTED |
| no `sorry` left in the closure | ACCEPTED (exit 0) |

Declared project axioms become listed hypotheses only with `check-frontier.sh --axioms FILE` or
`fv check --frontier --frontier-axioms FILE` (not a `bin/fastverify` flag); the compiler-trust axioms of `native_decide`
can never be listed.

**A typical workflow.** On day 1, connect each target to sorried lemmas, check, and pin the frontier. On every later day,
judge each attempt against the pin, so no lemma can be weakened, no assumption hidden and no `sorry` moved into a
definition. On every pull request, run `ledger.py gate` against `main`'s result; `--block-dropped` flags a lemma that
left the closure unproved (for example a target proved by a trivial witness). An ACCEPTED target that uses no project
lemma at all deserves a look at its statement.

## Re-verify on every edit

For a project edited many times a day, the per-repository daemon `tools/fvwork` answers each submitted tree with the sound
verdict of the whole project. In v0.1 every request takes the cold sound path: `fvwork serve --check sound` (the default)
runs `bin/fastverify --preset sound` on exactly the submitted tree - a fresh build, export and trusted check; nothing of
the base, of earlier requests or of a memo is reused, and no pre-warmed legs are started - so a request costs about a
cold run of the project. The judged tree becomes the base of later `--files` requests. `fvwork init` also accepts a
project whose fast build hands off to the official build (for example a root `lakefile.lean`): if the base run reaches a
sound verdict, that state serves the cold sound path only, and `serve --experimental-incremental` refuses it. Opt-in;
[`tools/fvwork/README.md`](../fastverify/tools/fvwork/README.md).

**EXPERIMENTAL incremental machinery.** Reuse of the last build tree (exact, optimistic and interface modes), the
frontier and warm checks inside fvwork, `--build lake` states, `--copy-mode farm` and `--reuse-identical` are kept behind
`--experimental-incremental` (`fvwork serve`, `incr-reverify.sh`). Without the flag `fvwork serve` refuses
`--check frontier`, `--check warm` and a `--build lake` state (exit 2). With it, none of their ACCEPTED or CONDITIONAL
answers counts: they are reported as NO-VERDICT (exit 2) with `"provisional": "ACCEPTED"` or `"CONDITIONAL"` and trust
`none`. The incremental machinery is not claimed sound.

```bash
F=fastverify/tools/fvwork/fvwork.py
python3 -I $F init  --state "$ST" --project PROJECT --challenge CHALLENGE --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
    --packages "$WS" --threads 32 --closure-only
python3 -I $F serve --state "$ST" --jobs 8 [--guard 'wall=1800,procs=4096'] [--pins fastverify/check/sound/pins-437.env] &
python3 -I $F verify --state "$ST" --tree PROJECT          # or --git REPO --rev HEAD, or --files changes.json
    #   [--no-advance] candidate, judged concurrently                    [--merge] enters the base only if ACCEPTED
python3 -I $F watch --state "$ST" --tree PROJECT           # verify on every save
```

- `changes.json` maps paths to new content (`{"Path/File.lean": "..." | null}`).
- Keep the state on a local XFS or btrfs disk, not under `/home` or `/tmp`.
- `verify` exits 0 ACCEPTED, 1 REJECTED, 2 no verdict. A failing build gives `bin/fastverify`'s verdict (REJECTED after
  its official confirmation) without per-module diagnostics.
- For conditional verdicts while proving, use `fv verify --modulo-frontier` or `fv check --frontier`
  ([conditional verdicts](#conditional-verdicts-while-proving)); fvwork's `--check frontier` is experimental.
- From an editor (`fv watch` is EXPERIMENTAL in v0.1 and needs `--experimental`): `fv watch --experimental PROJECT --challenge CHALLENGE --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --lsp-out .fastverify.lsp.json --sarif .fastverify.sarif`, or
  copy `fastverify/tools/editor/vscode-tasks.json` to `.vscode/tasks.json`.

**Many agents on one repository.** Send every attempt as a candidate (`--no-advance`, `serve --jobs K`); resend only an
ACCEPTED candidate with `--merge` (it is judged again, so concurrent fills never overwrite each other). Requests longer
than `--slow-lane` (120 s) stop counting against `--jobs`; with `--jobs K` each request gets threads/K. Every request is
a cold run, so budget the memory and threads of one cold verification per concurrent request.

### Warm delta judge (not in v0.1)

Not in v0.1: the warm delta judge. fvwork, fvserve and incr-reverify refuse it; the standalone `check/warm/fvcheckd.py` is research code, is not sound in its current form, and is not used by any entry point. Use `fvwork serve` (cold sound path) for repeated checks.

## Serve proof attempts to provers and RL pipelines

For single attempts against a fixed problem set (attempt, verdict, feedback; best-of-N; RL rewards), run `tools/fvserve`.
It pays the fixed costs once, batches attempts of different theorems into one export and one judge run, and answers
attempts that do not compile as soon as their build ends. Opt-in;
[`tools/fvserve/README.md`](../fastverify/tools/fvserve/README.md).

```bash
fastverify/tools/fvserve/fork/build.sh "$TC" FORKDIR     # optional compile worker; $TC = official toolchain prefix (4.33.1 or 4.37.0-rc1)
python3 -I fastverify/tools/fvserve/fvserve.py serve --state "$ST" --pset math=PSETDIR:"$PIN" --packages "$WS" \
    --toolchain "$TC" --threads 32 --profile shared --fork-server FORKDIR/fvfork --snapshot-header $'import Mathlib\nimport Aesop' &
python3 -I fastverify/tools/fvserve/fvserve.py submit --state "$ST" --pset math --theorem my_thm attempt.lean
python3 -I fastverify/tools/http/fvapi.py --fvserve-state "$ST" --default-pset math --host 127.0.0.1 --port 8080
fastverify/bin/fv attempt attempt.lean --pset math --theorem my_thm --http http://127.0.0.1:8080
```

- `PSETDIR` is a challenge directory that states every problem with `:= sorry`, with its official export (pinned by
  `$PIN`). `fv mint PROJECT --out DIR --for-fvserve` mints sub-challenges that `fvserve` can serve directly.
- `--snapshot-header` must equal the problems' header; otherwise every attempt pays a plain `import Mathlib`.
- `--profile shared` sets per-attempt limits, a 120 s attempt timeout, a slow lane, per-client fairness and queue bounds
  ([limits](#share-one-verifier-limits-and-isolation)). On 8-16 GB machines use `--profile laptop`; use
  `--max-inflight 1` on 8 GB and at most 2-3 on 16 GB. Add `--max-pending-per-client N` for untrusted multi-tenant use.
- `--warm-check` (the warm delta judge) is not in v0.1 and refuses to start; start `fvserve` without it.
- Pass `--toolchain` explicitly (the same official toolchain prefix as the fork build). Lean 4.37.0-rc1 problem sets: a
  4.37 `--toolchain`, a 4.37 `--packages` workspace and
  `--pins fastverify/check/sound/pins-437.env`.
- A running service keeps the code it started with: `fvserve.py stats --state "$ST"` reports `code` and `stale`; restart
  when `stale` is not empty.

**Rewards.** A counted ACCEPTED (trust `sound`, `sound-conditional` or `notary`) = 1, everything else = 0. A model that
renames the problem's theorem is REJECTED. The HTTP API requires an explicit `theorem` per request by default, so an
attempt cannot earn another problem's reward (`--custom-id-is-theorem` for clients whose `custom_id` names the theorem).
The explicit `theorem` field is the supported path. Inferring the theorem from the source
(`--experimental-theorem-inference`) is EXPERIMENTAL in v0.1 and not reward-safe against adversarial multi-theorem
submissions; what it cannot read exactly is NO-VERDICT, and every inferred answer carries
`"theorem_inference": "experimental"`. Sizing: as a starting point, plan about 6-7
CPUs of verification per accelerator serving an 8B prover model; measure with your own model.

### HTTP

`fvapi.py` serves `GET /health`, `GET /metrics` (Prometheus), `POST /v1/verify`, `POST /v1/verify/batch`, and the
Kimina-compatible `POST /verify` and `POST /api/check`. It binds to loopback by default; use `--api-key-file` for a Bearer
token, and keep `--max-concurrent`, `--max-connections`, `--header-timeout` and `--body-timeout` for exposed deployments
([endpoints and limits](reference/cli.md#http-endpoints-fvapipy)).

### MCP

`fastverify/tools/mcp/fastverify-mcp` is an MCP server (JSON-RPC 2.0 over stdio) whose tools verify attempts, batches,
projects and patches, check exports, triage lemmas and audit challenges ([tool list](reference/cli.md#mcp-tools-fastverify-mcp)).
These tools judge proofs; interactive Lean tools (goals, hover, tactics) help write them. Register trusted challenges
with `--challenge ID=DIR[:CHALLENGE_SHA256[:COMPARATOR_SHA256]]` (agents refer to `challenge_id`) and confine paths with
`--allow-root DIR`. Triage and the notary check (`notary: true`) are EXPERIMENTAL and need the server started with
`--experimental` (or `FV_EXPERIMENTAL=1`). Client configuration (replace `<...>`):

```json
{"mcpServers": {"fastverify": {
  "command": "<repo>/fastverify/tools/mcp/fastverify-mcp",
  "args": ["--fvserve-state", "<fvserve state>", "--fvwork-state", "<fvwork state>",
           "--challenge", "main=<challenge dir>:<PIN>:<CFG_PIN>", "--default-pset", "math",
           "--packages", "<workspace>", "--allow-root", "<workspace root>"]}}}
```

For a single attempt file in an editor: `fv watch --experimental attempt.lean --fvserve-state "$ST" --pset math --theorem my_thm`.

## Gate pull requests in CI

```bash
fastverify/bin/fv ci --experimental --project PROJECT --challenge CHALLENGE --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
    --packages "$WS" --cache-dir ci-cache --out-dir ci-out [--frontier] [--closure-only] [--wall 1800]
```

The CI gate (`fv ci`, `tools/ci-action/fv-ci.sh` and the GitHub action) is **EXPERIMENTAL in v0.1**: it runs only with
`--experimental` (action input `experimental: "true"`), and every run is a cold sound run. Its report publication is not
release grade; its known limitations are listed in [limitations](limitations.md#services).

`fv ci` runs `tools/ci-action/fv-ci.sh`, which is also a GitHub composite action
([`tools/ci-action/README.md`](../fastverify/tools/ci-action/README.md)); the default preset is `sound-auto`.

- In v0.1 `fv ci` ignores `--cache-dir` (every run is cold) and `--disk` has no effect.
- The verification commands run under the resource guard when it is available (`--wall`, default 3600 s, `0` disables
  the wrapper; optional `--disk`, `--mem`); a limit hit is NO-VERDICT.
- Outputs: `result.json`, SARIF 2.1.0, and a Markdown summary with statement-drift (`FV002`) and illegal-axiom (`FV003`)
  alerts and, with `--frontier`, the open-lemma ledger.
- A broken module outside the claim closure should not fail the gate, as with the official `lake comparator`: the fast
  builds of `sound-auto` build only the import closure of the solution module (the official build B0, chosen for very
  small projects, builds the configured solution module, `lake build C`). In v0.1 `--closure-only` has no further effect.
  Count no verdict as a failure.
- Do not run untrusted fork pull requests on persistent shared self-hosted runners.

## Sub-challenges for untrusted contributors (EXPERIMENTAL in v0.1)

Mint one pinned sub-challenge per open lemma, triage them, verify each submission against its sub-challenge, merge
verified proofs under a lock, and report progress. Every verdict comes from the judge.

```bash
S=fastverify/tools/subcontract
python3 -I $S/mint.py --experimental BLUEPRINT CHALLENGE OUT --packages "$WS" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
    --threads 16 --jobs 8
python3 -I $S/triage.py OUT/manifest.json --jobs 8
python3 -I $S/subverify.py --experimental OUT/manifest.json LEMMA_NAME submission.lean   # 0 accepted, 1 rejected, 2 no verdict
python3 -I $S/merge.py --experimental OUT/manifest.json OUT/verified_subproofs/*.verified.json   # re-runs the frontier check: 3 or 0
python3 -I $S/report.py OUT --markdown
```

## Advisory helpers

These tools never produce a verdict or change an exit code of a verifying command.

```bash
fastverify/bin/fv diff old.export new.export --targets Main.thm1,Main.thm2 --explain 5 [--json]
fastverify/bin/fv triage --experimental proposed_lemma.lean --snapshot-dir SNAP --repo PROJECT   # EXPERIMENTAL in v0.1
fastverify/bin/fv lookup proposed_lemma.lean --index MATHLIB_IDX --snapshot SNAP [--json]
fastverify/bin/fv audit CHALLENGE --challenge-sha256 "$PIN" --probe --reading-set reading-set.lean   # runs no sound check: no comparator pin
```

- **diff** classifies each target as identical, alpha-equal, proof changed, statement changed, removed or added, which
  tells a goalpost move from a refactoring. Compare exports of the same build configuration.
- **triage** runs static lints (unguarded `Nat` subtraction and division, `False` premises, unused binders, ...) and
  sandboxed probes (strict elaboration with `autoImplicit false`; negation and vacuity probes whose proofs are
  kernel-checked) on a proposed lemma. A header snapshot makes it fast on repeated calls.
- **lookup** answers whether a theorem with exactly this kernel statement already exists (binder names and implicitness
  ignored). Index once per library version (`dupfind.py index NAME EXPORT OUT`); `dupfind.py delta --index IDX
  NEW.export` lists new theorems that restate existing ones; `dupfind.py serve --index IDX --socket PATH` answers in
  milliseconds. Generalizations and instances are not reported.
- **audit** lints kernel terms (custom axioms, `opaque` or sorried definitions in statements, definitions shadowing
  library concepts, contradictory premises, `autoImplicit` typos, unguarded partial operations), runs kernel-certified
  probes, extracts the minimal reading set, and with `--solution-mode` flags targets proved without any project lemma.
  Its accuracy is measured only on a small held-out set (experimental).

## Share one verifier: limits and isolation

The sandbox (bubblewrap: no network, read-only `/`, home hidden) keeps an attempt from escaping; the guard
(`tools/guard/fvguard.py`) keeps it from consuming the machine: memory
including sandbox-private tmpfs, processes, threads, output, disk, wall and CPU time.

| situation | command |
|---|---|
| shared attempt service | `fvserve.py serve ... --profile shared` = `--svc-check --limits 'mem=2G,nproc=512,procs=64,threads=256,out=16M,disk=64M,fsize=64M,cpu=120' --attempt-timeout 120 --slow-after 10 --max-slow 8 --fair --max-pending 512 --request-timeout 10` (later flags override) |
| one run you did not write | `python3 -I fastverify/tools/guard/fvguard.py --mem 64G --wall 7200 --disk OUT:200G --json guard.json -- fastverify/bin/fastverify PROJECT CHALLENGE OUT --preset sound-auto ...` (exit 125 = a limit ended the run: no verdict) |
| daemon or CLI | `fvwork.py serve --guard SPEC` (default `wall=3600`); `fv verify --guard mem=16G,wall=600` |
| hard aggregate cap | a cgroup scope (`MemoryMax`, `TasksMax`) or `fvguard.py --cgroup systemd-user`; keep `--limits` for per-attempt caps |

- A limit hit is always NO-VERDICT, never REJECTED or ACCEPTED.
- Keep `--attempt-timeout` at 120 s or more for model output. The shared-profile limits were calibrated on real prover
  attempts.
- Memory is polled every 0.1-0.25 s, so an attempt can overshoot by what it allocates in between. Only a cgroup charges
  tmpfs and copy-on-write pages exactly; only the guard sees output volume, disk, wall time and one runaway child among
  many. Use both.
- Do not put a tree-wide `--mem` around a zygote build (each forked child shows the shared Mathlib pages in its RSS); use
  a cgroup there.
- Fork-server children may write only to their own output directory ([limitations](limitations.md#services)).

## Choose a preset and judge for your hardware

| machine class | recommended |
|---|---|
| laptop: 4-8 cores, 16 GB | `sound-auto`; `fvwork`; `fvserve --profile laptop` |
| CI runner: 4-16 cores, 16-32 GB | `sound-auto` (`fv ci --experimental` for the experimental CI gate) |
| workstation or shared node: 32-64 cores, 64-256 GB | `sound-auto`; `fvserve --profile shared`; the low-memory judges for exports of the size of the Riemann Hypothesis proof |
| big node: 256 GB or more, 128-384 threads | `--preset sound` for very large projects; export-in checks; the notary judge |

`sound-auto` already picks the low-memory judge when the default judge's estimated peak exceeds the memory budget
(cgroup `memory.max`, or MemAvailable), provided a compatible low-memory judge is installed, the check is the ordinary
sound check (no frontier) and no extra kernel is required. The ultra-low-memory judge is never chosen automatically; run
`fastverify/check/lowmem/check-sound-ultralowmem.sh` directly.

**Which judge fits** (the smallest cgroup memory limit, swap off, under which each judge accepted in one run; the limits
are binary, GiB; thread counts and times per cell are in [benchmarks](benchmarks.md#judging-an-export-by-machine-budget)):

| export | sound judge | low-memory judge | ultra-low-memory judge |
|---|---|---|---|
| 1.1 GB (an 11k-module project) | 6 GB | 3 GB | 1 GB |
| 6.07 GB (all of Mathlib) | 24 GB | 12 GB | 8 GB |
| 61.6 GB (the Riemann Hypothesis proof) | 256 GB | 128 GB | 64 GB |

The table is for the default (two-kernel) judge. An enabled `con-leche` needs about 0.8 x the export size + 1-2 GB more
(45.1 GiB on the 61.6 GB export), `nanoda` more (70.4 GiB there).

Rules of thumb for the default judge: about 3.5 GB plus 0.15 GB per thread for a project-size export (up to about 1 GB);
16-32 threads gave the shortest wall time for such exports; more threads were slower. The three legs run concurrently, so the peak is
their sum. From sources, `--preset sound` on a Mathlib-importing project needs 60-75 GB at any thread count because of
the zygote; below a 96 GB budget the zygote items are dropped.

**When a limit is hit**, a memory kill never becomes a verdict: the judge answers DECLINED; retry with fewer threads or a
low-memory judge. A killed `lean` makes the fast build decline to a slower build (B3, then B1, then B0); in the official
build it is reported as ERROR.

**Many checks on one node** cost about N times the single peak. Two-fold CPU oversubscription is efficient; at four-fold
the gain shrinks. Keep N x threads at or below 2 x cores. In one shared memory budget, the low-memory judge completes
where several concurrent default judges are OOM-killed.

## Lean versions

- The release admission gate `check/xversion` admits **45 official releases, v4.26.0-rc1 to v4.37.0-rc1**. `tools/configure.py` registers
  4.33.1 and 4.36.0; register any other installed release, including 4.37.0-rc1, with `python3 -I fastverify/tools/addrelease.py --elan-home ~/.elan <release>`; it verifies the tree
  against a shipped whole-tree manifest (`fastverify/toolchains/`, 14 releases) and refuses a release without one unless
  you deliberately pin a trusted installation with `--pin-new`. Releases up to v4.25 are refused. The gate can only veto.
- **4.33.1**: the full fast path (fast build, native exporter, zygote and PGO toolchains).
- **4.36.0 and 4.37.0-rc1**: the transformed fast build B3 of `--preset sound` / `sound-auto` only (through a port of the
  Lake 4.35+ planner; the exact fast build B1 declines, so a confirmation uses the official build) and native exporter (for 4.37,
  byte-identical to the bundled `leanexport` or it declines); a pinned PGO toolchain for 4.37.0-rc1.
- **Other admitted releases**: the official `lake build`, the release's official exporter, and the judge.
- **The 4.37.0-rc1 judge** (`check/sound/pins-437.env`) is built from the official 4.37.0-rc1 comparator judge code and
  kernel, plus `gruszka`. `--preset sound` and `sound-auto` select it for 4.37.0-rc1 challenges (from the challenge's
  `lean-toolchain`, or the challenge export's meta line in export-only runs); with explicit checks pass
  `--pins check/sound/pins-437.env`, or `--pins 437` in `fv`. Its encapsulated replay uses an untrusted hide list
  (`--hide check/sound/hide/lean-4.37.0-rc1-no-expose.txt`), so a wrong list costs only time
  ([architecture](concepts/architecture.md#the-judge-and-its-variants)); its basis and known false rejects:
  [limitations](limitations.md#assurance). A host without the 4.37 binaries answers no verdict; there is no fallback
  to the 4.36 judge.
- On 4.37 module-system repositories, keep base and pull-request builds on one configuration: mixed build flags defeat
  the interface cutoff and renumber auxiliary lemmas in diffs.
- Lake 4.37 writes a large setup record per module: the official build of a very large 4.37 project can need several
  hundred GB of disk.

## Very large runs

For projects of the size of the Riemann Hypothesis proof (deployment to a large host, preflight, what to watch in
`result.json`, recovery), follow [large runs](large-runs.md). The reproduction commands of the
published runs are in [benchmarks.md](benchmarks.md#reproducing-the-riemann-hypothesis-runs).
