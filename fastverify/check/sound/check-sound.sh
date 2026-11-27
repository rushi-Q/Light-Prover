#!/bin/bash -p
# fastverify SOUND CHECK (option CS, preset `sound`): the trusted check of soundness conditions (2)-(4) of docs/concepts/soundness.md.
#
#   check-sound.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--log FILE] [--timeout S]
#                  [--workdir DIR] [--keep-config-kernels] [--hints FILE|none] [--incr-dir DIR] [--private-inputs]
#                  [--pins FILE] [--hide FILE]
#   check-sound.sh --preflight [--pins FILE]
#
# v2.2 (decision logic UNCHANGED): `--hide FILE` hands the Lean-kernel leg a list of definitions (one name
#   per line, <= 16 MiB) for the ENCAPSULATED REPLAY of pleanchecker >= D23-E (PCHK_HIDE_FILE): those definitions and every
#   earlier theorem are visible to later kernel checks by their types only - the 4.37 module system's own view - and a kernel
#   error in that environment is re-checked in the full one, which decides. The list is an availability-only input (a wrong
#   list costs time, never a verdict; argument in check/sound/src-437/PChk/Par.lean, D23-E); it is copied into the private
#   work dir and recorded (path + sha256) in the JSON result as `hide`, `hide_sha256`. Without --hide: the plain replay.
#
# v3 (decision logic UNCHANGED): `--pins FILE` selects another pins file of the same format, so the
#   same wiring can run the trusted check built from ANOTHER official Lean release (check/sound/pins-437.env: the official
#   v4.37.0-rc1 comparator judge code + kernel, for projects on 4.37.0-rc1). A pins file may set TC_VERSION (the elan name of
#   the official toolchain its judge binaries were built from; verified against fastverify/toolchains on every run; default
#   leanprover/lean4:v4.36.0) and TC_LABEL (text of the verdict basis; default 4.36). The pins file's path and sha256 go into
#   the JSON result (`pins`, `pins_sha256`, `toolchain`). Without --pins nothing changes.
# v2.3-H (the two-kernel decision logic UNCHANGED): EXTRA VETO-ONLY KERNELS. `con-leche
#   --verified` and `nanoda_bin` 0.4.31, both bundled with the official Lean v4.37.0-rc1 release and pinned by sha256
#   (PIN con_leche / PIN nanoda; their self-test export PIN selftest_kbad), run OUTSIDE ccmp: started by this script next
#   to ccmp, each in its own bwrap sandbox (read-only /, no network, tmpfs home/tmp, own session), with its own log and exit
#   status written by the trusted wrapper into $W/xko (no sandbox can write there: ccmp's binds only $W/tmp and $W/home
#   writable) - nothing an extra kernel does can stop or change the two-kernel judge. RULE: the two-kernel verdict is computed exactly as before. Only if it is ACCEPTED are the enabled
#   extra kernels consulted (classification table: xk_classify below): a kernel's OWN rejection of a declaration turns the
#   verdict into REJECTED; an acceptance is recorded; anything else (declined/unsupported construct, malformed input or
#   format/version mismatch, Nat-size limit, OOM, stack overflow, signal, panic outside the type checker, timeout, missing
#   binary, failed self-test) is 'not decided (<reason>)': the verdict stays ACCEPTED - unless that kernel was made
#   mandatory with --require-kernel NAME, then 'not decided' = DECLINED (no verdict). A two-kernel REJECTED / DECLINED
#   stands as it is (the extra kernels are stopped). ACCEPTED therefore still requires the official kernel AND gruszka;
#   an extra kernel can only remove accepts. Defaults: BOTH OFF (opt-in). con-leche's default is the one-line switch
#   XK_CONLECHE_DEFAULT below (off; 'auto' = on by default, skipped and recorded 'skipped (memory)' when the memory
#   estimate of the judge + con-leche exceeds this run's budget): it rejects some valid proofs that unfold a theorem body
#   (theorem bodies are opaque to it), so turning it on by default changes existing verdicts. nanoda is opt-in for its
#   cost. Options: --kernel NAME (enable, veto only), --require-kernel NAME (mandatory), --skip-kernel NAME (one name per
#   option), --kernel-jobs N (threads of each extra kernel; default min(threads, 64)), --kernel-grace S (bounds every
#   OPTIONAL kernel to S s after the two-kernel ACCEPT; without it a default-on kernel gets max(600 s, the judge's wall) and
#   a --kernel kernel is waited for; a --require-kernel kernel is always waited for; only --timeout bounds those). nanoda's config is written here: stack_size_bytes = 1 GiB per worker (its
#   32 MiB default false-rejects valid deep proofs; RUST_MIN_STACK has no effect), Nat/String extensions on, all axioms
#   admitted (nanoda is a typing veto; the axiom policy stays ccmp's official closure check). JSON: `extra_kernels` (per
#   kernel: mode, status, reason, rc, wall_s, max_rss_kb, message, sha256), `extra_kernels_summary`, `kernel_grace_s`,
#   `two_kernel_wall_s`. `--xk-classify NAME LOG RC` prints the classification of a recorded run (test interface; never a
#   verdict, exit 2). Argument: check/sound/README.md. Without the pins lines the run is the v2.2 judge.
# exit 0 = ACCEPTED, 1 = REJECTED, 2 = no verdict (DECLINED / could not run). Last stdout line = one JSON object.
#
# v2 (pinned binaries UNCHANGED, wiring only):
#   * LEG-SCOPED VERDICT, NO SHARED LOG. Every kernel leg runs through a wrapper written by this script that sends the
#     leg's own stdout/stderr to a private file ($W/tmp/leg-<leg>.log) and records the leg's exit status in
#     $W/tmp/leg-<leg>.rc. ccmp's log therefore holds ccmp's OWN lines only (plus bwrap's), so the decision below reads
#     (1) ccmp's exit code, (2) ccmp's own first `error:` line, (3) each leg's recorded exit status and, for the Lean leg,
#     one anchored message in that leg's own log. A declaration name or any other export content can no longer put a
#     fake `error:` / `... accepts the solution` / resource line in front of the judge's own lines (these
#     classes are availability only - no text line was ever sufficient for an ACCEPT, which always needed rc=0).
#     ACCEPTED additionally requires every leg's recorded exit status to be 0 (defense in depth; it can only remove accepts).
#   * PRIVATE INPUTS BY DEFAULT. Every input gets a COPY of its own whatever its size (new inode: nothing the caller
#     still holds - a writable mapping, a later write(2) - can reach what the legs read). `--private-inputs` = the
#     CALLER asserts that nothing else can write the export during the check (the package's orchestrator: it wrote the
#     export itself, and in export-in mode it copied the given file first); then inputs > 4 GiB are hard-linked instead of
#     copied (no second copy of a 61.6 GB export). The ctime stamp is now defense in depth in EVERY mode.
#   * STRUCTURED STATUS in the JSON result: `legs` (per leg: recorded exit status, wall ms from ccmp, first message),
#     `compare_ms`, `inputs` (size and copy/link of each input). No field was removed. Argument: check/sound/README.md.
#
# What decides (all of it is code that already existed and was reviewed; this script only wires it):
#   * ccmp (pchk d876802) = the official Lean 4.36 `lake comparator` judge code: compareAt (statements of every target
#     theorem and every definition they mention, incl. the kernel primitives the comparator checks) + checkAxioms
#     (only the permitted axioms in the closure), and the kernels, all concurrently; verdict = conjunction.
#   * Lean kernel = pleanchecker (Lean.Replay's walk, every addDeclCore on a worker thread, LINKED AGAINST THE OFFICIAL
#     4.36 KERNEL LIBRARIES), plugged in through ccmp's CCMP_LEANCHECKER (in place of `leanchecker --from-export`).
#   * second, independent kernel = gruszka, attached through the OFFICIAL comparator mechanism `external_kernels`
#     (Lake's runExternalKernel: sandboxed, the export path appended, nonzero exit = failure). The challenge's own
#     external kernels / enable_nanoda are REPLACED by gruszka (S1(4): any second kernel; its bugs can only cause false
#     rejects because the official kernel must accept too). --keep-config-kernels keeps them as extra legs (veto only).
#   * --incr-dir DIR (S08, overlap of the Lean-kernel leg with the build): the Lean kernel leg is
#     `pleanchecker --attach=DIR`: it asks the `pleanchecker --incremental=DIR` process started at the beginning of the
#     build (which has kernel-checked snapshot exports of already-built modules into ONE environment, PChk/Incr.lean)
#     to judge exactly ccmp's export path (request with a fresh random nonce, answer in DIR/res-NONCE); if no such
#     process answers, the same binary runs the unchanged non-incremental replay. Either way the leg's exit code is a
#     verdict of the official-kernel replay code on this export (Incr.lean: incremental ACCEPT only when every
#     constant of the export is identical to a kernel-checked one or is checked now; anything else -> the unchanged
#     replay of the whole export decides).
# Differences to check A (C1), all on the "no verdict / reject" side: no prechk gate (it only imitated official-tool
# failure modes), no nanoda (replaced by gruszka). Nothing verdict-relevant is read from the environment (env -i).
# The whole script is one function, parsed before it runs: replacing the file during a run cannot change that run.
main() {
# nothing verdict-relevant from the caller's environment (finding 016): re-exec under env -i with a fixed PATH
q01_env_clean() {  # exactly the clean environment (no caller-settable marker)
  local v
  for v in $(compgen -e); do case "$v" in PATH|LANG|PWD|OLDPWD|SHLVL|_) ;; *) return 1;; esac; done
  [ "$PATH" = /usr/bin:/bin ] && [ "${LANG:-}" = C.UTF-8 ]
}
if ! q01_env_clean; then
  if [ "${1:-}" = --clean-env-reexec ]; then
    printf '{"checker":"%s","verdict":"DECLINED","exit":2,"reason":"environment not clean after the env -i re-exec"}\n' "$(/usr/bin/basename "$0")"
    exit 2
  fi
  exec /usr/bin/env -i PATH=/usr/bin:/bin LANG=C.UTF-8 /bin/bash -p "$(/usr/bin/readlink -f "$0")" --clean-env-reexec "$@"
fi
if [ "${1:-}" = --clean-env-reexec ]; then shift; fi
# macOS: this judge runs three programs at once and needs ccmp, which has no macOS build in this version. The two
# low-memory judges run there natively (check/sound/macos/README.md).
if [ "$(/usr/bin/uname -s 2>/dev/null)" = Darwin ]; then
  printf '%s\n' '{"checker":"checkSound","verdict":"DECLINED","exit":2,"reason":"not available on macOS: use check/lowmem/check-sound-lowmem.sh or check/lowmem/check-sound-ultralowmem.sh"}'
  exit 2
fi
set -u
umask 077
T_START=$(date +%s.%N)
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PKGROOT=$(cd "$HERE/../.." && pwd)
SELF=checkSound
WIRING=check-sound-v2.3-H   # the wiring version of this script (the pins' SOUND_VERSION describes the binaries)
FINISHED=0; W=
on_exit() {
  local rc=$?
  [ -n "${ST_PID:-}" ] && kill "$ST_PID" 2>/dev/null && wait "$ST_PID" 2>/dev/null
  [ -n "${XK_ON:-}" ] && [ "${XK_REAPED:-0}" != 1 ] && xk_killall
  [ -n "$W" ] && rm -rf "$W"
  [ -n "${PINS_PRIV:-}" ] && rm -f "$PINS_PRIV"
  if [ "$FINISHED" != 1 ]; then
    printf '{"checker":"%s","verdict":"DECLINED","exit":2,"reason":"internal error (exit %s)"}\n' "$SELF" "$rc"
    [ -n "${JSONF:-}" ] && printf '{"checker":"%s","verdict":"DECLINED","exit":2,"reason":"internal error (exit %s)"}\n' "$SELF" "$rc" > "$JSONF" 2>/dev/null
    exit 2
  fi
}
trap on_exit EXIT
trap 'exit 2' INT TERM HUP
json_str() { /usr/bin/python3 -I -c 'import json,sys; print(json.dumps(sys.argv[1]))' "$1"; }
LOGF=
log() { if [ -n "$LOGF" ]; then printf '%s\n' "$*" >> "$LOGF"; else printf '%s\n' "$*" >&2; fi; }
finish() {  # finish EXIT VERDICT REASON
  local ex=$1 v=$2 why=$3 now wall tj=null; now=$(date +%s.%N)
  # v2.3-H: the extra veto kernels are consulted exactly once, here, after the two-kernel decision. xk_settle may turn an
  # ACCEPTED into REJECTED (a genuine rejection) or DECLINED (a required kernel did not decide / integrity); it never
  # changes a REJECTED or DECLINED and never produces an ACCEPTED.
  if [ "${XK_DONE:-0}" != 1 ]; then
    XK_DONE=1; TWO_WALL=$(echo "$now - $T_START" | bc | sed 's/^\./0./')
    xk_settle "$ex" "$v" "$why"; ex=$XK_EX; v=$XK_V; why=$XK_WHY; now=$(date +%s.%N)
  fi
  wall=$(echo "$now - $T_START" | bc | sed 's/^\./0./')
  case "${T:-}" in ''|*[!0-9]*|0?*) ;; *) tj=$T;; esac   # a canonical decimal only (else null)
  log "[$SELF] verdict $v (exit $ex): $why"
  local js; js=$(printf '{"checker":"%s","verdict":"%s","exit":%s,"wall_s":%s,"reason":%s,"ccmp_rc":%s,"threads":%s,"version":%s,"wiring":"%s","basis":%s,"binaries_sha256":%s,"leg_ms":%s,"legs":%s,"compare_ms":%s,"inputs":%s,"private_inputs_asserted":%s,"pins":%s,"pins_sha256":%s,"toolchain":%s,"hide":%s,"hide_sha256":%s,"extra_permitted_axioms":%s,"challenge_sha256":%s,"comparator_sha256":%s}\n' \
    "$SELF" "$v" "$ex" "$wall" "$(json_str "$why")" "${CCMP_RC:-null}" "$tj" "$(json_str "${SOUND_VERSION:-unknown}")" "$WIRING" \
    "$(json_str "${BASIS:-}")" "${BIN_JSON:-null}" "${LEG_JSON:-null}" "${LEGS_JSON:-null}" "${COMPARE_MS:-null}" "${INPUTS_JSON:-null}" "${PRIVIN:-0}" \
    "$(json_str "${PINS:-}")" "$(json_str "${PINS_SHA:-}")" "$(json_str "${TC_VERSION:-}")" "$(json_str "${HIDE:-}")" "$(json_str "${HIDE_SHA:-}")" "${XAXJ:-null}" "$(json_str "${CSHA_GOT:-}")" "$(json_str "${CFGSHA_GOT:-}")")
  js="${js%\}},\"extra_kernels\":${XK_JSON:-null},\"extra_kernels_summary\":$(json_str "${XK_SUM:-}"),\"kernel_grace_s\":${XK_GRACE_USED:-null},\"two_kernel_wall_s\":${TWO_WALL:-null}}"   # v2.3-H
  printf '%s\n' "$js"
  if [ -n "${JSONF:-}" ]; then printf '%s\n' "$js" > "$JSONF" || true; fi
  FINISHED=1
  exit "$ex"
}
decline() { finish 2 DECLINED "$1"; }
# ---------- v2.3-H: classification of an extra kernel's recorded run -> accepted | rejected | not decided ----------
# xk_classify NAME LOGFILE RC prints three lines: status, reason (for 'not decided'), message (the deciding line). Inputs are
# the kernel's own log (written by the trusted wrapper, never shared with another leg) and the exit status the wrapper
# recorded. Only 'rejected' can change a verdict (ACCEPTED -> REJECTED); 'accepted' / 'not decided' leave the two-kernel
# verdict as it is (a REQUIRED kernel must be 'accepted'). TABLE:
#  con-leche (exit status documented by `con-leche --help`: 0 accepted, 1 rejected, 2 declined, 3 error):
#   rc 0 + the line 'con-leche: accepted N declarations (--verified)'                     -> accepted
#   rc 0 without that line                                                                 -> not decided
#   rc 1 + a runtime/resource line not written by con-leche itself (Lean runtime: 'INTERNAL PANIC: out of memory' etc.)
#                                                                                          -> not decided (resource)
#   rc 1 + first 'con-leche: invalid: ' line = one of con-leche's limits ('the kernel refused ...' [Nat size, Nat.pow result
#          size, 32-bit operand], 'resource limit: fuel exhausted: ...')                 -> not decided (resource limit)
#   rc 1 + a 'con-leche: invalid: <reason> [at <declaration> ...]' line                    -> REJECTED
#   rc 1 without such a line                                                               -> not decided
#   rc 2 'not implemented yet' / 'declined' (e.g. non-standard axioms, sorryAx use)        -> not decided (declined)
#   rc 3 bad usage, malformed input, internal failure (format / version mismatch)          -> not decided (error)
#  nanoda_bin 0.4.31 (src/main.rs: a configuration / input error returns Err -> exit 1; every type-checking failure is a
#  Rust panic -> exit 101; a stack overflow or failed allocation aborts -> SIGABRT, exit 134):
#   rc 0 + 'Checked N declarations with no errors' / '... with no typechecker errors'      -> accepted
#   rc 101 + FIRST panic location in nanoda's checker (src/tc.rs, inductive.rs, quot.rs, expr.rs, level.rs), except the
#          two non-judgement panics there ('failed to spawn checking thread', 'stack_size_bytes must be ...')
#                                                                                          -> REJECTED
#   rc 101 + first panic elsewhere (parser.rs = format, util.rs = limits/config, std library, printers)
#                                                                                          -> not decided
#   rc 1 'Error: ...' (configuration, I/O, parse, malformed inductive block)                -> not decided (error)
#   rc 2 'Declined: ...' (export format outside what nanoda reads, e.g. non-continuous back-references)
#                                                                                          -> not decided (declined)
#  any kernel: rc 124 timeout, 137 SIGKILL (OOM killer / time limit), 134 abort (stack overflow, OOM), 139 SIGSEGV, any
#  other status, no recorded status (stopped / never finished)                             -> not decided
# Forgery: export content reaches these logs only inside a kernel's own message lines (declaration names). A name with an
# embedded newline could forge a line of its own; the only effects are a lost veto ('not decided' = today's two-kernel
# verdict) or a false REJECTED - never an ACCEPTED, which always needs the two-kernel ACCEPT.
xk_classify() {
  /usr/bin/python3 -I - "$1" "$2" "$3" <<'PY'
import re, sys
name, logf, rc = sys.argv[1], sys.argv[2], sys.argv[3].strip()
try:
    with open(logf, "rb") as f:
        text = f.read(64 << 20).decode("utf-8", "replace")
except OSError:
    text = ""
lines = [ln.rstrip("\r") for ln in text.split("\n")]
rc = int(rc) if rc.isdigit() else None
def out(st, why="", msg=""):
    c = lambda x: " ".join(x.split())[:400]
    print(st); print(c(why)); print(c(msg)); sys.exit(0)
def first(pat, src=None):
    for ln in (lines if src is None else src):
        if re.search(pat, ln):
            return ln
    return ""
SIG = {124: "timeout", 137: "killed by SIGKILL (OOM killer or time limit)", 134: "aborted (SIGABRT: stack overflow, failed allocation or runtime abort)",
       139: "segmentation fault (SIGSEGV)", 135: "bus error (SIGBUS)", 136: "SIGFPE", 132: "SIGILL", 133: "SIGTRAP", 143: "terminated (SIGTERM)"}
RES = r"(?i)(memory allocation of \d+ bytes failed|out of memory|bad_alloc|cannot allocate memory|failed to create thread|failed to spawn|overflowed its stack|stack overflow|deep recursion|INTERNAL PANIC|PANIC at|Resource temporarily unavailable|fatal runtime error|Segmentation fault|Killed)"
if rc is None:
    out("not decided", "no exit status recorded (stopped or never finished)")
if name == "con-leche":
    nonstats = [ln for ln in lines if ln.strip() and not ln.startswith("con-leche: stats:")]
    if rc == 0:
        acc = first(r"^con-leche: accepted \d+ declarations \(--verified\)$")
        if acc:
            out("accepted", "", acc)
        out("not decided", "exit 0 without con-leche's acceptance line")
    if rc == 1:
        rt = first(RES, [ln for ln in lines if not ln.startswith("con-leche: ")])
        if rt:
            out("not decided", "resource failure or runtime panic (exit 1): " + rt)
        inv = first(r"^con-leche: invalid: ")
        if not inv:
            out("not decided", "exit 1 without con-leche's rejection line: " + (nonstats[0] if nonstats else "(empty log)"))
        reason = inv[len("con-leche: invalid: "):].split(" [at ", 1)[0]
        # con-leche's own resource / implementation limits, reported with exit 1 (strings of the pinned binary 8fff3f05):
        # 'the kernel refused a `Nat` numeral because its size exceeds the maximum ...', 'the kernel refused to evaluate
        # `Nat.pow` because the result would exceed the maximum numeral size ...', 'the kernel refused to evaluate `<op>`
        # because its second argument does not fit in a 32-bit unsigned integer', 'resource limit: fuel exhausted: <loop>'
        if reason.startswith("the kernel refused ") or re.match(r"(resource limit:|fuel exhausted:)", reason):   # fixed text
            out("not decided", "resource limit of con-leche: " + inv)
        if re.match(r"(?i)(deep recursion|stack overflow|out of memory|memory allocation)", reason):   # fixed text only (names follow it)
            out("not decided", "resource failure reported as a declaration error: " + inv)
        out("rejected", "", inv)
    if rc == 2:
        out("not decided", "declined (unsupported feature): " + (first(r"^con-leche: (not implemented yet|declined)") or (nonstats[0] if nonstats else "")))
    if rc == 3:
        out("not decided", "error (bad usage, malformed input or internal failure): " + (nonstats[0] if nonstats else "(empty log)"))
elif name == "nanoda":
    if rc == 0:
        acc = first(r"^Checked \d+ declarations with no (typechecker )?errors")
        if acc:
            out("accepted", "", acc)
        out("not decided", "exit 0 without nanoda's success line")
    if rc == 101:
        P = re.compile(r"^thread '[^']*'(?: \(\d+\))? panicked at (.+):(\d+):(\d+):$")
        for i, ln in enumerate(lines):
            m = P.match(ln)
            if m:
                loc, msg = m.group(1), (lines[i + 1] if i + 1 < len(lines) else "")
                if loc in ("src/tc.rs", "src/inductive.rs", "src/quot.rs", "src/expr.rs", "src/level.rs") and \
                        not re.match(r"(failed to spawn checking thread|stack_size_bytes must be greater than zero)", msg):
                    out("rejected", "", "nanoda type checker (%s:%s): %s" % (loc, m.group(2), msg))
                out("not decided", "panic outside nanoda's type checker (%s:%s): %s" % (loc, m.group(2), msg))
        out("not decided", "exit 101 without a panic location line")
    if rc == 1:
        out("not decided", "error (configuration, input or format): " + (first(r"^Error") or first(r"\S")))
    if rc == 2:
        out("not decided", "declined (format limit): " + (first(r"^Declined") or first(r"\S")))
else:
    out("not decided", "unknown extra kernel " + name)
why = SIG.get(rc, "exit %d" % rc)
r = first(RES)
out("not decided", why + (": " + r if r else ""))
PY
}
# the extra kernels' helpers (defined before anything can call finish -> xk_settle; they read $W etc. at call time)
xk_sandbox() {  # xk_sandbox BINDIR TAG -> the bwrap prefix (one line, embedded in the generated wrapper)
  printf '%senv -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dev /dev --proc /proc --ro-bind "%s" "%s" --ro-bind "%s" "%s" --bind "%s/xk-%s" "%s/xk-%s" --chdir "%s/xk-%s" --setenv HOME "%s/xk-%s" --setenv TMPDIR "%s/xk-%s" --setenv LANG C.UTF-8 --setenv LEAN_ABORT_ON_PANIC 1 --setenv PATH /usr/bin:/bin --' \
    "$XK_TMO" "$1" "$1" "$W" "$W" "$W" "$2" "$W" "$2" "$W" "$2" "$W" "$2" "$W" "$2"
}
mkxk() {  # mkxk NAME: writes $W/bin/xk-NAME (usage: xk-NAME EXPORT TAG; TAG is one of a fixed set chosen by this script)
  local n=$1 b=${XK_BIN[$1]} bd; bd=$(dirname "${XK_BIN[$1]}")
  { printf '#!/bin/sh\nset -C\nE=$1; TAG=$2\ncase "$TAG" in %s|selftest-%s-good|selftest-%s-bad) ;; *) exit 2;; esac\nmkdir "%s/xk-$TAG" || exit 2\n' "$n" "$n" "$n" "$W"
    case "$n" in
      con-leche)   # --verified = the mode con-leche's soundness theorem covers; the export is its single positional argument
        printf '%s /usr/bin/time -f "%%e %%M" -o "%s/xk-$TAG/time" "%s" --verified --jobs=%s -- "$E" > "%s/xko/leg-$TAG.log" 2>&1\n' \
          "$(xk_sandbox "$bd" '$TAG')" "$W" "$b" "$KJOBS" "$W";;
      nanoda)   # config written here (trusted): 1 GiB worker stacks, Nat/String extensions as Lake's comparator sets them,
                # ALL axioms admitted (typing veto only: the axiom policy is ccmp's official closure check)
        printf 'printf %s "$E" > "%s/xk-$TAG/nanoda.json" || exit 2\n' \
          "'{\"export_file_path\":\"%s\",\"use_stdin\":false,\"num_threads\":$KJOBS,\"stack_size_bytes\":1073741824,\"nat_extension\":true,\"string_extension\":true,\"unpermitted_axiom_hard_error\":false,\"unsafe_permit_all_axioms\":true,\"print_success_message\":true,\"pp_declars\":[]}'" "$W"
        printf '%s /usr/bin/time -f "%%e %%M" -o "%s/xk-$TAG/time" "%s" "%s/xk-$TAG/nanoda.json" > "%s/xko/leg-$TAG.log" 2>&1\n' \
          "$(xk_sandbox "$bd" '$TAG')" "$W" "$b" "$W" "$W";;
    esac
    printf 'rc=$?; echo "$rc" > "%s/xko/leg-$TAG.rc"; exit $rc\n' "$W"
  } > "$W/bin/xk-$n"
  chmod 755 "$W/bin/xk-$n"
}
xk_rc() { [ -n "$W" ] || return 0; local f=$W/xko/leg-$1.rc; [ -f "$f" ] && [ ! -L "$f" ] && head -c 16 -- "$f" | tr -cd '0-9' | cut -c1-5; }
xk_timefile() {  # xk_timefile TAG -> "wall maxrss_kb" from the last line of /usr/bin/time's output (empty if none)
  local f=$W/xk-$1/time l; [ -f "$f" ] || return 0
  l=$(tail -n 1 -- "$f" | tr -cd '0-9. '); case "$l" in *[0-9]*' '*[0-9]*) printf '%s' "$l";; esac
}
xk_verdict() {  # xk_verdict NAME TAG -> sets XV_ST XV_WHY XV_MSG (xk_classify on the recorded run)
  { read -r XV_ST; read -r XV_WHY; read -r XV_MSG; } < <(xk_classify "$1" "${W:-/nonexistent}/xko/leg-$2.log" "$(xk_rc "$2")")
  [ -n "$XV_ST" ] || { XV_ST="not decided"; XV_WHY="classification failed"; }
}
xk_selftest_ok() {  # every enabled extra kernel must accept selftest_good and reject selftest_kbad here
  local g gw b bw
  xk_verdict "$1" "selftest-$1-good"; g=$XV_ST; gw=$XV_WHY; xk_verdict "$1" "selftest-$1-bad"; b=$XV_ST; bw=$XV_WHY
  XK_ST_WHY="good: $g${gw:+ ($gw)}, kbad: $b${bw:+ ($bw)}"
  [ "$g" = accepted ] && [ "$b" = rejected ]
}
xk_killall() {  # stop every extra kernel still running: each wrapper runs in a session of its own (setsid) and its
                # timeout (--foreground) stays in that process group; bwrap --die-with-parent takes the sandboxed kernel
                # along. SIGTERM, up to 2 s for the groups to exit, SIGKILL for survivors, reap. No sleep if none ran.
  local n p alive i
  alive=; for n in $XK_ON; do for p in ${XK_PID[$n]:-} ${XK_STPID[$n]:-}; do kill -0 "$p" 2>/dev/null && { kill -TERM -- "-$p" 2>/dev/null; alive="$alive $p"; }; done; done
  for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do
    [ -n "$alive" ] || break
    p=; for n in $alive; do kill -0 -- "-$n" 2>/dev/null && p="$p $n"; done; alive=$p
    [ -n "$alive" ] && sleep 0.1
  done
  for p in $alive; do kill -KILL -- "-$p" 2>/dev/null; done
  for n in $XK_ON; do for p in ${XK_PID[$n]:-} ${XK_STPID[$n]:-}; do wait "$p" 2>/dev/null; done; done
  XK_REAPED=1
}
xk_wait() {  # after a two-kernel ACCEPT: required kernels and kernels named by --kernel are waited for (bounded only by
             # --timeout, unless --kernel-grace is given); default-on ('auto') kernels up to the grace max(600 s, judge wall)
  local n p grace deadline busy
  if [ -n "$KGRACE" ]; then grace=$KGRACE
  else grace=$(printf '%.0f' "$CCMP_WALL" 2>/dev/null || echo 600); [ "$grace" -ge 600 ] 2>/dev/null || grace=600; fi
  XK_GRACE_USED=$grace
  for n in $XK_ON; do
    case "${XK_MODE[$n]}" in required) [ -n "${XK_PID[$n]:-}" ] && wait "${XK_PID[$n]}" 2>/dev/null;;
      optional) [ -z "$KGRACE" ] && [ -n "${XK_PID[$n]:-}" ] && wait "${XK_PID[$n]}" 2>/dev/null;; esac
  done
  deadline=$(( $(date +%s) + grace ))
  while :; do
    busy=0; for n in $XK_ON; do [ -n "${XK_PID[$n]:-}" ] && kill -0 "${XK_PID[$n]}" 2>/dev/null && busy=1; done
    [ "$busy" = 1 ] || break
    if [ "$(date +%s)" -ge "$deadline" ]; then
      for n in $XK_ON; do [ -n "${XK_PID[$n]:-}" ] && kill -0 "${XK_PID[$n]}" 2>/dev/null && XK_TIMEDOUT[$n]=1; done
      break
    fi
    sleep 0.5
  done
  deadline=$(( $(date +%s) + 300 ))   # the self-tests are tiny exports (seconds)
  while :; do
    busy=0; for n in $XK_ON; do for p in ${XK_STPID[$n]:-}; do kill -0 "$p" 2>/dev/null && busy=1; done; done
    [ "$busy" = 1 ] && [ "$(date +%s)" -lt "$deadline" ] || break
    sleep 0.5
  done
  xk_killall
}
xk_settle() {  # xk_settle EXIT VERDICT REASON -> XK_EX XK_V XK_WHY (the final verdict), XK_JSON, XK_SUM
  XK_EX=$1; XK_V=$2; XK_WHY=$3
  local n sum=
  if [ -n "$XK_ON" ]; then
    if [ "$XK_V" = ACCEPTED ]; then xk_wait; else xk_killall; fi
    for n in $XK_ON; do
      XK_RC[$n]=$(xk_rc "$n"); set -- $(xk_timefile "$n"); XK_WALL[$n]=${1:-}; XK_RSS[$n]=${2:-}
      if [ "$XK_V" != ACCEPTED ]; then
        XK_STATUS[$n]="not consulted"; XK_REASON[$n]="the two-kernel verdict is $XK_V; an extra kernel can only veto an ACCEPTED"
      elif [ "${XK_TIMEDOUT[$n]:-}" = 1 ]; then
        XK_STATUS[$n]="not decided"; XK_REASON[$n]="timeout: still running $XK_GRACE_USED s after the two-kernel verdict (--kernel-grace)"
      elif ! xk_selftest_ok "$n"; then
        XK_STATUS[$n]="not decided"; XK_REASON[$n]="self-test failed: the pinned $n does not give the known verdicts on the self-test exports here ($XK_ST_WHY)"
      else
        xk_verdict "$n" "$n"; XK_STATUS[$n]=$XV_ST; XK_REASON[$n]=$XV_WHY; XK_MSG[$n]=$XV_MSG
      fi
      log "[$SELF] extra kernel $n (${XK_MODE[$n]}): ${XK_STATUS[$n]}${XK_REASON[$n]:+ (${XK_REASON[$n]})}${XK_MSG[$n]:+: ${XK_MSG[$n]}} rc=${XK_RC[$n]:-none} wall=${XK_WALL[$n]:-?}s rss=${XK_RSS[$n]:-?}kB"
      [ -z "$W" ] || log "$(grep -v ': stats: ' -- "$W/xko/leg-$n.log" 2>/dev/null | tail -n 6 | cut -c1-400)"
    done
    if [ "$XK_V" = ACCEPTED ]; then   # integrity after the extra kernels ran (fail closed, as for the two-kernel judge)
      for n in $XK_ON; do [ "$(sha256sum "${XK_BIN[$n]}" | cut -d' ' -f1)" = "${XK_SHA[$n]}" ] || { XK_EX=2; XK_V=DECLINED; XK_WHY="pinned extra kernel $n changed during the run"; }; done
      [ "$(sha256sum "$XK_KBAD" | cut -d' ' -f1)" = "${PIN_SHA[selftest_kbad]}" ] || { XK_EX=2; XK_V=DECLINED; XK_WHY="pinned selftest_kbad changed during the run"; }
      [ "$(stamp)" = "$STAMP0" ] || { XK_EX=2; XK_V=DECLINED; XK_WHY="an input file was modified during the check (extra kernels)"; }
    fi
  fi
  for n in $XK_NAMES; do sum="$sum${sum:+; }$n: ${XK_STATUS[$n]:-off}${XK_REASON[$n]:+ (${XK_REASON[$n]})}"; done
  XK_SUM=$sum
  XK_JSON=$(/usr/bin/python3 -I - "$XK_NAMES" \
    "${XK_MODE[con-leche]}" "${XK_STATUS[con-leche]:-}" "${XK_REASON[con-leche]:-}" "${XK_RC[con-leche]:-}" "${XK_WALL[con-leche]:-}" "${XK_RSS[con-leche]:-}" "${XK_MSG[con-leche]:-}" "${XK_SHA[con-leche]:-}" \
    "${XK_MODE[nanoda]}" "${XK_STATUS[nanoda]:-}" "${XK_REASON[nanoda]:-}" "${XK_RC[nanoda]:-}" "${XK_WALL[nanoda]:-}" "${XK_RSS[nanoda]:-}" "${XK_MSG[nanoda]:-}" "${XK_SHA[nanoda]:-}" <<'PY' 2>/dev/null
import json, sys
names = sys.argv[1].split(); a = sys.argv[2:]; out = {}
for i, n in enumerate(names):
    mode, st, why, rc, wall, rss, msg, sha = a[i * 8:(i + 1) * 8]
    try:
        w = float(wall) if wall else None
    except ValueError:
        w = None
    out[n] = {"mode": mode, "status": st or "off", "reason": why or None, "rc": int(rc) if rc.isdigit() else None,
              "wall_s": w, "max_rss_kb": int(rss) if rss.isdigit() else None, "message": msg or None, "sha256": sha or None}
print(json.dumps(out, ensure_ascii=False))
PY
) || XK_JSON=null
  [ -n "$XK_JSON" ] || XK_JSON=null
  [ "$XK_V" = ACCEPTED ] || return 0
  for n in $XK_ON; do   # a genuine rejection by any enabled extra kernel vetoes the two-kernel ACCEPT
    if [ "${XK_STATUS[$n]}" = rejected ]; then
      XK_EX=1; XK_V=REJECTED; XK_WHY="rejected by the extra kernel $n: ${XK_MSG[$n]} (the official Lean $TC_LABEL kernel and gruszka had accepted; an extra kernel can reject a valid proof - con-leche treats theorem bodies as opaque - and --skip-kernel $n gives the two-kernel verdict)"; return 0
    fi
  done
  for n in $XK_NAMES; do   # a required extra kernel that did not accept: no verdict
    if [ "${XK_MODE[$n]}" = required ] && [ "${XK_STATUS[$n]}" != accepted ]; then
      XK_EX=2; XK_V=DECLINED; XK_WHY="the required extra kernel $n did not decide (${XK_STATUS[$n]}${XK_REASON[$n]:+: ${XK_REASON[$n]}}): no verdict"; return 0
    fi
  done
  XK_WHY="$XK_WHY; extra veto kernels: $sum"
  BASIS="${BASIS:-}; veto-only extra kernels (bundled with the official Lean v4.37.0-rc1 release): $sum"
}

# v2.3-H: extra veto kernels. XK_MODE: off | auto (default-on, memory-guarded, optional) | optional (--kernel) |
# required (--require-kernel: its 'not decided' = no verdict). Later options override earlier ones.
declare -A XK_MODE XK_PIN XK_BIN XK_SHA XK_STATUS XK_REASON XK_MSG XK_RC XK_PID XK_STPID XK_WALL XK_RSS XK_TIMEDOUT XK_WHYOFF
XK_NAMES="con-leche nanoda"; XK_ON=; XK_DONE=0; XK_JSON=; XK_SUM=; XK_GRACE_USED=; XK_T0=; CCMP_WALL=0; KJOBS=; KGRACE=
XK_CONLECHE_DEFAULT=off   # DEFAULT SWITCH: off = opt-in like nanoda;
                          # auto = on by default, skipped and recorded 'skipped (memory)' when the memory guard says no
XK_MODE[con-leche]=$XK_CONLECHE_DEFAULT; XK_PIN[con-leche]=con_leche
XK_WHYOFF[con-leche]="opt-in: --kernel con-leche or --require-kernel con-leche (it rejects some valid proofs that unfold a theorem body)"
XK_MODE[nanoda]=off; XK_WHYOFF[nanoda]="opt-in: --kernel nanoda or --require-kernel nanoda"; XK_PIN[nanoda]=nanoda
xk_name_ok() { case "${1:-}" in con-leche|nanoda) true;; *) false;; esac; }   # exact names only (one name per option)

# ---------- arguments ----------
PREFLIGHT=0
if [ "${1:-}" = --xk-classify ]; then   # v2.3-H test interface: classification of a recorded run; never a verdict (exit 2)
  [ $# = 4 ] || { echo "usage: $(basename "$0") --xk-classify con-leche|nanoda LOGFILE RC" >&2; FINISHED=1; exit 2; }
  { read -r st; read -r why; read -r msg; } < <(xk_classify "$2" "$3" "$4")
  printf '{"checker":"%s","mode":"xk-classify","verdict":"NOT_A_VERDICT","kernel":%s,"status":%s,"reason":%s,"message":%s}\n' \
    "$SELF" "$(json_str "$2")" "$(json_str "$st")" "$(json_str "$why")" "$(json_str "$msg")"
  FINISHED=1; exit 2
fi
if [ "${1:-}" = --preflight ]; then PREFLIGHT=1; shift; set -- "$HERE/pins.env" "$HERE/pins.env" "$HERE/pins.env" "$@"; fi
[ $# -ge 3 ] || { echo "usage: check-sound.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--log FILE] [--timeout S] [--workdir DIR] [--keep-config-kernels] [--hints FILE|none] [--incr-dir DIR] [--private-inputs] [--pins FILE] [--hide FILE] | --preflight [--pins FILE]" >&2; decline "usage"; }
E_IN=$1; C_IN=$2; CFG_IN=$3; shift 3
T=; WD=; JSONF=; TMO=0; KEEPK=0; HINTS=; INCR=; PRIVIN=0; PINSOPT=; HIDE=; HIDE_SHA=; XAX=; XAXJ=null
while [ $# -gt 0 ]; do
  case "$1" in
    --private-inputs) PRIVIN=1; shift;;
    --pins) PINSOPT=${2:-}; shift 2 || decline "--pins needs a value";;
    --hide) HIDE=${2:-}; shift 2 || decline "--hide needs a value";;
    --extra-axioms) XAX=${2:-}; shift 2 || decline "--extra-axioms needs a value";;
    --threads) T=${2:-}; shift 2 || decline "--threads needs a value";;
    --workdir) WD=${2:-}; shift 2 || decline "--workdir needs a value";;
    --json) JSONF=${2:-}; shift 2 || decline "--json needs a value";;
    --timeout) TMO=${2:-}; shift 2 || decline "--timeout needs a value";;
    --keep-config-kernels) KEEPK=1; shift;;
    --hints) HINTS=${2:-}; shift 2 || decline "--hints needs a value";;
    --incr-dir) INCR=${2:-}; shift 2 || decline "--incr-dir needs a value";;
    --log) LOGF=${2:-}; shift 2 || decline "--log needs a value"; : > "$LOGF" || decline "cannot write log $LOGF";;
    --kernel) xk_name_ok "${2:-}" || decline "--kernel: unknown extra kernel '${2:-}' (known: $XK_NAMES)"
      [ "${XK_MODE[$2]}" = required ] || XK_MODE[$2]=optional; shift 2;;
    --require-kernel) xk_name_ok "${2:-}" || decline "--require-kernel: unknown extra kernel '${2:-}' (known: $XK_NAMES)"
      XK_MODE[$2]=required; shift 2;;
    --skip-kernel) xk_name_ok "${2:-}" || decline "--skip-kernel: unknown extra kernel '${2:-}' (known: $XK_NAMES)"
      [ "${XK_MODE[$2]}" != required ] || decline "--skip-kernel $2 contradicts --require-kernel $2"
      XK_MODE[$2]=off; XK_WHYOFF[$2]="disabled by --skip-kernel"; shift 2;;
    --kernel-jobs) KJOBS=${2:-}; shift 2 || decline "--kernel-jobs needs a value";;
    --kernel-grace) KGRACE=${2:-}; shift 2 || decline "--kernel-grace needs a value";;
    --require-sorried-holes) Q02_RSH=1; shift;;   # Q02: the sorried-hole rule for every release (DECLINED if violated)
    --challenge-sha256) CSHA_PIN=${2:-}; shift 2 || decline "--challenge-sha256 needs a value"; [ -n "$CSHA_PIN" ] || decline "--challenge-sha256 needs a non-empty value";;
    --comparator-sha256) CFGSHA_PIN=${2:-}; shift 2 || decline "--comparator-sha256 needs a value"; [ -n "$CFGSHA_PIN" ] || decline "--comparator-sha256 needs a non-empty value";;
    *) decline "unknown argument '$1'";;
  esac
done
if [ -z "$T" ]; then T=$(nproc 2>/dev/null || echo 1); fi
case "$T" in ''|*[!0-9]*|0) decline "--threads must be a positive number";; esac
# numeric options become plain base-10 integers right after validation (at most 9
# digits; '08' -> 8): the JSON result never carries a zero-padded number and bash arithmetic never reads octal.
[ "${#T}" -le 9 ] || decline "--threads must be a positive number"; T=$((10#$T))
[ "$T" -ge 1 ] || decline "--threads must be a positive number"
case "$TMO" in ''|*[!0-9]*) decline "--timeout must be a number of seconds (0 = none)";; esac
[ "${#TMO}" -le 9 ] || decline "--timeout must be a number of seconds (0 = none)"; TMO=$((10#$TMO))
case "$KGRACE" in *[!0-9]*) decline "--kernel-grace must be a number of seconds";; esac
[ "${#KGRACE}" -le 9 ] || decline "--kernel-grace must be a number of seconds"   # at most 9 digits, no wrap
[ -z "$KGRACE" ] || KGRACE=$((10#$KGRACE))   # decimal (a leading zero is not octal)
case "$KJOBS" in *[!0-9]*) decline "--kernel-jobs must be a positive number";; esac
AS=$(ulimit -v)   # every replay worker reserves a ~1 GiB stack (finding 042): cap threads to the address space
if [ "$AS" != unlimited ]; then
  cap=$(( AS / 4194304 )); [ "$cap" -ge 1 ] || cap=1
  if [ "$T" -gt "$cap" ]; then log "[$SELF] address-space limit ${AS} KB: threads $T -> $cap"; T=$cap; fi
fi
if [ -z "$KJOBS" ]; then KJOBS=$T; [ "$KJOBS" -le 64 ] || KJOBS=64; fi   # v2.3-H: extra kernels' threads (T is final here)
[ "${#KJOBS}" -le 9 ] || decline "--kernel-jobs must be a positive number"   # at most 9 digits, no wrap
KJOBS=$((10#$KJOBS)); [ "$KJOBS" -ge 1 ] || decline "--kernel-jobs must be a positive number"   # decimal
for f in "$E_IN" "$C_IN" "$CFG_IN"; do
  [ -n "$f" ] || decline "empty input path"
  r=$(readlink -f -- "$f") || decline "cannot resolve '$f'"
  { [ -f "$r" ] && [ ! -p "$r" ] && [ ! -c "$r" ] && [ ! -b "$r" ] && [ ! -S "$r" ]; } || decline "input is not a regular file: '$f'"
done
E_IN=$(readlink -f -- "$E_IN"); C_IN=$(readlink -f -- "$C_IN"); CFG_IN=$(readlink -f -- "$CFG_IN")

# ---------- pinned components: pins.env = SOUND_VERSION, TC36 and lines "PIN <name> <sha256> <path>" ----------
# v2.1: `--pins FILE` = another pins file of the same format (absolute path; parsed from a private copy whose sha256 is recorded in the JSON result);
# optional lines TC_VERSION=leanprover/lean4:vX (the official release the judge binaries were built from; the toolchain at
# TC36 must verify against fastverify/toolchains/<that release>.json) and TC_LABEL=X (text of the verdict basis).
PINS=$HERE/pins.env
if [ -n "$PINSOPT" ]; then
  case "$PINSOPT" in /*) ;; *) decline "--pins must be an absolute path";; esac
  PINS=$(readlink -f -- "$PINSOPT") || decline "cannot resolve --pins '$PINSOPT'"
  # (Boundary B4 like bin/fastverify, fvserve, fv_lowmem, fvcheckd) only this judge's own
  # pins files can be selected - after resolving every symlink, a pins*.env DIRECTLY in this script's directory. A
  # caller-made (self-consistent) pins file would let the caller choose the trusted binaries.
  case "$(basename -- "$PINS")" in pins*.env) ;; *) decline "--pins must name a pins*.env file in $HERE";; esac
  [ "$(dirname -- "$PINS")" = "$(readlink -f -- "$HERE")" ] || decline "--pins must name a pins*.env file in $HERE"
fi
[ -f "$PINS" ] || decline "missing $PINS"
# the pins file is read ONCE into a private copy; everything below parses the copy and the recorded sha256 is the copy's
# (nothing can change what was parsed after the fact)
PINS_PRIV=$(mktemp "${TMPDIR:-/tmp}/checkSound-pins.XXXXXX") || decline "cannot create a private copy of the pins file"
cp -- "$PINS" "$PINS_PRIV" || decline "cannot copy the pins file"
PINS_SHA=$(sha256sum "$PINS_PRIV" | cut -d' ' -f1)
SOUND_VERSION=$(sed -n 's/^SOUND_VERSION=//p' "$PINS_PRIV" | head -1)
TC_VERSION=$(sed -n 's/^TC_VERSION=//p' "$PINS_PRIV" | head -1); [ -n "$TC_VERSION" ] || TC_VERSION=leanprover/lean4:v4.36.0
TC_LABEL=$(sed -n 's/^TC_LABEL=//p' "$PINS_PRIV" | head -1); [ -n "$TC_LABEL" ] || TC_LABEL=4.36
case "$TC_VERSION" in leanprover/lean4:v[0-9]*) ;; *) decline "pins: TC_VERSION must name an official release (leanprover/lean4:vX)";; esac
TC36=$(sed -n 's/^TC36=//p' "$PINS_PRIV" | head -1)
if [ "$TC36" = @components ]; then
  # the package's registered toolchain of TC_VERSION: comparator.prefix for the default 4.36 (as before), otherwise the
  # lean_toolchains entry of config/components.json (written by tools/addrelease.py); verified below like any other path
  TC36=$(/usr/bin/python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); v=sys.argv[2]
print(c["comparator"]["prefix"] if v == "leanprover/lean4:v4.36.0" else c["lean_toolchains"][v]["prefix"])' \
         "$PKGROOT/config/components.json" "$TC_VERSION" 2>/dev/null) || decline "config/components.json has no toolchain prefix for $TC_VERSION"
fi
[ -n "$TC36" ] && [ -d "$TC36" ] || decline "official Lean $TC_LABEL toolchain not found ($TC36)"
declare -A PIN_PATH PIN_SHA
while read -r tag name sum path; do
  [ "$tag" = PIN ] || continue
  PIN_PATH[$name]=$path; PIN_SHA[$name]=$sum
done < "$PINS_PRIV"
BJ="{"; sep=
for name in ccmp pleanchecker gruszka selftest_comparator selftest_challenge selftest_good selftest_bad; do
  p=${PIN_PATH[$name]:-}; [ -n "$p" ] || decline "pins.env has no PIN for $name"
  [ -f "$p" ] || decline "pinned file missing: $p"
  got=$(sha256sum "$p" | cut -d' ' -f1)
  [ "$got" = "${PIN_SHA[$name]}" ] || decline "sha256 mismatch for $p (got $got, pinned ${PIN_SHA[$name]})"
  BJ="$BJ$sep\"$name\":\"$got\""; sep=,
done
BIN_JSON="$BJ}"   # only a complete object goes into the JSON
CCMP=${PIN_PATH[ccmp]}; PLC_BIN=${PIN_PATH[pleanchecker]}; GRUSZKA=${PIN_PATH[gruszka]}
PLC_INCR_BIN=   # optional (S08 overlap): a separately pinned pleanchecker with the --attach/--incremental modes
if [ -n "$INCR" ] && [ -n "${PIN_PATH[pleanchecker_incr]:-}" ]; then
  p=${PIN_PATH[pleanchecker_incr]}; [ -f "$p" ] || decline "pinned file missing: $p"
  got=$(sha256sum "$p" | cut -d' ' -f1)
  [ "$got" = "${PIN_SHA[pleanchecker_incr]}" ] || decline "sha256 mismatch for $p (got $got, pinned ${PIN_SHA[pleanchecker_incr]})"
  PLC_INCR_BIN=$p; BIN_JSON="${BIN_JSON%\}},\"pleanchecker_incr\":\"$got\"}"
fi
/usr/bin/python3 -I "$PKGROOT/lib/toolchain.py" verify "$TC36" "$TC_VERSION" > /dev/null 2>&1 \
  || decline "the official Lean $TC_LABEL toolchain at $TC36 does not verify against fastverify/toolchains ($TC_VERSION)"
# v2.3-H: the extra veto kernels' pins (optional lines PIN con_leche / PIN nanoda / PIN selftest_kbad; always fully hashed,
# also in cached runs of the service variant). No pin line: optional -> 'not configured', required -> no verdict. Pinned file
# missing: optional -> 'not decided', required -> no verdict. A present file whose sha256 differs from its pin -> no verdict,
# always (fail closed, as for every pinned component). selftest_kbad = a KERNEL-invalid export (the good self-test export
# with the proof of fvSelfTest replaced by an ill-typed one; the comparator-level selftest_bad carries a custom axiom, which
# con-leche declines): every enabled extra kernel must accept selftest_good and reject selftest_kbad in this run.
XK_KBAD=${PIN_PATH[selftest_kbad]:-}
if [ -n "$XK_KBAD" ] && [ -f "$XK_KBAD" ]; then
  got=$(sha256sum "$XK_KBAD" | cut -d' ' -f1)
  [ "$got" = "${PIN_SHA[selftest_kbad]}" ] || decline "sha256 mismatch for $XK_KBAD (got $got, pinned ${PIN_SHA[selftest_kbad]})"
elif [ -n "$XK_KBAD" ]; then XK_KBAD=; XK_KBAD_MISSING=1
fi
XK_EBYTES=$(stat -c %s -- "$E_IN" 2>/dev/null || echo 0)
for n in $XK_NAMES; do
  XK_STATUS[$n]=; XK_REASON[$n]=; XK_MSG[$n]=; XK_RC[$n]=; XK_WALL[$n]=; XK_RSS[$n]=; XK_SHA[$n]=; XK_BIN[$n]=; XK_PID[$n]=; XK_STPID[$n]=; XK_TIMEDOUT[$n]=
  if [ "${XK_MODE[$n]}" = off ]; then XK_STATUS[$n]=off; XK_REASON[$n]=${XK_WHYOFF[$n]:-}; continue; fi
  pn=${XK_PIN[$n]}; p=${PIN_PATH[$pn]:-}
  if [ -z "$p" ]; then
    [ "${XK_MODE[$n]}" != required ] || decline "the pins file has no PIN $pn (required extra kernel $n)"
    XK_STATUS[$n]="not configured"; XK_REASON[$n]="no PIN $pn in the pins file"; continue
  fi
  if [ ! -f "$p" ]; then
    [ "${XK_MODE[$n]}" != required ] || decline "pinned file missing: $p (required extra kernel $n)"
    XK_STATUS[$n]="not decided"; XK_REASON[$n]="pinned binary missing: $p"; continue
  fi
  got=$(sha256sum "$p" | cut -d' ' -f1)
  [ "$got" = "${PIN_SHA[$pn]}" ] || decline "sha256 mismatch for $p (got $got, pinned ${PIN_SHA[$pn]})"
  if [ -z "$XK_KBAD" ]; then
    [ "${XK_MODE[$n]}" != required ] || decline "no usable PIN selftest_kbad (the extra kernels' self-test export; required extra kernel $n)"
    XK_STATUS[$n]="not decided"; XK_REASON[$n]="no usable PIN selftest_kbad (kernel-level self-test export${XK_KBAD_MISSING:+: file missing})"; continue
  fi
  if [ "${XK_MODE[$n]}" = auto ] && [ "$PREFLIGHT" != 1 ]; then
    # memory guard (availability only: a skipped optional kernel leaves today's two-kernel judge): estimated peak of the
    # judge's three concurrent legs (D09 model, as lib/autotune.py: 4.2 x export + 87 MB/thread + 1 GiB) + con-leche's
    # (measured, check/sound/README.md: <= 0.85 x export + 2 GiB) against this run's budget = min(MemAvailable,
    # memory.max - memory.current over the cgroup chain); no budget known -> run it
    mg=$(/usr/bin/python3 -I - "$XK_EBYTES" "$T" <<'PY' 2>/dev/null
import os, sys
e, t = int(sys.argv[1]), int(sys.argv[2])
def rd(p):
    try:
        return open(p).read().strip()
    except OSError:
        return None
v = None
for ln in (rd("/proc/meminfo") or "").splitlines():
    if ln.startswith("MemAvailable:"):
        v = int(ln.split()[1]) * 1024
for ln in (rd("/proc/self/cgroup") or "").splitlines():
    q = ln.split(":", 2)
    if len(q) == 3 and q[0] == "0":
        d = "/sys/fs/cgroup" + q[2].rstrip("/")
        while d.startswith("/sys/fs/cgroup") and d != "/sys/fs/cgroup":
            mx, cur = rd(d + "/memory.max"), rd(d + "/memory.current")
            if mx and cur and mx != "max":
                v = int(mx) - int(cur) if v is None else min(v, int(mx) - int(cur))
            d = os.path.dirname(d)
need = 4.2 * e + (87 << 20) * t + (1 << 30) + 0.85 * e + (2 << 30)
if v is None:
    print("ok")
elif need <= v:
    print("ok")
else:
    print("skip estimated peak of the judge + con-leche %d MiB > memory budget %d MiB" % (int(need) >> 20, v >> 20))
PY
) || mg=ok
    case "$mg" in skip*) XK_STATUS[$n]="skipped (memory)"; XK_REASON[$n]=${mg#skip }; continue;; esac
  fi
  XK_BIN[$n]=$p; XK_SHA[$n]=$got; XK_ON="$XK_ON $n"; BIN_JSON="${BIN_JSON%\}},\"$pn\":\"$got\"}"
done
XK_ON=${XK_ON# }
[ -z "$XK_ON" ] || BIN_JSON="${BIN_JSON%\}},\"selftest_kbad\":\"${PIN_SHA[selftest_kbad]}\"}"

# ---------- private work dir, private names of the inputs (v2: a copy of its own by default; see priv below) ----------
if [ "$PREFLIGHT" = 1 ]; then WD=/tmp; INCR=; fi
if [ -n "$INCR" ]; then
  INCR=$(readlink -f -- "$INCR") || decline "cannot resolve --incr-dir"
  # the incremental process (sandbox: /tmp, /home hidden) must be able to read ccmp's private export name
  [ -n "$WD" ] || WD=$(dirname "$E_IN")
  case "$INCR/" in /tmp/*|/home/*|/root/*|/run/*|/var/*) log "[$SELF] --incr-dir $INCR is hidden in the kernel sandbox: the Lean leg will run non-incrementally";; esac
fi
if [ -z "$WD" ]; then
  if [ "$(stat -c %s -- "$E_IN")" -le 4294967296 ] && [ "$(stat -c %s -- "$C_IN")" -le 4294967296 ]; then WD=/tmp; else WD=$(dirname "$E_IN"); fi
fi
W=$(mktemp -d "$WD/.checkSound.XXXXXX" 2>/dev/null) || W=$(mktemp -d "/tmp/checkSound.XXXXXX") || decline "cannot create a work dir"
W=$(/usr/bin/realpath -e -- "$W") || decline "cannot resolve the work dir $W"   # absolute: a relative --workdir gave bwrap relative mount destinations
chmod 755 "$W"   # the kernels run as the same user inside bwrap; the dir must be traversable for the bound wrappers
mkdir -p "$W/bin" "$W/tmp" "$W/home"
mkdir -m 700 "$W/xko" || decline "cannot create $W/xko"   # v2.3-H: extra-kernel logs + exit statuses (no sandbox can write here)
# the inputs must be PRIVATE for the whole run (no other writer, no writable mapping): the three readers open them
# independently. v2 (D08): priv SRC DST [link-ok] gives EVERY input a COPY of its own, whatever its size (a new inode:
# nothing the caller still holds - a writable mapping, a later write(2), a concurrent check of the same shared file - can
# reach what the legs read; `cp --reflink=auto` = instant on XFS/btrfs, a full copy elsewhere). With --private-inputs the
# CALLER asserts that nothing else can write the export during the check (the package's orchestrator: it wrote the export
# itself into its own OUT / --export-dir, and in export-in mode it copied the given file into OUT first); then an export > 4 GiB
# is hard-linked instead of copied (no second copy of a 61.6 GB export; inputs <= 4 GiB are still copied: a hard link changes
# the SOURCE's link count and ctime, which a concurrent check of the same shared file would see in its end-of-run stamp). The
# challenge export is always copied. Prints copy|link.
priv() {
  if [ "${3:-}" = link-ok ] && [ "$PRIVIN" = 1 ] && [ "$(stat -c %s -- "$1")" -gt 4294967296 ]; then
    if ln -- "$1" "$2" 2>/dev/null; then echo link; return 0; fi
    log "[$SELF] cannot hard-link $1 into $W (another filesystem?): copying it instead"
  fi
  cp --reflink=auto -- "$1" "$2" || return 1
  echo copy
}
if [ "$PREFLIGHT" = 1 ]; then
  cp -- "${PIN_PATH[selftest_good]}" "$W/solution.export"; cp -- "${PIN_PATH[selftest_challenge]}" "$W/challenge.export"
  cp -- "${PIN_PATH[selftest_comparator]}" "$W/comparator.orig.json"
else
  PRIV_E=$(priv "$E_IN" "$W/solution.export" link-ok) || decline "cannot copy the export into $W (no space? use --workdir DIR on a filesystem with room, or --private-inputs if nothing else can write the export during the check)"
  PRIV_C=$(priv "$C_IN" "$W/challenge.export") || decline "cannot copy the challenge export into $W"
  cp -- "$CFG_IN" "$W/comparator.orig.json" || decline "cannot copy the config"
  INPUTS_JSON=$(printf '{"export":{"size":%s,"private":"%s"},"challenge":{"size":%s,"private":"%s"}}' \
    "$(stat -c %s -- "$E_IN")" "$PRIV_E" "$(stat -c %s -- "$C_IN")" "$PRIV_C")
  log "[$SELF] private inputs: export $PRIV_E ($(stat -c %s -- "$E_IN") bytes), challenge export $PRIV_C$([ "$PRIVIN" = 1 ] && echo "; --private-inputs asserted by the caller")"
fi
# the paths below are embedded in the kernel wrappers (double-quoted): refuse shell-special characters (fail closed)
case "$W$INCR$PLC_BIN$PLC_INCR_BIN$GRUSZKA$T" in *[\"\\\$\`]*|*$'\n'*) decline "a path used by the kernel wrappers contains a shell-special character";; esac
case "${XK_BIN[con-leche]}${XK_BIN[nanoda]}$KJOBS${PIN_PATH[selftest_good]}$XK_KBAD" in *[\"\\\$\`\']*|*$'\n'*) decline "a path used by the extra-kernel wrappers contains a shell-special character";; esac   # v2.3-H
# S03: optional scheduling hints for the Lean kernel replay (declaration names, one per line, e.g. the slow jobs of an
# earlier run): ORDER ONLY - the named jobs are served first by the replay workers so they start early; every job is still
# checked exactly once and the verdict does not depend on this file (a wrong or hostile hint file can only make the run
# slower; an unreadable one is ignored by pleanchecker). Default: the package's hints/default.txt (timing data of earlier
# checks, e.g. RH's slow declarations; names absent from an export are ignored); --hints none disables.
: > "$W/hints"
if [ -z "$HINTS" ] && [ -f "$HERE/hints/default.txt" ]; then HINTS=$HERE/hints/default.txt; fi
if [ "$HINTS" = none ]; then HINTS=; fi
if [ -n "$HINTS" ]; then
  { [ -f "$HINTS" ] && [ "$(stat -L -c %s -- "$HINTS")" -le 16777216 ]; } || decline "--hints: not a regular file <= 16 MiB: '$HINTS'"
  cp -- "$HINTS" "$W/hints" || decline "cannot copy the hints file"
fi
# v2.2: the hide list of the encapsulated replay (D23-E), same discipline as the hints
HIDEENV=
if [ -n "$HIDE" ]; then
  { [ -f "$HIDE" ] && [ "$(stat -L -c %s -- "$HIDE")" -le 16777216 ]; } || decline "--hide: not a regular file <= 16 MiB: '$HIDE'"
  cp -- "$HIDE" "$W/hide" || decline "cannot copy the hide list"
  HIDE_SHA=$(sha256sum "$W/hide" | cut -d' ' -f1); HIDEENV="PCHK_HIDE_FILE=\"$W/hide\" "
fi
# the comparison, the Lean-kernel leg and the second kernel read the inputs INDEPENDENTLY, so an input must not change
# while they run. inode + size + mtime do not see an in-place rewrite that restores the mtime; the ctime (with ns) does for
# write(2)/truncate/chmod/utime/link changes (set to "now", not settable back by unprivileged code) -> any such change = no
# verdict. DEFENSE IN DEPTH only: stores through a writable shared mapping of an already-dirty page may not update the times
# (tmpfs: never after the first fault) - the guarantee is that inputs are private (see priv above; export-in copies first).
stamp() { stat -c '%i %s %y %z' -- "$W/solution.export" "$W/challenge.export"; }
STAMP0=$(stamp)

# ---------- kernel wrappers (bound read-only into ccmp's kernel sandbox as the kernel executables) ----------
# v2: every leg's own stdout/stderr goes to ITS OWN file $W/tmp/leg-<leg>.log (self-test legs: leg-selftest-<leg>-<export>.log)
# and its exit status to $W/tmp/leg-<leg>.rc, both written by the wrapper (trusted wiring, generated here) - never by the leg
# itself, never into ccmp's log. $W/tmp is the writable bind of ccmp's sandbox; the judged export has the fixed private name
# $W/solution.export, which is how the wrapper tells the judged run from the self-test runs.
# Lean kernel: pleanchecker with -jT; worker stacks 1 GiB - 128 KiB - 128 MiB (check A's stack rule; overflow -> no verdict)
PLC_STACK_KB=917376
mkplc() {  # mkplc FILE BINARY [INCR_DIR]: the Lean-kernel leg wrapper (ccmp calls it as `<leanchecker> --silent --from-export EXPORT`)
  local attach=; [ -n "${3:-}" ] && attach="\"--attach=$3\" "
  cat > "$1" <<EOF
#!/bin/sh
for a do shift; [ "\$a" = --silent ] || set -- "\$@" "\$a"; done
for a do L=\$a; done
case "\$L" in "$W/solution.export") N=lean;; *) N=selftest-lean-\$(basename "\$L");; esac
${HIDEENV}PCHK_PRIO_FILE="$W/hints" PCHK_SLOW_MS=10000 LEAN_STACK_SIZE_KB=$PLC_STACK_KB "$2" -j$T -v $attach"\$@" > "$W/tmp/leg-\$N.log" 2>&1
rc=\$?; echo "\$rc" > "$W/tmp/leg-\$N.rc"; exit \$rc
EOF
  chmod 755 "$1"
}
# the plain wrapper (always used by the self-test, and by the judge without --incr-dir)
mkplc "$W/bin/plc-plain" "$PLC_BIN"
if [ -n "$INCR" ] && [ -z "$PLC_INCR_BIN" ]; then log "[$SELF] --incr-dir given but no PIN pleanchecker_incr: plain replay"; INCR=; fi
if [ -n "$INCR" ]; then   # S08 overlap: served by the --incremental=DIR process (falls back to the plain replay itself)
  mkplc "$W/bin/plc" "$PLC_INCR_BIN" "$INCR"
else
  cp "$W/bin/plc-plain" "$W/bin/plc"
fi
# second kernel: Lake appends the export path -> gruszka EXPORT WORKERS
# the end of the judge's --timeout budget (epoch s; 0 = none) for the gruszka wrapper's retry - counted from
# now, before the judge starts the run its timeout covers, so never later than that timeout
DL=0; [ "$TMO" -gt 0 ] && DL=$(( $(date +%s) + TMO ))
cat > "$W/bin/gruszka-kernel" <<EOF
#!/bin/sh
[ \$# = 1 ] || { echo "gruszka wrapper: expected 1 argument (the export), got \$#" >&2; exit 2; }
case "\$1" in "$W/solution.export") N=k2;; *) N=selftest-k2-\$(basename "\$1");; esac
# Availability: a gruszka decline ONLY for worker-table room depends on the schedule (a
# declaration that runs before the results it reuses exist evaluates them again and can fill its worker's tables), not on
# the input's validity: the judged export's leg runs gruszka ONCE more with 1 worker (the deterministic schedule:
# file/namespace order) and keeps that answer. Trigger (all of it): the judged export (never a self-test), exit
# status exactly 2, a complete log (non-empty, ends with a newline), every line is 'note: ...' except exactly one
# 'declined: ' line, which is the LAST line and ends ': a worker table is full'. Anything else is never retried (residual:
# gruszka prints names unescaped; a crafted name can at most cause this one extra run). The retry runs only inside the
# REMAINING time of the judge's --timeout (DL; none left: no retry; over it: killed, exit 124/137 = no verdict from
# gruszka), with the judge's own worker count (lowmem: T_EFF, the memory-capped count), and only if the first attempt's log could be archived (leg-<leg>-retries.log; first exit status in
# leg-<leg>.retry -> judge JSON legs.k2.retry). A retry ended by a signal keeps its exit status (128+n): gruszka gave no
# verdict, and the judge's existing rule decides (README). Veto-only (S1(4)): ACCEPTED still needs the official-kernel
# leg and the comparison.
DL=$DL
w=$T
"$GRUSZKA" "\$1" \$w > "$W/tmp/leg-\$N.log" 2>&1; rc=\$?
if [ "\$N" = k2 ] && [ "\$rc" -eq 2 ] && [ \$w -gt 1 ] && [ -s "$W/tmp/leg-\$N.log" ] && [ -z "\$(tail -c 1 "$W/tmp/leg-\$N.log")" ] \\
    && awk 'BEGIN { d = 0; bad = 0 } /^declined: / { d++ } { last = \$0; if (\$0 !~ /^(declined|note): /) bad = 1 }
            END { exit !(d == 1 && !bad && last ~ /^declined: .*: a worker table is full\$/) }' "$W/tmp/leg-\$N.log"; then
  left=; [ "\$DL" -gt 0 ] && left=\$(( DL - \$(date +%s) ))
  if [ -n "\$left" ] && [ "\$left" -le 0 ]; then
    { cat "$W/tmp/leg-\$N.log"; echo "[gruszka wrapper] declined for worker-table room: no time left for a 1-worker retry"; } >> "$W/tmp/leg-\$N-retries.log"
  elif ! { cat "$W/tmp/leg-\$N.log"; echo "[gruszka wrapper] declined for worker-table room (first attempt above)"; } >> "$W/tmp/leg-\$N-retries.log"; then
    : # the first attempt could not be archived: no retry (the leg stays DECLINED)
  elif ! echo "\$rc" > "$W/tmp/leg-\$N.retry"; then
    echo "[gruszka wrapper] could not record the first exit status (leg-\$N.retry): no retry" >> "$W/tmp/leg-\$N-retries.log"
  else
    echo "[gruszka wrapper] again with 1 worker\${left:+ (at most \$left s)}" >> "$W/tmp/leg-\$N-retries.log"
    w=1
    if [ -n "\$left" ]; then /usr/bin/timeout --foreground --kill-after=5 "\$left" "$GRUSZKA" "\$1" \$w > "$W/tmp/leg-\$N.log" 2>&1; rc=\$?
    else "$GRUSZKA" "\$1" \$w > "$W/tmp/leg-\$N.log" 2>&1; rc=\$?; fi
    [ "\$rc" -le 2 ] || echo "[gruszka wrapper] the 1-worker retry ended with exit \$rc (signal or time limit): no verdict from gruszka" >> "$W/tmp/leg-\$N-retries.log"
  fi
fi
echo "\$rc" > "$W/tmp/leg-\$N.rc"; exit \$rc
EOF
printf '#!/bin/sh\ncommand -v "$1"\n' > "$W/bin/which"     # ccmp resolves kernel executables with `which`
chmod 755 "$W/bin/plc" "$W/bin/gruszka-kernel" "$W/bin/which"
# ---------- v2.3-H: extra veto kernels (run OUTSIDE ccmp) ----------
# $W/bin/xk-NAME EXPORT TAG: the kernel in a bwrap sandbox like ccmp's (read-only /, no network, tmpfs home/root/run/tmp,
# clean environment, $W read-only, only $W/xk-TAG writable), started in a session of its own; its stdout+stderr ->
# $W/xko/leg-TAG.log, its exit status -> $W/xko/leg-TAG.rc (written by this trusted wrapper with noclobber,
# never by the kernel; $W/xko is writable by no sandbox), wall + peak RSS
# -> $W/xk-TAG/time (/usr/bin/time INSIDE the sandbox, so the figure is the kernel's own). --timeout bounds it.
XK_TMO=; [ "$TMO" -gt 0 ] && XK_TMO="/usr/bin/timeout --foreground --kill-after=30 $TMO "   # --foreground: stays in the wrapper's process group (xk_killall reaches it)
for n in $XK_ON; do mkxk "$n"; done

# ---------- config: the challenge's comparator.json, kernels replaced by the pinned second kernel ----------
: > "$W/kept.txt"   # kept config kernels (--keep-config-kernels): "<i>\t<name>" per line, written by the rewrite below
# (S1(3)) ACCEPTED means "from propext, Quot.sound, Classical.choice". A config permitting any other axiom
# is refused unless the caller lists EXACTLY those extra names with --extra-axioms FILE (one per line, <= 1 MiB; e.g.
# check-frontier.sh's internal checks); they are then recorded in the JSON (extra_permitted_axioms) and in the basis.
: > "$W/extra-axioms"
if [ -n "$XAX" ]; then
  { [ -f "$XAX" ] && [ "$(stat -L -c %s -- "$XAX")" -le 1048576 ]; } || decline "--extra-axioms: not a regular file <= 1 MiB: '$XAX'"
  cp -- "$XAX" "$W/extra-axioms" || decline "cannot copy the --extra-axioms list"
fi
CFGMSG=$(/usr/bin/python3 -I - "$W/comparator.orig.json" "$W/comparator.json" "$W/bin/gruszka-kernel" "$KEEPK" "$W" "$W/extra-axioms" <<'PY' 2>&1
import json, os, shlex, sys
src, dst, gk, keep, W = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4] == "1", sys.argv[5]
def no_dups(pairs):
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate key in the configuration")
    return dict(pairs)
def bad_const(x):
    raise ValueError("non-standard JSON constant %s" % x)
# The ORIGINAL comparator.json is validated first, exactly as the official 4.36 comparator reads it. The
# block below is the validator from check/notary/check-notary.sh, copied VERBATIM;
# in this judge the challenge's external kernels / enable_nanoda are replaced by the judge's own second kernel (the
# documented rewrite below), which is why the official PATH lookup of the challenge's kernel commands does not apply.
# before anything is checked or rewritten, the file is read EXACTLY as far as the official 4.36
# comparator reads it (src/lean/lake/Lake/CLI/Check.lean runComparator: Json.parse, then the derived FromJson of
# Lake.Check.Config, then "nothing to check", then resolveExternalKernels' configuration checks). Any official
# configuration error (the official comparator exits 2: no verdict) is refused here -> DECLINED; the rewrite below can
# therefore never turn an official configuration error into a verdict. Lean's Json.parse: duplicate keys refused, a
# positive exponent > 100000 refused, a lone surrogate escape becomes U+FFFD (applied here too, before the
# duplicate-key check, as Lean does). Numbers are kept as their literal text (JNum, never converted: the official
# decoder ignores numbers in fields it does not read, and Python's int() has a 4300-digit limit); a resource limit of
# this reader (recursion / memory) is reported as the notary's own limit, not as an official error. Environment-
# dependent checks (an external kernel command that is not on the official host's PATH) are made for the judge's own
# kernel environment below (every kept command must resolve there; the challenge's kernels are run, recorded in
# "config_rewrite").
class JNum:
    __slots__ = ("s",)
    def __init__(self, s):
        self.s = s
def lean_num(x):
    m = x.lower().partition("e")
    e = m[2].lstrip("+").lstrip("0") or "0"
    if m[1] and not m[2].startswith("-") and (len(e) > 6 or (len(e) == 6 and e > "100000")):
        raise ValueError("JSON number exponent too large (Lean's Json.parse refuses it)")
    return JNum(x)
def lean_str(t):
    return "".join("\ufffd" if 0xD800 <= ord(ch) <= 0xDFFF else ch for ch in t)
def lean_val(v):
    if isinstance(v, str):
        return lean_str(v)
    if isinstance(v, list):
        return [lean_val(y) for y in v]
    return v
def lean_pairs(pairs):
    d = {}
    for k, v in pairs:
        k = lean_str(k)
        if k in d:
            raise ValueError("duplicate object key %r" % k)
        d[k] = lean_val(v)
    return d
def jshow(x):
    return json.dumps(x, default=lambda o: o.s if isinstance(o, JNum) else str(o))[:80]
def off_err(msg):
    sys.exit("official comparator configuration error (the official 4.36 comparator stops with exit 2, no verdict): " + msg)
try:
    c = lean_val(json.loads(open(src, "rb").read().decode("utf-8", errors="strict"), object_pairs_hook=lean_pairs,
                            parse_constant=bad_const, parse_float=lean_num, parse_int=lean_num))
except SystemExit:
    raise
except (RecursionError, MemoryError) as e:
    sys.exit("the notary's own resource limit while reading the configuration (%s; not an official error): no verdict" % type(e).__name__)
except Exception as e:
    off_err("malformed configuration: %s" % e)
if not isinstance(c, dict):
    off_err("Lake.Check.Config.challenge_module: String expected (the configuration is not a JSON object)")
def fj_str(k):
    if not isinstance(c.get(k), str):
        off_err("Lake.Check.Config.%s: String expected" % k)
def fj_arr_str(k, optional):
    x = c.get(k)
    if x is None and optional:
        return []
    if not isinstance(x, list):
        off_err("Lake.Check.Config.%s: expected JSON array, got %s" % (k, jshow(x)))
    if not all(isinstance(y, str) for y in x):
        off_err("Lake.Check.Config.%s: String expected" % k)
    return x
fj_str("challenge_module")
fj_str("solution_module")
off_tn = fj_arr_str("theorem_names", False)
off_dn = fj_arr_str("definition_names", True)
fj_arr_str("permitted_axioms", False)
off_en = c.get("enable_nanoda")
if off_en is not None and not isinstance(off_en, bool):
    off_err("Lake.Check.Config.enable_nanoda?: Bool expected")
off_ek = c.get("external_kernels")
if off_ek is not None:
    if not isinstance(off_ek, dict):
        off_err("Lake.Check.Config.external_kernels?: object expected")
    for kn, kc in off_ek.items():
        if not isinstance(kc, list):
            off_err("Lake.Check.Config.external_kernels?: expected JSON array, got %s" % jshow(kc))
        if not all(isinstance(y, str) for y in kc):
            off_err("Lake.Check.Config.external_kernels?: String expected")
if not off_tn and not off_dn:
    off_err("nothing to check: the configuration names no theorems or definitions")
if off_en is True and off_ek:
    off_err("cannot use `enable_nanoda` and `external_kernels` at the same time")
for kn, kc in (off_ek or {}).items():
    if not kc or kc[0].split(chr(0))[0][:1] in ("", "-") or kc[0].split(chr(0))[0].rsplit("/", 1)[-1] in ("", ".", ".."):
        off_err("`%s` has an empty command" % kn)
# end of the verbatim validator block
try:
    c = json.loads(open(src, "rb").read().decode("utf-8", errors="strict"), object_pairs_hook=no_dups,
                   parse_constant=bad_const)
except Exception as e:
    sys.exit("config is not strict JSON (%s)" % e)
if not isinstance(c, dict):
    sys.exit("config is not a JSON object")
def _is_letter_like(c):
    v = ord(c)
    return (
        (0x3B1 <= v <= 0x3C9 and v != 0x3BB)
        or (0x391 <= v <= 0x3A9 and v != 0x3A0 and v != 0x3A3)
        or (0x3CA <= v <= 0x3FB)
        or (0x1F00 <= v <= 0x1FFE)
        or (0x2100 <= v <= 0x214F)
        or (0x1D49C <= v <= 0x1D59F)
        or (0x00C0 <= v <= 0x00FF and v != 0x00D7 and v != 0x00F7)
        or (0x0100 <= v <= 0x017F)
    )

def _is_subscript_alnum(c):
    v = ord(c)
    return (0x2080 <= v <= 0x2089) or (0x2090 <= v <= 0x209C) or (0x1D62 <= v <= 0x1D6A) or v == 0x2C7C

def _is_id_first(c):
    return ("a" <= c <= "z") or ("A" <= c <= "Z") or c == "_" or _is_letter_like(c)

def _is_id_rest(c):
    return (
        ("a" <= c <= "z")
        or ("A" <= c <= "Z")
        or ("0" <= c <= "9")
        or c in ("_", "'", "!", "?")
        or _is_letter_like(c)
        or _is_subscript_alnum(c)
    )

def parse_lean_name(s):
    """Exact mirror of Lean 4 `String.toName` (`Init/Meta/Defs.lean:splitNameLitAux` + `Substring.Raw.toName`).
    Returns a canonical component tuple: `()` for `Name.anonymous`, `(("s", str) | ("n", int), ...)` otherwise."""
    n = len(s)
    if n == 0:
        return ()
    i = 0
    comps = []
    while True:
        if i >= n:
            return ()
        c = s[i]
        if c == "«":
            j = s.find("»", i + 1)
            if j < 0:
                return ()
            comps.append(("s", s[i + 1 : j]))
            i = j + 1
        elif _is_id_first(c):
            j = i + 1
            while j < n and _is_id_rest(s[j]):
                j += 1
            comps.append(("s", s[i:j]))
            i = j
        elif "0" <= c <= "9":
            j = i + 1
            while j < n and ("0" <= s[j] <= "9"):
                j += 1
            comps.append(("n", int(s[i:j])))
            i = j
        else:
            return ()
        if i == n:
            return tuple(comps)
        if s[i] == ".":
            i += 1
        else:
            return ()

def q02_canon(x):
    t = parse_lean_name(x) if isinstance(x, str) else ()
    if not t:
        sys.exit("config: name %r is not a Lean name" % (x,))
    return t
Q02_S1 = set(q02_canon(n) for n in ("propext", "Quot.sound", "Classical.choice"))
Q02_PRIMS = set(q02_canon(n) for n in ("Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq",
    "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List",
    "eagerReduce", "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam", "Quot",
    "Quot.mk", "Quot.lift", "Quot.ind",   # the comparator's primitiveTargets + builtinTargets
    "Nat.zero", "Nat.succ", "List.cons", "List.nil", "Bool", "Bool.true", "Bool.false", "Eq", "Eq.refl", "dontcare",
    "Lean.reduceBool", "Lean.reduceNat"))   # + kernel-implicit names (their closure: xversion/xvcheck.py)
q02_ax = c.get("permitted_axioms")
if not isinstance(q02_ax, list) or not all(isinstance(x, str) for x in q02_ax):
    sys.exit("permitted_axioms is not a list of names")
q02_allow = sorted(set(l.strip() for l in open(sys.argv[6], encoding="utf-8", errors="strict") if l.strip()))
q02_extra = sorted(set(x for x in q02_ax if q02_canon(x) not in Q02_S1))
if set(q02_canon(x) for x in q02_extra) != set(q02_canon(x) for x in q02_allow):
    if q02_extra:
        sys.exit("permitted_axioms %s outside GOAL S1(3) (propext, Quot.sound, Classical.choice)%s" % (
            q02_extra, "" if not q02_allow else "; --extra-axioms lists %s" % sorted(q02_allow)))
    sys.exit("--extra-axioms lists %s but the config permits no axiom outside GOAL S1(3)" % sorted(q02_allow))
q02_dn = c.get("definition_names")
q02_dn = [] if q02_dn is None else q02_dn
q02_tn = c.get("theorem_names")
q02_tn = [] if q02_tn is None else q02_tn
if not isinstance(q02_dn, list) or not all(isinstance(x, str) for x in q02_dn):
    sys.exit("definition_names is not a list of names")
if not isinstance(q02_tn, list) or not all(isinstance(x, str) for x in q02_tn):
    sys.exit("theorem_names is not a list of names")
q02_bad = sorted(x for x in q02_dn if q02_canon(x) in (Q02_PRIMS | set(map(q02_canon, q02_tn)) | set(map(q02_canon, q02_ax))))
if q02_bad:
    sys.exit("definition_names %s overlap the kernel primitives / quotient builtins / theorem_names / permitted_axioms" % q02_bad)
with open(os.path.join(W, "extra-axioms.json"), "w", encoding="utf-8") as xf:
    json.dump(q02_extra, xf)
ek = c.get("external_kernels")
if c.get("enable_nanoda") is True and isinstance(ek, dict) and len(ek) > 0:
    sys.exit("enable_nanoda together with external_kernels (the official comparator refuses this)")
if keep:
    kernels = dict(ek) if isinstance(ek, dict) else {}
    if c.get("enable_nanoda") is True:
        kernels["nanoda"] = ["nanoda_bin"]
else:
    kernels = {}
if "gruszka (second kernel)" in kernels:
    sys.exit("config already names a kernel 'gruszka (second kernel)'")
# v2: a kept kernel runs through a wrapper of its own too (own log + recorded exit status; nothing in ccmp's log). ccmp
# appends the export path (or, for a kernel whose NAME contains "noda", its generated nanoda config) to the command.
with open(os.path.join(W, "kept.txt"), "w", encoding="utf-8") as kf:
    for i, (name, cmd) in enumerate(sorted(kernels.items())):
        # as Lake - a non-empty executable (cmd[0]); later arguments may be empty strings
        if not (isinstance(cmd, list) and cmd and all(isinstance(x, str) for x in cmd) and cmd[0]):
            sys.exit("external kernel %r has no usable command" % name)
        if "\n" in name or "\t" in name:
            sys.exit("external kernel name with a newline/tab: %r" % name)
        wp = os.path.join(W, "bin", "kept-%d" % i)
        with open(wp, "w", encoding="utf-8") as f:
            f.write("#!/bin/sh\n%s \"$@\" > %s 2>&1\nrc=$?; echo \"$rc\" > %s; exit $rc\n" % (
                " ".join(shlex.quote(x) for x in cmd), shlex.quote(os.path.join(W, "tmp", "leg-kept-%d.log" % i)),
                shlex.quote(os.path.join(W, "tmp", "leg-kept-%d.rc" % i))))
        os.chmod(wp, 0o755)
        kernels[name] = [wp]
        kf.write("%d\t%s\n" % (i, name))
kernels["gruszka (second kernel)"] = [gk]
# only the keys of Lake.Check.Config go to the private config - the official decoder ignores every
# other key, and Python would re-serialize an ignored finite number such as 1e309 as the non-JSON token Infinity
c = {k: v for k, v in c.items() if k in ("challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms",
                                 "enable_nanoda", "external_kernels")}
c.pop("enable_nanoda", None)
c["external_kernels"] = kernels
with open(dst, "w", encoding="utf-8") as f:
    json.dump(c, f, ensure_ascii=False)
PY
) || decline "config refused: $CFGMSG"
XAXJ=$(/usr/bin/python3 -I -c 'import json,sys; print(json.dumps(json.load(open(sys.argv[1]))))' "$W/extra-axioms.json" 2>/dev/null) || decline "cannot read the extra-axioms record"
# the private copies the legs will read are measured here; with --challenge-sha256 /
# --comparator-sha256 (64 lowercase hex) the caller's pins are verified against THESE copies (no window between the caller's
# check and the judge's copy); a mismatch is no verdict. Skipped only by --preflight (the copies are then the self-test's).
if [ "${PREFLIGHT:-0}" != 1 ]; then
  CSHA_GOT=$(sha256sum "$W/challenge.export" | cut -d' ' -f1); CFGSHA_GOT=$(sha256sum "$W/comparator.orig.json" | cut -d' ' -f1)
  for q02pin in "${CSHA_PIN:-}" "${CFGSHA_PIN:-}"; do
    case "$q02pin" in '') ;; *[!0-9a-f]*) decline "--challenge-sha256 / --comparator-sha256 must be 64 lowercase hex digits";; esac
    [ -z "$q02pin" ] || [ "${#q02pin}" = 64 ] || decline "--challenge-sha256 / --comparator-sha256 must be 64 lowercase hex digits"
  done
  [ -z "${CSHA_PIN:-}" ] || [ "$CSHA_GOT" = "$CSHA_PIN" ] || decline "challenge export sha256 $CSHA_GOT (private copy) != --challenge-sha256 $CSHA_PIN"
  [ -z "${CFGSHA_PIN:-}" ] || [ "$CFGSHA_GOT" = "$CFGSHA_PIN" ] || decline "comparator config sha256 $CFGSHA_GOT (private copy) != --comparator-sha256 $CFGSHA_PIN"
fi
# cross-version gate on the PRIVATE copies (check/xversion/xvcheck.py): the release
# that exported the challenge must be admitted (releases.json) and its extra comparator rules must hold (4.37: challenge
# definitions sorried). rc 0 + OK -> continue; rc 1 + REJECTED -> REJECTED; anything else -> no verdict.
if [ "${PREFLIGHT:-0}" != 1 ]; then
  XVPY=$PKGROOT/check/xversion/xvcheck.py
  [ -f "$XVPY" ] || decline "xversion gate: check/xversion/xvcheck.py missing"
  /usr/bin/python3 -I "$XVPY" "$W/challenge.export" "$W/comparator.orig.json" --releases "$PKGROOT/check/xversion/releases.json" ${Q02_RSH:+--require-sorried-holes} \
    --json "$W/xversion.json" > "$W/xversion.out" 2>&1
  XV_RC=$?
  XV_V=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict",""))' "$W/xversion.json" 2>/dev/null)
  XV_REASON=$(/usr/bin/python3 -I -c 'import json,sys; print(str(json.load(open(sys.argv[1])).get("reason",""))[:300])' "$W/xversion.json" 2>/dev/null)
  if [ "$XV_RC" = 0 ] && [ "$XV_V" = OK ]; then
    :
  elif [ "$XV_RC" = 1 ] && [ "$XV_V" = REJECTED ]; then
    finish 1 REJECTED "xversion: $XV_REASON"
  else
    decline "xversion gate failed (rc=$XV_RC): $XV_REASON"
  fi
fi
JPATH="$W/bin:$TC36/bin:/usr/bin:/bin"
runj() {  # runj CMD... : ccmp in a bwrap sandbox like the official comparator's, clean environment
  env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session \
    --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dev /dev --proc /proc \
    --ro-bind "$TC36" "$TC36" --ro-bind "$W" "$W" \
    --bind "$W/tmp" "$W/tmp" --bind "$W/home" "$W/home" --chdir "$W" \
    --setenv HOME "$W/home" --setenv TMPDIR "$W/tmp" --setenv LANG C.UTF-8 --setenv LEAN_ABORT_ON_PANIC 1 \
    --setenv LEAN_NUM_THREADS "$T" --setenv PATH "$JPATH" --setenv CCMP_LEANCHECKER "${PLC_W:-$W/bin/plc}" \
    -- "$@"
}

# ---------- self-test (every run): the pinned binaries must give the known verdicts on two tiny exports ----------
STCFG=$W/st.json
/usr/bin/python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("enable_nanoda",None); c["external_kernels"]={"gruszka (second kernel)":[sys.argv[3]]}; json.dump(c,open(sys.argv[2],"w"))' \
  "${PIN_PATH[selftest_comparator]}" "$STCFG" "$W/bin/gruszka-kernel" || decline "cannot write the self-test config"
selftest() {  # writes the two exit codes to $W/st.rc
  local g b PLC_W=$W/bin/plc-plain   # the self-test never talks to the incremental process
  runj "$CCMP" "$TC36" "$STCFG" "${PIN_PATH[selftest_challenge]}" "${PIN_PATH[selftest_good]}" > "$W/st_good.log" 2>&1; g=$?
  runj "$CCMP" "$TC36" "$STCFG" "${PIN_PATH[selftest_challenge]}" "${PIN_PATH[selftest_bad]}" > "$W/st_bad.log" 2>&1; b=$?
  echo "$g $b" > "$W/st.rc"
}
selftest_ok() {  # the self-test must have given the known verdicts (good: both kernels accept; bad: rejected)
  local g b; read -r g b < "$W/st.rc" 2>/dev/null || { g=x; b=x; }
  if [ "$g" != 0 ] || ! grep -q '^gruszka (second kernel) kernel accepts the solution$' "$W/st_good.log" \
     || ! grep -q '^Lean default kernel accepts the solution$' "$W/st_good.log" || [ "$b" != 1 ]; then
    log "$(tail -8 "$W/st_good.log" 2>/dev/null)"; log "$(tail -5 "$W/st_bad.log" 2>/dev/null)"
    decline "self-test failed (good rc=$g, bad rc=$b): the pinned binaries cannot run here"
  fi
}
if [ "$PREFLIGHT" = 1 ]; then
  selftest; selftest_ok
  xkst=   # v2.3-H: every enabled extra kernel must give the known verdicts on the two self-test exports
  for n in $XK_ON; do
    "$W/bin/xk-$n" "${PIN_PATH[selftest_good]}" "selftest-$n-good" > /dev/null 2>&1; "$W/bin/xk-$n" "$XK_KBAD" "selftest-$n-bad" > /dev/null 2>&1
    if xk_selftest_ok "$n"; then xkst="$xkst $n:ok"; XK_STATUS[$n]="self-test ok"
    else [ "${XK_MODE[$n]}" != required ] || { XK_ON=; decline "self-test of the required extra kernel $n failed ($XK_ST_WHY)"; }
      xkst="$xkst $n:FAILED(judged runs record 'not decided': $XK_ST_WHY)"; XK_STATUS[$n]="self-test failed"; XK_REASON[$n]=$XK_ST_WHY; fi
  done
  for n in $XK_NAMES; do case "${XK_STATUS[$n]}" in off|"not configured"|"not decided"|"skipped (memory)") xkst="$xkst $n:${XK_STATUS[$n]}";; esac; done
  log "[$SELF] extra kernels:${xkst:- none enabled}"
  XK_ON=
  finish 0 PREFLIGHT_OK "pinned binaries present, sha256 OK, self-test passed"
fi
# judged run: the self-test runs CONCURRENTLY with the judge (off the critical path); the verdict still requires it
selftest & ST_PID=$!
# v2.3-H: the extra veto kernels start now (judged export + their two self-tests), each in a session of its own (setsid) so
# the whole process group can be stopped; nothing of theirs is read before finish -> xk_settle
for n in $XK_ON; do
  setsid "$W/bin/xk-$n" "$W/solution.export" "$n" < /dev/null > /dev/null 2>&1 & XK_PID[$n]=$!
  setsid "$W/bin/xk-$n" "${PIN_PATH[selftest_good]}" "selftest-$n-good" < /dev/null > /dev/null 2>&1 & XK_STPID[$n]=$!
  setsid "$W/bin/xk-$n" "$XK_KBAD" "selftest-$n-bad" < /dev/null > /dev/null 2>&1 & XK_STPID[$n]="${XK_STPID[$n]} $!"
  log "[$SELF] extra kernel $n started (${XK_MODE[$n]}, jobs=$KJOBS)"
done
XK_T0=$(date +%s.%N)

# ---------- the judge ----------
if [ "$TMO" -gt 0 ]; then TPFX=(timeout --kill-after=30 "$TMO"); else TPFX=(); fi
log "[$SELF] ccmp start: threads=$T version=$SOUND_VERSION"
runj "${TPFX[@]}" "$CCMP" "$TC36" "$W/comparator.json" "$W/challenge.export" "$W/solution.export" > "$W/ccmp.log" 2>&1
CCMP_RC=$?
CCMP_WALL=$(echo "$(date +%s.%N) - $XK_T0" | bc | sed 's/^\./0./')
log "$(cat "$W/ccmp.log")"
for f in "$W"/tmp/leg-*.log; do [ -f "$f" ] || continue; log "--- $(basename "$f") (last 64 KiB) ---"; log "$(tail -c 65536 "$f")"; done
LEG_JSON=$(/usr/bin/python3 -I -c '
import json, re, sys
d = {}
for ln in open(sys.argv[1], errors="replace"):
    m = re.match(r"^\[ccmp\] (.*) finished after (\d+) ms$", ln.strip())
    if m: d[m.group(1)] = int(m.group(2))
print(json.dumps(d))' "$W/ccmp.log" 2>/dev/null) || LEG_JSON=null
# v2: structured per-leg status (diagnostics for the caller; the decision below uses only leg_rc and one anchored message)
leg_rc() { local f=$W/tmp/leg-$1.rc; [ -f "$f" ] && head -c 16 -- "$f" | tr -cd '0-9' | cut -c1-5; }
LEGS_JSON=$(/usr/bin/python3 -I - "$W/tmp" "$LEG_JSON" "$W/kept.txt" <<'PY' 2>/dev/null
import json, os, re, sys
d, keptf = sys.argv[1], sys.argv[3]
ms = json.loads(sys.argv[2]) if sys.argv[2] != "null" else {}
def rc(n):
    try:
        s = open(os.path.join(d, "leg-%s.rc" % n), errors="replace").read(16).strip()
    except OSError:
        return None
    return int(s) if s.isdigit() else None
def msg(n, pat):
    try:
        lines = open(os.path.join(d, "leg-%s.log" % n), errors="replace").read(4000000).splitlines()
    except OSError:
        return None
    for i, ln in enumerate(lines):
        if re.search(pat, ln):
            return "\n".join(lines[i:i + 2])[:400]
    return lines[-1][:400] if lines else ""
legs = {"lean": {"rc": rc("lean"), "ms": ms.get("kernel Lean default"),
                 "message": msg("lean", r"^(Lean default kernel|Quotient post-check|Stack overflow|deep recursion|\(kernel\))")},
        "k2": {"rc": rc("k2"), "ms": ms.get("kernel gruszka (second kernel)"),
               "message": msg("k2", r"(?i)accept|reject|error|panic|fatal|declin")}}
# a gruszka run retried with 1 worker after a decline for worker-table room is recorded (wrapper: leg-k2.retry)
try:
    _fr = open(os.path.join(d, "leg-k2.retry"), errors="replace").read(16).strip()
    legs["k2"]["retry"] = {"reason": "a worker table is full", "first_rc": int(_fr) if _fr.isdigit() else None, "workers": 1}
except (OSError, KeyError):
    pass
try:
    # records end with "\n" only (a kernel name may contain "\r"; universal newlines would split it)
    for ln in open(keptf, encoding="utf-8", newline="").read().split("\n"):
        if not ln:
            continue
        i, name = ln.split("\t", 1)
        legs["kept-" + i] = {"name": name, "rc": rc("kept-" + i), "ms": ms.get("kernel " + name),
                             "message": msg("kept-" + i, r"(?i)accept|reject|error|panic|fatal")}
except OSError:
    pass
print(json.dumps({"legs": legs, "compare_ms": ms.get("compare (parse, compareAt, checkAxioms)")}))
PY
) || LEGS_JSON='{"legs":null,"compare_ms":null}'
COMPARE_MS=$(/usr/bin/python3 -I -c 'import json,sys; v=json.loads(sys.argv[1]).get("compare_ms"); print("null" if v is None else int(v))' "$LEGS_JSON" 2>/dev/null) || COMPARE_MS=null
LEGS_JSON=$(/usr/bin/python3 -I -c 'import json,sys; print(json.dumps(json.loads(sys.argv[1]).get("legs")))' "$LEGS_JSON" 2>/dev/null) || LEGS_JSON=null
wait "$ST_PID"; selftest_ok
if [ "$TMO" -gt 0 ] && { [ "$CCMP_RC" = 124 ] || [ "$CCMP_RC" = 137 ]; }; then decline "time limit of $TMO s exceeded"; fi
[ "$(stamp)" = "$STAMP0" ] || decline "an input file was modified during the check"
for name in ccmp pleanchecker gruszka ${PLC_INCR_BIN:+pleanchecker_incr}; do   # the pinned binaries must still be the pinned ones
  [ "$(sha256sum "${PIN_PATH[$name]}" | cut -d' ' -f1)" = "${PIN_SHA[$name]}" ] || decline "pinned $name changed during the run"
done
BASIS="challenge export as given (sha256 checked by the caller); statements + axioms: official Lean $TC_LABEL comparator judge code (ccmp compareAt + checkAxioms); kernel 1: official Lean $TC_LABEL kernel libraries (pleanchecker parallel Lean.Replay walk${INCR:+, incremental/overlapped with the build (PChk/Incr.lean)}); kernel 2: gruszka (independent)"
[ "${XAXJ:-null}" = "[]" ] || BASIS="$BASIS; EXTRA permitted axioms beyond GOAL S1(3) (--extra-axioms): $XAXJ"
# v2: the Lean leg's stack is deliberately smaller than the official walk's, so a stack / deep-recursion failure of OUR leg is
# "could not decide", not a rejection. It is recognised ONLY in that leg's own log, by the exact texts the official code
# prints (Lean.Kernel.Exception.deepRecursion -> "(kernel) deep recursion detected" on a line of its own after Par.lean's
# "while replaying declaration '<name>':"; the runtime's stack_space_exception "deep recursion was detected at '...'";
# the runtime's "Stack overflow detected. Aborting." precedes an abort = exit 134, handled by the exit code). Residual
# (availability only): a declaration name containing two newlines can forge such a line inside the leg's own reject message,
# turning that export's REJECTED into DECLINED; the fix would be a distinct exit code in pleanchecker (binary change).
DEEP_RE='^(\(kernel\) deep recursion detected|Lean default kernel rejects the solution: deep recursion was detected at |deep recursion was detected at |Stack overflow detected\. Aborting\.)$'
lean_deep() { [ -f "$W/tmp/leg-lean.log" ] && grep -qE "$DEEP_RE" "$W/tmp/leg-lean.log"; }
case "$CCMP_RC" in
  0) ;;
  1) # ccmp reports exactly ONE error line: a failure of its own comparison / axiom check, else the first failing kernel
     # leg ('<kernel> exited with N' / 'Error while interacting with <kernel> kernel'). v2: the legs write to their own
     # files, so this is ccmp's OWN first error line; a kernel leg is judged by its recorded exit status (leg_rc, written
     # by the trusted wrapper) and, for the Lean leg, by lean_deep on its own log. Every branch below ends in REJECTED or
     # DECLINED (no verdict): none can produce an ACCEPT.
     ERR=$(grep -m1 -E '^error:' "$W/ccmp.log" | cut -c1-400)
     [ -n "$ERR" ] || decline "ccmp exited 1 without an error line"
     LRC=$(leg_rc lean)
     case "$ERR" in
       "error: Lean default exited with 1")
         # the official-kernel leg rejected (its wrapper must have recorded the same status)
         [ "${LRC:-}" = 1 ] || decline "inconsistent status of the official-kernel leg (ccmp: exited with 1; recorded: '${LRC:-none}'): no verdict"
         if lean_deep; then decline "the official-kernel leg ran out of stack (deep recursion; its stack is smaller than the official walk's): no verdict"; fi
         finish 1 REJECTED "$ERR";;
       "error: Lean default exited with "*|"error: Error while interacting with Lean default kernel"*)
         decline "the official-kernel leg could not finish ($ERR): no verdict";;
       "error: gruszka (second kernel) exited with 1")
         finish 1 REJECTED "$ERR";;
       "error: gruszka (second kernel) exited with "*|"error: Error while interacting with gruszka (second kernel) kernel"*)
         # gruszka: exit 1 = reject; any other exit = it could not decide (decline, crash, kill) -> no verdict, unless the
         # official Lean kernel's own recorded status is a rejection (and not a stack failure)
         if [ "${LRC:-}" = 1 ] && ! lean_deep; then finish 1 REJECTED "$ERR (and the official-kernel leg rejected)"; fi
         decline "the second kernel could not decide ($ERR)";;
       "error: "*" exited with 1")   # a kept config kernel (--keep-config-kernels) rejected: veto
         finish 1 REJECTED "$ERR";;
       "error: "*" exited with "*|"error: Error while interacting with "*)
         decline "a configured kernel could not finish ($ERR): no verdict";;
       *)  # ccmp's own judgment (compareAt / checkAxioms / config / parse of the official comparator code). The judge's
           # messages start with fixed text ("Const not found ...", "Challenge and solution ...", "Axiom '...' is not
           # permitted ...": names only follow it), so a resource failure of ccmp ITSELF is recognised at the start of the
           # message only - export content cannot steer this branch
         if printf '%s\n' "$ERR" | grep -qE '^error: (memory allocation of [0-9]+ bytes failed|out of memory|std::bad_alloc|failed to create thread|resource exhausted|Stack overflow detected|deep recursion was detected at |\(kernel\) deep recursion detected)'; then
           decline "ccmp could not finish ($ERR): no verdict"
         fi
         finish 1 REJECTED "$ERR";;
     esac;;
  2) decline "ccmp could not run: $(grep -m1 -E '^error:' "$W/ccmp.log" | cut -c1-300)";;
  *) decline "ccmp terminated abnormally (rc=$CCMP_RC)";;
esac
# ACCEPT: ccmp's own success and acceptance lines (its log is its own now) AND every leg's recorded exit status 0
grep -q '^Your solution is okay!$' "$W/ccmp.log" || decline "ccmp rc=0 without the official success line"
grep -q '^Lean default kernel accepts the solution$' "$W/ccmp.log" || decline "ccmp rc=0 but no acceptance line of the Lean kernel"
grep -q '^gruszka (second kernel) kernel accepts the solution$' "$W/ccmp.log" || decline "ccmp rc=0 but no acceptance line of the second kernel"
[ "$(leg_rc lean)" = 0 ] || decline "ccmp rc=0 but the official-kernel leg's recorded exit status is '$(leg_rc lean)', not 0"
[ "$(leg_rc k2)" = 0 ] || decline "ccmp rc=0 but the second kernel's recorded exit status is '$(leg_rc k2)', not 0"
while IFS=$'\t' read -r ki kname; do
  [ -n "$ki" ] || continue
  grep -qxF -- "$kname kernel accepts the solution" "$W/ccmp.log" || decline "ccmp rc=0 but no acceptance line of the kept kernel '$kname'"
  [ "$(leg_rc "kept-$ki")" = 0 ] || decline "ccmp rc=0 but the kept kernel '$kname' recorded exit status '$(leg_rc "kept-$ki")', not 0"
done < "$W/kept.txt"
finish 0 ACCEPTED "statements + axioms match the challenge (official judge code); the official Lean $TC_LABEL kernel (parallel replay) and the independent kernel gruszka accept every declaration of the export"
}
main "$@"; exit $?
