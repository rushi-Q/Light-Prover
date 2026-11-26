#!/bin/bash -p
# fastverify NOTARY CHECK (preset `notary`):
#   Maximum-assurance, strictly-offline trusted check with:
#     (1) Unmodified official Lean 4.36 release libraries (NO PGO/ThinLTO rebuild, GLIBC_2.17,
#         zero libstdc++, bit-for-bit reproducible across Intel Ubuntu 22.04 and AMD Ubuntu 24.04;
#         strictly offline Par.lean with zero pleanchecker_incr IPC).
#     (2) R7 Runtime Cross-Leg Canonical Environment SHA-256 Digest Cross-Check:
#         ccmp-notary, pleanchecker-notary, and gruszka-r7 independently hash the exact AST
#         environment they parsed (`fv-env-sha256-v1` across all 3 legs + `fv-env-strict-sha256-v1`
#         across ccmp and pleanchecker). ACCEPTED requires ALL participating legs' SHA-256 digests
#         and constant counts to match bit-for-bit — structurally closing parser differentials and
#         MAP_SHARED TOCTOU split-brain attacks!
#     (3) Selectable vetted independent-kernel matrix (`--kernels gruszka[,con-ron][,con-leche][,nanoda]`,
#         default `gruszka`). gruszka-r7 is ALWAYS run (it is the second kernel of S1(4) and the third,
#         independent parser of the R7 digest; a list without it gets it added, recorded in "kernels"). `all` =
#         gruszka,con-ron,con-leche (the two verified kernels bundled with Lean 4.36; NOT nanoda). Every selected kernel
#         is MANDATORY for ACCEPTED. Each extra kernel's own recorded run is classified by notary_xk_classify (the
#         table of check-sound.sh's xk_classify, adapted to the 4.36 bundle: anchored lines only, resource limits and
#         runtime failures = not decided, nanoda exit 101 in its type checker = rejected, exit 1 = error). Verdicts once
#         the comparison and the official kernel accepted: gruszka exit 1 or a nanoda type-checker rejection ->
#         REJECTED; a con-ron / con-leche rejection -> DECLINED (both treat theorem bodies as opaque, so they reject
#         some valid proofs that unfold a theorem body: a veto, never a REJECTED of their own); any kernel that did not
#         decide -> DECLINED. A rejection by the official kernel or the comparison is REJECTED as before.
#     (4) All check-sound v2 wiring invariants: per-leg isolated stdout/stderr + wrapper-recorded
#         exit statuses, private copies by default, concurrent self-test, post-run ctime + pin re-hash.
#     (5) check/notary/README.md: the R7 gate ALWAYS needs all three
#         digests of the candidate (ccmp, Lean replay, gruszka-r7; never a 2-leg gate) and the report's
#         r7_digest.attestation lists exactly which legs agreed on which digest; digest files and leg status files are
#         parsed strictly (one canonical value per field, nothing else, else DECLINED); the comparator config is first
#         read exactly as the official 4.36 comparator reads it (an official configuration error = DECLINED, never a
#         verdict) and the rewrite of its external kernels is recorded in "config_rewrite"; the self-test's negative
#         control must fail for the expected reason (and its positive control give the pinned digests), bounded by the
#         time limit; evidence-writing failures of the Lean leg or ccmp are DECLINED (not REJECTED); gruszka reads the
#         candidate under an .ndjson name; a gruszka 'unknown constant' rejection (declaration order, not bound by R7) is
#         'not decided'; a concurrent scan vetoes ACCEPTED for fields gruszka-r7 narrows to 32 bits (projection index,
#         bound variable, regular reducibility height >= 2^32); the report is written by a JSON encoder and a --json
#         report that cannot be written means DECLINED.
#     (6) The challenge's configured kernels are run (mandatory, labelled "config kernel <name>",
#         resolved in the judge's kernel environment before anything runs, classified like the selected kernels; no
#         unidentified kernel exit is REJECTED); config numbers are never converted and lone surrogates are normalized as
#         in Lean; one strict status reader feeds gate and report; the negative control checks every leg that ran on it;
#         a lost stdout report exits 2. See check/notary/README.md.
#     (7) Challenge-configured kernels run in their own nested sandbox (read-only work dir, private /tmp), by the
#         `which` path; --challenge-sha256 requires --comparator-sha256; nanoda's 101 on the negative
#         control must name fvCheat. Section 5.6.
#
# Usage:
#   check-notary.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--kernels LIST]
#                   [--json FILE] [--log FILE] [--timeout S] [--workdir DIR]
#                   [--keep-config-kernels] [--hints FILE|none] [--private-inputs]
#   check-notary.sh --preflight [--kernels LIST]
#   --kernels LIST: comma list of gruszka, con-ron, con-leche, nanoda, or 'all' (= gruszka,con-ron,con-leche); gruszka is
#   always run (added if missing). Every listed kernel must accept for ACCEPTED.
# Exit: 0 = ACCEPTED, 1 = REJECTED, 2 = DECLINED (no verdict). Last stdout line = JSON.
# v0.1 STATUS: the notary preset is EXPERIMENTAL. The public CLI runs it only with
# --experimental (bin/fastverify --preset notary / --check CN). This script called directly is not gated; its known
# classification limitations are listed in check/notary/README.md.
main() {
trap '' PIPE   # before the environment guard's refusal write (was set only after it)
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
# SIGPIPE is ignored by the judge shell from here on (before any argument is read): a write to a
# closed stderr / stdout pipe by the shell itself (a failed redirection message, a job-status message) is a failed write,
# never a death by signal 13; the verdict and exit stay the ones finish() reports
trap '' PIPE
set -u
umask 077
T_START=$(date +%s.%N)
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PKGROOT=$(cd "$HERE/../.." && pwd)
SELF=checkNotary
WIRING=check-notary-v1-D13-R7-f3-f6.9.3
FINISHED=0; W=
on_exit() {
  local rc=$?
  [ -n "${ST_PID:-}" ] && kill "$ST_PID" 2>/dev/null && wait "$ST_PID" 2>/dev/null
  [ -n "${VS_PID:-}" ] && kill "$VS_PID" 2>/dev/null && wait "$VS_PID" 2>/dev/null
  [ -n "$W" ] && rm -rf "$W"
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
# every diagnostic write runs in a subshell that ignores SIGPIPE, so a closed stderr / log pipe is
# a failed write (ignored), never a SIGPIPE death of the judge; the verdict's own stdout write is handled in finish()
# (the subshell's own error output goes to /dev/null, the text itself through a saved copy of stderr)
log() { ( trap '' PIPE; exec 3>&2 2>/dev/null; if [ -n "$LOGF" ]; then printf '%s\n' "$*" >> "$LOGF"; else printf '%s\n' "$*" >&3; fi ); }
errmsg() { ( trap '' PIPE; exec 3>&2 2>/dev/null; printf '%s\n' "$*" >&3 ); }
finish() {
  local ex=$1 v=$2 why=$3 now wall tj=null; now=$(date +%s.%N)
  wall=$(echo "$now - $T_START" | bc | sed 's/^\(-\{0,1\}\)\./\10./')   # '-.5' -> '-0.5' (valid JSON)
  case "${T:-}" in ''|*[!0-9]*|0?*) ;; *) tj=$T;; esac   # a canonical decimal only (else null)
  # the report is built by a JSON encoder; every embedded fragment must parse as JSON
  # (numbers as numbers), else the verdict becomes DECLINED; the --json report is written (and checked) BEFORE the
  # stdout line: a report that cannot be written turns any verdict into DECLINED (exit 2). The verdict/exit printed and
  # returned are the encoder's (same as requested unless downgraded); if the encoder itself fails: minimal DECLINED.
  local js rc
  js=$(/usr/bin/python3 -I -c "$F6_REPORT_PY" "${JSONF:-}" \
    s checker "$SELF" s verdict "$v" n exit "$ex" n wall_s "$wall" s reason "$why" n ccmp_rc "${CCMP_RC:-null}" n threads "$tj" \
    s version "${NOTARY_VERSION:-unknown}" s wiring "$WIRING" s kernels "${KERNELS_ARG:-gruszka}" s basis "${BASIS:-}" \
    j binaries_sha256 "${BIN_JSON:-null}" j leg_ms "${LEG_JSON:-null}" j legs "${LEGS_JSON:-null}" n compare_ms "${COMPARE_MS:-null}" \
    j inputs "${INPUTS_JSON:-null}" n private_inputs_asserted "${PRIVIN:-0}" j r7_digest "${R7_JSON:-null}" \
    j kernel_status "${KSTAT_JSON:-null}" j config_rewrite "${CFGRW_JSON:-null}" j veto_scan "${VETO_JSON:-null}" \
    j selftest "${ST_JSON:-null}" s workdir "${W:-}" j pinned_inputs "${PIN_JSON:-null}" 2>/dev/null)
  rc=$?
  case "$rc:$js" in
    [012]:'{'*) trap '' PIPE   # a closed stdout pipe is a write error here, not a SIGPIPE death
                if ! printf '%s\n' "$js"; then   # a lost stdout report is never a verdict
                  [ -z "${JSONF:-}" ] || printf '{"checker":"%s","verdict":"DECLINED","exit":2,"reason":"the report could not be written to standard output: no verdict"}\n' "$SELF" > "$JSONF" 2>/dev/null
                  rc=2
                fi;;
    *) js="{\"checker\":\"$SELF\",\"verdict\":\"DECLINED\",\"exit\":2,\"reason\":\"internal error: the report encoder failed (rc $rc)\"}"
       printf '%s\n' "$js"; [ -z "${JSONF:-}" ] || printf '%s\n' "$js" > "$JSONF" 2>/dev/null; rc=2;;
  esac
  # the diagnostic line states the EFFECTIVE verdict (after any downgrade by the report writer or
  # a failed stdout delivery), the same one stdout and the exit status carry
  local ev; ev=$(printf '%s' "$js" | sed -n 's/^{"checker":"[^"]*","verdict":"\([A-Z_]*\)".*/\1/p')
  case "$rc" in 0|1) [ -n "$ev" ] || ev=$v;; *) ev=DECLINED;; esac
  if [ "$ev" = "$v" ] && [ "$rc" = "$ex" ]; then log "[$SELF] verdict $v (exit $ex): $why"
  else log "[$SELF] verdict $ev (exit $rc): downgraded from $v: the report could not be delivered as such ($why)"; fi
  FINISHED=1
  exit "$rc"
}
# argv: JSONF then (type key value)* with type s = string, n = JSON number or null, j = JSON fragment (object/array/null)
F6_REPORT_PY='
import json, sys
jf, rest = sys.argv[1], sys.argv[2:]
def nocon(x):
    raise ValueError("non-standard JSON constant " + x)
d, bad = {}, []
for i in range(0, len(rest) - 2, 3):
    t, k, val = rest[i], rest[i + 1], rest[i + 2]
    if t == "s":
        d[k] = val
        continue
    try:
        x = None if val in ("", "null") else json.loads(val, parse_constant=nocon)
    except Exception:
        x, _ = None, bad.append(k)
    if t == "n" and not (x is None or (type(x) in (int, float))):
        x, _ = None, bad.append(k)
    if t == "j" and not (x is None or isinstance(x, (dict, list))):
        x, _ = None, bad.append(k)
    d[k] = x
if {"ACCEPTED": 0, "PREFLIGHT_OK": 0, "SCOPE_OK": 0, "REJECTED": 1, "DECLINED": 2}.get(d.get("verdict"), -1) != d.get("exit"):
    bad.append("verdict/exit")
def down(why):
    if d.get("verdict") != "DECLINED" or d.get("exit") != 2:
        d["reason"] = why + " (was %s: %s)" % (d.get("verdict"), d.get("reason"))
    d["verdict"], d["exit"] = "DECLINED", 2
if bad:
    down("internal error: report field(s) %s not valid JSON of the expected type: no verdict" % ", ".join(sorted(set(bad))))
line = json.dumps(d, separators=(",", ":"))
if jf:
    try:
        with open(jf, "w", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception as e:
        down("cannot write the --json report %r (%s): no verdict" % (jf, e))
        line = json.dumps(d, separators=(",", ":"))
        try:
            with open(jf, "w", encoding="utf-8") as f:
                f.write(line + "\n")
        except Exception:
            pass
print(line)
sys.exit(d["exit"])
'
decline() { finish 2 DECLINED "$1"; }
# classification of one kernel leg's OWN recorded run (log + exit status written by the trusted
# wrapper) -> three lines: status (accepted | rejected | not decided), reason, message. The table of check-sound.sh's
# xk_classify (v2.3-H), adapted to the kernels bundled with the official Lean 4.36.0 release (con-leche a6380d68, con-ron
# 4e5616d9, nanoda_bin 0.4.17 8241c5e6; all inside the verified TC36) and to gruszka-r7:
#  gruszka: rc 0 accepted; rc 1 rejected; anything else not decided (2 = gruszka's own decline).
#  con-leche / con-ron (`--help`: 0 accepted, 1 rejected, 2 declined, 3 usage/malformed/internal; con-ron aborts with 134
#   on a failed allocation): rc 0 + 'NAME: accepted N declarations (--verified)' -> accepted (rc 0 without it: not
#   decided); rc 1 + a runtime/resource line NOT written by the kernel itself (no 'NAME: ' prefix) -> not decided; rc 1 +
#   the FIRST 'NAME: invalid: ' / 'con-ron: rejected: ' line whose reason (the text before ' [at ') STARTS with a resource
#   limit ('the kernel refused ', 'resource limit:', 'fuel exhausted:', deep recursion / stack overflow / out of memory /
#   memory allocation) -> not decided; any other such line -> rejected; rc 1 without one -> not decided; rc 2/3 and
#   signals -> not decided. Only fixed text at a fixed position is matched: a declaration name (export content, it follows
#   ' [at ') cannot turn a rejection into 'not decided' or back.
#  nanoda_bin 0.4.17 (config written by ccmp-notary as Lake 4.36 writes it, no print_success_message: an acceptance is
#   exit 0 with no output): rc 0 accepted; rc 101 + FIRST panic location in its checker (src/tc.rs, inductive.rs, quot.rs,
#   expr.rs, level.rs) with a COMPLETE message line from the type-check-failure whitelist (NANODA_DEF)
#   and no resource marker in the log -> rejected (any other checker panic: not decided); rc 101 with
#   another first panic location (parser, limits) -> not decided; rc 1 ('Error: ...' configuration / input / format) and
#   anything else -> not decided.
notary_xk_classify() {
  /usr/bin/python3 -I - "$1" "$2" "$3" <<'PY'
import re, sys
name, logf, rc = sys.argv[1], sys.argv[2], sys.argv[3].strip()
OVERSIZE = False
try:
    with open(logf, "rb") as f:
        raw = f.read((64 << 20) + 1)
    OVERSIZE = len(raw) > (64 << 20)   # never classify from a prefix of a larger log
    text = raw[:64 << 20].decode("utf-8", "replace")
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
if OVERSIZE and rc != 0:
    out("not decided", "kernel log larger than 64 MiB: not classified")
if name == "gruszka":
    if rc == 0:
        out("accepted", "", first(r"^accepted") or "exit 0")
    if rc == 1:
        rj = first(r"^rejected: ")
        # gruszka resolves a constant by its declaration position, the official reader is
        # order-independent and R7 hashes the sorted map (the order is not bound): an 'unknown constant' rejection can be
        # an order artefact (official 4.36 accepts B := A declared before A) -> not decided (DECLINED), never REJECTED
        # (two forms: the checker's 'unknown constant X' (tc.rs infer_const: not visible at this position) and the
        # loader's 'X is not declared before the theorem (rule-p)' (susz read.rs: a proof block names a later constant))
        if re.match(r"rejected: .*: unknown constant ", rj) or re.match(r"rejected: .* is not declared before the theorem \(rule-p\)$", rj):
            out("not decided", "gruszka-r7 rejection by declaration order ('unknown constant' / rule-p; the order is not bound by R7 and the official reader is order-independent)", rj)
        # exit 1 alone is no rejection: gruszka's own complete 'rejected: ' line is required
        if not rj or not re.match(r"rejected: \S", rj) or not re.search("^" + re.escape(rj) + "\n", text, re.M):
            out("not decided", "gruszka exit 1 without a complete 'rejected: ' line", rj)
        out("rejected", "", rj)
    if rc == 2:
        out("not decided", "declined: " + (first(r"^(declined|index invalid)") or first(r"\S")))
elif name in ("con-leche", "con-ron"):
    pfx = name + ": "
    nonstats = [ln for ln in lines if ln.strip() and not ln.startswith(pfx + "stats:")]
    if rc == 0:
        acc = first(r"^" + re.escape(pfx) + r"accepted \d+ declarations \(--verified\)$")
        if acc:
            out("accepted", "", acc)
        out("not decided", "exit 0 without %s's acceptance line" % name)
    if rc == 1:
        rt = first(RES, [ln for ln in lines if not ln.startswith(pfx)])
        if rt:
            out("not decided", "resource failure or runtime panic (exit 1): " + rt)
        inv = first(r"^" + re.escape(pfx) + r"(invalid|rejected): ")
        if not inv:
            out("not decided", "exit 1 without %s's rejection line: " % name + (nonstats[0] if nonstats else "(empty log)"))
        reason = re.sub(r"^" + re.escape(pfx) + r"(invalid|rejected): ", "", inv).split(" [at ", 1)[0]
        if reason.startswith("the kernel refused ") or re.match(r"(resource limit:|fuel exhausted:)", reason):
            out("not decided", "resource limit of %s: " % name + inv)
        if re.match(r"(?i)(deep recursion|stack overflow|out of memory|memory allocation)", reason):
            out("not decided", "resource failure reported as a declaration error: " + inv)
        out("rejected", "", inv)
    if rc == 2:
        out("not decided", "declined (unsupported feature): " + (first(r"^" + re.escape(pfx) + r"(not implemented yet|declined)") or (nonstats[0] if nonstats else "")))
    if rc == 3:
        out("not decided", "error (bad usage, malformed input or internal failure): " + (nonstats[0] if nonstats else "(empty log)"))
elif name == "nanoda":
    NANODA_DEF = re.compile(
        r"assertion failed: self\.def_eq\(u, v\)"
        r"|assertion failed: !self\.ctx\.has_fvars\(info\.ty\)"
        r"|assertion failed: self\.ctx\.no_dupes_all_params\(info\.uparams\)"
        r"|assertion failed: self\.ctx\.all_uparams_defined\((c_uparam, this_declar_info|l, declar_info)\.uparams\)"
        r"|ensur_sort could not produce a sort|ensure_pi could not produce a pi|infer_sort_of could not infer a sort|expected a sort"
        r"|infer_proj prop|Ran out of param telescope|Ran out of constructor telescope( getting field)?"
        r"|no loose bvars allowed in infer|Loose bvars are not allowed"
        r"|non-positive occurrence|Constructor argument was too large for the corresponding inductive type"
        r"|nested types cannot contain locals \(loose bvars found\)"
        r"|Recursors must be derived from an associated inductive \S.*"
        r"|invalid quotient declaration \S.*|Bad `Eq` type; \S.*|cannot add Quot; improperly formed `Eq` type := \S.*"
        r"|assertion failed: self\.is_valid_ind_app\(st, parent_ind_name, ctor_type_cursor\)"
        r"|assertion failed: self\.which_valid_ind_app\(st, ctor_type_cursor\)\.is_some\(\)"
        r"|assertion failed: self\.ctx\.eq_antisymm\(codom_level, st\.block_codom\.unwrap\(\)\)"
        r"|assertion failed: old\.aux_data_ck\(new\)|assertion failed: old_ctor\.aux_data_ck\(&new_ctor\)"
        r"|assertion failed: old_r\.aux_data_ck\(new_r\)|assertion failed: original\.aux_data_ck\(&restored\)")
    if rc == 0:
        out("accepted", "", first(r"^Checked \d+ declarations") or "exit 0")
    if rc == 101:
        P = re.compile(r"^thread '[^']*'(?: \(\d+\))? panicked at (.+):(\d+):(\d+):$")
        for i, ln in enumerate(lines):
            m = P.match(ln)
            if m:
                loc, msg = m.group(1), (lines[i + 1] if i + 1 < len(lines) else "")
                # 'declaration not found in infer_const, X' = nanoda reached a constant it has not
                # loaded (declaration order / an axiom it does not load) - a limitation, never an identified rejection
                if msg.startswith("declaration not found in infer_const"):
                    out("not decided", "nanoda could not resolve a declaration (order / loading limitation, %s:%s): %s" % (loc, m.group(2), msg))
                # 'rejected' only for a COMPLETE message line (terminated by a newline) that
                # identifies a type-check failure - the whitelist below, from nanoda 0.4.17 src/{tc,inductive,quot}.rs -
                # at a checker location, with no resource / runtime marker anywhere in the log. An empty or cut message,
                # the parent's join error ('A thread in `check_all_declars` panicked while being joined'), an unwrap /
                # index / explicit panic or an internal invariant (assert_eq, nesting state) = not decided.
                # resource / runtime failures only from the Rust runtime's own lines
                # (line start: allocation failure, fatal runtime error, a thread that overflowed its stack), never from
                # text that can quote prover-chosen names
                complete = i + 2 < len(lines)
                rt = re.compile(r"(memory allocation of \d+ bytes failed|fatal runtime error: |thread '[^']*'(?: \(\d+\))? has overflowed its stack)")
                if loc in ("src/tc.rs", "src/inductive.rs", "src/quot.rs", "src/expr.rs", "src/level.rs") and complete \
                        and NANODA_DEF.fullmatch(msg) and not any(rt.match(x) for x in lines):
                    out("rejected", "", "nanoda type checker (%s:%s): %s" % (loc, m.group(2), msg))
                if loc in ("src/tc.rs", "src/inductive.rs", "src/quot.rs", "src/expr.rs", "src/level.rs"):
                    out("not decided", "nanoda panic without a complete, identified type-check failure (%s:%s): %s" % (loc, m.group(2), msg or "(no message line)"))
                out("not decided", "panic outside nanoda's type checker (%s:%s): %s" % (loc, m.group(2), msg))
        out("not decided", "exit 101 without a panic location line")
    if rc == 1:
        out("not decided", "error (configuration, input or format): " + (first(r"^Error") or first(r"\S")))
    if rc == 2:
        out("not decided", "declined (format limit): " + (first(r"^Declined") or first(r"\S")))
else:
    out("not decided", "unknown kernel " + name)
why = SIG.get(rc, "exit %d" % rc)
r = first(RES)
out("not decided", why + (": " + r if r else ""))
PY
}
# the official-kernel leg's exit 1 is a proof rejection only with its own COMPLETE rejection message
# (src/Main.lean, PChk/Par.lean): 'Lean default kernel rejects the solution: E' where E is a kernel exception ('(kernel)
# ...') - directly, or after PChk's "while replaying declaration 'X':" on the next line - or one of the replay's structural
# checks (Invalid / No such constructor / recursor, Unexpected quotient declaration, Export record of X differs, C1 (Lean
# #16489)); or 'Quotient post-check rejects the solution: ...'. The line must be newline-terminated. A kernel exception
# that is a resource limit ('(kernel) deep recursion detected / interrupted / deterministic timeout / excessive memory
# consumption detected') is not a rejection. A runtime failure is recognised ONLY on the
# runtime's own lines - a line that STARTS with the Lean runtime's / allocator's / C++ runtime's text (INTERNAL PANIC,
# Stack overflow detected, deep recursion was detected at, uncaught exception:, memory allocation of N bytes failed,
# terminate called, std::bad_alloc, out of memory, failed to create thread, fatal runtime error) - never inside a '[pchk]'
# line or the rejection message (declaration names and pretty-printed terms are chosen by the prover: a name such as
# 'Foo.interrupted_sum' must not turn a rejection into no verdict). Signal deaths are exit statuses (never this branch).
# Prints the rejection line; exit 1 = no definite rejection.
lean_definite_reject() {   # [LOGFILE] (default: the candidate's Lean leg log)
  local f=${1:-$W/tmp/leg-lean.log}
  [ -f "$f" ] || return 1
  /usr/bin/python3 -I - "$f" <<'PY'
import re, sys
try:
    with open(sys.argv[1], "rb") as f:
        raw = f.read((64 << 20) + 1)
except OSError:
    sys.exit(1)
if len(raw) > (64 << 20):   # never decide from a prefix of a larger log
    sys.exit(1)
try:
    text = raw.decode("utf-8")   # a damaged (non-UTF-8) log is no definite evidence
except UnicodeDecodeError:
    sys.exit(1)
lines = text.split("\n")
RT = re.compile(r"(INTERNAL PANIC|Stack overflow detected\. Aborting\.|deep recursion was detected at |uncaught exception: |"
                r"memory allocation of \d+ bytes failed|terminate called |std::bad_alloc|out of memory|failed to create thread|"
                r"fatal runtime error)")
PFX, QPFX = "Lean default kernel rejects the solution: ", "Quotient post-check rejects the solution: "
if any(RT.match(ln) for ln in lines if not ln.startswith("[pchk")):
    sys.exit(1)
KRES = re.compile(r"\(kernel\) (deep recursion detected|interrupted|deterministic timeout|excessive memory consumption detected)\s*")
KX0 = re.compile(r"\(kernel\) \S.*")
class _KX:
    @staticmethod
    def fullmatch(x):
        return KX0.fullmatch(x) and not KRES.fullmatch(x)
KX = _KX
ST = re.compile(r"Invalid (constructor|recursor) \S.*|No such (constructor|recursor) \S.*|Unexpected quotient declaration \S.*|"
                r"Export record of \S.* differs from the kernel's constant|C1 \(Lean #16489\): \S.*")
for i, ln in enumerate(lines):
    done = i + 1 < len(lines)
    if ln.startswith(QPFX):
        # only the post-check's own two messages (src/Main.lean), never an I/O exception text
        if done and re.fullmatch(r"(Could not find quotient constant in final kernel env: |Quotient constant mismatch on: )Quot(\.mk|\.lift|\.ind)?", ln[len(QPFX):]):
            print(ln); sys.exit(0)
        sys.exit(1)
    if ln.startswith(PFX):
        e = ln[len(PFX):]
        if re.fullmatch(r"while replaying declaration '.*':", e):
            if i + 2 < len(lines) and (KX.fullmatch(lines[i + 1]) or ST.fullmatch(lines[i + 1])):
                print(ln + " " + lines[i + 1]); sys.exit(0)
            sys.exit(1)
        if done and (KX.fullmatch(e) or ST.fullmatch(e)):
            print(ln); sys.exit(0)
        sys.exit(1)
sys.exit(1)
PY
}
# test interface (never a verdict): check-notary.sh --lean-classify LOGFILE prints 'rejected' + the definite
# rejection line, or 'not decided'
if [ "${1:-}" = --lean-classify ]; then
  [ $# = 2 ] || { errmsg "usage: check-notary.sh --lean-classify LOGFILE"; FINISHED=1; exit 2; }
  if LREJ=$(lean_definite_reject "$2"); then printf 'rejected\n%s\n' "$LREJ"; else echo "not decided"; fi
  FINISHED=1; exit 2
fi
# test interface (never a verdict): check-notary.sh --xk-classify NAME LOGFILE RC prints the three classification lines
if [ "${1:-}" = --xk-classify ]; then
  [ $# = 4 ] || { errmsg "usage: check-notary.sh --xk-classify gruszka|con-ron|con-leche|nanoda LOGFILE RC"; FINISHED=1; exit 2; }
  notary_xk_classify "$2" "$3" "$4"; FINISHED=1; exit 2
fi
# (gruszka-r7 hashes a lazy proof block's 64-bit projection index / bound-variable index while its
# checker saturates them to 32 bits; it clamps a regular reducibility height to 2^32-1 where Lean takes it mod 2^32):
# until gruszka-r7 is rebuilt, ACCEPTED is vetoed for an export with such a field >= 2^32.
# Only exports gruszka-r7 accepts matter (ACCEPTED needs it), and its packer (vendor/susz/src/pack/json.rs) reads
# numbers only as plain digit runs after ':' / ',' / '[' and JSON whitespace (keys may be escaped): stage 1 = grep for any
# such number >= 2^32 (line number + byte offset only), stage 2 = each candidate line parsed exactly; a candidate line
# that does not parse, has a repeated key, or is a proj / bvar / regular-hint record with a value >= 2^32 vetoes.
# Names with large numeric components and natVal literals (strings) never veto. Any scan failure vetoes (fail-closed).
# grep -a (a NUL byte made grep print 'binary file matches' and nothing else); records split across lines or
# with a NUL never reach ACCEPTED anyway: ccmp-notary's line-oriented JSON reader rejects them.
F6_BIG_RE='[,:[][[:space:]]*([1-9][0-9]{10,}|[5-9][0-9]{9}|4[3-9][0-9]{8}|429[5-9][0-9]{6}|42949[7-9][0-9]{4}|429496[89][0-9]{3}|4294967[3-9][0-9]{2}|429496729[6-9])([^0-9]|$)'
f6_veto_scan() {  # EXPORT OUT_JSON (always writes OUT_JSON; {"veto": false} only after a complete scan)
  local f=$1 out=$2 rc
  LC_ALL=C /usr/bin/grep -a -n -b -E -e "$F6_BIG_RE" -- "$f" | LC_ALL=C /usr/bin/cut -d: -f1,2 > "$out.cand"
  rc=("${PIPESTATUS[@]}")
  if { [ "${rc[0]}" != 0 ] && [ "${rc[0]}" != 1 ]; } || [ "${rc[1]}" != 0 ]; then
    printf '{"veto":true,"reason":"veto scan failed (grep rc %s, cut rc %s)"}\n' "${rc[0]}" "${rc[1]}" > "$out"; return
  fi
  /usr/bin/python3 -I - "$f" "$out.cand" "$out" <<'PY' 2>/dev/null || printf '{"veto":true,"reason":"veto scan failed (stage 2)"}\n' > "$out"
import json, sys
exp, cand, out = sys.argv[1:4]
LIM = 1 << 32
res = {"veto": False, "candidates": 0, "reasons": []}
def dup(pairs):
    ks = [k for k, _ in pairs]
    if len(ks) != len(set(ks)):
        raise ValueError("repeated key")
    return dict(pairs)
def nat(x):
    return type(x) is int and x >= LIM
with open(exp, "rb") as f, open(cand, encoding="ascii") as cf:
    for c in cf:
        lno, off = c.strip().split(":")
        res["candidates"] += 1
        f.seek(int(off))
        raw = f.readline()
        why = None
        try:
            r = json.loads(raw.decode("utf-8"), object_pairs_hook=dup, strict=False)
            if isinstance(r, dict):
                p = r.get("proj")
                if "ie" in r and isinstance(p, dict) and nat(p.get("idx")):
                    why = "projection index %d >= 2^32" % p["idx"]
                if "ie" in r and nat(r.get("bvar")):
                    why = "bound variable index %d >= 2^32" % r["bvar"]
                dd = r.get("def")
                h = dd.get("hints") if isinstance(dd, dict) else None
                if isinstance(h, dict) and nat(h.get("regular")):
                    why = "regular reducibility height %d >= 2^32" % h["regular"]
        except Exception as e:
            why = "line with a number >= 2^32 that does not parse exactly (%s)" % str(e)[:80]
        if why:
            res["veto"] = True
            if len(res["reasons"]) < 8:
                res["reasons"].append("line %s: %s" % (lno, why))
with open(out, "w") as o:
    json.dump(res, o)
PY
}
# test interface (never a verdict): check-notary.sh --veto-scan EXPORT prints the scan result
if [ "${1:-}" = --veto-scan ]; then
  [ $# = 2 ] && [ -f "$2" ] || { errmsg "usage: check-notary.sh --veto-scan EXPORT"; FINISHED=1; exit 2; }
  VT=$(mktemp -d /tmp/checkNotary-veto.XXXXXX) || { FINISHED=1; exit 2; }
  f6_veto_scan "$2" "$VT/veto.json"; cat "$VT/veto.json"; rm -rf "$VT"; FINISHED=1; exit 2
fi

# ---------- arguments ----------
PREFLIGHT=0; SCOPE_ONLY=0
# check-notary.sh --scope-check CHALLENGE_EXPORT COMPARATOR_JSON [--challenge-sha256 HEX
# --comparator-sha256 HEX] = the v0.1 kernel-scope decision alone, for a caller (the public notary preset) that must apply
# it BEFORE anything can give a verdict (a solution build): SCOPE_OK (exit 0) or DECLINED (exit 2), never a verdict on a
# solution. It runs the normal argument, pin, config and cross-version steps on the private copies and stops before any
# kernel (the challenge export stands in for the solution operand; it is never checked).
if [ "${1:-}" = --scope-check ]; then
  SCOPE_ONLY=1; shift
  [ $# -ge 2 ] || { errmsg "usage: check-notary.sh --scope-check CHALLENGE_EXPORT COMPARATOR_JSON [--challenge-sha256 HEX --comparator-sha256 HEX]"; decline "usage"; }
  set -- "$1" "$@"
fi
if [ "${1:-}" = --preflight ]; then PREFLIGHT=1; shift; set -- "$HERE/pins.env" "$HERE/pins.env" "$HERE/pins.env" "$@"; fi
[ $# -ge 3 ] || { errmsg "usage: check-notary.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--kernels gruszka,con-ron,con-leche,nanoda] [--json FILE] [--log FILE] [--timeout S] [--workdir DIR] [--keep-config-kernels] [--hints FILE|none] [--private-inputs] [--challenge-sha256 HEX --comparator-sha256 HEX] | --preflight"; decline "usage"; }
E_IN=$1; C_IN=$2; CFG_IN=$3; shift 3
T=; WD=; JSONF=; TMO=0; KEEPK=1; HINTS=; PRIVIN=0; KERNELS_ARG=gruszka   # the challenge's kernels always run
while [ $# -gt 0 ]; do
  case "$1" in
    --private-inputs) PRIVIN=1; shift;;
    --threads) T=${2:-}; shift 2 || decline "--threads needs a value";;
    --kernels) KERNELS_ARG=${2:-}; shift 2 || decline "--kernels needs a value";;
    --workdir) WD=${2:-}; shift 2 || decline "--workdir needs a value";;
    --json) JSONF=${2:-}; shift 2 || decline "--json needs a value";;
    --timeout) TMO=${2:-}; shift 2 || decline "--timeout needs a value";;
    --keep-config-kernels) KEEPK=1; shift;;   # the default (kept for compatibility)
    --hints) HINTS=${2:-}; shift 2 || decline "--hints needs a value";;
    --log) LOGF=${2:-}; shift 2 || decline "--log needs a value"   # the open error text never reaches stderr
           ( : > "$LOGF" ) 2>/dev/null || { q=$LOGF; LOGF=; decline "cannot write log $q"; };;
    --require-sorried-holes) Q02_RSH=1; shift;;   # Q02: the sorried-hole rule for every release (DECLINED if violated)
    --challenge-sha256) CSHA_PIN=${2:-}; shift 2 || decline "--challenge-sha256 needs a value"; [ -n "$CSHA_PIN" ] || decline "--challenge-sha256 needs a non-empty value";;
    --comparator-sha256) CFGSHA_PIN=${2:-}; shift 2 || decline "--comparator-sha256 needs a value"; [ -n "$CFGSHA_PIN" ] || decline "--comparator-sha256 needs a non-empty value";;
    *) decline "unknown argument '$1'";;
  esac
done
# A run with a pinned challenge (--challenge-sha256) must
# also pin the comparator config (--comparator-sha256); refused before anything runs. Both pins are verified on the private
# copies below and recorded in the report ("pinned_inputs").
if [ "$PREFLIGHT" = 1 ] && { [ -n "${CSHA_PIN:-}" ] || [ -n "${CFGSHA_PIN:-}" ]; }; then
  decline "--preflight checks the pinned binaries and self-test fixtures only; --challenge-sha256 / --comparator-sha256 are not used there: refused"
fi
if [ -n "${CSHA_PIN:-}" ] && [ -z "${CFGSHA_PIN:-}" ]; then
  decline "--challenge-sha256 requires --comparator-sha256 (the sha256 of the official comparator.json): refused"
fi
[ -n "$T" ] || T=$(nproc 2>/dev/null || echo 1)
case "$T" in ''|*[!0-9]*|0) decline "--threads must be a positive number";; esac
# numeric options become plain base-10 integers right after validation (at most 9
# digits; '08' -> 8): the JSON result never carries a zero-padded number and bash arithmetic never reads octal.
[ "${#T}" -le 9 ] || decline "--threads must be a positive number"; T=$((10#$T))
[ "$T" -ge 1 ] || decline "--threads must be a positive number"
case "$TMO" in ''|*[!0-9]*) decline "--timeout must be a number of seconds (0 = none)";; esac
[ "${#TMO}" -le 9 ] || decline "--timeout must be a number of seconds (0 = none)"; TMO=$((10#$TMO))
AS=$(ulimit -v)
if [ "$AS" != unlimited ]; then
  cap=$(( AS / 4194304 )); [ "$cap" -ge 1 ] || cap=1
  if [ "$T" -gt "$cap" ]; then log "[$SELF] address-space limit ${AS} KB: threads $T -> $cap"; T=$cap; fi
fi

# Parse --kernels list (gruszka, con-ron, con-leche, nanoda, all)
USE_GRUSZKA=0; USE_CONRON=0; USE_CONLECHE=0; USE_NANODA=0
if [ "$KERNELS_ARG" = all ]; then KERNELS_ARG="gruszka,con-ron,con-leche"; fi
IFS=',' read -ra KLIST <<< "$KERNELS_ARG"
for k in "${KLIST[@]}"; do
  case "$k" in
    gruszka) USE_GRUSZKA=1;;
    con-ron) USE_CONRON=1;;
    con-leche) USE_CONLECHE=1;;
    nanoda) USE_NANODA=1;;
    '') ;;
    *) decline "unknown kernel in --kernels: '$k' (allowed: gruszka, con-ron, con-leche, nanoda, all)";;
  esac
done
if [ $((USE_GRUSZKA + USE_CONRON + USE_CONLECHE + USE_NANODA)) -eq 0 ]; then
  decline "--kernels must select at least one independent second kernel (S1(4))"
fi
# gruszka-r7 is mandatory: it is the notary's second kernel (S1(4)) and the third parser of the R7
# digest (ccmp and pleanchecker share FastParse + fv_env_digest.c). A list without it gets it added (never dropped silently);
# KERNELS_ARG becomes the effective list in a fixed order (it is what "kernels", the basis and the reason report).
if [ "$USE_GRUSZKA" = 0 ]; then log "[$SELF] --kernels $KERNELS_ARG: gruszka-r7 added (mandatory: second kernel + R7 third parser)"; USE_GRUSZKA=1; fi
KERNELS_ARG=gruszka; [ "$USE_CONRON" = 0 ] || KERNELS_ARG="$KERNELS_ARG,con-ron"
[ "$USE_CONLECHE" = 0 ] || KERNELS_ARG="$KERNELS_ARG,con-leche"; [ "$USE_NANODA" = 0 ] || KERNELS_ARG="$KERNELS_ARG,nanoda"

for f in "$E_IN" "$C_IN" "$CFG_IN"; do
  [ -n "$f" ] || decline "empty input path"
  r=$(readlink -f -- "$f") || decline "cannot resolve '$f'"
  { [ -f "$r" ] && [ ! -p "$r" ] && [ ! -c "$r" ] && [ ! -b "$r" ] && [ ! -S "$r" ]; } || decline "input is not a regular file: '$f'"
done
E_IN=$(readlink -f -- "$E_IN"); C_IN=$(readlink -f -- "$C_IN"); CFG_IN=$(readlink -f -- "$CFG_IN")

# ---------- pinned components ----------
PINS=$HERE/pins.env
[ -f "$PINS" ] || decline "missing $PINS"
NOTARY_VERSION=$(sed -n 's/^NOTARY_VERSION=//p' "$PINS" | head -1)
TC36=$(sed -n 's/^TC36=//p' "$PINS" | head -1)
if [ "$TC36" = @components ]; then
  TC36=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' \
         "$PKGROOT/config/components.json" 2>/dev/null) || decline "cannot read comparator.prefix"
fi
[ -n "$TC36" ] && [ -d "$TC36" ] || decline "official Lean 4.36 toolchain not found ($TC36)"
declare -A PIN_PATH PIN_SHA
while read -r tag name sum path; do
  [ "$tag" = PIN ] || continue
  PIN_PATH[$name]=$path; PIN_SHA[$name]=$sum
done < "$PINS"
BJ="{"; sep=
for name in ccmp_notary pleanchecker_notary gruszka_r7 selftest_comparator selftest_challenge selftest_good selftest_bad; do
  p=${PIN_PATH[$name]:-}; [ -n "$p" ] || decline "pins.env has no PIN for $name"
  [ -f "$p" ] || decline "pinned file missing: $p"
  got=$(sha256sum "$p" | cut -d' ' -f1)
  [ "$got" = "${PIN_SHA[$name]}" ] || decline "sha256 mismatch for $p (got $got, pinned ${PIN_SHA[$name]})"
  BJ="$BJ$sep\"$name\":\"$got\""; sep=,
done
BIN_JSON="$BJ}"
CCMP=${PIN_PATH[ccmp_notary]}; PLC_BIN=${PIN_PATH[pleanchecker_notary]}; GRUSZKA=${PIN_PATH[gruszka_r7]}
/usr/bin/python3 -I "$PKGROOT/lib/toolchain.py" verify "$TC36" leanprover/lean4:v4.36.0 > /dev/null 2>&1 \
  || decline "official Lean 4.36 toolchain at $TC36 does not verify"

# Verify any requested bundled 4.36 external kernels exist inside the verified TC36
CONRON_BIN="$TC36/bin/con-ron"
CONLECHE_BIN="$TC36/bin/con-leche"
NANODA_BIN="$TC36/bin/nanoda_bin"
[ "$USE_CONRON" = 0 ] || [ -x "$CONRON_BIN" ] || decline "missing bundled con-ron at $CONRON_BIN"
[ "$USE_CONLECHE" = 0 ] || [ -x "$CONLECHE_BIN" ] || decline "missing bundled con-leche at $CONLECHE_BIN"
[ "$USE_NANODA" = 0 ] || [ -x "$NANODA_BIN" ] || decline "missing bundled nanoda_bin at $NANODA_BIN"

# ---------- private workdir & private inputs ----------
if [ "$PREFLIGHT" = 1 ]; then WD=/tmp; fi
if [ -z "$WD" ]; then
  if [ "$(stat -c %s -- "$E_IN")" -le 4294967296 ] && [ "$(stat -c %s -- "$C_IN")" -le 4294967296 ]; then WD=/tmp; else WD=$(dirname "$E_IN"); fi
fi
W=$(mktemp -d "$WD/.checkNotary.XXXXXX" 2>/dev/null) || W=$(mktemp -d "/tmp/checkNotary.XXXXXX") || decline "cannot create work dir"
W=$(/usr/bin/realpath -e -- "$W") || decline "cannot resolve the work dir $W"   # symlinked / relative --workdir
chmod 755 "$W"
mkdir -p "$W/bin" "$W/tmp" "$W/home"
priv() {
  if [ "${3:-}" = link-ok ] && [ "$PRIVIN" = 1 ] && [ "$(stat -c %s -- "$1")" -gt 4294967296 ]; then
    if ln -- "$1" "$2" 2>/dev/null; then echo link; return 0; fi
  fi
  cp --reflink=auto -- "$1" "$2" || return 1
  echo copy
}
if [ "$PREFLIGHT" = 1 ]; then
  cp -- "${PIN_PATH[selftest_good]}" "$W/solution.export"
  cp -- "${PIN_PATH[selftest_challenge]}" "$W/challenge.export"
  cp -- "${PIN_PATH[selftest_comparator]}" "$W/comparator.orig.json"
else
  PRIV_E=$(priv "$E_IN" "$W/solution.export" link-ok) || decline "cannot copy export into $W"
  PRIV_C=$(priv "$C_IN" "$W/challenge.export") || decline "cannot copy challenge export into $W"
  cp -- "$CFG_IN" "$W/comparator.orig.json" || decline "cannot copy config"
  INPUTS_JSON=$(printf '{"export":{"size":%s,"private":"%s"},"challenge":{"size":%s,"private":"%s"}}' \
    "$(stat -c %s -- "$E_IN")" "$PRIV_E" "$(stat -c %s -- "$C_IN")" "$PRIV_C")
  priv_note=""; [ "$PRIVIN" = 1 ] && priv_note="; --private-inputs asserted by caller"
  log "[$SELF] private inputs: export $PRIV_E ($(stat -c %s -- "$E_IN") bytes), challenge $PRIV_C$priv_note"
fi
case "$W$PLC_BIN$GRUSZKA$CONRON_BIN$CONLECHE_BIN$NANODA_BIN$T" in *[\"\\\$\`]*|*$'\n'*) decline "shell-special character in path";; esac

: > "$W/hints"
if [ -z "$HINTS" ] && [ -f "$PKGROOT/check/sound/hints/default.txt" ]; then HINTS=$PKGROOT/check/sound/hints/default.txt; fi
if [ "$HINTS" = none ]; then HINTS=; fi
if [ -n "$HINTS" ]; then
  { [ -f "$HINTS" ] && [ "$(stat -c %s -- "$HINTS")" -le 16777216 ]; } || decline "--hints invalid"
  cp -- "$HINTS" "$W/hints" || decline "cannot copy hints"
fi
# NDJSON sniffing: gruszka-r7 packs a FILE.ndjson as NDJSON but sniffs the first byte of any other name
# (a leading space on the metadata line sent a valid export to its binary Susz reader: 'bad magic', exit 1, REJECTED):
# the candidate is handed to it under an .ndjson name (a relative symlink inside the private work dir; no ctime change)
if [ "$PREFLIGHT" != 1 ]; then ln -s solution.export "$W/solution.ndjson" || decline "cannot name the private copy for gruszka-r7"; fi
stamp() { stat -c '%i %s %y %z' -- "$W/solution.export" "$W/challenge.export"; }
STAMP0=$(stamp)

# ---------- per-leg wrappers (isolated stdout/stderr + recorded exit status + R7 digest out) ----------
PLC_STACK_KB=917376
cat > "$W/bin/plc" <<EOF
#!/bin/sh
for a do shift; [ "\$a" = --silent ] || set -- "\$@" "\$a"; done
for a do L=\$a; done
case "\$L" in
  "$W/solution.export") N=lean; DOUT="$W/tmp/digest-lean.txt";;
  *) N=selftest-lean-\$(basename "\$L"); DOUT="$W/tmp/digest-selftest-lean-\$(basename "\$L").txt";;
esac
PCHK_PRIO_FILE="$W/hints" PCHK_SLOW_MS=10000 PCHK_DIGEST_OUT="\$DOUT" LEAN_STACK_SIZE_KB=$PLC_STACK_KB "$PLC_BIN" -j$T -v "\$@" > "$W/tmp/leg-\$N.log" 2>&1
rc=\$?; echo "\$rc" > "$W/tmp/leg-\$N.rc.tmp" && mv -f "$W/tmp/leg-\$N.rc.tmp" "$W/tmp/leg-\$N.rc"; exit \$rc
EOF

# the end of the judge's --timeout budget (epoch s; 0 = none) for the gruszka wrapper's retry - counted from
# now, before the judge starts the run its timeout covers, so never later than that timeout
DL=0; [ "$TMO" -gt 0 ] && DL=$(( $(date +%s) + TMO ))
cat > "$W/bin/gruszka-kernel" <<EOF
#!/bin/sh
[ \$# = 1 ] || { echo "gruszka wrapper: expected 1 argument" >&2; exit 2; }
case "\$1" in
  "$W/solution.export") N=k2; DOUT="$W/tmp/digest-k2.txt"; IN="$W/solution.ndjson";;
  *) N=selftest-k2-\$(basename "\$1"); DOUT="$W/tmp/digest-selftest-k2-\$(basename "\$1").txt"; IN=\$1;;
esac
# Availability: a gruszka decline ONLY for worker-table room depends on the schedule (a
# declaration that runs before the results it reuses exist evaluates them again and can fill its worker's tables), not on
# the input's validity: the judged export's leg runs gruszka ONCE more with 1 worker (the deterministic schedule:
# file/namespace order) and keeps that answer. Trigger (all of it): the judged export (never a self-test), exit
# status exactly 2, a complete log (non-empty, ends with a newline), every line is 'note: ...' except exactly one
# 'declined: ' line, which is the LAST line and ends ': a worker table is full'. Anything else is never retried (residual:
# gruszka prints names unescaped; a crafted name can at most cause this one extra run). The retry runs only inside the
# REMAINING time of the judge's --timeout (DL; none left: no retry; over it: killed, exit 124/137 = no verdict from
# gruszka), and only if the first attempt's log could be archived (leg-<leg>-retries.log; first exit status in
# leg-<leg>.retry -> judge JSON legs.k2.retry). A retry ended by a signal keeps its exit status (128+n): gruszka gave no
# verdict, and the judge's existing rule decides (README). Veto-only (S1(4)): ACCEPTED still needs the official-kernel
# leg and the comparison.
DL=$DL
w=$T
# (notary only) the R7 digest file is removed before the FIRST attempt as well (status 2 if it cannot be)
rm -f "\$DOUT"; [ ! -e "\$DOUT" ] || { echo "gruszka wrapper: cannot remove an old R7 digest" > "$W/tmp/leg-\$N.log"; echo 2 > "$W/tmp/leg-\$N.rc.tmp" && mv -f "$W/tmp/leg-\$N.rc.tmp" "$W/tmp/leg-\$N.rc"; exit 2; }
GRUSZKA_DIGEST_OUT="\$DOUT" "$GRUSZKA" "\$IN" \$w > "$W/tmp/leg-\$N.log" 2>&1; rc=\$?
if [ "\$N" = k2 ] && [ "\$rc" -eq 2 ] && [ \$w -gt 1 ] && [ -s "$W/tmp/leg-\$N.log" ] && [ -z "\$(tail -c 1 "$W/tmp/leg-\$N.log")" ] \\
    && awk 'BEGIN { d = 0; bad = 0 } /^declined: / { d++ } { last = \$0; if (\$0 !~ /^(declined|note): /) bad = 1 }
            END { exit !(d == 1 && !bad && last ~ /^declined: .*: a worker table is full\$/) }' "$W/tmp/leg-\$N.log"; then
  left=; [ "\$DL" -gt 0 ] && left=\$(( DL - \$(date +%s) ))
  if [ -n "\$left" ] && [ "\$left" -le 0 ]; then
    { cat "$W/tmp/leg-\$N.log"; echo "[gruszka wrapper] declined for worker-table room: no time left for a 1-worker retry"; } >> "$W/tmp/leg-\$N-retries.log"
  elif { cat "$W/tmp/leg-\$N.log"; echo "[gruszka wrapper] declined for worker-table room: again with 1 worker\${left:+ (at most \$left s)}"; } >> "$W/tmp/leg-\$N-retries.log" \\
      && echo "\$rc" > "$W/tmp/leg-\$N.retry" && rm -f "\$DOUT" && [ ! -e "\$DOUT" ] && :; then
    w=1
    if [ -n "\$left" ]; then GRUSZKA_DIGEST_OUT="\$DOUT" /usr/bin/timeout --kill-after=5 "\$left" "$GRUSZKA" "\$IN" \$w > "$W/tmp/leg-\$N.log" 2>&1; rc=\$?
    else GRUSZKA_DIGEST_OUT="\$DOUT" "$GRUSZKA" "\$IN" \$w > "$W/tmp/leg-\$N.log" 2>&1; rc=\$?; fi
    [ "\$rc" -le 2 ] || echo "[gruszka wrapper] the 1-worker retry ended with exit \$rc (signal or time limit): no verdict from gruszka" >> "$W/tmp/leg-\$N-retries.log"
  fi
fi
# (notary) the status file is written atomically, once, after the last attempt
echo "\$rc" > "$W/tmp/leg-\$N.rc.tmp" && mv -f "$W/tmp/leg-\$N.rc.tmp" "$W/tmp/leg-\$N.rc"; exit \$rc
EOF

# Cap jobs for con-leche / con-ron cleanly (con-leche aborts if uncapped on 96+ cores!)
T_CL=$T; [ "$T_CL" -gt 32 ] && T_CL=32
cat > "$W/bin/con-ron-kernel" <<EOF
#!/bin/sh
[ \$# = 1 ] || exit 2
case "\$1" in "$W/solution.export") N=con-ron;; *) N=selftest-con-ron-\$(basename "\$1");; esac
"$CONRON_BIN" --verified --jobs=$T_CL "\$1" > "$W/tmp/leg-\$N.log" 2>&1
rc=\$?; echo "\$rc" > "$W/tmp/leg-\$N.rc.tmp" && mv -f "$W/tmp/leg-\$N.rc.tmp" "$W/tmp/leg-\$N.rc"; exit \$rc
EOF

cat > "$W/bin/con-leche-kernel" <<EOF
#!/bin/sh
[ \$# = 1 ] || exit 2
case "\$1" in "$W/solution.export") N=con-leche;; *) N=selftest-con-leche-\$(basename "\$1");; esac
"$CONLECHE_BIN" --verified --jobs=$T_CL "\$1" > "$W/tmp/leg-\$N.log" 2>&1
rc=\$?; echo "\$rc" > "$W/tmp/leg-\$N.rc.tmp" && mv -f "$W/tmp/leg-\$N.rc.tmp" "$W/tmp/leg-\$N.rc"; exit \$rc
EOF

cat > "$W/bin/nanoda-kernel" <<EOF
#!/bin/sh
[ \$# = 1 ] || exit 2
# nanoda gets ccmp-notary's generated config (its export_file_path names the export)
case "\$(head -c 65536 "\$1")" in
  *'"export_file_path":"$W/solution.export"'*) N=nanoda;;
  *'"export_file_path":"${PIN_PATH[selftest_good]}"'*) N=selftest-nanoda-$(basename "${PIN_PATH[selftest_good]}");;
  *'"export_file_path":"${PIN_PATH[selftest_bad]}"'*) N=selftest-nanoda-$(basename "${PIN_PATH[selftest_bad]}");;
  *) N=nanoda-unknown;;
esac
"$NANODA_BIN" "\$1" > "$W/tmp/leg-\$N.log" 2>&1
rc=\$?; echo "\$rc" > "$W/tmp/leg-\$N.rc.tmp" && mv -f "$W/tmp/leg-\$N.rc.tmp" "$W/tmp/leg-\$N.rc"; exit \$rc
EOF

printf '#!/bin/sh\ncommand -v "$1"\n' > "$W/bin/which"
chmod 755 "$W/bin/plc" "$W/bin/gruszka-kernel" "$W/bin/con-ron-kernel" "$W/bin/con-leche-kernel" "$W/bin/nanoda-kernel" "$W/bin/which"

# ---------- config rewrite ----------
: > "$W/kept.txt"
CFGMSG=$(/usr/bin/python3 -I - "$W/comparator.orig.json" "$W/comparator.json" "$W" "$KEEPK" \
  "$USE_GRUSZKA" "$USE_CONRON" "$USE_CONLECHE" "$USE_NANODA" "$T" "$TC36" <<'PY' 2>&1
import json, os, shlex, sys
src, dst, W = sys.argv[1], sys.argv[2], sys.argv[3]
keep = sys.argv[4] == "1"
u_gz, u_cr, u_cl, u_na = [x == "1" for x in sys.argv[5:9]]
threads = int(sys.argv[9])
TC36 = sys.argv[10]
def no_dups(pairs):
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)): raise ValueError("duplicate key")
    return dict(pairs)
def bad_const(x): raise ValueError(f"non-standard JSON constant {x}")
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
if not isinstance(c, dict): sys.exit("config is not a JSON object")
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
q02_allow = []
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
ek = c.get("external_kernels")
if c.get("enable_nanoda") is True and isinstance(ek, dict) and len(ek) > 0:
    sys.exit("enable_nanoda together with external_kernels")
kernels = {}
if keep:
    if isinstance(ek, dict): kernels.update(ek)
    if c.get("enable_nanoda") is True: kernels["nanoda"] = ["nanoda_bin"]
# v0.1 scope: the only challenge-configured kernel the notary runs is the bundled
# nanoda registration exactly as Lake's documented template / enable_nanoda gives it ({"nanoda": ["nanoda_bin"]}); any
# other configured kernel = no verdict (use --preset reference: the official stage applies Lake's rules). The general code below
# stays for post-release. (A challenge judged by a release other than 4.36 is checked after the cross-version gate.)
if kernels and kernels != {"nanoda": ["nanoda_bin"]}:
    sys.exit("v0.1 scope: the notary runs no challenge-configured kernel other than the bundled nanoda registration "
             "({\"nanoda\": [\"nanoda_bin\"]} or enable_nanoda: true); this config declares %s - no verdict, use --preset "
             "reference (the package's official comparator stage applies Lake's rules to that configuration)" % json.dumps(sorted(kernels), ensure_ascii=True)[:200])
# the challenge's kernels are run by default (Lake's kernel set: a
# notary ACCEPTED needs every challenge-configured kernel to accept). Every kept command must resolve, as `which` resolves
# it in the judge's kernel environment (PATH = TC36/bin:/usr/bin:/bin; the judge's wrapper directory is not searched), to a
# regular executable visible inside the sandbox - else no verdict BEFORE anything runs (Lake stops with exit 2 when it
# cannot resolve a configured kernel; resolving later would let the comparison deliver a REJECTED first). The wrapper runs the resolved
# path. Each kept kernel gets its own execution label "config kernel <name>" (it can no longer collide with the notary's
# own kernels; a name containing "noda" keeps ccmp's nanoda config argument, as in Lake) and a class: the bundled
# nanoda_bin / con-ron / con-leche of TC36 are classified by notary_xk_classify like the selected ones; any other kernel's
# non-zero exit is not an identified proof rejection (DECLINED, never REJECTED). kept.txt = "<i>\t<class>\t<label>".
def resolve_exe(x):   # -> (the path `which` prints = what Lake runs and binds, its realpath = identity/class) or None
    # resolved in the package's official comparator invocation environment (check/official/check.sh: env -i
    # PATH=<release toolchain>/bin:/usr/bin:/bin) - the reference for "Lake would start" - and the same executable is then
    # bound read-only into the judge's sandbox and the kernel's own sandbox at that path (as Lake binds kernelExe)
    cands = [x] if "/" in x else [os.path.join(d, x) for d in (os.path.join(TC36, "bin"), "/usr/bin", "/bin")]
    for p in cands:
        if not os.path.isabs(p) or any(c in p for c in "\n\t\0"):
            return None
        if os.path.isfile(p) and os.access(p, os.X_OK):
            return p, os.path.realpath(p)
    return None
BUNDLED = {os.path.realpath(os.path.join(TC36, "bin", b)): k for b, k in (("nanoda_bin", "nanoda"), ("con-ron", "con-ron"), ("con-leche", "con-leche"))}
kept_map = {}
kexes = []
with open(os.path.join(W, "kept.txt"), "w", encoding="utf-8") as kf:
    for i, (name, cmd) in enumerate(sorted(kernels.items())):
        # as Lake - a non-empty executable (cmd[0]); later arguments may be empty strings
        if not (isinstance(cmd, list) and cmd and all(isinstance(x, str) for x in cmd) and cmd[0]):
            sys.exit(f"external kernel {name!r} has no usable command")
        if "\n" in name or "\t" in name:
            sys.exit(f"external kernel name with newline/tab: {name!r}")
        res = resolve_exe(cmd[0])
        if res is None:
            sys.exit(f"external kernel {name!r}: command {cmd[0]!r} was not found in the judge's kernel environment "
                     f"(PATH {TC36}/bin:/usr/bin:/bin, visible in the sandbox; Lake stops with exit 2 on an unresolvable kernel)")
        wp_exe, rp = res
        cls = BUNDLED.get(rp, "other")
        label = "config kernel " + name
        wp = os.path.join(W, "bin", f"kept-{i}")
        # the kernel runs by the `which` path in its OWN sandbox, built like Lake's (Lake/CLI/Check.lean
        # buildSandboxArgs for runExternalKernel): / read-only, tmpfs over /home /root /tmp /run /var, a clean environment
        # (LEAN_ABORT_ON_PANIC=1, HOME=/tmp/home), and only the inputs Lake supplies bound back read-only: its last argument
        # (the generated config for a "noda" kernel, else the export), the export, the executable and the release prefix.
        # The judge's work dir (other legs' status, log and R7 digest files) is not reachable; the kernel writes only its
        # own log through the file descriptor the trusted wrapper opened.
        sol = os.path.join(W, "solution.export")
        iso = ["/usr/bin/bwrap", "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/tmp", "--dir", "/tmp/home",
               "--dev", "/dev", "--proc", "/proc", "--clearenv", "--tmpfs", "/run", "--tmpfs", "/var",
               "--ro-bind", "@LAST@", "@LAST@", "--ro-bind", sol, sol, "--ro-bind", wp_exe, wp_exe, "--ro-bind", TC36, TC36,
               "--setenv", "LEAN_ABORT_ON_PANIC", "1", "--setenv", "HOME", "/tmp/home",
               "--unshare-all", "--die-with-parent", "--new-session", "--chdir", "/tmp", "--"]
        kexes.append(wp_exe)
        with open(wp, "w", encoding="utf-8") as f:
            f.write("#!/bin/sh\nfor a do L=$a; done\n%s \"$@\" > %s 2>&1\nrc=$?; echo \"$rc\" > %s && mv -f %s %s; exit $rc\n" % (
                " ".join('"$L"' if x == "@LAST@" else shlex.quote(x) for x in iso + [wp_exe] + cmd[1:]),
                shlex.quote(os.path.join(W, "tmp", f"leg-kept-{i}.log")),
                shlex.quote(os.path.join(W, "tmp", f"leg-kept-{i}.rc.tmp")), shlex.quote(os.path.join(W, "tmp", f"leg-kept-{i}.rc.tmp")),
                shlex.quote(os.path.join(W, "tmp", f"leg-kept-{i}.rc"))))
        os.chmod(wp, 0o755)
        kept_map[label] = [wp]
        kf.write(f"{i}\t{cls}\t{label}\n")
kernels = kept_map   # labels are distinct: "config kernel " + distinct names; the notary's own labels never start so
with open(os.path.join(W, "kept-exes.txt"), "w", encoding="utf-8") as f:   # bound read-only into the judge's sandbox
    f.write("".join(x + "\n" for x in sorted(set(kexes))))

if u_gz: kernels["gruszka (second kernel)"] = [os.path.join(W, "bin", "gruszka-kernel")]
if u_cr: kernels["con-ron (verified)"] = [os.path.join(W, "bin", "con-ron-kernel")]
if u_cl: kernels["con-leche (verified)"] = [os.path.join(W, "bin", "con-leche-kernel")]
if u_na: kernels["nanoda (bundled)"] = [os.path.join(W, "bin", "nanoda-kernel")]
# only the keys of Lake.Check.Config go to the private config - the official decoder ignores every
# other key, and Python would re-serialize an ignored finite number such as 1e309 as the non-JSON token Infinity
c = {k: v for k, v in c.items() if k in ("challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms",
                                 "enable_nanoda", "external_kernels")}
c.pop("enable_nanoda", None)
c["external_kernels"] = kernels
# no nanoda_threads: ccmp-notary then generates num_threads=4 for nanoda-style kernels, as Lake does
with open(dst, "w", encoding="utf-8") as f:
    json.dump(c, f, ensure_ascii=False)
# the intentional rewrite, recorded in the report ("config_rewrite")
rw = {"mode": "keep-config-kernels" if keep else "replace",
      "challenge_external_kernels": sorted(off_ek or {}), "challenge_enable_nanoda": off_en,
      "dropped": [] if keep else sorted(off_ek or {}) + (["nanoda (enable_nanoda)"] if off_en is True else []),
      "judge_external_kernels": sorted(kernels),
      "note": "the challenge's configured kernels are run (mandatory, labelled 'config kernel <name>') next to the "
              "notary's own kernels (gruszka-r7 + --kernels)"}
with open(os.path.join(W, "cfgrw.json"), "w", encoding="utf-8") as f:
    json.dump(rw, f, ensure_ascii=False)
PY
) || decline "config refused: $CFGMSG"
CFGRW_JSON=$(head -c 65536 "$W/cfgrw.json" 2>/dev/null) || decline "config rewrite record missing"
[ "$PREFLIGHT" = 1 ] && CFGRW_JSON=
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
  PIN_JSON="{\"challenge_sha256\":\"$CSHA_GOT\",\"comparator_sha256\":\"$CFGSHA_GOT\",\"challenge_pinned\":$([ -n "${CSHA_PIN:-}" ] && echo true || echo false),\"comparator_pinned\":$([ -n "${CFGSHA_PIN:-}" ] && echo true || echo false)}"
fi
# cross-version gate on the PRIVATE copies (check/xversion/xvcheck.py): the release
# that exported the challenge must be admitted (releases.json) and its extra comparator rules must hold (4.37: challenge
# definitions sorried). rc 0 + OK -> continue; rc 1 + REJECTED -> REJECTED; anything else -> no verdict.
if [ "${PREFLIGHT:-0}" != 1 ]; then
  XVPY=$PKGROOT/check/xversion/xvcheck.py
  [ -f "$XVPY" ] || decline "xversion gate: check/xversion/xvcheck.py missing"
  # the ORIGINAL file, as the package's official comparator stage (check/official/check.sh) gives
  # it to this gate: until that reference stage uses the shared decoder, a config it refuses gets no verdict here either
  /usr/bin/python3 -I "$XVPY" "$W/challenge.export" "$W/comparator.orig.json" --releases "$PKGROOT/check/xversion/releases.json" ${Q02_RSH:+--require-sorried-holes} \
    --json "$W/xversion.json" > "$W/xversion.out" 2>&1
  XV_RC=$?
  XV_V=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict",""))' "$W/xversion.json" 2>/dev/null)
  XV_REASON=$(/usr/bin/python3 -I -c 'import json,sys; print(str(json.load(open(sys.argv[1])).get("reason",""))[:300])' "$W/xversion.json" 2>/dev/null)
  # v0.1 scope: the official stage judges a challenge of release >= 4.37 with THAT release (its own
  # bundled kernels and kernel-name rules); the notary runs only the 4.36 release's nanoda: configured kernels on such a
  # challenge = no verdict. Decided BEFORE the cross-version verdict (a release-rule failure of an
  # out-of-scope challenge is reported as the scope decline, with the --preset reference guidance); a release that is
  # unknown here counts as out of scope for configured kernels.
  XV_VER=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("lean_version",""))' "$W/xversion.json" 2>/dev/null)
  if [ -s "$W/kept.txt" ]; then
    /usr/bin/python3 -I -c 'import re,sys; m=re.match(r"(\d+)\.(\d+)", sys.argv[1]); sys.exit(0 if m and (int(m.group(1)), int(m.group(2))) < (4, 37) else 1)' "$XV_VER" \
      || decline "v0.1 scope: the challenge is Lean ${XV_VER:-unknown (the cross-version gate could not identify the release)}; the official stage judges a Lean >= 4.37 challenge with that release and its bundled kernels, the notary runs only the 4.36 nanoda: challenge-configured kernels on it = no verdict (use --preset reference)"
  fi
  # --scope-check ends here: the challenge and its comparator config are within the v0.1 notary scope
  # (the release rule itself is the caller's own cross-version gate; no kernel ran, nothing about a solution is claimed)
  if [ "$SCOPE_ONLY" = 1 ]; then
    # SCOPE_OK only with an identified release and a gate that completed (OK or a release-rule
    # REJECTED, which the caller's own gate reports); a challenge the gate could not read = DECLINED
    { [ "$XV_RC" = 0 ] || [ "$XV_RC" = 1 ]; } && printf '%s' "$XV_VER" | grep -qE '^[0-9]+\.[0-9]+' \
      || decline "scope check: the cross-version gate could not identify the challenge's release (rc=$XV_RC): $XV_REASON"
    BASIS="notary preset: v0.1 kernel-scope check only (config validated, configured kernels within scope, release identified); no kernel ran"
    finish 0 SCOPE_OK "within the v0.1 notary scope (Lean ${XV_VER:-unknown}; challenge-configured kernels: $([ -s "$W/kept.txt" ] && echo 'the bundled nanoda registration' || echo none))"
  fi
  if [ "$XV_RC" = 0 ] && [ "$XV_V" = OK ]; then
    :
  elif [ "$XV_RC" = 1 ] && [ "$XV_V" = REJECTED ]; then
    finish 1 REJECTED "xversion: $XV_REASON"
  else
    decline "xversion gate failed (rc=$XV_RC): $XV_REASON"
  fi
fi

JPATH="$W/bin:$TC36/bin:/usr/bin:/bin"
CCMP_DIR=$(dirname "$CCMP"); PLC_DIR=$(dirname "$PLC_BIN"); GZ_DIR=$(dirname "$GRUSZKA")
KEXE_BINDS=()   # each challenge-configured kernel's resolved executable, read-only at its path (as Lake binds it)
while IFS= read -r kx; do [ -n "$kx" ] && KEXE_BINDS+=(--ro-bind "$kx" "$kx"); done < <(cat "$W/kept-exes.txt" 2>/dev/null)
runj() {
  env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session \
    --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dev /dev --proc /proc \
    --ro-bind "$TC36" "$TC36" --ro-bind "$CCMP_DIR" "$CCMP_DIR" \
    --ro-bind "$PLC_DIR" "$PLC_DIR" --ro-bind "$GZ_DIR" "$GZ_DIR" \
    --ro-bind "$W" "$W" "${KEXE_BINDS[@]}" \
    --bind "$W/tmp" "$W/tmp" --bind "$W/home" "$W/home" --chdir "$W" \
    --setenv HOME "$W/home" --setenv TMPDIR "$W/tmp" --setenv LANG C.UTF-8 --setenv LEAN_ABORT_ON_PANIC 1 \
    --setenv LEAN_NUM_THREADS "$T" --setenv PATH "$JPATH" --setenv CCMP_LEANCHECKER "$W/bin/plc" \
    --setenv CCMP_DIGEST_OUT "${CCMP_DOUT:-$W/tmp/digest-ccmp.txt}" \
    -- "$@"
}

# every wrapper records its status atomically (write leg-X.rc.tmp, then rename): a status file is absent or complete
# (a wrapper killed by the sandbox teardown after an early comparator stop no longer leaves an empty leg-X.rc behind).
# a leg's recorded exit status is exactly what its wrapper writes ('echo "$rc"': a canonical decimal
# 0..255 and one newline, a regular file of at most 4 bytes); anything else = no status (prints nothing). Before, non-digits
# were stripped, so damaged status text could read as 0.
# ONE reading per status file: leg_rc_load reads every leg-*.rc of $W/tmp once (opened O_NOFOLLOW |
# O_NONBLOCK, the OPENED descriptor must be a regular file of at most 4 bytes holding exactly "N\n", N <= 255; anything else
# = present but no valid status); leg_rc / leg_present answer from that single reading, for the gate, the classifier and
# the report alike. Called after the self-test controls (--preflight) / after ccmp and the self-test finished.
declare -A LRC_MEMO=() LRC_PRESENT=()
leg_rc_load() {
  local n v
  LRC_MEMO=(); LRC_PRESENT=()
  while IFS=$'\t' read -r n v; do [ -n "$n" ] || continue; LRC_PRESENT[$n]=1; LRC_MEMO[$n]=$v; done < <(/usr/bin/python3 -I -c '
import os, re, stat, sys
d = sys.argv[1]
for e in sorted(os.listdir(d)):
    if not (e.startswith("leg-") and e.endswith(".rc")) or "\t" in e or "\n" in e:
        continue
    v = ""
    try:
        fd = os.open(os.path.join(d, e), os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        try:
            st = os.fstat(fd)
            if stat.S_ISREG(st.st_mode) and st.st_size <= 4:
                m = re.fullmatch(rb"(0|[1-9][0-9]{0,2})\n", os.read(fd, 8))
                if m and int(m.group(1)) <= 255:
                    v = m.group(1).decode()
        finally:
            os.close(fd)
    except OSError:
        pass
    print(e[4:-3] + "\t" + v)' "$W/tmp")
}
leg_rc() { printf '%s' "${LRC_MEMO[$1]-}"; }
leg_present() { [ -n "${LRC_PRESENT[$1]-}" ]; }
# ---------- self-test (verifies binaries + 3-way R7 digest agreement on good.export!) ----------
# Both controls are checked for their EXPECTED behaviour, not only an
# exit status. Positive control (pinned good.export): exit 0, the official success line, every run kernel's acceptance
# line and recorded exit 0, no error line, and the three R7 digests equal to the PINNED values of good.export below.
# Negative control (pinned bad.export): exit 1 with exactly one error line, the comparator's own rejection of the pinned
# fixture ("Illegal axiom detected: 'fvCheat'"), after ccmp parsed both exports, no success line, no ccmp digest (the
# axiom check fails before ccmp hashes), and any leg that recorded an exit accepted the (well-typed) fixture (a kernel
# that finished before the comparison failed may print its acceptance line: allowed). Each control runs under a time limit (--timeout, or 900 s without one; one deadline for both): a control
# that does not finish = DECLINED. --preflight runs the selected --kernels on the controls too (a behavioural test of
# each, not only an existence check); the real run's controls run gruszka (the candidate run exercises the others).
F6_GOOD_ENV=d7ac0b750bd015009ae42e39d293fcffb201380e2d2164d80c78f6d5541f23eb
F6_GOOD_STRICT=dbef3747969d875167e4b293a70d7909cc79a902c8ea8e2cae3aac05dfbabc3c
F6_GOOD_COUNT=584
F6_BAD_ERR="error: Illegal axiom detected: 'fvCheat'"
ST_TMO=$TMO; [ "$ST_TMO" -gt 0 ] || ST_TMO=900
ST_XK=; [ "$PREFLIGHT" = 1 ] && ST_XK="$USE_CONRON$USE_CONLECHE$USE_NANODA"
STCFG=$W/st.json
/usr/bin/python3 -I -c '
import json, sys
c = json.load(open(sys.argv[1])); c.pop("enable_nanoda", None)
k = {"gruszka (second kernel)": [sys.argv[3] + "/gruszka-kernel"]}
for flag, name, w in zip(sys.argv[4], ("con-ron (verified)", "con-leche (verified)", "nanoda (bundled)"), ("con-ron", "con-leche", "nanoda")):
    if flag == "1":
        k[name] = [sys.argv[3] + "/" + w + "-kernel"]
c["external_kernels"] = k
json.dump(c, open(sys.argv[2], "w"))' "${PIN_PATH[selftest_comparator]}" "$STCFG" "$W/bin" "${ST_XK:-000}" "$T" \
  || decline "cannot write self-test config"
selftest() {
  local g=skip b=skip rem dl CCMP_DOUT="$W/tmp/digest-selftest-ccmp-good.txt"
  dl=$(( $(date +%s) + ST_TMO ))
  rem=$(( dl - $(date +%s) ))
  if [ "$rem" -ge 1 ]; then
    runj timeout --kill-after=10 "$rem" "$CCMP" "$TC36" "$STCFG" "${PIN_PATH[selftest_challenge]}" "${PIN_PATH[selftest_good]}" > "$W/st_good.log" 2>&1; g=$?
  fi
  CCMP_DOUT="$W/tmp/digest-selftest-ccmp-bad.txt"
  rem=$(( dl - $(date +%s) ))
  if [ "$rem" -ge 1 ]; then
    runj timeout --kill-after=10 "$rem" "$CCMP" "$TC36" "$STCFG" "${PIN_PATH[selftest_challenge]}" "${PIN_PATH[selftest_bad]}" > "$W/st_bad.log" 2>&1; b=$?
  fi
  echo "$g $b" > "$W/st.rc"
}
check_r7_files() {
  # Args: CCMP_F LEAN_F K2_F [EXPECT_ENV EXPECT_STRICT EXPECT_COUNT] -> prints JSON, returns 0
  # iff ALL THREE digest files parse strictly and agree (env: ccmp == lean == gruszka; strict: ccmp == lean; counts:
  # all three) [and equal the expected values]. A digest file is exactly the producer's format (ccmp / Lean:
  # env_sha256_v1, env_strict_sha256_v1, const_count, digest_ms; gruszka-r7: env_sha256_v1, const_count, digest_ms), one
  # line each in this order, ASCII, '\n'-terminated, a regular file (not a symlink) of at most 4096 bytes; digests = 64
  # lowercase hex, numbers = canonical non-negative decimals (no sign, no leading zero, at most 19 digits). A missing
  # gruszka-r7 digest is never skipped: there is no 2-leg R7 gate.
  /usr/bin/python3 -I - "$@" <<'PY'
import json, os, re, stat, sys
HEX64 = re.compile(r"[0-9a-f]{64}")
DEC = re.compile(r"0|[1-9][0-9]{0,18}")
KEYS = {"ccmp": ("env_sha256_v1", "env_strict_sha256_v1", "const_count", "digest_ms"),
        "lean": ("env_sha256_v1", "env_strict_sha256_v1", "const_count", "digest_ms"),
        "gruszka": ("env_sha256_v1", "const_count", "digest_ms")}
def load(leg, p):
    if not p:
        return None, "no digest file given"
    try:
        fd = os.open(p, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except FileNotFoundError:
        return None, "missing"
    except OSError as e:
        return None, "cannot open: %s" % e.strerror
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            return None, "not a regular file"
        data = os.read(fd, 4097)
    finally:
        os.close(fd)
    if len(data) > 4096:
        return None, "larger than 4096 bytes"
    try:
        text = data.decode("ascii")
    except UnicodeDecodeError:
        return None, "not ASCII"
    if not text.endswith("\n"):
        return None, "not newline-terminated"
    lines, keys, d = text[:-1].split("\n"), KEYS[leg], {}
    if len(lines) != len(keys):
        return None, "%d lines, expected exactly %d (%s)" % (len(lines), len(keys), ", ".join(keys))
    for want, ln in zip(keys, lines):
        k, sep, v = ln.partition("=")
        if not sep or k != want:
            return None, "line %r where '%s=...' is expected" % (ln[:80], want)
        if k.startswith("env_"):
            if not HEX64.fullmatch(v):
                return None, "%s is not 64 lowercase hex digits" % k
            d[k] = v
        else:
            if not DEC.fullmatch(v):
                return None, "%s %r is not a canonical non-negative decimal" % (k, v[:40])
            d[k] = int(v)
    return d, None
a = sys.argv[1:]
legs, errs = {}, []
for leg, p in zip(("ccmp", "lean", "gruszka"), (a + ["", "", ""])[:3]):
    d, e = load(leg, p)
    if e:
        errs.append("missing or invalid %s digest (%s)" % (leg, e))
    else:
        legs[leg] = d
res = {"verified": False, "legs": legs}
if not errs:
    c, l, k = legs["ccmp"], legs["lean"], legs["gruszka"]
    if c["env_sha256_v1"] != l["env_sha256_v1"]:
        errs.append("R7_ENV_DIGEST_MISMATCH ccmp!=lean (%s!=%s)" % (c["env_sha256_v1"][:16], l["env_sha256_v1"][:16]))
    if c["env_strict_sha256_v1"] != l["env_strict_sha256_v1"]:
        errs.append("R7_STRICT_DIGEST_MISMATCH ccmp!=lean (%s!=%s)" % (c["env_strict_sha256_v1"][:16], l["env_strict_sha256_v1"][:16]))
    if c["const_count"] != l["const_count"]:
        errs.append("R7_CONST_COUNT_MISMATCH ccmp=%d!=lean=%d" % (c["const_count"], l["const_count"]))
    if c["env_sha256_v1"] != k["env_sha256_v1"]:
        errs.append("R7_ENV_DIGEST_MISMATCH ccmp!=gruszka (%s!=%s)" % (c["env_sha256_v1"][:16], k["env_sha256_v1"][:16]))
    if c["const_count"] != k["const_count"]:
        errs.append("R7_CONST_COUNT_MISMATCH ccmp=%d!=gruszka=%d" % (c["const_count"], k["const_count"]))
    if len(a) >= 6 and not errs and (c["env_sha256_v1"], c["env_strict_sha256_v1"], str(c["const_count"])) != tuple(a[3:6]):
        errs.append("R7_SELFTEST_DIGEST_UNEXPECTED (got %s/%s/%d, pinned %s/%s/%s)" % (
            c["env_sha256_v1"][:16], c["env_strict_sha256_v1"][:16], c["const_count"], a[3][:16], a[4][:16], a[5]))
if not errs:
    c = legs["ccmp"]
    res.update(verified=True, env_sha256_v1=c["env_sha256_v1"], env_strict_sha256_v1=c["env_strict_sha256_v1"],
               const_count=c["const_count"], matched_legs=["ccmp", "lean", "gruszka"], strict_matched_legs=["ccmp", "lean"],
               attestation={
                   "env_sha256_v1": {"value": c["env_sha256_v1"], "agreed": ["ccmp", "lean", "gruszka"]},
                   "env_strict_sha256_v1": {"value": c["env_strict_sha256_v1"], "agreed": ["ccmp", "lean"],
                                            "not_computed_by": ["gruszka"]},
                   "const_count": {"value": c["const_count"], "agreed": ["ccmp", "lean", "gruszka"]},
                   "parsers": {"ccmp": "FastParse.lean + fv_env_digest.c (ccmp-notary)",
                               "lean": "FastParse.lean + fv_env_digest.c (pleanchecker-notary)",
                               "gruszka": "susz packer + env_digest.rs (gruszka-r7)"}})
else:
    res["errors"] = errs
print(json.dumps(res))
sys.exit(0 if not errs else 1)
PY
}
selftest_ok() {
  local g b gb bb why= k lab tag st
  read -r g b < "$W/st.rc" 2>/dev/null || { g=x; b=x; }
  gb=$(basename "${PIN_PATH[selftest_good]}"); bb=$(basename "${PIN_PATH[selftest_bad]}")
  case " $g $b " in *" 124 "*|*" 137 "*|*" skip "*) ST_JSON="{\"good_rc\":\"$g\",\"bad_rc\":\"$b\",\"ok\":false}"
    decline "self-test did not finish within its time limit (${ST_TMO} s; good rc=$g, bad rc=$b): no verdict";; esac
  # positive control
  [ "$g" = 0 ] || why="positive control exited '$g', not 0 ($(grep -m1 '^error:' "$W/st_good.log" | cut -c1-200))"
  [ -n "$why" ] || grep -qx 'Your solution is okay!' "$W/st_good.log" || why="positive control without the official success line"
  [ -n "$why" ] || ! grep -q '^error:' "$W/st_good.log" || why="positive control printed an error line"
  for k in "gruszka:gruszka (second kernel):k2" "con-ron:con-ron (verified):con-ron" "con-leche:con-leche (verified):con-leche" "nanoda:nanoda (bundled):nanoda"; do
    tag=${k%%:*}; lab=${k#*:}; lab=${lab%:*}; st=${k##*:}
    case "$tag" in gruszka) ;; con-ron) [ "${ST_XK:0:1}" = 1 ] || continue;; con-leche) [ "${ST_XK:1:1}" = 1 ] || continue;;
      nanoda) [ "${ST_XK:2:1}" = 1 ] || continue;; esac
    [ -n "$why" ] || grep -qxF "$lab kernel accepts the solution" "$W/st_good.log" || why="positive control without the acceptance line of $lab"
    [ -n "$why" ] || [ "$(leg_rc "selftest-$st-$gb")" = 0 ] || why="positive control: $tag recorded exit '$(leg_rc "selftest-$st-$gb")', not 0"
    if [ -z "$why" ] && [ "$tag" != gruszka ]; then
      [ "$(notary_xk_classify "$tag" "$W/tmp/leg-selftest-$st-$gb.log" "$(leg_rc "selftest-$st-$gb")" | head -1)" = accepted ] \
        || why="positive control: $tag's own run is not classified accepted"
    fi
  done
  [ -n "$why" ] || grep -qx 'Lean default kernel accepts the solution' "$W/st_good.log" || why="positive control without the Lean acceptance line"
  [ -n "$why" ] || [ "$(leg_rc "selftest-lean-$gb")" = 0 ] || why="positive control: Lean leg recorded exit '$(leg_rc "selftest-lean-$gb")', not 0"
  if [ -z "$why" ]; then
    ST_R7=$(check_r7_files "$W/tmp/digest-selftest-ccmp-good.txt" "$W/tmp/digest-selftest-lean-$gb.txt" "$W/tmp/digest-selftest-k2-$gb.txt" \
            "$F6_GOOD_ENV" "$F6_GOOD_STRICT" "$F6_GOOD_COUNT") || why="positive control R7: $ST_R7"
  fi
  # negative control
  [ -n "$why" ] || [ "$b" = 1 ] || why="negative control exited '$b', not 1"
  [ -n "$why" ] || { [ "$(grep -c '^error:' "$W/st_bad.log")" = 1 ] && grep -qxF -- "$F6_BAD_ERR" "$W/st_bad.log"; } \
    || why="negative control without the expected rejection ($F6_BAD_ERR) as its only error line"
  [ -n "$why" ] || grep -qE '^\[ccmp\] exports parsed after [0-9]+ ms$' "$W/st_bad.log" || why="negative control: ccmp did not parse the exports"
  [ -n "$why" ] || ! grep -qx 'Your solution is okay!' "$W/st_bad.log" || why="negative control printed the official success line"
  [ -n "$why" ] || { [ ! -e "$W/tmp/digest-selftest-ccmp-bad.txt" ] && [ ! -L "$W/tmp/digest-selftest-ccmp-bad.txt" ]; } \
    || why="negative control: ccmp wrote a digest (its axiom check must fail before it hashes)"
  # every leg run on the negative control (the selected preflight kernels too). Only an ABSENT status
  # record is allowed (the comparator stopped early); a present one (even empty) must read strictly and be the expected
  # outcome: the Lean leg and gruszka-r7 accept the well-typed fixture (0); con-ron / con-leche accept it or decline its
  # non-standard axiom fvCheat (exit 2 with that line); nanoda accepts it or stops on the axiom in its checker (101).
  local nk nr ne
  for k in "lean:selftest-lean-$bb" "k2:selftest-k2-$bb" $([ "${ST_XK:0:1}" = 1 ] && echo "con-ron:selftest-con-ron-$bb") \
           $([ "${ST_XK:1:1}" = 1 ] && echo "con-leche:selftest-con-leche-$bb") $([ "${ST_XK:2:1}" = 1 ] && echo "nanoda:selftest-nanoda-$bb"); do
    nk=${k%%:*}; k=${k#*:}
    leg_present "$k" || continue
    nr=$(leg_rc "$k"); ne=bad
    case "$nk:$nr" in
      lean:0|k2:0|con-ron:0|con-leche:0|nanoda:0) ne=ok;;
      nanoda:101) grep -qE "^declaration not found in infer_const, fvCheat$" "$W/tmp/leg-$k.log" 2>/dev/null && ne=ok;;
      con-ron:2|con-leche:2) grep -qE "^$nk: (declined|not implemented yet): non-standard axiom.*fvCheat" "$W/tmp/leg-$k.log" 2>/dev/null && ne=ok;;
    esac
    [ -n "$why" ] || [ "$ne" = ok ] || why="negative control: leg $k recorded status '$nr', not the expected outcome on the well-typed fixture"
  done
  ST_JSON="{\"good_rc\":\"$g\",\"bad_rc\":\"$b\",\"ok\":$([ -z "$why" ] && echo true || echo false),\"time_limit_s\":$ST_TMO}"
  [ -z "$why" ] || decline "self-test failed: $why"
}
if [ "$PREFLIGHT" = 1 ]; then
  # challenge-configured kernels run in a nested sandbox: check that this host allows it
  runj /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp -- /bin/true \
    > "$W/nested.log" 2>&1 || decline "the nested sandbox for challenge-configured kernels does not work on this host: $(head -c 300 "$W/nested.log")"
  selftest; leg_rc_load; selftest_ok
  XK_DONE=gruszka; [ "${ST_XK:0:1}" = 1 ] && XK_DONE="$XK_DONE,con-ron"; [ "${ST_XK:1:1}" = 1 ] && XK_DONE="$XK_DONE,con-leche"
  [ "${ST_XK:2:1}" = 1 ] && XK_DONE="$XK_DONE,nanoda"
  finish 0 PREFLIGHT_OK "notary pins verified; self-test passed (positive control accepted by the comparison, the Lean leg and the kernels $XK_DONE, which were run, with the pinned 3-leg R7 digests; negative control rejected for the expected reason)"
fi
selftest & ST_PID=$!
f6_veto_scan "$W/solution.export" "$W/veto.json" & VS_PID=$!

# ---------- run judge ----------
if [ "$TMO" -gt 0 ]; then TPFX=(timeout --kill-after=30 "$TMO"); else TPFX=(); fi
log "[$SELF] ccmp-notary start: threads=$T kernels=$KERNELS_ARG version=$NOTARY_VERSION"
runj "${TPFX[@]}" "$CCMP" "$TC36" "$W/comparator.json" "$W/challenge.export" "$W/solution.export" > "$W/ccmp.log" 2>&1
CCMP_RC=$?
wait "$ST_PID"; ST_PID=   # both finished -> every status file is final; read them once
leg_rc_load
log "$(cat "$W/ccmp.log")"
for f in "$W"/tmp/leg-*.log; do [ -f "$f" ] || continue; log "--- $(basename "$f") (last 64 KiB) ---"; log "$(tail -c 65536 "$f")"; done
LEG_JSON=$(/usr/bin/python3 -I -c '
import json, re, sys
d = {}
for ln in open(sys.argv[1], errors="replace", newline="").read().split("\n"):   # LF only (labels may contain CR)
    m = re.match(r"^\[ccmp\] (.*) finished after (\d+) ms$", ln.strip(" \t\n"))
    if m: d[m.group(1)] = int(m.group(2))
print(json.dumps(d))' "$W/ccmp.log" 2>/dev/null) || LEG_JSON=null
# ONE status reader - the gate's leg_rc - feeds the report too (name=value, empty = no valid record)
RCS=; for n in lean k2 con-ron con-leche nanoda $(cut -f1 "$W/kept.txt" 2>/dev/null | sed 's/^/kept-/'); do RCS="$RCS$n=$(leg_rc "$n");"; done
LEGS_JSON=$(/usr/bin/python3 -I - "$W/tmp" "$LEG_JSON" "$W/kept.txt" "$USE_GRUSZKA" "$USE_CONRON" "$USE_CONLECHE" "$USE_NANODA" "$RCS" <<'PY' 2>/dev/null
import json, os, re, sys
d, keptf = sys.argv[1], sys.argv[3]
ms = json.loads(sys.argv[2]) if sys.argv[2] != "null" else {}
u_gz, u_cr, u_cl, u_na = [x == "1" for x in sys.argv[4:8]]
RC = dict(kv.split("=", 1) for kv in sys.argv[8].split(";") if kv)
def rc(n):   # the value the gate's leg_rc read (strict "N\n", 0..255, regular file), else null
    v = RC.get(n, "")
    return int(v) if v.isdigit() else None
def msg(n, pat):
    try: lines = open(os.path.join(d, f"leg-{n}.log"), errors="replace").read(4000000).splitlines()
    except OSError: return None
    for i, ln in enumerate(lines):
        if re.search(pat, ln): return "\n".join(lines[i:i + 2])[:400]
    return lines[-1][:400] if lines else ""
legs = {"lean": {"rc": rc("lean"), "ms": ms.get("kernel Lean default"),
                 "message": msg("lean", r"^(Lean default kernel|Quotient post-check|Stack overflow|deep recursion|\(kernel\))")}}
if u_gz:
    legs["k2"] = {"rc": rc("k2"), "ms": ms.get("kernel gruszka (second kernel)"),
                  "message": msg("k2", r"(?i)accept|reject|error|panic|fatal|declin")}
    try:   # retried with 1 worker after a decline for worker-table room (wrapper: leg-k2.retry)
        _fr = open(os.path.join(d, "leg-k2.retry"), errors="replace").read(16).strip()
        legs["k2"]["retry"] = {"reason": "a worker table is full", "first_rc": int(_fr) if _fr.isdigit() else None, "workers": 1}
    except OSError:
        pass
if u_cr:
    legs["con-ron"] = {"rc": rc("con-ron"), "ms": ms.get("kernel con-ron (verified)"),
                       "message": msg("con-ron", r"(?i)error|reject|panic|fatal|oom|verified")}
if u_cl:
    legs["con-leche"] = {"rc": rc("con-leche"), "ms": ms.get("kernel con-leche (verified)"),
                         "message": msg("con-leche", r"(?i)error|reject|panic|memory allocation|oom|bad_alloc")}
if u_na:
    legs["nanoda"] = {"rc": rc("nanoda"), "ms": ms.get("kernel nanoda (bundled)"),
                      "message": msg("nanoda", r"(?i)error|reject|panic|fatal")}
try:
    # records end with "\n" only (a kernel name may contain "\r"; universal newlines would split it)
    for ln in open(keptf, encoding="utf-8", newline="").read().split("\n"):
        if not ln:
            continue
        i, cls, name = ln.split("\t", 2)
        legs[f"kept-{i}"] = {"name": name, "class": cls, "rc": rc(f"kept-{i}"), "ms": ms.get("kernel " + name),
                             "message": msg(f"kept-{i}", r"(?i)accept|reject|error|panic|fatal")}
except OSError: pass
print(json.dumps({"legs": legs, "compare_ms": ms.get("compare (parse, compareAt, checkAxioms)")}))
PY
) || LEGS_JSON='{"legs":null,"compare_ms":null}'
COMPARE_MS=$(/usr/bin/python3 -I -c 'import json,sys; v=json.loads(sys.argv[1]).get("compare_ms"); print("null" if v is None else int(v))' "$LEGS_JSON" 2>/dev/null) || COMPARE_MS=null
LEGS_JSON=$(/usr/bin/python3 -I -c 'import json,sys; print(json.dumps(json.loads(sys.argv[1]).get("legs")))' "$LEGS_JSON" 2>/dev/null) || LEGS_JSON=null

selftest_ok
if [ "$TMO" -gt 0 ] && { [ "$CCMP_RC" = 124 ] || [ "$CCMP_RC" = 137 ]; }; then decline "time limit of $TMO s exceeded"; fi
[ "$(stamp)" = "$STAMP0" ] || decline "an input file was modified during the check"
for name in ccmp_notary pleanchecker_notary gruszka_r7; do
  [ "$(sha256sum "${PIN_PATH[$name]}" | cut -d' ' -f1)" = "${PIN_SHA[$name]}" ] || decline "pinned $name changed during the run"
done

# no R7 claim before the candidate's digest gate passed (set again right before ACCEPTED)
BASIS="notary preset (unmodified official Lean 4.36 release libs, strictly offline, GLIBC_2.17); kernels=$KERNELS_ARG; R7 digest gate not reached"
F6_DEFINITE_REJECT_RE="^error: (Const not found in (challenge|solution)|Const does not match between challenge and target |Challenge and solution (constant kind don't match|theorem statement do not match)|(Challenge|Solution) constant is not a (definition|theorem)|Constant not found in solution |Illegal axiom detected: |Duplicate declaration: |(Name|Level|Expr) not found |(Name|Level|Expr) index [0-9]+ bound twice|(Name|Level|Expr)\\.[A-Za-z.]+ invalid|Expr\\.lit (natVal|strVal) invalid|[a-z]+Info invalid|Inductive invalid|Invalid JSON|Expected JSON object|Invalid binder info: |Unknown safety parameter: |unknown quot kind: |Unknown export object with keys |failed to convert to name idx)"
# evidence I/O: the Lean leg prints its acceptance and only then waits for its R7 digest task
# (src/Main.lean): an exit 1 after 'Lean default kernel accepts the solution' without a quotient post-check rejection is a
# failure to write the evidence, as is an uncaught OS-level I/O error ('(error code: N)'): DECLINED, never REJECTED
lean_evidence_err() {
  [ -f "$W/tmp/leg-lean.log" ] || return 1
  if grep -qx 'Lean default kernel accepts the solution' "$W/tmp/leg-lean.log" \
     && ! grep -q '^Quotient post-check rejects the solution: ' "$W/tmp/leg-lean.log"; then return 0; fi
  grep -qE '^uncaught exception: .*\(error code: [0-9]+\)$' "$W/tmp/leg-lean.log" && return 0
  grep -qF -- "$W/tmp/digest-lean.txt" "$W/tmp/leg-lean.log"
}
DEEP_RE='^(\(kernel\) deep recursion detected|Lean default kernel rejects the solution: deep recursion was detected at |deep recursion was detected at |Stack overflow detected\. Aborting\.)$'
lean_deep() { [ -f "$W/tmp/leg-lean.log" ] && grep -qE "$DEEP_RE" "$W/tmp/leg-lean.log"; }
# leg tag of a selected kernel (wrapper log/rc file name: leg-<tag>.log / .rc)
xk_tag() { case "$1" in gruszka) echo k2;; *) echo "$1";; esac; }
# notary_kernels_decide: after the comparison and the official kernel accepted, classify EVERY selected kernel from its
# own recorded run and combine (sets KD_EX KD_V KD_WHY and KSTAT_JSON): gruszka rejected or nanoda rejected -> REJECTED;
# else con-ron / con-leche rejected -> DECLINED (veto; they treat theorem bodies as opaque); else any kernel not accepted
# -> DECLINED (all selected kernels are mandatory); else ACCEPTED-so-far (KD_V=ok).
notary_kernels_decide() {
  local k st why msg rej= veto= nd= js="{" sep=
  for k in gruszka con-ron con-leche nanoda; do
    case "$k" in gruszka) [ "$USE_GRUSZKA" = 1 ] || continue;; con-ron) [ "$USE_CONRON" = 1 ] || continue;;
                 con-leche) [ "$USE_CONLECHE" = 1 ] || continue;; nanoda) [ "$USE_NANODA" = 1 ] || continue;; esac
    { read -r st; read -r why; read -r msg; } < <(notary_xk_classify "$k" "$W/tmp/leg-$(xk_tag "$k").log" "$(leg_rc "$(xk_tag "$k")")")
    js="$js$sep$(json_str "$k"):{\"status\":$(json_str "$st"),\"reason\":$(json_str "$why"),\"message\":$(json_str "$msg")}"; sep=,
    case "$st" in
      rejected) case "$k" in gruszka|nanoda) [ -n "$rej" ] || rej="$k: $msg";; *) [ -n "$veto" ] || veto="$k: $msg";; esac;;
      accepted) ;;
      *) [ -n "$nd" ] || nd="$k (${why:-no status})";;
    esac
  done
  # the challenge's kept kernels too - the bundled nanoda / con-ron / con-leche by the same table (a
  # nanoda format error is 'not decided', never a rejection); any other kernel: exit 0 accepted, anything else is not an
  # identified proof rejection ('not decided' -> DECLINED)
  local ki kcls klab krc
  while IFS=$'\t' read -r ki kcls klab; do
    [ -n "$ki" ] || continue
    krc=$(leg_rc "kept-$ki")
    case "$kcls" in
      nanoda|con-ron|con-leche) { read -r st; read -r why; read -r msg; } < <(notary_xk_classify "$kcls" "$W/tmp/leg-kept-$ki.log" "$krc");;
      *) case "$krc" in 0) st=accepted; why=; msg="exit 0";; '') st="not decided"; why="no exit status recorded"; msg=;;
           *) st="not decided"; why="unfamiliar kernel exit $krc: no identified proof rejection"; msg=;; esac;;
    esac
    js="$js$sep$(json_str "kept-$ki"):{\"name\":$(json_str "$klab"),\"class\":$(json_str "$kcls"),\"status\":$(json_str "$st"),\"reason\":$(json_str "$why"),\"message\":$(json_str "$msg")}"; sep=,
    case "$st" in
      rejected) case "$kcls" in nanoda) [ -n "$rej" ] || rej="$klab: $msg";; *) [ -n "$veto" ] || veto="$klab: $msg";; esac;;
      accepted) ;;
      *) [ -n "$nd" ] || nd="$klab (${why:-no status})";;
    esac
  done < "$W/kept.txt"
  KSTAT_JSON="$js}"
  if [ -n "$rej" ]; then KD_EX=1; KD_V=REJECTED; KD_WHY="rejected by the independent kernel $rej (the comparison and the official 4.36 kernel had accepted)"
  elif [ -n "$veto" ]; then KD_EX=2; KD_V=DECLINED; KD_WHY="the verified kernel $veto - con-ron / con-leche treat theorem bodies as opaque and can reject a valid proof that unfolds a theorem body (the comparison, the official 4.36 kernel and gruszka accepted): no verdict (it is mandatory for ACCEPTED, never a REJECTED on its own)"
  elif [ -n "$nd" ]; then KD_EX=2; KD_V=DECLINED; KD_WHY="the kernel $nd did not decide: no verdict (every selected and every challenge-configured kernel is mandatory in the notary)"
  else KD_EX=0; KD_V=ok; KD_WHY=""; fi
}

case "$CCMP_RC" in
  0) ;;
  1) ERRF=$(grep -m1 -E '^error:' "$W/ccmp.log"); ERR=${ERRF:0:400}   # classify the complete line
     [ -n "$ERRF" ] || decline "ccmp exited 1 without an error line"
     # a cut diagnostic (the error line not newline-terminated, ending in an empty field ':', or not valid UTF-8) is no rejection
     /usr/bin/python3 -I -c 'import sys
d = open(sys.argv[1], "rb").read()
i = d.find(b"\nerror:"); i = 0 if d.startswith(b"error:") else (i + 1 if i >= 0 else -1)
j = d.find(b"\n", i) if i >= 0 else -1
l = d[i:j] if j > i else sys.exit(1)
l.decode("utf-8"); sys.exit(1 if l.rstrip().endswith(b":") else 0)' "$W/ccmp.log" 2>/dev/null \
       || decline "ccmp's error line is incomplete (not newline-terminated or not valid UTF-8): $ERR: no verdict"
     LRC=$(leg_rc lean)
     case "$ERRF" in
       "error: Lean default exited with 1")
         [ "${LRC:-}" = 1 ] || decline "inconsistent Lean leg status (recorded '${LRC:-none}')"
         if lean_deep; then decline "official-kernel leg ran out of stack (deep recursion): no verdict"; fi
         if lean_evidence_err; then decline "the official-kernel leg could not produce its evidence (R7 digest / I/O error after its verdict, exit 1): no verdict"; fi
         LREJ=$(lean_definite_reject) || decline "the official-kernel leg exited 1 without a complete, definite rejection message (no kernel exception / replay check / quotient post-check line, or a resource / runtime failure in its log): no verdict"
         finish 1 REJECTED "$ERR (official kernel: ${LREJ:0:300})";;
       "error: Lean default exited with "*|"error: Error while interacting with Lean default kernel"*)
         decline "official-kernel leg could not finish ($ERR): no verdict";;
       "error: gruszka (second kernel) exited with "*|"error: Error while interacting with gruszka (second kernel) kernel"*|\
       "error: con-leche (verified) exited with "*|"error: Error while interacting with con-leche (verified) kernel"*|\
       "error: con-ron (verified) exited with "*|"error: Error while interacting with con-ron (verified) kernel"*|\
       "error: nanoda (bundled) exited with "*|"error: Error while interacting with nanoda (bundled) kernel"*|\
       "error: config kernel "*" exited with "*|"error: Error while interacting with config kernel "*)
         # ccmp-notary reports an external kernel only after the comparison AND the official kernel accepted
         # (CCmpNotary.lean verifyMatchConcurrent), and it waits for every external kernel: classify all of them
         if [ "${LRC:-}" = 1 ]; then   # only with the Lean leg's own definite rejection
           LREJ=$(lean_definite_reject) && finish 1 REJECTED "$ERR (and official-kernel leg rejected: ${LREJ:0:300})"
           decline "$ERR, and the official-kernel leg exited 1 without a complete, definite rejection message: no verdict"
         fi
         notary_kernels_decide
         case "$KD_V" in
           REJECTED) finish 1 REJECTED "$KD_WHY";;
           DECLINED) decline "$KD_WHY";;
           *) decline "ccmp reported '$ERR' but every selected kernel's own run was classified accepted: no verdict";;
         esac;;
       "error: "*" exited with "*|"error: Error while interacting with "*)   # no unidentified kernel is a REJECTED
         decline "configured kernel could not finish ($ERR): no verdict";;
       "error: config kernel "*)   # a configured kernel's failure in any other form is never a proof rejection
         decline "configured kernel failure ($ERR): no verdict";;
       *)
         if printf '%s\n' "$ERRF" | grep -qE '^error: (memory allocation of [0-9]+ bytes failed|out of memory|std::bad_alloc|failed to create thread|resource exhausted|Stack overflow detected|deep recursion was detected at |\(kernel\) deep recursion detected)'; then
           decline "ccmp could not finish ($ERR): no verdict"
         fi
         # evidence I/O: an OS-level I/O error of ccmp itself (e.g. writing its R7 digest,
         # CCmpNotary.lean verifyCompareFast; Lean's IO.Error text '... (error code: N)') is not a judgement
         # (tested on the COMPLETE line, not on the 400-character display string)
         if printf '%s\n' "$ERRF" | grep -qE '\(error code: [0-9]+\)$' || grep -qF -- "$W/tmp/digest-ccmp.txt" "$W/ccmp.log"; then
           decline "ccmp could not produce its evidence (I/O error: $ERR): no verdict"
         fi
         # REJECTED only for a definite rejection by the comparator (Lake/Check/Compare.lean +
         # ParAxioms: statements, kinds, definitions, axioms) or by the export reader (LeanExport/Parse.lean, FastParse:
         # malformed / duplicate / unbound records - the official comparator exits 1 on them too); anything else = no verdict
         if printf '%s\n' "$ERRF" | grep -qE "$F6_DEFINITE_REJECT_RE"; then finish 1 REJECTED "$ERR"; fi
         decline "unrecognised comparator failure ($ERR): no verdict";;
     esac;;
  2) decline "ccmp could not run: $(grep -m1 -E '^error:' "$W/ccmp.log" | cut -c1-300)";;
  *) decline "ccmp terminated abnormally (rc=$CCMP_RC)";;
esac

# ---------- ACCEPTANCE GATE: v2 leg checks + MANDATORY R7 SHA-256 CROSS-CHECK ----------
grep -q '^Your solution is okay!$' "$W/ccmp.log" || decline "ccmp rc=0 without official success line"
grep -q '^Lean default kernel accepts the solution$' "$W/ccmp.log" || decline "ccmp rc=0 without Lean acceptance line"
[ "$(leg_rc lean)" = 0 ] || decline "Lean leg recorded exit '$(leg_rc lean)', not 0"

if [ "$USE_GRUSZKA" = 1 ]; then
  grep -q '^gruszka (second kernel) kernel accepts the solution$' "$W/ccmp.log" || decline "ccmp rc=0 without gruszka acceptance line"
  [ "$(leg_rc k2)" = 0 ] || decline "gruszka leg recorded exit '$(leg_rc k2)', not 0"
fi
if [ "$USE_CONRON" = 1 ]; then
  grep -q '^con-ron (verified) kernel accepts the solution$' "$W/ccmp.log" || decline "ccmp rc=0 without con-ron acceptance line"
  [ "$(leg_rc con-ron)" = 0 ] || decline "con-ron leg recorded exit '$(leg_rc con-ron)', not 0"
fi
if [ "$USE_CONLECHE" = 1 ]; then
  grep -q '^con-leche (verified) kernel accepts the solution$' "$W/ccmp.log" || decline "ccmp rc=0 without con-leche acceptance line"
  [ "$(leg_rc con-leche)" = 0 ] || decline "con-leche leg recorded exit '$(leg_rc con-leche)', not 0"
fi
if [ "$USE_NANODA" = 1 ]; then
  grep -q '^nanoda (bundled) kernel accepts the solution$' "$W/ccmp.log" || decline "ccmp rc=0 without nanoda acceptance line"
  [ "$(leg_rc nanoda)" = 0 ] || decline "nanoda leg recorded exit '$(leg_rc nanoda)', not 0"
fi
# every selected kernel is mandatory: its own recorded run must be classified 'accepted' too
notary_kernels_decide
[ "$KD_V" = ok ] || decline "ccmp rc=0 but ${KD_WHY:-a selected kernel was not classified accepted}"
while IFS=$'\t' read -r ki kcls kname; do
  [ -n "$ki" ] || continue
  grep -qxF -- "$kname kernel accepts the solution" "$W/ccmp.log" || decline "missing acceptance line of kept kernel '$kname'"
  [ "$(leg_rc "kept-$ki")" = 0 ] || decline "kept kernel '$kname' recorded exit '$(leg_rc "kept-$ki")', not 0"
done < "$W/kept.txt"

# R7 CROSS-LEG SHA-256 DIGEST GATE (MUST PASS FOR ACCEPTED!) - always all three digests of the candidate
[ "$USE_GRUSZKA" = 1 ] || decline "internal: gruszka-r7 was not run (it is mandatory for the R7 gate)"
R7_JSON=$(check_r7_files "$W/tmp/digest-ccmp.txt" "$W/tmp/digest-lean.txt" "$W/tmp/digest-k2.txt") || {
  decline "R7 cross-leg canonical env SHA-256 digest check FAILED: $R7_JSON"
}
# veto of fields gruszka-r7 narrows (see f6_veto_scan); the scan ran concurrently
# with --timeout the join is bounded too (deadline = start + TMO + 60 s); not finished = DECLINED
if [ "$TMO" -gt 0 ]; then
  VS_DL=$(( ${T_START%.*} + TMO + 60 ))
  while kill -0 "$VS_PID" 2>/dev/null && [ "$(date +%s)" -lt "$VS_DL" ]; do sleep 1; done
  if kill -0 "$VS_PID" 2>/dev/null; then decline "veto scan did not finish within the time limit ($TMO s + 60 s): no verdict"; fi
fi
wait "$VS_PID"; VS_PID=
VETO_JSON=$(head -c 65536 "$W/veto.json" 2>/dev/null)
VETO=$(/usr/bin/python3 -I -c 'import json,sys; j=json.loads(sys.argv[1]); print("no" if j.get("veto") is False else "yes: " + "; ".join(j.get("reasons") or [str(j.get("reason"))])[:600])' "$VETO_JSON" 2>/dev/null) || VETO="yes: veto scan result unreadable"
case "$VETO" in no) ;; *) VETO_JSON=${VETO_JSON:-null}
  decline "veto: the export has a field that gruszka-r7 reads differently from Lean (narrowed to 32 bits) - ${VETO#yes: }: no verdict until gruszka-r7 is rebuilt";; esac

BASIS="notary preset (unmodified official Lean 4.36 release libs, strictly offline, GLIBC_2.17); R7 cross-leg SHA-256 env digest verified for the candidate: env_sha256_v1 agreed by ccmp, lean, gruszka; env_strict_sha256_v1 agreed by ccmp, lean; kernels=$KERNELS_ARG"
finish 0 ACCEPTED "notary ACCEPTED: statements + axioms match (official judge code); official 4.36 release kernel + independent kernel(s) [$KERNELS_ARG] accepted; R7 canonical env SHA-256 digests of the candidate matched bit-for-bit: env_sha256_v1 across ccmp, lean and gruszka-r7, env_strict_sha256_v1 across ccmp and lean"
}
main "$@"; exit $?
