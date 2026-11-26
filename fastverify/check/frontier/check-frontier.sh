#!/bin/bash -p
# fastverify CONDITIONAL CHECK modulo an explicit sorry frontier (wrapper + fast preparer).
#
#   check-frontier.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--allowed FILE] [--pinned DIR] [--threads N] [--json FILE]
#                     --allowed FILE: one Lean name per line; CONDITIONAL only if every open lemma (and every F member)
#                     is listed EXACTLY (canonical names; a private lemma as _private.<module>.0.<x>), checked HERE
#                     [--log FILE] [--timeout S] [--workdir DIR] [--integrity-cache DIR] [--keep DIR] [--base RESULT]
#                     [--hints FILE|none] [--incr-dir DIR]   (both passed to check B's sound check, as in the sound preset)
#                     [--hide FILE]   (availability only: the encapsulated-replay hide list of the Lean-kernel leg, passed to
#                                      BOTH sound checks; needs a sound check that accepts --hide, i.e. check-sound(-svc) v2.2)
#                     [--axioms FILE]   (declared PROJECT axioms, one name per line, allowed as listed hypotheses next to
#                                        the open lemmas: they join F, their statements are minted into C'; refused if a
#                                        target / definition target / permitted axiom / sorryAx / compiler-trust axiom)
#                     [--pins FILE]   (passed to BOTH sound checks and the preflight: another reviewed pins file of the sound
#                                      check, e.g. check/sound/pins-437.env = the Lean 4.37.0-rc1 trusted check; a private
#                                      copy is used, its sha256 is in the result and in the --a-cache key)
#                     [--a-cache DIR]
#   --a-cache DIR (SERVICE option, default off; TRUSTED like pins.env): a record of an earlier ACCEPTED check A is kept in
#                 DIR, keyed by sha256 of (C', C, check A's configuration, check/sound/pins.env, the sound check script);
#                 a later run with the SAME key skips check A (the frontier challenge was already shown to agree with the
#                 official challenge by the same trusted check). DIR must be a real directory owned by the caller with no
#                 group/other access, records regular files owned by the caller (else: refused / not used). Whoever can
#                 write DIR can make the wrapper skip check A: keep it as private as pins.env (fvwork's state dir).
#   --base RESULT (informational, ledger): report for each open lemma of an earlier result whether it is still open, now
#                 proved, or absent from the targets' closure ("dropped": no longer used - check the proof did not bypass it)
#   check-frontier.sh --preflight [--pins FILE] [--integrity-cache DIR]
# exit 0 = ACCEPTED    (no open lemma: check B is exactly the sound check CS of the export with the challenge's own config)
#      3 = CONDITIONAL (every target of the official challenge is derivable from the permitted axioms + the statements of
#                       the reported frontier F; each statement is a record of the frontier challenge C', sha256 reported)
#      1 = REJECTED, 2 = no verdict (DECLINED / could not run). Last stdout line = one JSON object.
#
# What decides: ONLY two runs of the UNCHANGED sound check (check/sound/check-sound.sh, or check-sound-svc.sh with
# --integrity-cache); argument: check/frontier/README.md.
#   untrusted: tools/frontier/frontier.py prepare (+ the pinned fast preparer fvfrontier-prep): F = the open lemmas,
#     S' = the export with each frontier THEOREM turned into an axiom of the same name/universes/type (in place),
#     C' = the official challenge export VERBATIM + the closure in S' of the frontier axioms (re-indexed) [or a pinned C'].
#   trusted (this script): private copies; the two configurations are built HERE from the challenge's own configuration
#     (A = its permitted_axioms):  check A = CS(C' vs C, permitted A + sorryAx [if C has sorryAx])  - C' agrees with the
#     official challenge on every target statement and every definition it mentions;  check B = CS(S' vs C', permitted
#     A + F) - S' agrees with C' on the targets and on the frontier axioms' statements, both kernels accept every
#     declaration of S', only A + F occur in the targets' closure.  CONDITIONAL iff F is non-empty and A and B accepted
#     (exit code AND JSON verdict of each run); ACCEPTED iff F is empty and CS(S' vs C, the challenge's own config)
#     accepted. A frontier name may not be a target, a definition target, a permitted axiom or sorryAx.
# The whole script is one function, parsed before it runs: replacing the file during a run cannot change that run.
main() {
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
set -u
umask 077
T_START=$(date +%s.%N)
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PKGROOT=$(cd "$HERE/../.." && pwd)
SELF=checkFrontier
FINISHED=0; W=; KEEP=
on_exit() {
  local rc=$?
  if [ -n "$W" ]; then
    if [ -n "$KEEP" ]; then rm -rf "$KEEP" 2>/dev/null; mv "$W" "$KEEP" 2>/dev/null || rm -rf "$W"; else rm -rf "$W"; fi
  fi
  if [ "$FINISHED" != 1 ]; then
    printf '{"checker":"%s","verdict":"DECLINED","exit":2,"reason":"internal error (exit %s)"}\n' "$SELF" "$rc"
    [ -n "${JSONF:-}" ] && printf '{"checker":"%s","verdict":"DECLINED","exit":2,"reason":"internal error (exit %s)"}\n' "$SELF" "$rc" > "$JSONF" 2>/dev/null
    exit 2
  fi
}
trap on_exit EXIT
trap 'exit 2' INT TERM HUP
LOGF=
log() { if [ -n "$LOGF" ]; then printf '%s\n' "$*" >> "$LOGF"; else printf '%s\n' "$*" >&2; fi; }
finish() {  # finish EXIT VERDICT REASON
  local ex=$1 v=$2 why=$3 js
  js=$(/usr/bin/python3 -I - "$SELF" "$v" "$ex" "$why" "$T_START" "${W:-}" "${SOUND_SCRIPT:-}" "${FSHA:-}" "${PINS:-}" "${PINS_SHA:-}" <<'PY'
import json, sys, time, os
self_, v, ex, why, t0, w, sscript, fsha, pins, pins_sha = sys.argv[1:11]
def load(p, last=True):
    try:
        with open(p, encoding="utf-8") as f:
            t = f.read()
        if not last:
            return json.loads(t)
        lines = [l for l in t.splitlines() if l.strip()]
        return json.loads(lines[-1]) if lines else None
    except Exception:
        return None
info = load(os.path.join(w, "fr", "frontier.json"), last=False) if w else None
F = load(os.path.join(w, "F.json"), last=False) if w else None
out = {"checker": self_, "verdict": v, "exit": int(ex), "wall_s": round(time.time() - float(t0), 3), "reason": why}
if isinstance(F, list):
    stm = (info or {}).get("statements") or {}
    lem = (info or {}).get("frontier_lemma_of") or {}
    # name = the open lemma (display; with the redirect rewrite it stays a theorem), axiom = the hypothesis check B permits
    out["frontier"] = [dict({"name": (stm.get(n) or {}).get("lemma") or lem.get(n) or n, "axiom": n},
                            **{k: x for k, x in (stm.get(n) or {}).items() if k not in ("name", "lemma")}) for n in F]
    out["frontier_size"] = len(F)
    if info and info.get("rewrite"):
        out["rewrite"] = info.get("rewrite")
if info:
    sc = info.get("scan") or {}
    out["blockers"] = {k: sc.get(k) for k in ("sorry_in_targets", "sorry_in_definitions", "other_axioms", "missing",
                                              "sorry_outside_allowed", "open_lemma_in_statement") if sc.get(k) is not None}
    if v == "REJECTED":   # say WHERE (untrusted diagnostics of the preparation; the verdict came from check B)
        why_more = []
        for k, label in (("sorry_in_targets", "sorry in a target's proof"), ("sorry_in_definitions", "sorry in a definition"),
                         ("sorry_outside_allowed", "sorried theorem outside the allowed frontier"),
                         ("other_axioms", "axiom outside the permitted ones"), ("missing", "missing constant"),
                         ("open_lemma_in_statement", "open lemma inside a target statement's closure")):
            xs = sc.get(k) or []
            if xs:
                why_more.append("%s: %s" % (label, ", ".join((x if isinstance(x, str) else x.get("name", "?") + (
                    " (%s)" % " > ".join(str(p) for p in x["path"][:12]) if k == "open_lemma_in_statement" and isinstance(x.get("path"), list) else ""))
                    for x in xs[:8])))
        if why_more:
            out["reason"] = why + " [" + "; ".join(why_more) + "]"
    out["frontier_closed"] = sc.get("frontier_closed") or []
    if isinstance(sc.get("probe"), dict):
        out["base_status"] = sc.get("probe")
    if sc.get("outside_pinned_frontier"):
        out["outside_pinned_frontier"] = sc.get("outside_pinned_frontier")
    out["prepare_seconds"] = (info.get("seconds") or {})
    out["preparer"] = "fast (fvfrontier-prep)" if info.get("fast_preparer_ms") else "python (fvfrontier-prep missing or not pinned: slow)"
checks = {}
for k in ("A", "B"):
    j = load(os.path.join(w, "check_%s.json" % k)) if w else None
    if j is not None:
        checks[k] = j
if checks:
    out["checks"] = checks
if fsha:
    out["frontier_challenge_sha256"] = fsha
out["sound_check_script"] = sscript or None
if pins:
    out["pins"] = pins
if pins_sha:
    out["pins_sha256"] = pins_sha
tcb = (checks.get("B") or {}).get("toolchain") if checks else None
kern = ("the kernels of the sound check with %s (%s)" % (os.path.basename(pins), tcb or "toolchain of that pins file")
        if pins else "the official Lean 4.36 kernel and by gruszka")
out["basis"] = ("two runs of the unchanged sound check: A = frontier challenge C' vs the official challenge (pins every "
                "target statement), B = rewritten solution S' (each open lemma stays a theorem whose value is a fresh axiom "
                "with its statement; declared --axioms are listed as they are) vs C' (permitted axioms + F; "
                "both kernels replay S')")
if v == "CONDITIONAL":
    out["claim"] = ("every target of the official challenge is derivable from the permitted axioms PLUS the statements of "
                    "the %d frontier hypotheses (open lemmas; declared axioms) listed in 'frontier' (authoritative statements: the records of the frontier "
                    "challenge export, sha256 %s), and from nothing else; every declaration of the rewritten export is "
                    "accepted by %s" % (len(F or []), fsha, kern))
elif v == "ACCEPTED":
    out["basis"] = "no open lemma: the unchanged sound check (CS) of the export with the challenge's own configuration accepted"
print(json.dumps(out, ensure_ascii=False))
PY
) || js="{\"checker\":\"$SELF\",\"verdict\":\"DECLINED\",\"exit\":2,\"reason\":\"cannot write the result\"}"
  if ! printf '%s' "$js" | grep -q "\"verdict\": \"$v\""; then ex=2; v=DECLINED; js="{\"checker\":\"$SELF\",\"verdict\":\"DECLINED\",\"exit\":2,\"reason\":\"result JSON inconsistent\"}"; fi
  log "[$SELF] verdict $v (exit $ex): $why"
  printf '%s\n' "$js"
  if [ -n "${JSONF:-}" ]; then printf '%s\n' "$js" > "$JSONF" || true; fi
  FINISHED=1
  exit "$ex"
}
decline() { finish 2 DECLINED "$1"; }

# ---------- arguments ----------
PREFLIGHT=0
if [ "${1:-}" = --preflight ]; then PREFLIGHT=1; shift; fi
if [ "$PREFLIGHT" = 0 ]; then
  [ $# -ge 3 ] || { echo "usage: check-frontier.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--allowed FILE] [--pinned DIR] [--threads N] [--json FILE] [--log FILE] [--timeout S] [--workdir DIR] [--integrity-cache DIR] [--keep DIR] | --preflight" >&2; decline "usage"; }
  E_IN=$1; C_IN=$2; CFG_IN=$3; shift 3
fi
T=; WD=; JSONF=; TMO=0; ICACHE=; ALLOWED=; PINNED=; BASE=; HINTS=; INCR=; ACACHE=; PINS=; AXIOMS=; HIDE=
while [ $# -gt 0 ]; do
  case "$1" in
    --threads) T=${2:-}; shift 2 || decline "--threads needs a value";;
    --workdir) WD=${2:-}; shift 2 || decline "--workdir needs a value";;
    --json) JSONF=${2:-}; shift 2 || decline "--json needs a value";;
    --timeout) TMO=${2:-}; shift 2 || decline "--timeout needs a value";;
    --integrity-cache) ICACHE=${2:-}; shift 2 || decline "--integrity-cache needs a value";;
    --allowed) ALLOWED=${2:-}; shift 2 || decline "--allowed needs a value";;
    --pinned) PINNED=${2:-}; shift 2 || decline "--pinned needs a value";;
    --base) BASE=${2:-}; shift 2 || decline "--base needs a value";;
    --a-cache) ACACHE=${2:-}; shift 2 || decline "--a-cache needs a value";;
    --private-inputs) shift;;   # accepted for check-sound compatibility: the checks here only ever read fresh private files
    --keep) KEEP=${2:-}; shift 2 || decline "--keep needs a value";;
    --hints) HINTS=${2:-}; shift 2 || decline "--hints needs a value";;
    --incr-dir) INCR=${2:-}; shift 2 || decline "--incr-dir needs a value";;
    --pins) PINS=${2:-}; shift 2 || decline "--pins needs a value";;
    --axioms) AXIOMS=${2:-}; shift 2 || decline "--axioms needs a value";;
    --hide) HIDE=${2:-}; shift 2 || decline "--hide needs a value";;
    --log) LOGF=${2:-}; shift 2 || decline "--log needs a value"; : > "$LOGF" || decline "cannot write log $LOGF";;
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
if [ -n "$ICACHE" ]; then SOUND_SCRIPT=$PKGROOT/check/sound/check-sound-svc.sh; SX=(--integrity-cache "$ICACHE"); else SOUND_SCRIPT=$PKGROOT/check/sound/check-sound.sh; SX=(); fi
[ -f "$SOUND_SCRIPT" ] || decline "sound check script missing: $SOUND_SCRIPT"
FR=$PKGROOT/tools/frontier/frontier.py
[ -f "$FR" ] || decline "tools/frontier/frontier.py missing"
# (Boundary B4) --pins (handed to both sound checks and their preflight) must be one of
# the sound check's own pins files - after resolving every symlink, a pins*.env directly in check/sound/; the
# sound checks are given that confined package path (they refuse any other, so not this script's private copy).
if [ -n "$PINS" ]; then
  PINS=$(readlink -f -- "$PINS") || decline "--pins: cannot resolve '$PINS'"
  case "$(basename -- "$PINS")" in pins*.env) ;; *) decline "--pins must name a pins*.env file in $PKGROOT/check/sound";; esac
  [ "$(dirname -- "$PINS")" = "$(readlink -f -- "$PKGROOT/check/sound")" ] || decline "--pins must name a pins*.env file in $PKGROOT/check/sound"
fi
if [ "$PREFLIGHT" = 1 ]; then
  PFX=(); [ -n "$PINS" ] && PFX=(--pins "$PINS")
  out=$("$SOUND_SCRIPT" --preflight "${SX[@]}" "${PFX[@]}" 2>/dev/null) || decline "the sound check preflight failed: $(printf '%s' "$out" | tail -c 300)"
  /usr/bin/python3 -I -c 'import ast,sys; ast.parse(open(sys.argv[1]).read())' "$FR" || decline "frontier.py does not parse"
  finish 0 PREFLIGHT_OK "sound check preflight passed; frontier preparer present"
fi

# ---------- private work dir, private copies of the challenge export and the configuration ----------
for f in "$E_IN" "$C_IN" "$CFG_IN"; do
  [ -n "$f" ] || decline "empty input path"
  r=$(readlink -f -- "$f") || decline "cannot resolve '$f'"
  { [ -f "$r" ] && [ ! -p "$r" ]; } || decline "input is not a regular file: '$f'"
done
E_IN=$(readlink -f -- "$E_IN"); C_IN=$(readlink -f -- "$C_IN"); CFG_IN=$(readlink -f -- "$CFG_IN")
if [ -z "$WD" ]; then WD=$(dirname "$E_IN"); fi
W=$(mktemp -d "$WD/.checkFrontier.XXXXXX" 2>/dev/null) || W=$(mktemp -d "/tmp/checkFrontier.XXXXXX") || decline "cannot create a work dir"
W=$(/usr/bin/realpath -e -- "$W") || decline "cannot resolve the work dir $W"   # absolute and symlink-free, as in check-sound.sh
chmod 700 "$W"
cp --reflink=auto -- "$C_IN" "$W/challenge.export" || decline "cannot copy the challenge export"
cp -- "$CFG_IN" "$W/comparator.orig.json" || decline "cannot copy the config"
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
# --pins: one private copy (keys PINS_SHA / the A-cache); the sound checks get the confined package path and
# make their own private copy of it; default = the package's pins
PINSF=$PKGROOT/check/sound/pins.env; PNX=()
if [ -n "$PINS" ]; then
  r=$(readlink -f -- "$PINS") || decline "--pins: cannot resolve '$PINS'"
  { [ -f "$r" ] && [ ! -p "$r" ] && [ "$(stat -c %s -- "$r")" -le 1048576 ]; } || decline "--pins: not a regular file <= 1 MiB: '$PINS'"
  cp -- "$r" "$W/pins.env" || decline "cannot copy the pins file"; chmod 400 "$W/pins.env"
  PINSF=$W/pins.env; PNX=(--pins "$PINS")   # the confined package path (the sound check copies + hashes it)
fi
PINS_SHA=$(sha256sum -- "$PINSF" | cut -d' ' -f1)
# --hide: one private copy, given to every sound-check run (availability only: the kernels still check every declaration)
if [ -n "$HIDE" ]; then
  grep -q -- '--hide)' "$SOUND_SCRIPT" || decline "--hide: $(basename "$SOUND_SCRIPT") does not accept --hide (needs check-sound v2.2)"
  { [ -f "$HIDE" ] && [ "$(stat -L -c %s -- "$HIDE")" -le 16777216 ]; } || decline "--hide: not a regular file <= 16 MiB: '$HIDE'"
  cp -- "$HIDE" "$W/hide" || decline "cannot copy the hide list"; chmod 400 "$W/hide"; PNX+=(--hide "$W/hide")
fi
PARGS=(--frontier auto)
if [ -n "$ALLOWED" ]; then
  { [ -f "$ALLOWED" ] && [ "$(stat -c %s -- "$ALLOWED")" -le 16777216 ]; } || decline "--allowed: not a regular file <= 16 MiB: '$ALLOWED'"
  cp -- "$ALLOWED" "$W/allowed" || decline "cannot copy the allowed list"; PARGS=(--frontier "@$W/allowed")
  ALLOWED_SHA=$(sha256sum -- "$W/allowed" | cut -d' ' -f1)   # the trusted F <= --allowed check reads exactly these bytes
  case "$ALLOWED_SHA" in ""|*[!0-9a-f]*) decline "cannot hash the private copy of the allowed list";; esac
  [ "${#ALLOWED_SHA}" = 64 ] || decline "cannot hash the private copy of the allowed list"   # (r2) never skip the check
fi
[ -n "$PINNED" ] && PARGS+=(--pinned "$(readlink -f -- "$PINNED")")
if [ -n "$AXIOMS" ]; then   # declared project axioms: the preparer puts the used ones into F (validated below like every F name)
  { [ -f "$AXIOMS" ] && [ "$(stat -c %s -- "$AXIOMS")" -le 16777216 ]; } || decline "--axioms: not a regular file <= 16 MiB: '$AXIOMS'"
  cp -- "$AXIOMS" "$W/axioms" || decline "cannot copy the axioms list"; PARGS+=(--axioms "@$W/axioms")
  AXIOMS_SHA=$(sha256sum -- "$W/axioms" | cut -d' ' -f1)
  case "$AXIOMS_SHA" in ""|*[!0-9a-f]*) decline "cannot hash the private copy of the axioms list";; esac
  [ "${#AXIOMS_SHA}" = 64 ] || decline "cannot hash the private copy of the axioms list"
fi
if [ -n "$BASE" ]; then   # informational only (ledger): which of the base result's open lemmas are proved / dropped now
  /usr/bin/python3 -I - "$BASE" "$W/base.probe" <<'PY' 2>/dev/null && PARGS+=(--probe "$W/base.probe") || log "[$SELF] --base: cannot read the base result (ignored)"
import json, sys
t = open(sys.argv[1], encoding="utf-8").read()
try:
    j = json.loads(t)
except ValueError:
    j = json.loads([l for l in t.splitlines() if l.strip()][-1])
fr = j["frontier"]["frontier"] if isinstance(j.get("frontier"), dict) else j.get("frontier")
names = [e["name"] for e in (fr or []) if isinstance(e, dict) and isinstance(e.get("name"), str) and "\n" not in e["name"]]
open(sys.argv[2], "w", encoding="utf-8").write("".join(n + "\n" for n in names))
PY
fi

# ---------- untrusted preparation: F, S' (fresh file in W), C' (fresh file in W) ----------
if [ "$TMO" -gt 0 ]; then TPFX=(timeout --kill-after=10 "$TMO"); else TPFX=(); fi
"${TPFX[@]}" /usr/bin/python3 -I "$FR" prepare "$E_IN" "$W/challenge.export" "$W/comparator.orig.json" "$W/fr" "${PARGS[@]}" \
  > "$W/prepare.out" 2> "$W/prepare.err"
PRC=$?
log "[$SELF] prepare rc=$PRC: $(tail -c 400 "$W/prepare.out")"
[ "$PRC" = 0 ] || { log "$(tail -c 1500 "$W/prepare.err")"; decline "frontier preparation failed (rc=$PRC): $(tail -c 300 "$W/prepare.err" | tr '\n' ' ')"; }
SP=$W/fr/solution.frontier.export; CP=$W/fr/frontier/challenge.export
{ [ -f "$SP" ] && [ -f "$CP" ] && [ -f "$W/fr/frontier.json" ]; } || decline "frontier preparation produced no inputs"
chmod 444 "$SP" "$CP" "$W/challenge.export"

# ---------- trusted: F and the two configurations, built from the challenge's own configuration ----------
CFGMSG=$(/usr/bin/python3 -I - "$W" "${ALLOWED_SHA:-}" "${AXIOMS_SHA:-}" <<'PY' 2>&1
import json, sys, os
w = sys.argv[1]
def no_dups(pairs):
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate key in the configuration")
    return dict(pairs)
# The ORIGINAL comparator.json is validated first, exactly as the official 4.36 comparator reads it. The
# block below is the validator from check/notary/check-notary.sh, copied VERBATIM;
# in this judge the challenge's external kernels / enable_nanoda are replaced by the judge's own second kernel (the
# documented rewrite below), which is why the official PATH lookup of the challenge's kernel commands does not apply.
src = os.path.join(w, "comparator.orig.json")
def bad_const(x):
    raise ValueError("non-standard JSON constant %s" % x)
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
c = json.loads(open(os.path.join(w, "comparator.orig.json"), "rb").read().decode("utf-8", errors="strict"), object_pairs_hook=no_dups)
if not isinstance(c, dict) or not isinstance(c.get("permitted_axioms"), list) or not isinstance(c.get("theorem_names"), list):
    sys.exit("config: permitted_axioms / theorem_names missing")
A = c["permitted_axioms"]; T = c["theorem_names"]; D = c.get("definition_names") or []
if not all(isinstance(x, str) for x in A + T + list(D)):
    sys.exit("config: names must be strings")
if "sorryAx" in A:
    sys.exit("the configuration already permits sorryAx")
# (S1(3)) the challenge's own configuration may only permit propext, Quot.sound, Classical.choice and its
# definition holes may not be kernel primitives / targets / axioms; the two internal sound checks get their extra axioms
# (sorryAx for check A, the frontier F for check B) through --extra-axioms
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
info = json.load(open(os.path.join(w, "fr", "frontier.json"), encoding="utf-8"))
F = info.get("frontier")
if not isinstance(F, list) or not all(isinstance(x, str) and x and "\n" not in x for x in F) or len(set(F)) != len(F):
    sys.exit("frontier list malformed")
bad = sorted(set(F) & (set(T) | set(D) | set(A) | {"sorryAx"}))
if bad:
    sys.exit("frontier contains a target / definition target / permitted axiom / sorryAx: %s" % bad)
# trust axioms of the compiler / native_decide are never open lemmas
trust = sorted(n for n in F if n in ("Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler")
               or "._native.native_decide.ax_" in n or n.startswith("_native.native_decide.ax_"))
if trust:
    sys.exit("frontier contains a compiler / native_decide trust axiom: %s" % trust)
q02_F = [q02_canon(n) for n in F]
if len(set(q02_F)) != len(q02_F):
    sys.exit("frontier list contains duplicate names (canonical)")
q02_forb = set(map(q02_canon, list(T) + list(D) + list(A) + ["sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"]))
def q02_native_ax(t):
    return any(t[i] == ("s", "_native") and t[i + 1] == ("s", "native_decide") and t[i + 2][0] == "s"
               and t[i + 2][1].startswith("ax_") for i in range(len(t) - 2))
q02_badF = sorted(n for n, t in zip(F, q02_F) if t in q02_forb or q02_native_ax(t))
if q02_badF:
    sys.exit("frontier contains a target / definition target / permitted axiom / sorryAx / trust axiom (canonical): %s" % q02_badF)
# with --allowed FILE, F <= the allowed list, decided HERE (trusted) on canonical Lean names (the
# String.toName mirror above) from the private copy W/allowed, whose sha256 was taken when it was copied (argv[2]). An open
# lemma L is in F as its redirect axiom L._fv_frontier_axiom (fast preparer) or as L itself (Python preparer); L must be
# listed EXACTLY: a private declaration only with its full kernel name _private.<module>.0.<x> (module included), never by
# its source spelling <x>. A declared project axiom (--axioms, private copy W/axioms, sha256 argv[3]) may be in F as itself.
# A list entry ending in the reserved redirect suffix `_fv_frontier_axiom` names nothing (only `L` itself allows L).
# Anything else in F means the untrusted preparation broke the allowed contract: no verdict (this can only remove a
# CONDITIONAL, never create one).
import hashlib
def f4_names(p, want, what):
    b = open(p, "rb").read()
    if hashlib.sha256(b).hexdigest() != want:
        sys.exit("the private copy of the %s list changed during the preparation" % what)
    out = set()
    for ln in b.decode("utf-8", errors="strict").split("\n"):
        s = ln.strip(" \t\r\n")   # as the preparer's readNames (String.trimAscii: space, tab, CR, LF); skip empty / '#' lines
        if not s or s.startswith("#"):
            continue
        t = parse_lean_name(s)
        if t and t[-1] != ("s", "_fv_frontier_axiom"):   # (r2) the redirect suffix is reserved: such an entry names nothing
            out.add(t)
    return out
f4_alw_sha = sys.argv[2] if len(sys.argv) > 2 else ""
f4_ax_sha = sys.argv[3] if len(sys.argv) > 3 else ""
if f4_alw_sha:
    f4_allowed = f4_names(os.path.join(w, "allowed"), f4_alw_sha, "--allowed")
    f4_axioms = f4_names(os.path.join(w, "axioms"), f4_ax_sha, "--axioms") if f4_ax_sha else set()
    f4_sfx = ("s", "_fv_frontier_axiom")
    f4_out = sorted(n for n, t in zip(F, q02_F)
                    if not (t in f4_allowed or t in f4_axioms or (len(t) > 1 and t[-1] == f4_sfx and t[:-1] in f4_allowed)))
    if f4_out:
        sys.exit("frontier outside the --allowed list (exact canonical names; a private declaration is listed as "
                 "_private.<module>.0.<name>): %s" % f4_out[:20])
F = sorted(F)
json.dump(F, open(os.path.join(w, "F.json"), "w"), ensure_ascii=False)
# cfgA / cfgB keep only the keys of Lake.Check.Config (the official decoder ignores the others; Python
# would re-serialize an ignored finite number such as 1e309 as the non-JSON token Infinity)
c = {k: v for k, v in c.items() if k in ("challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms",
                                 "enable_nanoda", "external_kernels")}
b = dict(c); b["permitted_axioms"] = A + F
json.dump(b, open(os.path.join(w, "cfgB.json"), "w"), ensure_ascii=False)
csorry = b'"pre":0,"str":"sorryAx"}' in open(os.path.join(w, "challenge.export"), "rb").read()
a = dict(c); a["permitted_axioms"] = A + (["sorryAx"] if csorry else [])
json.dump(a, open(os.path.join(w, "cfgA.json"), "w"), ensure_ascii=False)
with open(os.path.join(w, "xaxA.txt"), "w", encoding="utf-8") as xf:
    xf.write("sorryAx\n" if csorry else "")
with open(os.path.join(w, "xaxB.txt"), "w", encoding="utf-8") as xf:
    xf.write("".join(n + "\n" for n in F))
print(len(F))
PY
) || decline "config refused: $CFGMSG"
FSIZE=$CFGMSG
case "$FSIZE" in ''|*[!0-9]*) decline "internal: frontier size '$FSIZE'";; esac
stamp() { stat -c '%i %s %y %z' -- "$SP" "$CP" "$W/challenge.export"; }
STAMP0=$(stamp)
FSHA=$(sha256sum "$CP" | cut -d' ' -f1)
# W stays 0700: the kernels run inside bwrap as the same user; each check makes its own work dir inside

# ---------- optional cache of check A (see --a-cache) ----------
AKEY=; AHIT=0
if [ -n "$ACACHE" ] && [ "$FSIZE" -gt 0 ]; then
  { [ -d "$ACACHE" ] && [ ! -L "$ACACHE" ] && [ "$(stat -c %u -- "$ACACHE")" = "$(id -u)" ] && [ "$(( 0$(stat -c %a -- "$ACACHE") & 077 ))" = 0 ]; } \
    || decline "--a-cache $ACACHE: not a directory owned by the caller without group/other access"
  AKEY=$( { printf 'frontier-A-v1\n'; sha256sum -- "$CP" "$W/challenge.export" "$W/cfgA.json" "$PINSF" "$SOUND_SCRIPT" | cut -d' ' -f1; } | sha256sum | cut -d' ' -f1)
  AREC=$ACACHE/A-$AKEY.ok
  if [ -f "$AREC" ] && [ ! -L "$AREC" ] && [ "$(stat -c %u -- "$AREC")" = "$(id -u)" ] && [ "$(head -c 64 "$AREC")" = "$AKEY" ]; then AHIT=1; fi
fi

# ---------- the two runs of the unchanged sound check ----------
TB=$T; TA=0
if [ "$FSIZE" -gt 0 ]; then   # threads in proportion to the two exports' sizes (the replay work scales with them)
  SA=$(stat -c %s -- "$CP"); SB=$(stat -c %s -- "$SP")
  TA=$(( T * SA / (SA + SB + 1) )); [ "$TA" -ge 1 ] || TA=1; TB=$(( T - TA )); [ "$TB" -ge 1 ] || { TB=1; TA=$(( T > 1 ? T - 1 : 1 )); }
fi
SPFX=(--private-inputs); [ "$TMO" -gt 0 ] && SPFX+=(--timeout "$TMO")
# check B may use the same Lean-kernel leg options as the sound preset (order hints; --incr-dir: the reviewed S08
# incremental leg - feed it the previous REWRITTEN export S' so only the changed constants are replayed); check A: plain
BX=(); [ -n "$HINTS" ] && BX+=(--hints "$HINTS"); [ -n "$INCR" ] && BX+=(--incr-dir "$INCR")
# the sound check refuses permitted axioms outside GOAL S1(3) unless they are listed with --extra-axioms
# (only a sound check that knows the flag holds configs to S1(3); an older one judges A + sorryAx / A + F as before)
XA=(); XB=()
if grep -q -- '--extra-axioms)' "$SOUND_SCRIPT"; then
  [ -s "$W/xaxA.txt" ] && XA=(--extra-axioms "$W/xaxA.txt")
  [ -s "$W/xaxB.txt" ] && XB=(--extra-axioms "$W/xaxB.txt")
fi
if [ "$FSIZE" -gt 0 ] && [ "$AHIT" = 1 ]; then
  TB=$T   # check A cached: B gets every thread
  printf '{"checker":"checkSound","verdict":"ACCEPTED","exit":0,"cached":true,"a_cache_key":"%s","reason":"check A accepted this frontier challenge in an earlier run (--a-cache)"}\n' "$AKEY" > "$W/check_A.json"
  "$SOUND_SCRIPT" "$SP" "$CP" "$W/cfgB.json" --threads "$TB" --json "$W/check_B.json" --workdir "$W" "${SPFX[@]}" "${SX[@]}" "${PNX[@]}" "${BX[@]}" "${XB[@]}" > "$W/check_B.out" 2> "$W/check_B.err"
  RB=$?; RA=0
elif [ "$FSIZE" -gt 0 ]; then
  "$SOUND_SCRIPT" "$CP" "$W/challenge.export" "$W/cfgA.json" --threads "$TA" --json "$W/check_A.json" --workdir "$W" "${SPFX[@]}" "${SX[@]}" "${PNX[@]}" "${XA[@]}" > "$W/check_A.out" 2> "$W/check_A.err" &
  PA=$!
  "$SOUND_SCRIPT" "$SP" "$CP" "$W/cfgB.json" --threads "$TB" --json "$W/check_B.json" --workdir "$W" "${SPFX[@]}" "${SX[@]}" "${PNX[@]}" "${BX[@]}" "${XB[@]}" > "$W/check_B.out" 2> "$W/check_B.err"
  RB=$?
  AKILLED=0
  if [ "$RB" = 1 ]; then kill "$PA" 2>/dev/null && AKILLED=1; fi   # B rejected: A cannot change that (it only matters for CONDITIONAL)
  wait "$PA"; RA=$?
  if [ "$AKILLED" = 1 ] && [ "$RA" != 0 ]; then   # label the stopped run honestly (check-sound's SIGTERM path says 'internal error')
    printf '{"checker":"checkSound","verdict":"STOPPED","exit":2,"reason":"terminated (early stop: check B already rejected)"}\n' > "$W/check_A.json"
  fi
else
  # no open lemma: check B is the plain sound check of S' (= a copy of the export) against the official challenge
  "$SOUND_SCRIPT" "$SP" "$W/challenge.export" "$W/comparator.orig.json" --threads "$TB" --json "$W/check_B.json" --workdir "$W" "${SPFX[@]}" "${SX[@]}" "${PNX[@]}" "${BX[@]}" "${XB[@]}" > "$W/check_B.out" 2> "$W/check_B.err"
  RB=$?; RA=-
fi
for k in A B; do [ -s "$W/check_$k.json" ] || tail -n 1 "$W/check_$k.out" > "$W/check_$k.json" 2>/dev/null; done
log "[$SELF] check A rc=$RA: $(cut -c1-300 "$W/check_A.json" 2>/dev/null)"
log "[$SELF] check B rc=$RB: $(cut -c1-300 "$W/check_B.json" 2>/dev/null)"
[ "$(stamp)" = "$STAMP0" ] || decline "an input was modified during the check"
[ "$(sha256sum "$CP" | cut -d' ' -f1)" = "$FSHA" ] || decline "the frontier challenge changed during the check"
verdict_of() { /usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$1" 2>/dev/null || echo "?"; }
VB=$(verdict_of "$W/check_B.json"); VA=-; [ "$FSIZE" -gt 0 ] && VA=$(verdict_of "$W/check_A.json")
reason_of() { /usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("reason",""))' "$1" 2>/dev/null; }
if [ "$RB:$VB" = 0:ACCEPTED ]; then
  if [ "$FSIZE" = 0 ]; then finish 0 ACCEPTED "no open lemma; the unchanged sound check accepted the export"; fi
  if [ "$RA:$VA" = 0:ACCEPTED ]; then
    if [ -n "$AKEY" ] && [ "$AHIT" = 0 ]; then   # record the acceptance (atomically) for later runs with the same key
      printf '%s\n' "$AKEY" > "$ACACHE/.A-$AKEY.tmp.$$" && mv -f "$ACACHE/.A-$AKEY.tmp.$$" "$ACACHE/A-$AKEY.ok" 2>/dev/null || rm -f "$ACACHE/.A-$AKEY.tmp.$$"
    fi
    finish 3 CONDITIONAL "$FSIZE open lemma(s); A: the frontier challenge agrees with the official challenge; B: the export with the frontier as axioms is accepted against it"
  fi
  if [ "$RA:$VA" = 1:REJECTED ]; then decline "check A: the minted frontier challenge does not agree with the official challenge ($(reason_of "$W/check_A.json")): no verdict"; fi
  decline "check A gave no verdict (rc=$RA, $VA)"
fi
if [ "$RB:$VB" = 1:REJECTED ]; then finish 1 REJECTED "check B: $(reason_of "$W/check_B.json")"; fi
# (a rejection by B stands even if A was stopped or failed: B judges the export itself; a wrong frontier challenge can
#  only make B reject a valid export - availability, never an acceptance)
decline "check B gave no verdict (rc=$RB, $VB)"
}
main "$@"; exit $?
