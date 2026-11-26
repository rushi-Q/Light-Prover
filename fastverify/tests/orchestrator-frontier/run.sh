#!/bin/bash
# tests/orchestrator-frontier/run.sh [FV_ROOT] (coverage gaps of lib/fastverify.py): no test drives the orchestrator's
# cross-version VETO or its --modulo-frontier verdict mapping (check/sound/test/preset.sh, tests/frontier-conditional = check-frontier.sh
# alone, tests/other-releases = admitted releases only), so mutants that turn the veto into ACCEPTED (PY-0149
# `run.res["verdict"] = "REJECTED"` -> "ACCEPTED"), drop it (PY-0146), or give a CONDITIONAL verdict exit 0 (PY-0177
# `rc = 3` -> `rc = 0`) or no CONDITIONAL at all (PY-0040..0044) survive every suite.
# Cases (export-in --preset sound on the pinned self-test GOOD export, each in a PRIVATE package copy):
#   xv-veto        check/xversion/xvcheck.py = a stub that REJECTS (exit 1, verdict REJECTED, as for a 4.37 challenge whose
#                  definition is sorried) -> exit 1, verdict REJECTED, basis = the cross-version gate, the sound check never runs
#   fr-conditional --modulo-frontier, check/frontier/check-frontier.sh = a stub (preflight -> the real script) that reports
#                  CONDITIONAL (exit 3) -> exit 3, verdict CONDITIONAL, trust sound-conditional (never ACCEPTED, never exit 0)
#   fr-accepted    the same stub reporting ACCEPTED (exit 0) -> exit 0 ACCEPTED (control of the frontier path)
#   fr-lying       the stub exits 3 but its JSON claims ACCEPTED -> no verdict (ERROR exit 2: a report that disagrees
#                  with the exit status is never a verdict; previously the exit code decided -> CONDITIONAL)
set -u
FV=${1:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}
W=$(mktemp -d "${TMPDIR:-/tmp}/fv-frxv.XXXXXX"); trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$FV/check/sound/pins.env"; }
GOOD=$(pin selftest_good); mkdir -p "$W/chal"; cp "$(pin selftest_challenge)" "$W/chal/challenge.export"; cp "$(pin selftest_comparator)" "$W/chal/comparator.json"
CSHA=$(sha256sum "$W/chal/challenge.export" | cut -d' ' -f1)
CFGSHA=$(sha256sum "$W/chal/comparator.json" | cut -d' ' -f1)   # the comparator pin is required with the challenge pin
pass=0; fail=0
cpkg() { rsync -a --exclude tests --exclude pipeline --exclude 'review-*' --exclude __pycache__ "$FV/" "$W/pkg-$1/"; echo "$W/pkg-$1"; }
run() {  # run NAME PKG WANT_EXIT WANT_VERDICT WANT_BASIS_SUBSTRING [extra fastverify args]
  local n=$1 p=$2 we=$3 wv=$4 wb=$5; shift 5
  local out=$W/out-$n
  "$p/bin/fastverify" - "$W/chal" "$out" --from-export "$GOOD" --preset sound --threads 4 --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" "$@" > "$W/log-$n" 2>&1; local rc=$?
  local v; v=$(python3 -I -c 'import json,sys
r=json.load(open(sys.argv[1])); b=str(r.get("verdict_basis")); print(r["verdict"], r.get("exit"), str(r.get("verdict_fast")), int(sys.argv[2] in b), r.get("trust"))' "$out/result.json" "$wb" 2>/dev/null)
  set -- $v
  if [ "$rc" = "$we" ] && [ "${1:-}" = "$wv" ] && [ "${2:-}" = "$we" ] && [ "${3:-}" = "$wv" ] && [ "${4:-}" = 1 ]; then
    echo "PASS $n: exit $rc verdict $1 verdict_fast $3 trust ${5:-}"; pass=$((pass+1))
  else echo "FAIL $n: expected exit $we verdict $wv (basis ~ '$wb'), got exit $rc / '$v' :: $(tail -1 "$W/log-$n" | cut -c1-200)"; fail=$((fail+1)); fi
}
# --- cross-version veto ---
P=$(cpkg xv); mv "$P/check/xversion/xvcheck.py" "$P/check/xversion/xvcheck.real.py"
cat > "$P/check/xversion/xvcheck.py" <<'PY'
import json, os, runpy, sys
_real = os.path.join(os.path.dirname(os.path.abspath(__file__)), "xvcheck.real.py")
if __name__ != "__main__":   # imported by the orchestrator (Lean names, release reader): the real module's functions
    import importlib.util as _u
    _s = _u.spec_from_file_location("xvcheck_real_q04", _real); _m = _u.module_from_spec(_s); _s.loader.exec_module(_m)
    globals().update({k: v for k, v in vars(_m).items() if not k.startswith("__")})
else:
    a = sys.argv[1:]
    if "--json" in a and len(a) >= 3 and not any(x.startswith("--self") for x in a):   # the orchestrator's call: veto
        json.dump({"verdict": "REJECTED", "reason": "test stub: Challenge definition is sorried (4.37 rule)"}, open(a[a.index("--json") + 1], "w"))
        sys.exit(1)
    sys.argv = [_real] + a   # any other caller: the real gate
    runpy.run_path(sys.argv[0], run_name="__main__")
PY
run xv-veto "$P" 1 REJECTED "cross-version gate"
if [ -e "$W/out-xv-veto/log/check_sound.log" ] || [ -e "$W/out-xv-veto/log/sound.json" ]; then echo "FAIL xv-veto-no-check: the sound check ran after the veto"; fail=$((fail+1))
elif [ ! -e "$W/out-xv-veto/log/xversion.json" ]; then echo "FAIL xv-veto-no-check: no log/xversion.json (layout changed?)"; fail=$((fail+1))
else echo "PASS xv-veto-no-check: no sound check after the veto"; pass=$((pass+1)); fi
# --- --modulo-frontier verdict mapping ---
mkfr() {  # mkfr NAME EXIT JSON_VERDICT -> package copy whose check-frontier.sh (non-preflight) writes JSON_VERDICT and exits EXIT
  local P; P=$(cpkg "fr-$1"); mv "$P/check/frontier/check-frontier.sh" "$P/check/frontier/check-frontier.real.sh"
  cat > "$P/check/frontier/check-frontier.sh" <<SH
#!/bin/bash
# test stub of check-frontier.sh (accepts --pins and the identity pins --challenge-sha256 / --comparator-sha256, like the
# real script: bin/fastverify runs only judges that take the pins)
case " \$* " in *" --preflight "*) exec "\$(dirname "\$(readlink -f "\$0")")/check-frontier.real.sh" "\$@";; esac
j=""; prev=""; for x in "\$@"; do [ "\$prev" = --json ] && j=\$x; prev=\$x; done
[ -n "\$j" ] && printf '{"verdict": "$3", "exit": $2, "frontier": [{"name": "stubLemma"}], "frontier_size": 1, "claim": "test stub claim", "checks": {}}\n' > "\$j"
exit $2
SH
  chmod 755 "$P/check/frontier/check-frontier.sh"; echo "$P"
}
run fr-conditional "$(mkfr cond 3 CONDITIONAL)" 3 CONDITIONAL "SOUND-CONDITIONAL" --modulo-frontier
run fr-accepted "$(mkfr acc 0 ACCEPTED)" 0 ACCEPTED "" --modulo-frontier
# (layout control for xv-veto-no-check: a run that does reach the sound check leaves log/check_sound.log)
if [ -e "$W/out-fr-accepted/log/check_sound.log" ]; then echo "PASS layout-control: log/check_sound.log present when the check runs"; pass=$((pass+1))
else echo "FAIL layout-control: no log/check_sound.log in a run that reached the check"; fail=$((fail+1)); fi
# a report that disagrees with the exit status is no verdict (was: the exit code decided -> CONDITIONAL)
run fr-lying "$(mkfr lie 3 ACCEPTED)" 2 ERROR "stage report says verdict" --modulo-frontier
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]
