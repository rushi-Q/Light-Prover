#!/bin/bash
# tests/frontier-axiom-scope/run.sh [WORKDIR] -- regression test: frontier.py never widens the permitted axioms beyond S1(3) (CRITICAL,
# tools/frontier/frontier.py bypassed GOAL S1(3)): frontier.py forwarded every non-S1 permitted axiom of the
# caller's comparator.json (sorryAx, a custom `axiom cheat : False`) to check-sound.sh --extra-axioms and reported a
# plain ACCEPTED (exit 0) for `theorem prove_false : False` while check-sound.sh and check-frontier.sh DECLINE.
# Reproduction inputs in data/ (SHA256SUMS).
# Rows:
#   evidence/<case>/{verify,pin,scan,prepare,run}: every frontier.py subcommand refuses a config outside S1(3) with NO
#     verdict (exit 2, verdict NO_VERDICT), never ACCEPTED / CONDITIONAL; check-sound.sh / check-frontier.sh still DECLINE
#   canonical/*: a non-S1 axiom spelled «...» is refused; S1 names spelled «propext» are accepted (same parser as the judges)
#   parser/judge-equivalence: frontier.py's parse_lean_name == check-sound.sh's (extracted from its heredoc) on a corpus
#   check/tampered-*: `frontier.py check OUTDIR` re-derives the --extra-axioms lists: a main config permitting more than
#     A + F, a frontier naming sorryAx / a target, a compare config permitting a custom axiom -> refused (exit 2)
#   control/*: S1 config: prove_false := sorry -> at most CONDITIONAL (open subgoal False, exit 3); cheat -> REJECTED
# verify/run pass the comparator pin with the challenge pin (both required), so these rows are
#   refused for the S1(3) / EXTRA reason they test, not for a missing pin.
# Exit 0 iff every row PASS. FV_ROOT=<package> runs the rows against another package copy (the test data stays here).
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
FR=$FV/tools/frontier/frontier.py
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/frontier-axiom-scope.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
(cd "$HERE/data" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: SHA256SUMS mismatch"; echo "RESULT pass=0 fail=1"; exit 1; }
cp -a "$HERE/data/sorry" "$HERE/data/custom_axiom" "$W/"
chmod -R u+w "$W"
jfield() { python3 -I -c 'import json,sys
t=open(sys.argv[1],encoding="utf-8",errors="replace").read().strip()
try: j=json.loads(t)
except Exception:
    try: j=json.loads(t.splitlines()[-1])
    except Exception: print("unparsable"); sys.exit()
print(j.get(sys.argv[2]))' "$1" "$2" 2>/dev/null || echo unparsable; }
refused() {  # refused ROW RC OUTFILE : exit 2 and last JSON line verdict NO_VERDICT
  local row=$1 rc=$2 out=$3 v
  v=$(jfield "$out" verdict)
  if [ "$rc" = 2 ] && [ "$v" = NO_VERDICT ]; then ok "$row" "exit 2, NO_VERDICT: $(jfield "$out" why | cut -c1-110)"
  else ko "$row" "exit $rc verdict $v (want exit 2 NO_VERDICT) :: $(tail -c 300 "$out" | tr '\n' ' ')"; fi
}
for CASE in sorry custom_axiom; do
  D=$W/$CASE; CSHA=$(sha256sum "$D/challenge.export" | cut -d' ' -f1)
  python3 -I "$FR" verify "$D/solution.export" "$D/challenge.export" "$D/comparator.json" "$W/fr_$CASE" \
    --challenge-sha256 "$CSHA" --comparator-sha256 "$(sha256sum "$D/comparator.json" | cut -d' ' -f1)" --threads 4 > "$W/verify_$CASE.out" 2> "$W/verify_$CASE.err"; rc=$?
  refused "evidence/$CASE/verify" $rc "$W/verify_$CASE.out"
  jfield "$W/verify_$CASE.out" why | grep -q 'outside GOAL S1(3)' && ok "evidence/$CASE/verify-reason" "the S1(3) refusal" \
    || ko "evidence/$CASE/verify-reason" "$(jfield "$W/verify_$CASE.out" why | cut -c1-200)"
  python3 -I "$FR" pin "$D/solution.export" "$D/challenge.export" "$D/comparator.json" "$W/pin_$CASE" --threads 4 \
    > "$W/pin_$CASE.out" 2>&1; rc=$?
  if [ "$rc" = 2 ] && [ ! -e "$W/pin_$CASE/frontier.json" ]; then ok "evidence/$CASE/pin" "exit 2, nothing pinned"
  else ko "evidence/$CASE/pin" "exit $rc $(tail -c 200 "$W/pin_$CASE.out" | tr '\n' ' ')"; fi
  python3 -I "$FR" scan "$D/solution.export" "$D/comparator.json" > "$W/scan_$CASE.out" 2>/dev/null; rc=$?
  refused "evidence/$CASE/scan" $rc "$W/scan_$CASE.out"
  python3 -I "$FR" prepare "$D/solution.export" "$D/challenge.export" "$D/comparator.json" "$W/prep_$CASE" \
    > "$W/prep_$CASE.out" 2>/dev/null; rc=$?
  refused "evidence/$CASE/prepare" $rc "$W/prep_$CASE.out"
  [ ! -e "$W/prep_$CASE" ] && ok "evidence/$CASE/prepare-writes-nothing" "no OUTDIR created" || ko "evidence/$CASE/prepare-writes-nothing" "OUTDIR exists"
  mkdir -p "$W/run_$CASE/proj"   # refused before any build (the challenge dir's config is outside S1(3))
  python3 -I "$FR" run "$W/run_$CASE/proj" "$D" "$W/run_$CASE/out" --challenge-sha256 "$CSHA" --comparator-sha256 "$(sha256sum "$D/comparator.json" | cut -d' ' -f1)" > "$W/run_$CASE.out" 2>/dev/null; rc=$?
  if [ "$rc" = 2 ] && [ "$(jfield "$W/run_$CASE.out" verdict)" = NO_VERDICT ] && [ ! -e "$W/run_$CASE/out/fv" ] \
      && jfield "$W/run_$CASE.out" why | grep -q 'outside GOAL S1(3)'; then   # the S1(3) refusal, not another one
    ok "evidence/$CASE/run" "exit 2, refused before bin/fastverify ran: $(jfield "$W/run_$CASE.out" why | cut -c1-90)"
  else ko "evidence/$CASE/run" "exit $rc $(tail -c 200 "$W/run_$CASE.out" | tr '\n' ' ')"; fi
  "$FV/check/sound/check-sound.sh" "$D/solution.export" "$D/challenge.export" "$D/comparator.json" --challenge-sha256 "$CSHA" \
    --threads 4 --json "$W/cs_$CASE.json" > /dev/null 2>&1; rc=$?
  [ "$rc" = 2 ] && ok "evidence/$CASE/check-sound" "DECLINED (unchanged judge)" || ko "evidence/$CASE/check-sound" "exit $rc"
  "$FV/check/frontier/check-frontier.sh" "$D/solution.export" "$D/challenge.export" "$D/comparator.json" --challenge-sha256 "$CSHA" \
    --threads 4 --workdir "$W" --json "$W/cf_$CASE.json" > /dev/null 2>&1; rc=$?
  [ "$rc" = 2 ] && ok "evidence/$CASE/check-frontier" "DECLINED" || ko "evidence/$CASE/check-frontier" "exit $rc"
done

# ---- canonical names (the judges' parser) ----
D=$W/sorry
python3 -I - "$D/comparator.json" "$W" <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
S1 = ["propext", "Quot.sound", "Classical.choice"]
for name, ax in (("guillemet-sorry", S1 + ["«sorryAx»"]), ("guillemet-custom", S1 + ["«cheat»"]),
                 ("not-a-name", S1 + ["cheat axiom"]), ("guillemet-s1", ["«propext»", "Quot.«sound»", "Classical.choice"])):
    d = dict(c); d["permitted_axioms"] = ax
    json.dump(d, open("%s/cfg-%s.json" % (sys.argv[2], name), "w"))
open("%s/cfg-dupkey.json" % sys.argv[2], "w").write(
    '{"theorem_names":["prove_false"],"definition_names":[],"permitted_axioms":["sorryAx"],'
    '"permitted_axioms":["propext","Quot.sound","Classical.choice"]}')
PY
for n in guillemet-sorry guillemet-custom not-a-name dupkey; do
  python3 -I "$FR" scan "$D/solution.export" "$W/cfg-$n.json" > "$W/scan-$n.out" 2>/dev/null; rc=$?
  refused "canonical/$n" $rc "$W/scan-$n.out"
done
python3 -I "$FR" scan "$D/solution.export" "$W/cfg-guillemet-s1.json" > "$W/scan-s1.out" 2>/dev/null; rc=$?
[ "$rc" = 0 ] && [ "$(jfield "$W/scan-s1.out" targets)" = "['prove_false']" ] && ok "canonical/guillemet-s1-accepted" "«propext», Quot.«sound» = S1 (scan runs)" \
  || ko "canonical/guillemet-s1-accepted" "exit $rc $(tail -c 200 "$W/scan-s1.out")"

# ---- the parser is the judges' parser ----
r=$(python3 -I - "$FR" "$FV/check/sound/check-sound.sh" <<'PY' 2>&1
import importlib.util, sys
spec = importlib.util.spec_from_file_location("frontier_under_test", sys.argv[1])
fr = importlib.util.module_from_spec(spec)
sys.path.insert(0, __import__("os").path.dirname(sys.argv[1]))
spec.loader.exec_module(fr)
src = open(sys.argv[2], encoding="utf-8").read()
i = src.find("def _is_letter_like(c):"); j = src.find("\ndef q02_canon", i)
if i < 0 or j < 0:
    print("SKIP judge parser not found in check-sound.sh"); sys.exit(0)
g = {}
exec(src[i:j], g)
corpus = ["", "a", "a.b", "a..b", ".a", "a.", "«»", "«a.b».c", "«a", "a.«b", "1", "a.1", "a.01", "0.a", "x'", "x!?", "α",
          "λ", "Π", "Σ", "αβ.γ", "a₁", "aᵢ", "ⱼ", "_", "_.1", "a b", "a\nb", "sorryAx", "«sorryAx»", "Quot.«sound»",
          "Classical.choice", "Nat.add", "ℕ", "𝔸", "ÿ", "×", "÷", "ŀ", "Ā", "a-b", "a/b", "«a»«b»", "a.«»", "«»."]
corpus += [chr(c) for c in range(0x20, 0x3000, 7)] + ["a" + chr(c) for c in range(0x20, 0x3000, 7)]
bad = [s for s in corpus if fr.parse_lean_name(s) != g["parse_lean_name"](s)]
print("OK %d" % len(corpus) if not bad else "DIFF %r" % bad[:5])
PY
)
case "$r" in OK*) ok parser/judge-equivalence "frontier.parse_lean_name == check-sound.sh parse_lean_name on ${r#OK } strings";;
  SKIP*) echo "SKIP parser/judge-equivalence: ${r#SKIP }";; *) ko parser/judge-equivalence "$(printf '%s' "$r" | tail -c 300)";; esac

# ---- `frontier.py check OUTDIR` with tampered internal configurations (prepared from an honest S1 config) ----
python3 -I - "$D/comparator.json" "$W/cfg-s1.json" <<'PY'
import json, sys
c = json.load(open(sys.argv[1])); c["permitted_axioms"] = ["propext", "Quot.sound", "Classical.choice"]
json.dump(c, open(sys.argv[2], "w"))
PY
python3 -I "$FR" prepare "$D/solution.export" "$D/challenge.export" "$W/cfg-s1.json" "$W/honest" > "$W/honest.out" 2>&1; prc=$?
if [ "$prc" = 0 ]; then
  for mode in main-extra-sorry main-extra-custom frontier-sorry frontier-target compare-custom; do
    rm -rf "$W/t-$mode"; cp -a "$W/honest" "$W/t-$mode"
    python3 -I - "$W/t-$mode" "$mode" <<'PY'
import json, os, sys
d, mode = sys.argv[1], sys.argv[2]
fj = os.path.join(d, "frontier.json"); info = json.load(open(fj))
B = os.path.join(d, "comparator.frontier.json"); A = os.path.join(d, "comparator.compare.json")
cb, ca = json.load(open(B)), json.load(open(A))
if mode == "main-extra-sorry":
    cb["permitted_axioms"].append("sorryAx")
elif mode == "main-extra-custom":
    cb["permitted_axioms"].append("cheat")
elif mode == "frontier-sorry":
    info["frontier"] = info["frontier"] + ["sorryAx"]; cb["permitted_axioms"].append("sorryAx")
elif mode == "frontier-target":
    info["frontier"] = info["frontier"] + ["prove_false"]; cb["permitted_axioms"].append("prove_false")
elif mode == "compare-custom":
    ca["permitted_axioms"].append("cheat")
json.dump(info, open(fj, "w")); json.dump(cb, open(B, "w")); json.dump(ca, open(A, "w"))
PY
    python3 -I "$FR" check "$W/t-$mode" --threads 4 > "$W/t-$mode.out" 2>/dev/null; rc=$?
    refused "check/tampered-$mode" $rc "$W/t-$mode.out"
  done
else ko check/prepare-honest "prepare of the S1 config failed: $(tail -c 300 "$W/honest.out")"; fi

# ---- uniform refusals, malformed OUTDIR, F = [] judged against the OFFICIAL challenge, run EXTRA ----
for spec in "--frontier sorryAx" "--frontier prove_false" "--axioms sorryAx" "--axioms Lean.ofReduceBool"; do
  n=$(echo "$spec" | tr -c 'A-Za-z0-9' _)
  python3 -I "$FR" prepare "$D/solution.export" "$D/challenge.export" "$W/cfg-s1.json" "$W/pl-$n" $spec > "$W/pl-$n.out" 2>/dev/null; rc=$?
  refused "prepare/list$n" $rc "$W/pl-$n.out"
done
if [ "$prc" = 0 ]; then
  rm -rf "$W/t-malformed"; cp -a "$W/honest" "$W/t-malformed"; echo '{"frontier": [' > "$W/t-malformed/frontier.json"
  python3 -I "$FR" check "$W/t-malformed" --threads 4 > "$W/t-malformed.out" 2>/dev/null; rc=$?
  refused "check/malformed-frontier-json" $rc "$W/t-malformed.out"
fi
r=$(python3 -I -B - "$FR" "$W" <<'PY' 2>&1
import importlib.util, json, os, shutil, sys
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("frontier_unit", sys.argv[1])
fr = importlib.util.module_from_spec(spec)
sys.path.insert(0, os.path.dirname(sys.argv[1]))
spec.loader.exec_module(fr)
w = sys.argv[2]
d = os.path.join(w, "honest")
if not hasattr(fr, "check_configs") or not os.path.isdir(d):
    print("FAIL no check_configs / honest OUTDIR"); sys.exit()
info = json.load(open(os.path.join(d, "frontier.json")))
calls = []
class P:
    returncode = 0
    def communicate(self):
        return b"", b""
def fake_run_check(e, c, cfgp, threads, logf, jsonf, svc=None, extra=(), **_kw):   # pins=... passed too
    calls.append((e, c, list(extra)))
    json.dump({"verdict": "ACCEPTED", "exit": 0, "extra_permitted_axioms": []}, open(jsonf, "w"))
    return P(), 0.0
fr.run_check = fake_run_check
# a forged frontier challenge C' (e.g. from a --pinned dir) while F = []: it must not be what the main check judges
cp = os.path.join(d, "frontier", "challenge.export")
os.chmod(cp, 0o644); open(cp, "ab").write(b"\n")
info["frontier_challenge_sha256"] = fr.sha256(cp)
json.dump(info, open(os.path.join(d, "frontier.json"), "w"))
v = fr.check(d, 4)
mains = [c for c in calls if c[0].endswith("solution.frontier.export")]
ok = len(info["frontier"]) == 0 and mains and os.path.realpath(mains[0][1]) == os.path.realpath(info["challenge_export"])
print(("PASS" if ok else "FAIL") + " F=%d main check judged against %s (official %s), verdict %s" % (
    len(info["frontier"]), mains[0][1] if mains else None, info["challenge_export"], v["verdict"]))
PY
)
case "$r" in PASS*) ok check/F-empty-judged-against-official-challenge "${r#PASS }";; *) ko check/F-empty-judged-against-official-challenge "$(printf '%s' "$r" | tail -c 300)";; esac
mkdir -p "$W/run-x/proj"
for x in "--comparator-config $D/comparator.json" "--challenge-sha256 0000" "--from-export $D/solution.export" "--preset fastest"; do
  n=$(echo "$x" | cut -d' ' -f1 | tr -c 'A-Za-z0-9' _)
  cp "$W/cfg-s1.json" "$W/run-x/comparator.json" 2>/dev/null; cp "$D/challenge.export" "$W/run-x/" 2>/dev/null
  python3 -I "$FR" run "$W/run-x/proj" "$W/run-x" "$W/run-x/out$n" --challenge-sha256 "$(sha256sum "$D/challenge.export" | cut -d' ' -f1)" --comparator-sha256 "$(sha256sum "$W/run-x/comparator.json" | cut -d' ' -f1)" -- $x > "$W/run-x$n.out" 2>/dev/null; rc=$?
  if [ "$rc" = 2 ] && [ "$(jfield "$W/run-x$n.out" verdict)" = NO_VERDICT ] && [ ! -e "$W/run-x/out$n/fv" ] \
      && jfield "$W/run-x$n.out" why | grep -q 'EXTRA bin/fastverify option.*not allowed'; then ok "run/extra$n-refused" "exit 2 before bin/fastverify ran (EXTRA option refused)"
  else ko "run/extra$n-refused" "exit $rc $(tail -c 200 "$W/run-x$n.out" | tr '\n' ' ')"; fi
done

# ---- controls with the S1 config (the trusted check runs) ----
python3 -I "$FR" verify "$D/solution.export" "$D/challenge.export" "$W/cfg-s1.json" "$W/ctl-sorry" --threads 4 \
  > "$W/ctl-sorry.out" 2>/dev/null; rc=$?
v=$(jfield "$W/ctl-sorry.out" verdict)
case "$rc:$v" in 0:*|*:ACCEPTED) ko control/sorry-s1 "exit $rc $v: a sorry proof of False ACCEPTED";;
  3:CONDITIONAL|1:REJECTED) ok control/sorry-s1 "exit $rc $v (never a plain acceptance; the open subgoal is reported)";;
  *) ko control/sorry-s1 "exit $rc $v :: $(tail -c 300 "$W/ctl-sorry.out")";; esac
D2=$W/custom_axiom
python3 -I - "$D2/comparator.json" "$W/cfg2-s1.json" <<'PY'
import json, sys
c = json.load(open(sys.argv[1])); c["permitted_axioms"] = ["propext", "Quot.sound", "Classical.choice"]
json.dump(c, open(sys.argv[2], "w"))
PY
python3 -I "$FR" verify "$D2/solution.export" "$D2/challenge.export" "$W/cfg2-s1.json" "$W/ctl-cheat" --threads 4 \
  > "$W/ctl-cheat.out" 2>/dev/null; rc=$?
v=$(jfield "$W/ctl-cheat.out" verdict)
[ "$rc:$v" = 1:REJECTED ] && ok control/custom-axiom-s1 "exit 1 REJECTED (cheat not permitted)" || ko control/custom-axiom-s1 "exit $rc $v :: $(tail -c 300 "$W/ctl-cheat.out")"
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
