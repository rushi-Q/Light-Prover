#!/bin/bash
# tests/fvwork-warm-base/run.sh [WORKDIR] -- regression test: no warm-delta path can accept against a stale base (CRITICAL,
# tools/fvwork/fvwork.py serve --check warm): a warm-delta verdict returned no export, so the base advanced its TREE to the
# new work/proj while keeping the previous base EXPORT loaded in the warm daemon (fvcheckd); later deltas were computed
# against the new tree but judged against the stale export -> `axiom fake_cheat : False` ACCEPTED (variant A: the same
# rejected request twice; variant B: two merge=True patches through fastverify-mcp fv_verify_patch, zero rejected
# requests). The projects of the reproduction are generated below.
# Two more warm-delta false accepts are known (deleted constants: no tombstones in
# the delta; --copy-mode hardlink: request code rewrites the stored base), so the package KEEPS the warm guard.
# Rows:
#   guard/serve-warm-refused, guard/hardlink-warm-refused, guard/incr-reverify-warm-daemon-refused: no warm-delta path
#     can run (fvwork serve --check warm exits; --copy-mode hardlink with --check warm exits; incr-reverify --warm-daemon
#     exits 2). On a copy WITHOUT the guard (e.g. FV_ROOT=<pre-guard copy>) these rows FAIL and the exploit rows run:
#   A/req1-rejected, A/base-export-binding, A/req2-not-accepted, B/step1-accepted, B/step2-not-accepted,
#   B/base-not-poisoned-as-accepted (only when `serve --check warm` starts; the pre-guard fvwork ACCEPTS the cheat there)
#   guard/real-state-warm-refused: a REAL state (init-challenge + fvwork init with the caller's comparator pin,
#     the exploit rows' setup) refuses serve --check warm too (only when the guard holds; needs the 4.33.1 toolchain)
# Without --experimental-incremental, fvwork serve refuses --check
#   warm with the experimental-incremental gate (exit 2, "uses the EXPERIMENTAL incremental machinery") before the warm guard is
#   reached, so the guard rows check BOTH: the gate without the flag, and the warm guard (resp. the hardlink refusal) WITH
#   --experimental-incremental. fvwork init REQUIRES the caller's --comparator-sha256: the setup passes the sha256
#   of the pinned challenge's comparator.json. Both options are passed only when this fvwork.py has them, so a pre-guard copy
#   (which predates them) still runs the exploit rows as before. Under --experimental-incremental an answer is never counted
#   (exit 2, NO-VERDICT, "provisional"), so on a copy with that gate but WITHOUT the guard the exploit rows would FAIL (want
#   exit 1 REJECTED) - never pass by accident.
# Every build runs in bin/fastverify's / fvwork's bwrap sandbox. Needs the official 4.33.1 toolchain and the warm binaries
# (/scratch/fastverify-next/warm/v1) for the exploit rows. Exit 0 iff every row PASS. FV_ROOT=<package> for another copy.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/fvwork-warm-base.XXXXXX") || exit 2
PIDS=()
cleanup() {
  for st in "$W/varA/fvw" "$W/varB/fvw"; do
    [ -S "$st/sock" ] && python3 -I -B "$FV/tools/fvwork/fvwork.py" stop --state "$st" > /dev/null 2>&1
  done
  for p in "${PIDS[@]}"; do kill "$p" 2>/dev/null; wait "$p" 2>/dev/null; done
  rm -rf "$W"
}
trap cleanup EXIT
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
# the interface of this fvwork.py: the experimental-incremental gate and the caller's comparator pin
XINC=(); grep -q 'add_argument("--experimental-incremental"' "$FV/tools/fvwork/fvwork.py" && XINC=(--experimental-incremental)
PINOPT=0; grep -q 'add_argument("--comparator-sha256"' "$FV/tools/fvwork/fvwork.py" && PINOPT=1
GATE="uses the EXPERIMENTAL incremental machinery"
# a refusal of warm mode: the message names the option and says it is not available / disabled (wording-independent)
refused_msg() { grep -q -- "$1" "$2" && grep -Eq "not available|disabled" "$2"; }   # refused_msg OPTION LOG
# ---------------- the guard: no warm-delta path can be started ----------------
mkdir -p "$W/g/fvw"; printf '{"fv": "%s", "threads": 2}\n' "$FV" > "$W/g/fvw/config.json"
timeout 60 python3 -I -B "$FV/tools/fvwork/fvwork.py" serve --state "$W/g/fvw" --check warm > "$W/g/warm.log" 2>&1; rc=$?
GUARD=0
if [ ${#XINC[@]} -gt 0 ]; then   # the gate refuses first (exit 2); the warm guard still refuses WITH the flag
  timeout 60 python3 -I -B "$FV/tools/fvwork/fvwork.py" serve --state "$W/g/fvw" --check warm "${XINC[@]}" > "$W/g/warmx.log" 2>&1; rcx=$?
  if [ "$rc" = 2 ] && grep -q "$GATE" "$W/g/warm.log" && [ "$rcx" != 0 ] && refused_msg "--check warm" "$W/g/warmx.log"; then
    GUARD=1; ok guard/serve-warm-refused "serve --check warm: experimental gate exit 2; with --experimental-incremental: the warm guard exits ($rcx)"
  else ko guard/serve-warm-refused "exit $rc / with the flag $rcx: $(tail -c 160 "$W/g/warm.log" | tr '\n' ' ') / $(tail -c 160 "$W/g/warmx.log" | tr '\n' ' ')"; fi
elif [ "$rc" != 0 ] && refused_msg "--check warm" "$W/g/warm.log"; then GUARD=1; ok guard/serve-warm-refused "fvwork serve --check warm exits ($rc)"
else ko guard/serve-warm-refused "exit $rc: $(tail -c 200 "$W/g/warm.log" | tr '\n' ' ')"; fi
timeout 60 python3 -I -B "$FV/tools/fvwork/fvwork.py" serve --state "$W/g/fvw" --check warm --copy-mode hardlink > "$W/g/hl.log" 2>&1; rc=$?
if [ ${#XINC[@]} -gt 0 ]; then
  timeout 60 python3 -I -B "$FV/tools/fvwork/fvwork.py" serve --state "$W/g/fvw" --check warm --copy-mode hardlink "${XINC[@]}" > "$W/g/hlx.log" 2>&1; rcx=$?
  [ "$rc" = 2 ] && grep -q "$GATE" "$W/g/hl.log" && [ "$rcx" != 0 ] && { grep -q "copy-mode hardlink" "$W/g/hlx.log" || refused_msg "--check warm" "$W/g/hlx.log"; } \
    && ok guard/hardlink-warm-refused "experimental gate exit 2; with --experimental-incremental exit $rcx ($(grep -o 'cannot be combined with --copy-mode hardlink' "$W/g/hlx.log" || echo guard))" \
    || ko guard/hardlink-warm-refused "exit $rc / with the flag $rcx: $(tail -c 160 "$W/g/hl.log" | tr '\n' ' ') / $(tail -c 160 "$W/g/hlx.log" | tr '\n' ' ')"
else
[ "$rc" != 0 ] && { grep -q "copy-mode hardlink" "$W/g/hl.log" || refused_msg "--check warm" "$W/g/hl.log"; } && ok guard/hardlink-warm-refused "exit $rc ($(grep -o 'cannot be combined with --copy-mode hardlink' "$W/g/hl.log" || echo guard))" \
  || ko guard/hardlink-warm-refused "exit $rc: $(tail -c 200 "$W/g/hl.log" | tr '\n' ' ')"
fi
mkdir -p "$W/g/ir"
bash "$FV/tools/incr/incr-reverify.sh" "$W/g" "$W/g" "$W/g" "$W/g/ir/out" --warm-daemon "$W/g" > "$W/g/ir.log" 2>&1; rc=$?
[ "$rc" = 2 ] && refused_msg "--warm-daemon" "$W/g/ir.log" && ok guard/incr-reverify-warm-daemon-refused "exit 2" \
  || ko guard/incr-reverify-warm-daemon-refused "exit $rc: $(tail -c 200 "$W/g/ir.log" | tr '\n' ' ')"
mkproj() {  # mkproj DIR NAME : lake skeleton (4.33.1, no packages)
  mkdir -p "$1"; printf 'leanprover/lean4:v4.33.1\n' > "$1/lean-toolchain"
  printf 'name = "%s"\ndefaultTargets = ["%s"]\n[[lean_lib]]\nname = "%s"\n' "$2" "$2" "$2" > "$1/lakefile.toml"
  printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n' > "$1/lake-manifest.json"
}
init_state() {  # init_state DIR : the pinned challenge + fvwork init on DIR/proj_good with the caller's pins
  local V=$1
  "$FV/bin/fv" init-challenge "$V/chal_src" "$V/pinned_chal" --threads 4 --json > "$V/initc.json" 2>&1 || return 1
  local pin; pin=$(awk '{print $1}' "$V/pinned_chal/challenge.export.sha256")
  local cp=(); [ "$PINOPT" = 1 ] && cp=(--comparator-sha256 "$(sha256sum < "$V/pinned_chal/comparator.json" | cut -c1-64)")   # the caller's comparator pin
  python3 -I -B "$FV/tools/fvwork/fvwork.py" init --state "$V/fvw" --project "$V/proj_good" --challenge "$V/pinned_chal" \
    --challenge-sha256 "$pin" "${cp[@]}" --packages "$V/empty_ws" --threads 4 --fv "$FV" --tc "$TC" > "$V/init.log" 2>&1 || return 1
}
serve() {  # serve DIR : fvwork init on DIR/proj_good + serve --check warm; waits for the warm sidecar
  local V=$1
  init_state "$V" || return 1
  python3 -I -B "$FV/tools/fvwork/fvwork.py" serve --state "$V/fvw" --check warm "${XINC[@]}" --jobs 2 --warm 0 --threads 4 > "$V/srv.log" 2>&1 &
  PIDS+=($!)
  for _ in $(seq 1 600); do
    [ -f "$V/fvw/warmd/ready.json" ] && [ -S "$V/fvw/sock" ] && return 0
    kill -0 "${PIDS[-1]}" 2>/dev/null || return 2
    sleep 0.5
  done
  return 3
}
jf() { python3 -I -c 'import json,sys
try: j=json.load(open(sys.argv[1]))
except Exception: print("unparsable"); sys.exit()
print(" ".join(str(j.get(k)) for k in sys.argv[2:]))' "$@"; }
mkchalA() {  # mkchalA DIR : variant A's challenge + proj_good + proj_cheat (as in the reproduction)
  local V=$1; mkdir -p "$V/empty_ws/.lake/packages"
  mkproj "$V/chal_src" WarmBugA
  printf 'theorem target_thm : ∀ n : Nat, n + 0 = n := by sorry\n' > "$V/chal_src/WarmBugA.lean"
  printf '{"challenge_module":"WarmBugA","solution_module":"WarmBugA","theorem_names":["target_thm"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}\n' > "$V/chal_src/comparator.json"
  cp -a "$V/chal_src" "$V/proj_good"; printf 'theorem target_thm : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n\n' > "$V/proj_good/WarmBugA.lean"
  cp -a "$V/chal_src" "$V/proj_cheat"; printf 'axiom fake_cheat : False\ntheorem target_thm : ∀ n : Nat, n + 0 = n := fake_cheat.elim\n' > "$V/proj_cheat/WarmBugA.lean"
}
if [ "$GUARD" = 1 ]; then
  # the exploit rows' setup on this interface: a real state (fvwork init with the caller's comparator pin) also
  # refuses serve --check warm (the gate without the flag, the warm guard with it); nothing warm starts
  if [ -n "$TC" ] && [ -x "$TC/bin/lean" ]; then
    VR=$W/real; mkchalA "$VR"; init_state "$VR"; irc=$?
    rec=$(jf "$VR/fvw/config.json" comparator_sha256); want=$(sha256sum < "$VR/pinned_chal/comparator.json" 2>/dev/null | cut -c1-64)
    timeout 60 python3 -I -B "$FV/tools/fvwork/fvwork.py" serve --state "$VR/fvw" --check warm --jobs 2 --warm 0 --threads 4 > "$VR/srv.log" 2>&1; rc=$?
    rcx=0; [ ${#XINC[@]} -gt 0 ] && { timeout 60 python3 -I -B "$FV/tools/fvwork/fvwork.py" serve --state "$VR/fvw" --check warm "${XINC[@]}" \
      --jobs 2 --warm 0 --threads 4 > "$VR/srvx.log" 2>&1; rcx=$?; }
    okr=0
    if [ ${#XINC[@]} -gt 0 ]; then
      [ "$irc" = 0 ] && { [ "$PINOPT" = 0 ] || [ "$rec" = "$want" ]; } && [ "$rc" = 2 ] && grep -q "$GATE" "$VR/srv.log" && [ "$rcx" != 0 ] \
        && refused_msg "--check warm" "$VR/srvx.log" && [ ! -e "$VR/fvw/warmd/ready.json" ] && okr=1
    else
      [ "$irc" = 0 ] && [ "$rc" != 0 ] && refused_msg "--check warm" "$VR/srv.log" && [ ! -e "$VR/fvw/warmd/ready.json" ] && okr=1
    fi
    [ "$okr" = 1 ] && ok guard/real-state-warm-refused "fvwork init with the caller's pin (exit 0, recorded ${rec:0:12}); serve --check warm exit $rc (gate), with --experimental-incremental exit $rcx (warm guard)" \
      || ko guard/real-state-warm-refused "init exit $irc (pin '$rec' vs '${want:0:12}'; $(tail -c 160 "$VR/init.log" | tr '\n' ' ')), serve exit $rc / $rcx: $(tail -c 160 "$VR/srv.log" | tr '\n' ' ')"
  else
    echo "SKIP guard/real-state-warm-refused: needs the official 4.33.1 toolchain"
  fi
  echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]; exit
fi
if [ -z "$TC" ] || [ ! -x "$TC/bin/lean" ] || [ ! -x /scratch/fastverify-next/warm/714773ea/lean4export-delta ]; then
  echo "SKIP exploit rows: needs the official 4.33.1 toolchain and /scratch/fastverify-next/warm/v1"; echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]; exit
fi

# ---------------- variant A ----------------
VA=$W/varA; mkchalA "$VA"
serve "$VA"; src=$?
if [ "$src" != 0 ]; then
  ko A/serve "fvwork serve --check warm did not come up (rc $src): $(tail -c 300 "$VA/srv.log" | tr '\n' ' ') $(tail -c 200 "$VA/init.log" | tr '\n' ' ')"
else
  python3 -I -B "$FV/tools/fvwork/fvwork.py" verify --state "$VA/fvw" --tree "$VA/proj_cheat" > "$VA/req1.json" 2>&1; r1=$?
  v1=$(jf "$VA/req1.json" verdict trust base_advanced)
  [ "$r1" = 1 ] && [ "${v1%% *}" = REJECTED ] && ok A/req1-rejected "exit 1 '$v1'" || ko A/req1-rejected "exit $r1 '$v1'"
  b=$(python3 -I -c 'import json,sys; b=json.load(open(sys.argv[1])); print("ok" if (b.get("export") is None or b.get("export_of") == (b.get("proj") or b.get("src"))) else "stale export %s for tree %s" % (b.get("export"), b.get("proj")))' "$VA/fvw/base.json" 2>&1)
  [ "$b" = ok ] && ok A/base-export-binding "advanced base: export null or the export of exactly its tree" || ko A/base-export-binding "$b"
  python3 -I -B "$FV/tools/fvwork/fvwork.py" verify --state "$VA/fvw" --tree "$VA/proj_cheat" > "$VA/req2.json" 2>&1; r2=$?
  v2=$(jf "$VA/req2.json" verdict trust why)
  case "$r2:$v2" in 0:*|*:ACCEPTED*) ko A/req2-not-accepted "exit $r2 '$v2' (stale-base acceptance of fake_cheat)";;
    1:REJECTED*) ok A/req2-not-accepted "exit 1 '$(printf '%s' "$v2" | cut -c1-120)'";;
    *) ko A/req2-not-accepted "exit $r2 '$v2' (want REJECTED)";; esac
  python3 -I -B "$FV/tools/fvwork/fvwork.py" stop --state "$VA/fvw" > /dev/null 2>&1
fi

# ---------------- variant B: merge=True patches through fastverify-mcp ----------------
VB=$W/varB; mkdir -p "$VB/empty_ws/.lake/packages"
mkproj "$VB/chal_src" WarmMerge; mkdir -p "$VB/chal_src/WarmMerge"
printf 'theorem h_lem : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n\n' > "$VB/chal_src/WarmMerge/Helper.lean"
printf 'import WarmMerge.Helper\ntheorem target_thm : ∀ n : Nat, n + 0 = n := by sorry\n' > "$VB/chal_src/WarmMerge.lean"
printf '{"challenge_module":"WarmMerge","solution_module":"WarmMerge","theorem_names":["target_thm"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}\n' > "$VB/chal_src/comparator.json"
cp -a "$VB/chal_src" "$VB/proj_good"; printf 'import WarmMerge.Helper\ntheorem target_thm : ∀ n : Nat, n + 0 = n := h_lem\n' > "$VB/proj_good/WarmMerge.lean"
serve "$VB"; src=$?
if [ "$src" != 0 ]; then
  ko B/serve "fvwork serve --check warm did not come up (rc $src): $(tail -c 300 "$VB/srv.log" | tr '\n' ' ')"
else
  python3 -I -B - "$FV" "$VB" > "$VB/mcp.out" 2>&1 <<'PY'
import json, os, subprocess, sys
fv, w = sys.argv[1], sys.argv[2]
reqs = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
    {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_verify_patch", "arguments": {"merge": True, "files": {
        "WarmMerge/Helper.lean": "axiom fake_cheat : False\ntheorem h_lem : ∀ n : Nat, n + 0 = n := fake_cheat.elim\n",
        "WarmMerge.lean": "import WarmMerge.Helper\ntheorem target_thm : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n\n"}}}},
    {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "fv_verify_patch", "arguments": {"merge": True, "files": {
        "WarmMerge.lean": "import WarmMerge.Helper\ntheorem target_thm : ∀ n : Nat, n + 0 = n := h_lem\n"}}}},
]
p = subprocess.run(["python3", "-I", "-B", os.path.join(fv, "tools", "mcp", "mcp_server.py"), "--allow-root", w,
                    "--fvwork-state", os.path.join(w, "fvw")], input="".join(json.dumps(r) + "\n" for r in reqs),
                   capture_output=True, text=True, timeout=1200)
for ln in p.stdout.splitlines():
    try:
        o = json.loads(ln)
    except ValueError:
        continue
    if o.get("id") in (2, 3):
        sc = (o.get("result") or {}).get("structuredContent") or {}
        print(json.dumps({"id": o["id"], **{k: sc.get(k) for k in ("verdict", "accepted", "reward", "trust", "exit_code", "reason")}}))
PY
  s2=$(grep '"id": 2' "$VB/mcp.out"); s3=$(grep '"id": 3' "$VB/mcp.out")
  v2=$(printf '%s' "$s2" | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.read()); print(j["verdict"], j["accepted"])' 2>/dev/null)
  v3=$(printf '%s' "$s3" | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.read()); print(j["verdict"], j["accepted"], j["reward"])' 2>/dev/null)
  [ "$v2" = "ACCEPTED True" ] && ok B/step1-accepted "the unused poisoned helper + inlined valid proof: '$v2' (legitimate)" \
    || ko B/step1-accepted "'$v2' $(tail -c 200 "$VB/mcp.out")"
  case "$v3" in "REJECTED False 0.0") ok B/step2-not-accepted "target := h_lem (h_lem := fake_cheat.elim): '$v3'";;
    *True*|ACCEPTED*) ko B/step2-not-accepted "'$v3' (stale-base acceptance through merge=True)";;
    *) ko B/step2-not-accepted "'$v3' (want REJECTED) $(printf '%s' "$s3" | cut -c1-200)";; esac
  bv=$(python3 -I -c 'import json,sys; b=json.load(open(sys.argv[1])); print(b.get("verdict"))' "$VB/fvw/base.json" 2>/dev/null)
  hel=$(python3 -I -c 'import json,sys,os; b=json.load(open(sys.argv[1])); p=b.get("proj") or b.get("src"); print(open(os.path.join(p,"WarmMerge.lean")).read().strip().splitlines()[-1])' "$VB/fvw/base.json" 2>/dev/null)
  case "$bv|$hel" in "ACCEPTED|"*":= h_lem") ko B/base-not-poisoned-as-accepted "base records the cheated tree as ACCEPTED";;
    *) ok B/base-not-poisoned-as-accepted "base verdict $bv, base target line '${hel:0:60}'";; esac
fi
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
