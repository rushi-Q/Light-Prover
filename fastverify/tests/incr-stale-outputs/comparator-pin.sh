#!/bin/bash
# tests/incr-stale-outputs/comparator-pin.sh [WORKDIR] -- comparator pin of the incremental entry points (bin/fastverify
# refuses a sound run that has --challenge-sha256 but no --comparator-sha256). The cold paths hash the comparator.json they
# pass (fvwork: the state's private copy; incr-reverify: CHALLENGE/comparator.json), forward --comparator-sha256 with
# --challenge-sha256, and refuse (exit 2) a caller pin that does not match. Rows:
#   fvwork/comparator-pin-forwarded     a valid edit ACCEPTED; the cold run's bin/fastverify argv carries --comparator-sha256 =
#                                       sha256 of the state's comparator.json
#   incr/comparator-pin-forwarded       the same through incr-reverify (default cold path)
#   incr/comparator-pin-caller-match    incr-reverify --comparator-sha256 <the right sha> -> ACCEPTED
#   incr/comparator-wrong-pin-refused   incr-reverify --comparator-sha256 <another sha> -> exit 2, no cold run
#   fvwork/init-wrong-comparator-pin-refused  fvwork init --comparator-sha256 <another sha> -> refused, no state
#   fvwork/init-comparator-pin-recorded fvwork init --comparator-sha256 <the right sha> -> config.json records it; a request
#                                       on that state is ACCEPTED
#   fvwork/unpinned-state-refused       a state without a recorded comparator pin (initialized by an earlier package): serve exits 2
#                                       telling the user to re-init
#   fvwork/dotfvwork-equals-cold (a module include_str's .fvwork/version.txt: kept, = direct run)
#   fvwork/m1-dotgit-equals-cold (a broken WarmCp/.git/Evil.lean: fvwork judges the tree a direct run judges),
#     fvwork/init-official-base, official-base-experimental-refused, official-base-serves-cold, init-no-plan-no-verdict-refused
#     (a base without a B3 plan serves the cold path), fvwork/l1-git-equals-commit (--git with an export-ignore file = the commit's tree), cli/*-exit2 (the refusals and usage
#     errors exit exactly 2: serve --check frontier without the flag, verify without a daemon, a missing / unparsable --files,
#     incr-reverify options without a value)
#   control/bin-fastverify-scheme2      bin/fastverify itself with --challenge-sha256 and no --comparator-sha256: exit 2 where
#                                       lib/fastverify.py has the scheme-2 refusal, else a verdict
# FV_ROOT=<package copy>. Needs the official 4.33.1 toolchain. Exit 0 iff every row PASS.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/incr-stale-cp.XXXXXX") || exit 2
W=$(readlink -f "$W")
FW=(python3 -I -B "$FV/tools/fvwork/fvwork.py")
PIDS=()
cleanup() { for st in "$W"/fvw "$W"/fvw2 "$W"/fvw4; do [ -S "$st/sock" ] && "${FW[@]}" stop --state "$st" > /dev/null 2>&1; done
  for p in "${PIDS[@]}"; do kill "$p" 2>/dev/null; wait "$p" 2>/dev/null; done; [ "${KEEP:-0}" = 1 ] || rm -rf "$W"; }
trap cleanup EXIT
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
if [ -z "$TC" ] || [ ! -x "$TC/bin/lean" ]; then echo "SKIP: needs the official 4.33.1 toolchain"; exit 0; fi
jf() { python3 -I -c 'import json,sys
try: j=json.load(open(sys.argv[1]))
except Exception: print("unparsable"); sys.exit()
def g(k):
    o=j
    for p in k.split("."):
        if isinstance(o, list): o = o[int(p)] if len(o) > int(p) else None
        elif isinstance(o, dict): o = o.get(p)
        else: o = None
    return o
print(" ".join(str(g(k)) for k in sys.argv[2:]))' "$@"; }
argpin() {  # argpin RESULT.json : the value after --comparator-sha256 in bin/fastverify's recorded argv (or "none")
  python3 -I -c 'import json,sys
try: a=json.load(open(sys.argv[1]))["fastverify"]["argv"]
except Exception: print("none"); sys.exit()
print(a[a.index("--comparator-sha256")+1] if "--comparator-sha256" in a else "none")' "$1"; }
FA='∀ n : Nat, n + 0 = n'
P=$W; mkdir -p "$P/chal_src/WarmCp" "$P/ws/.lake/packages"
printf 'leanprover/lean4:v4.33.1\n' > "$P/chal_src/lean-toolchain"
printf 'name = "WarmCp"\ndefaultTargets = ["WarmCp"]\n[[lean_lib]]\nname = "WarmCp"\nglobs = ["WarmCp", "WarmCp.+"]\n' > "$P/chal_src/lakefile.toml"
printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n' > "$P/chal_src/lake-manifest.json"
printf 'theorem h_lem : %s := fun n => Nat.add_zero n\n' "$FA" > "$P/chal_src/WarmCp/Helper.lean"
printf 'import WarmCp.Helper\ntheorem target_thm : %s := by sorry\n' "$FA" > "$P/chal_src/WarmCp.lean"
printf '{"challenge_module":"WarmCp","solution_module":"WarmCp","theorem_names":["target_thm"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}\n' > "$P/chal_src/comparator.json"
cp -a "$P/chal_src" "$P/proj_good"; printf 'import WarmCp.Helper\ntheorem target_thm : %s := h_lem\n' "$FA" > "$P/proj_good/WarmCp.lean"
cp -a "$P/proj_good" "$P/proj_edit"; printf 'theorem h_lem : %s := fun _ => rfl\n' "$FA" > "$P/proj_edit/WarmCp/Helper.lean"
"$FV/bin/fv" init-challenge "$P/chal_src" "$P/pinned" --threads 4 --json > "$P/initc.log" 2>&1
PIN=$(awk '{print $1}' "$P/pinned/challenge.export.sha256"); CPIN=$(sha256sum < "$P/pinned/comparator.json" | cut -c1-64)
BAD=$(printf 'x' | sha256sum | cut -c1-64)
# control: bin/fastverify itself (it requires the comparator pin together with the challenge pin)
PINRULE=no; grep -q 'comparator pin "scheme 2"' "$FV/lib/fastverify.py" && PINRULE=yes
"$FV/bin/fastverify" "$P/proj_good" "$P/pinned" "$P/ctl" --preset sound --threads 4 --packages "$P/ws" --challenge-sha256 "$PIN" \
  --export-dir none > "$P/ctl.log" 2>&1; crc=$?
if [ "$PINRULE" = yes ]; then [ $crc = 2 ] && ok control/bin-fastverify-scheme2 "pin rule present: no --comparator-sha256 -> exit 2 (refused)" \
  || ko control/bin-fastverify-scheme2 "pin rule present but exit $crc"
else [ $crc = 0 ] && ok control/bin-fastverify-scheme2 "pin rule absent: no --comparator-sha256 -> exit 0 (a verdict)" \
  || ko control/bin-fastverify-scheme2 "exit $crc"; fi
# fvwork: init (no pin), serve, a valid edit
"${FW[@]}" init --state "$P/fvw" --project "$P/proj_good" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --packages "$P/ws" \
  --threads 4 --fv "$FV" --tc "$TC" > "$P/init.log" 2>&1 || { ko fvwork/init "$(tail -c 300 "$P/init.log")"; echo "RESULT pass=$pass fail=$fail"; exit 1; }
"${FW[@]}" serve --state "$P/fvw" --check sound --jobs 1 --warm 0 --threads 4 > "$P/srv.log" 2>&1 & PIDS+=($!)
for _ in $(seq 1 600); do [ -S "$P/fvw/sock" ] && break; sleep 0.5; done
"${FW[@]}" verify --state "$P/fvw" --tree "$P/proj_edit" --no-advance > "$P/v1.out" 2>&1; rc=$?; tail -1 "$P/v1.out" > "$P/v1.json"
v=$(jf "$P/v1.json" verdict mode); sp=$(sha256sum < "$P/fvw/challenge/comparator.json" | cut -c1-64)
ap=$(argpin "$(jf "$P/v1.json" attempts.0.check.result)")
[ $rc = 0 ] && [ "$v" = "ACCEPTED cold" ] && [ "$ap" = "$sp" ] && ok fvwork/comparator-pin-forwarded "$v; --comparator-sha256 ${ap:0:12} = state's comparator.json" \
  || ko fvwork/comparator-pin-forwarded "exit $rc '$v', forwarded '$ap' vs ${sp:0:12} ($(jf "$P/v1.json" why))"
# incr-reverify (default cold path) on the fvwork base run
CH=$P/ich; mkdir -p "$CH"; cp "$P/pinned/challenge.export" "$P/pinned/comparator.json" "$P/pinned/lean-toolchain" "$CH/"
ir() { local n=$1; shift; rm -rf "$P/t-$n"; cp -a "$P/proj_edit" "$P/t-$n"
  INCR_TC=$TC bash "$FV/tools/incr/incr-reverify.sh" "$P/fvw/cold" "$P/t-$n" "$CH" "$P/i-$n" --challenge-sha256 "$PIN" --threads 4 \
    --packages "$P/ws" "$@" > "$P/i-$n.log" 2>&1; echo $?; }
rc=$(ir a --comparator-sha256 "$CPIN"); v=$(jf "$P/i-a/summary.json" verdict mode); ap=$(argpin "$P/i-a/cold/result.json")
[ "$rc" = 0 ] && [ "$v" = "ACCEPTED cold" ] && [ "$ap" = "$CPIN" ] && ok incr/comparator-pin-forwarded "$v; the caller's --comparator-sha256 ${ap:0:12} forwarded" \
  || ko incr/comparator-pin-forwarded "exit $rc '$v', forwarded '$ap' vs ${CPIN:0:12}"
rc=$(ir b); [ "$rc" = 2 ] && [ ! -e "$P/i-b/cold" ] && grep -q "is required" "$P/i-b.log" && ok incr/no-caller-pin-refused "no --comparator-sha256: exit 2, no cold run (never computed from the file)" \
  || ko incr/no-caller-pin-refused "exit $rc ($(tail -c 200 "$P/i-b.log"))"
rc=$(ir c --comparator-sha256 "$BAD")
[ "$rc" = 2 ] && [ ! -e "$P/i-c/cold" ] && grep -q "refused" "$P/i-c.log" && ok incr/comparator-wrong-pin-refused "exit 2, no cold run" \
  || ko incr/comparator-wrong-pin-refused "exit $rc ($(tail -c 200 "$P/i-c.log"))"
rc=$(ir d --comparator-sha256 ""); [ "$rc" = 2 ] && [ ! -e "$P/i-d/cold" ] && ok incr/empty-pin-refused "exit 2" || ko incr/empty-pin-refused "exit $rc"
# fvwork init with a caller pin (adopting the base run: no second build)
"${FW[@]}" init --state "$P/fvwbad" --project "$P/proj_good" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$BAD" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" --adopt "$P/fvw/cold" > "$P/initbad.log" 2>&1; rc=$?
[ $rc = 2 ] && [ ! -f "$P/fvwbad/config.json" ] && grep -q "refused" "$P/initbad.log" && ok fvwork/init-wrong-comparator-pin-refused "exit $rc, no state" \
  || ko fvwork/init-wrong-comparator-pin-refused "exit $rc ($(tail -c 200 "$P/initbad.log"))"
"${FW[@]}" init --state "$P/fvw2" --project "$P/proj_good" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" --adopt "$P/fvw/cold" > "$P/init2.log" 2>&1; rc=$?
rec=$(jf "$P/fvw2/config.json" comparator_sha256)
"${FW[@]}" serve --state "$P/fvw2" --check sound --jobs 1 --warm 0 --threads 4 > "$P/srv2.log" 2>&1 & PIDS+=($!)
for _ in $(seq 1 600); do [ -S "$P/fvw2/sock" ] && break; sleep 0.5; done
"${FW[@]}" verify --state "$P/fvw2" --tree "$P/proj_edit" --no-advance > "$P/v2.out" 2>&1; rc2=$?; tail -1 "$P/v2.out" > "$P/v2.json"
[ $rc = 0 ] && [ "$rec" = "$CPIN" ] && [ $rc2 = 0 ] && ok fvwork/init-comparator-pin-recorded "config comparator_sha256 ${rec:0:12}; request $(jf "$P/v2.json" verdict)" \
  || ko fvwork/init-comparator-pin-recorded "init exit $rc, recorded '$rec', request exit $rc2 $(jf "$P/v2.json" verdict why)"
# fvwork init: the caller's pin is required; an empty one is a usage error
"${FW[@]}" init --state "$P/fvwnop" --project "$P/proj_good" --challenge "$P/pinned" --challenge-sha256 "$PIN" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" --adopt "$P/fvw/cold" > "$P/initnop.log" 2>&1; rc=$?
"${FW[@]}" init --state "$P/fvwemp" --project "$P/proj_good" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" --adopt "$P/fvw/cold" > "$P/initemp.log" 2>&1; rc2=$?
[ $rc = 2 ] && [ $rc2 = 2 ] && [ ! -f "$P/fvwnop/config.json" ] && [ ! -f "$P/fvwemp/config.json" ] \
  && ok fvwork/init-pin-required "no --comparator-sha256 / an empty one: exit 2 / 2, no state" || ko fvwork/init-pin-required "exit $rc / $rc2"
rec2=$(jf "$P/fvw2/config.json" comparator_pin_from_caller)
[ "$rec2" = True ] && ok fvwork/init-pin-from-caller "config comparator_pin_from_caller True" || ko fvwork/init-pin-from-caller "'$rec2'"
# (L1) an experimental daemon answers a bad request with trust none
"${FW[@]}" init --state "$P/fvw4" --project "$P/proj_good" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" --adopt "$P/fvw/cold" > "$P/init4.log" 2>&1
if [ "$(jf "$P/fvw4/base.json" init_no_plan)" = True ]; then   # this tree's fast build declined (e.g. lean_lib
  # globs -> official build): the base has no B3 plan, so the EXPERIMENTAL machinery is refused (fail closed) - nothing to serve
  timeout 60 "${FW[@]}" serve --state "$P/fvw4" --check sound --jobs 1 --warm 0 --threads 4 --experimental-incremental > "$P/srv4.log" 2>&1; rc=$?
  [ $rc = 2 ] && grep -q "no B3 build tree" "$P/srv4.log" && ok exp/bad-request-trust-none "base without a B3 plan on this tree: serve --experimental-incremental refused (exit 2)" \
    || ko exp/bad-request-trust-none "no-plan base: experimental serve exit $rc ($(tail -c 200 "$P/srv4.log"))"
else
"${FW[@]}" serve --state "$P/fvw4" --check sound --jobs 1 --warm 0 --threads 4 --experimental-incremental > "$P/srv4.log" 2>&1 & PIDS+=($!)
for _ in $(seq 1 600); do [ -S "$P/fvw4/sock" ] && break; sleep 0.5; done
python3 -I -c 'import json,sys; json.dump({"../escape.lean": "theorem x : True := trivial"}, open(sys.argv[1], "w"))' "$P/esc.files"
"${FW[@]}" verify --state "$P/fvw4" --files "$P/esc.files" --no-advance > "$P/esc.out" 2>&1; rc=$?; tail -1 "$P/esc.out" > "$P/esc.json"
v=$(jf "$P/esc.json" verdict trust)
[ $rc = 2 ] && [ "$v" = "NO-VERDICT none" ] && ok exp/bad-request-trust-none "$v" || ko exp/bad-request-trust-none "exit $rc '$v'"
"${FW[@]}" stop --state "$P/fvw4" > /dev/null 2>&1
fi
# a state initialized by an earlier package (no caller-given comparator pin): serve refuses, exit 2, re-init message
"${FW[@]}" init --state "$P/fvw3" --project "$P/proj_good" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" --adopt "$P/fvw/cold" > "$P/init3.log" 2>&1
python3 -I -c 'import json,sys; p=sys.argv[1]; c=json.load(open(p)); c.pop("comparator_sha256", None); c.pop("comparator_pin_from_caller", None); json.dump(c, open(p, "w"))' "$P/fvw3/config.json"
timeout 60 "${FW[@]}" serve --state "$P/fvw3" --check sound --jobs 1 --warm 0 --threads 4 > "$P/srv3.log" 2>&1; rc=$?
[ $rc = 2 ] && grep -q "re-initialize" "$P/srv3.log" && ok fvwork/unpinned-state-refused "exit 2: $(head -c 120 "$P/srv3.log")" \
  || ko fvwork/unpinned-state-refused "exit $rc: $(tail -c 200 "$P/srv3.log")"
# ---- M1 (.git entries kept as a direct run keeps them), L1 (--git = a plain checkout), L2 (exit 2)
ctl() { local n=$1 t=$2; rm -rf "$P/c-$n" "$P/ctl-$n"; cp -a "$t" "$P/c-$n"; rm -rf "$P/c-$n/.lake"
  "$FV/bin/fastverify" "$P/c-$n" "$P/pinned" "$P/ctl-$n" --preset sound --threads 4 --packages "$P/ws" --challenge-sha256 "$PIN" \
    --comparator-sha256 "$CPIN" --export-dir none > "$P/ctl-$n.log" 2>&1; echo "$? $(jf "$P/ctl-$n/result.json" verdict)"; }
rm -rf "$P/proj_g1"; cp -a "$P/proj_edit" "$P/proj_g1"; mkdir -p "$P/proj_g1/WarmCp/.git"
printf 'theorem evil : (1 : Nat) = 2 := rfl\n' > "$P/proj_g1/WarmCp/.git/Evil.lean"
c=$(ctl g1 "$P/proj_g1")
"${FW[@]}" verify --state "$P/fvw2" --tree "$P/proj_g1" --no-advance > "$P/g1.out" 2>&1; rc=$?; tail -1 "$P/g1.out" > "$P/g1.json"
v="$rc $(jf "$P/g1.json" verdict)"; a=$(echo "$v" | awk '{print $1, ($2 ~ /^NO/ ? "NO" : $2)}'); b=$(echo "$c" | awk '{print $1, ($2 ~ /^NO/ ? "NO" : $2)}')
[ "$a" = "$b" ] && ok fvwork/m1-dotgit-equals-cold "fvwork $v = direct $c" || ko fvwork/m1-dotgit-equals-cold "fvwork $v != direct $c"
rm -rf "$P/proj_fv"; cp -a "$P/proj_edit" "$P/proj_fv"; mkdir -p "$P/proj_fv/.fvwork"; printf 'v1' > "$P/proj_fv/.fvwork/version.txt"
printf 'def fvver : String := include_str "../.fvwork/version.txt"\n' >> "$P/proj_fv/WarmCp/Helper.lean"
c=$(ctl fv "$P/proj_fv")
"${FW[@]}" verify --state "$P/fvw2" --tree "$P/proj_fv" --no-advance > "$P/fv.out" 2>&1; rc=$?; tail -1 "$P/fv.out" > "$P/fv.json"
v="$rc $(jf "$P/fv.json" verdict)"
[ "$v" = "$c" ] && [ "$rc" = 0 ] && ok fvwork/dotfvwork-equals-cold "fvwork $v = direct $c (.fvwork/version.txt kept)" || ko fvwork/dotfvwork-equals-cold "fvwork $v vs direct $c"
rm -rf "$P/repo"; cp -a "$P/proj_edit" "$P/repo"; printf 'WarmCp/Helper.lean export-ignore\n' > "$P/repo/.gitattributes"
git -C "$P/repo" init -q && git -C "$P/repo" add -A && git -C "$P/repo" -c user.email=t@t -c user.name=t commit -qm base
c=$(ctl repo "$P/repo")
"${FW[@]}" verify --state "$P/fvw2" --git "$P/repo" --rev HEAD --no-advance > "$P/l1.out" 2>&1; rc=$?; tail -1 "$P/l1.out" > "$P/l1.json"
v="$rc $(jf "$P/l1.json" verdict)"
[ "$v" = "$c" ] && [ "$rc" = 0 ] && ok fvwork/l1-git-equals-commit "fvwork --git $v = direct run on the commit's tree $c (export-ignore not applied)" \
  || ko fvwork/l1-git-equals-commit "fvwork --git $v vs direct $c"
# the same --git request with the repository under /tmp (the git sandbox mounts a tmpfs on /tmp)
GT=$(mktemp -d /tmp/incr-stale-git.XXXXXX); cp -a "$P/repo" "$GT/repo"
"${FW[@]}" verify --state "$P/fvw2" --git "$GT/repo" --rev HEAD --no-advance > "$P/l1t.out" 2>&1; rc=$?; tail -1 "$P/l1t.out" > "$P/l1t.json"
v="$rc $(jf "$P/l1t.json" verdict)"; rm -rf "$GT"
[ "$v" = "$c" ] && [ "$rc" = 0 ] && ok fvwork/l1-git-under-tmp-equals-commit "fvwork --git (repo under /tmp) $v = direct $c" \
  || ko fvwork/l1-git-under-tmp-equals-commit "fvwork --git (repo under /tmp) $v vs direct $c ($(jf "$P/l1t.json" why | cut -c1-120))"
timeout 60 "${FW[@]}" serve --state "$P/fvw3" --check frontier --jobs 1 --warm 0 --threads 4 > "$P/optin3.log" 2>&1; rc=$?
[ $rc = 2 ] && ok cli/serve-frontier-without-flag-exit2 "exit 2" || ko cli/serve-frontier-without-flag-exit2 "exit $rc (want exactly 2)"
"${FW[@]}" verify --state "$P/fvw3" --tree "$P/proj_edit" > "$P/nod.out" 2>&1; rc=$?
[ $rc = 2 ] && ok cli/verify-no-daemon-exit2 "exit 2" || ko cli/verify-no-daemon-exit2 "exit $rc (want exactly 2)"
"${FW[@]}" verify --state "$P/fvw2" --files "$P/nonexistent.json" > "$P/badf.out" 2>&1; rc=$?
printf '{bad' > "$P/bad.json"; "${FW[@]}" verify --state "$P/fvw2" --files "$P/bad.json" > "$P/badf2.out" 2>&1; rc2=$?
[ $rc = 2 ] && [ $rc2 = 2 ] && ok cli/verify-bad-files-exit2 "missing / unparsable --files: exit 2 / 2" || ko cli/verify-bad-files-exit2 "exit $rc / $rc2 (want 2 / 2)"
bash "$FV/tools/incr/incr-reverify.sh" "$P/fvw/cold" "$P/proj_edit" "$CH" "$P/i-mv" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --threads > "$P/i-mv.log" 2>&1; rc=$?
bash "$FV/tools/incr/incr-reverify.sh" "$P/fvw/cold" "$P/proj_edit" "$CH" "$P/i-mv2" --challenge-sha256 "$PIN" --comparator-sha256 > "$P/i-mv2.log" 2>&1; rc2=$?
[ $rc = 2 ] && [ $rc2 = 2 ] && ok cli/incr-missing-value-exit2 "--threads / --comparator-sha256 without a value: exit 2 / 2" || ko cli/incr-missing-value-exit2 "exit $rc / $rc2 (want 2 / 2)"
# strict path resolution: a missing parent / an empty path is refused (exit 2), nothing staged
bash "$FV/tools/incr/incr-reverify.sh" "$P/fvw/cold" "$P/nope/child" "$CH" "$P/i-np" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" > "$P/i-np.log" 2>&1; rc=$?
[ $rc = 2 ] && [ ! -e "$P/i-np/src" ] && [ ! -e "$P/i-np/cold" ] && ok cli/incr-missing-parent-refused "exit 2, nothing staged" || ko cli/incr-missing-parent-refused "exit $rc ($(ls "$P/i-np" 2>/dev/null | tr '\n' ' '))"
bash "$FV/tools/incr/incr-reverify.sh" "$P/fvw/cold" "" "$CH" "$P/i-ep" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" > "$P/i-ep.log" 2>&1; rc=$?
[ $rc = 2 ] && [ ! -e "$P/i-ep/src" ] && [ ! -e "$P/i-ep/cold" ] && ok cli/incr-empty-path-refused "exit 2, nothing staged" || ko cli/incr-empty-path-refused "exit $rc"
"${FW[@]}" verify --state "$P/fvw2" --tree "" --no-advance > "$P/et.out" 2>&1; rc=$?
"${FW[@]}" verify --state "$P/fvw2" --tree "$P/nope/child" --no-advance > "$P/mt.out" 2>&1; rc2=$?
[ $rc = 2 ] && [ $rc2 = 2 ] && ok cli/fvwork-empty-or-missing-tree-refused "empty / missing-parent --tree: exit 2 / 2" || ko cli/fvwork-empty-or-missing-tree-refused "exit $rc / $rc2"
# strict paths at fvwork init / watch / verify, and the daemon-side check reached directly
mkdir -p "$P/cwdx"; printf 'marker' > "$P/cwdx/CWD-MARKER"
( cd "$P/cwdx" && "${FW[@]}" init --state "$P/fvwe" --project "" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" \
    --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" > "$P/inite.log" 2>&1 ); rc=$?
"${FW[@]}" init --state "$P/fvwm" --project "$P/nope/x" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" > "$P/initm.log" 2>&1; rc2=$?
( cd "$P/cwdx" && "${FW[@]}" init --state "" --project "$P/proj_good" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" \
    --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" > "$P/inits.log" 2>&1 ); rc3=$?
[ $rc = 2 ] && [ $rc2 = 2 ] && [ $rc3 = 2 ] && [ ! -e "$P/fvwe" ] && [ ! -e "$P/fvwm" ] && [ ! -e "$P/cwdx/config.json" ] && [ ! -e "$P/cwdx/src0" ] \
  && ok fvwork/init-strict-paths "empty --project / missing-parent --project / empty --state: exit 2 / 2 / 2, nothing created" \
  || ko fvwork/init-strict-paths "exit $rc / $rc2 / $rc3 ($(ls "$P/cwdx" | tr '\n' ' '))"
timeout 30 "${FW[@]}" watch --state "$P/fvw2" --tree "" --interval 0.5 > "$P/watche.log" 2>&1; rc=$?
timeout 30 "${FW[@]}" watch --state "$P/fvw2" --tree "$P/nope/x" --interval 0.5 > "$P/watchm.log" 2>&1; rc2=$?
[ $rc = 2 ] && [ $rc2 = 2 ] && ok fvwork/watch-strict-tree "empty / missing-parent --tree: exit 2 / 2" || ko fvwork/watch-strict-tree "exit $rc / $rc2"
ln -sfn / "$P/rootlink"
"${FW[@]}" verify --state "$P/fvw2" --tree / --no-advance > "$P/vr.out" 2>&1; rc=$?
"${FW[@]}" verify --state "$P/fvw2" --tree "$P/rootlink" --no-advance > "$P/vl.out" 2>&1; rc2=$?
[ $rc = 2 ] && [ $rc2 = 2 ] && ok cli/verify-root-refused "--tree / and a link to /: exit 2 / 2 (nothing sent)" || ko cli/verify-root-refused "exit $rc / $rc2"
v=$(python3 -I - "$FV" "$P/fvw2" <<'PY'
import importlib.util, os, sys
sp = importlib.util.spec_from_file_location("fvw_raw", os.path.join(sys.argv[1], "tools", "fvwork", "fvwork.py"))
m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m)
out = []
for req in ({"tree": ""}, {"tree": "rel/dir"}, {"tree": "."}, {"git": ""}, {"git": "rel"}):
    r = m.request(sys.argv[2], dict(req, op="verify", advance=False))
    out.append("%s:%s" % (r.get("verdict"), r.get("exit")))
print(" ".join(out))
PY
)
case "$v" in "NO-VERDICT:2 NO-VERDICT:2 NO-VERDICT:2 NO-VERDICT:2 NO-VERDICT:2") ok daemon/raw-bad-paths-refused "raw requests (tree '', relative, '.', git '', relative): $v";; *) ko daemon/raw-bad-paths-refused "$v";; esac
# a base run without a B3 build tree / plan (the fast build declined: a root lakefile.lean -> official build,
# in the current package) still makes a state for the v0.1 cold path; the EXPERIMENTAL machinery refuses it; fail closed: a run
# without a plan AND without a sound verdict makes no state
rm -rf "$P/proj_lean"; cp -a "$P/proj_good" "$P/proj_lean"; rm -f "$P/proj_lean/lakefile.toml"
printf 'import Lake\nopen Lake DSL\n\npackage WarmCp\n\n@[default_target]\nlean_lib WarmCp\n' > "$P/proj_lean/lakefile.lean"
"${FW[@]}" init --state "$P/fvw5" --project "$P/proj_lean" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" > "$P/init5.log" 2>&1; rc=$?
b=$(jf "$P/fvw5/base.json" cold init_no_plan plan proj verdict)
[ $rc = 0 ] && [ "$b" = "True True None None ACCEPTED" ] && grep -q "no B3 build tree" "$P/init5.log" \
  && ok fvwork/init-official-base "lakefile.lean project (official build): init exit 0, cold base (cold/no-plan/plan/proj/verdict: $b)" \
  || ko fvwork/init-official-base "exit $rc '$b' ($(tail -c 300 "$P/init5.log"))"
timeout 60 "${FW[@]}" serve --state "$P/fvw5" --check sound --jobs 1 --warm 0 --threads 4 --experimental-incremental > "$P/srv5x.log" 2>&1; rc=$?
[ $rc = 2 ] && grep -q "no B3 build tree" "$P/srv5x.log" && ok fvwork/official-base-experimental-refused "serve --experimental-incremental: exit 2" \
  || ko fvwork/official-base-experimental-refused "exit $rc ($(tail -c 200 "$P/srv5x.log"))"
rm -f "$P/fvw5/sock"
"${FW[@]}" serve --state "$P/fvw5" --check sound --jobs 1 --warm 0 --threads 4 > "$P/srv5.log" 2>&1 & PIDS+=($!)
for _ in $(seq 1 600); do [ -S "$P/fvw5/sock" ] && break; sleep 0.5; done
python3 -I -c 'import json,sys; json.dump({"WarmCp/Helper.lean": open(sys.argv[2]).read()}, open(sys.argv[1], "w"))' "$P/ok5.files" "$P/proj_edit/WarmCp/Helper.lean"
python3 -I -c 'import json,sys; json.dump({"WarmCp.lean": open(sys.argv[2]).read()}, open(sys.argv[1], "w"))' "$P/bad5.files" "$P/chal_src/WarmCp.lean"
"${FW[@]}" verify --state "$P/fvw5" --files "$P/ok5.files" --no-advance > "$P/v5a.out" 2>&1; rc=$?; tail -1 "$P/v5a.out" > "$P/v5a.json"
"${FW[@]}" verify --state "$P/fvw5" --files "$P/bad5.files" --no-advance > "$P/v5b.out" 2>&1; rc2=$?; tail -1 "$P/v5b.out" > "$P/v5b.json"
va=$(jf "$P/v5a.json" verdict mode trust); vb=$(jf "$P/v5b.json" verdict mode trust)
[ $rc = 0 ] && [ "$va" = "ACCEPTED cold sound" ] && [ $rc2 = 1 ] && [ "$vb" = "REJECTED cold sound" ] \
  && ok fvwork/official-base-serves-cold "--files over the snapshot: valid edit $va; the sorry statement $vb" \
  || ko fvwork/official-base-serves-cold "exit $rc '$va' ($(jf "$P/v5a.json" why | cut -c1-120)) / exit $rc2 '$vb'"
"${FW[@]}" stop --state "$P/fvw5" > /dev/null 2>&1
mkdir -p "$P/adnv"; printf '{"verdict": "NO-VERDICT"}\n' > "$P/adnv/result.json"
"${FW[@]}" init --state "$P/fvw6" --project "$P/proj_lean" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" --adopt "$P/adnv" > "$P/init6.log" 2>&1; rc=$?
mkdir -p "$P/adnone"
"${FW[@]}" init --state "$P/fvw7" --project "$P/proj_lean" --challenge "$P/pinned" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" \
  --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" --adopt "$P/adnone" > "$P/init7.log" 2>&1; rc2=$?
[ $rc != 0 ] && [ $rc2 != 0 ] && [ ! -f "$P/fvw6/config.json" ] && [ ! -f "$P/fvw7/config.json" ] && grep -q "no sound verdict" "$P/init6.log" \
  && ok fvwork/init-no-plan-no-verdict-refused "no plan + NO-VERDICT / no result: exit $rc / $rc2, no state" \
  || ko fvwork/init-no-plan-no-verdict-refused "exit $rc / $rc2 ($(tail -c 200 "$P/init6.log"))"
echo "RESULT pass=$pass fail=$fail (pin rule present: $PINRULE)"
[ "$fail" = 0 ]
