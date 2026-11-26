#!/bin/bash
# tests/incr-stale-outputs/run.sh [WORKDIR] -- regression test: stale build outputs must never be judged in the edit
# loop. The NON-warm incremental paths (tools/fvwork serve --check sound, tools/incr/incr-reverify.sh without
# --warm-daemon) build with tools/incr/incr-build.py, which matched changed files against Lake's plan with raw paths (a
# lakefile `srcDir = "./src"` -> './src/...' paths never matched: NOTHING was rebuilt) and did not track files read at
# elaboration time (include_str): the stale outputs of the previous tree were exported and judged -> ACCEPTED for a
# submitted tree whose content differs (e.g. one that proves the target from `axiom fake_cheat : False`).
# Rows (both entry points; fvwork = serve --check sound, default (exact) mode, --tree requests, one --files request;
# incr = incr-reverify.sh on fvwork's base run (fvwork init), default and --optimistic):
#   {fvwork,incr}/srcdir-cheat-rejected     srcDir = "./src", the solution switches to `axiom fake_cheat`     -> REJECTED
#   fvwork/srcdir-cheat-files-rejected      the same as a sparse --files request                               -> REJECTED
#   {fvwork,incr}/srcdir-edit-accepted      srcDir = "./src", another valid proof                              -> ACCEPTED
#   {fvwork,incr}/include-str-cheat-not-accepted  the theorem's statement includes a non-module .lean file via
#                                           include_str; the file changes                                      -> not ACCEPTED
#   {fvwork,incr}/include-str-edit-accepted the solution's proof changes (data unchanged)                      -> ACCEPTED
#   {fvwork,incr}/reader-module-file-not-accepted  the solution include_str's ANOTHER module's source (a lib root it does
#                                           not import); that module changes                                   -> not ACCEPTED
#   {fvwork,incr}/plain-edit-accepted, {fvwork,incr}/plain-cheat-rejected  ordinary layout (Helper module + solution) ->
#                                           ACCEPTED / REJECTED (the normal edit loop still works)
#   {fvwork,incr}/build-rewrites-source-no-verdict  the solution's elaboration rewrites Helper.lean in the work tree: the
#                                           post-build verification (compiled sources = submitted files) -> NO VERDICT
#   incr/include-str-cheat-optimistic-not-accepted  the include_str cheat with incr-reverify --optimistic       -> not ACCEPTED
#   {fvwork,incr}/v1-token-free-reader-not-accepted (V1: `open IO FS in ... lines` inside an elab: elaboration-time
#       code anywhere -> full build); {fvwork,incr}/v2-macro-*-not-accepted (V2: the importer of a changed macro, default
#       EXACT mode and the EXPERIMENTAL optimistic modes); {fvwork,incr}/v3-lake-srcdir-not-accepted (V3: a srcDir under
#       .lake compiling a base-build leftover -> refused); {fvwork,incr}/v4-dirlink-retarget-not-accepted (V4: a
#       retargeted directory symlink -> refused); fvwork/default-mode-exact; {fvwork,incr}/optimistic-accept-confirmed-exact
#       (an optimistic ACCEPTED is provisional and confirmed by an exact attempt); incr/optimistic-only-not-counted (NO
#       VERDICT, provisional ACCEPTED); incr/manifest-dropped-rule (L1); incr/hardlink-base-sources-untouched (L2);
#       unit/memo-symlink-target (L3: memo digest follows symlinked files / directories)
#   memo/sanity, memo/after-release-change: fvwork --reuse-identical re-reports a memoized verdict for the same export
#                      (sanity) but NOT after release 4.33.1 is revoked in check/xversion/releases.json (a private
#                      package copy) -> no reused ACCEPTED
# Needs the official 4.33.1 toolchain. Every build runs in fvwork's / incr-build's bwrap sandbox. Exit 0 iff every row PASS.
# FV_ROOT=<package copy> runs the rows against another copy (live: the srcdir / include_str / reader / memo rows FAIL).
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/incr-stale.XXXXXX") || exit 2
W=$(readlink -f "$W")
PIDS=()
FW=(python3 -I -B "$FV/tools/fvwork/fvwork.py")
cleanup() {
  for st in "$W"/*/fvw "$W"/M/fvm; do [ -S "$st/sock" ] && "${FW[@]}" stop --state "$st" > /dev/null 2>&1; done
  for p in "${PIDS[@]}"; do kill "$p" 2>/dev/null; wait "$p" 2>/dev/null; done
  [ "${KEEP:-0}" = 1 ] || rm -rf "$W"
}
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
FA='∀ n : Nat, n + 0 = n'
mkproj() {  # mkproj DIR NAME [EXTRA-LAKEFILE-LINES] : lake skeleton (4.33.1, no packages)
  mkdir -p "$1"; printf 'leanprover/lean4:v4.33.1\n' > "$1/lean-toolchain"
  printf 'name = "%s"\ndefaultTargets = ["%s"]\n[[lean_lib]]\nname = "%s"\n%b' "$2" "$2" "$2" "${3:-}" > "$1/lakefile.toml"
  printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n' > "$1/lake-manifest.json"
}
cfgj() { printf '{"challenge_module":"%s","solution_module":"%s","theorem_names":["target_thm"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}\n' "$2" "$2" > "$1/comparator.json"; }
# setup P : P/chal_src + P/proj_good written; pinned challenge, fvwork init (the base run) + serve --check sound
setup() {
  local P=$1
  mkdir -p "$P/ws/.lake/packages"
  "$FV/bin/fv" init-challenge "$P/chal_src" "$P/pinned" --threads 4 --json > "$P/initc.log" 2>&1 || return 1
  PIN=$(awk '{print $1}' "$P/pinned/challenge.export.sha256")
  "${FW[@]}" init --state "$P/fvw" --project "$P/proj_good" --challenge "$P/pinned" --challenge-sha256 "$PIN" \
    --comparator-sha256 "$(sha256sum < "$P/pinned/comparator.json" | cut -c1-64)" \
    --packages "$P/ws" --threads 4 --fv "$FV" --tc "$TC" > "$P/init.log" 2>&1 || return 1
  "${FW[@]}" serve --state "$P/fvw" --check sound --jobs 1 --warm 0 --threads 4 > "$P/srv.log" 2>&1 &
  PIDS+=($!); local pid=$!
  for _ in $(seq 1 600); do [ -S "$P/fvw/sock" ] && return 0; kill -0 $pid 2>/dev/null || return 2; sleep 0.5; done
  return 3
}
# fv P NAME ARGS... : fvwork verify (no advance) -> "rc verdict outcome"
fv() {
  local P=$1 n=$2; shift 2
  "${FW[@]}" verify --state "$P/fvw" --no-advance "$@" > "$P/$n.out" 2>&1; local rc=$?
  tail -1 "$P/$n.out" > "$P/$n.json"
  echo "$rc $(jf "$P/$n.json" verdict attempts.-1.outcome)"
}
# ir P NAME TREE [ARGS...] : incr-reverify (non-warm) on fvwork's base run (fvwork init) -> "rc verdict"
ir() {
  local P=$1 n=$2 t=$3; shift 3
  local B=$P/fvw/cold CH=$P/ich
  if [ ! -d "$CH" ]; then   # fvwork's private challenge copy + the challenge's lean-toolchain (incr-reverify reads it)
    mkdir -p "$CH"; cp "$P/fvw/challenge/challenge.export" "$P/fvw/challenge/comparator.json" "$CH/"
    cp "$P/chal_src/lean-toolchain" "$CH/"
  fi
  local CS; CS=$(sha256sum "$CH/challenge.export" | cut -d' ' -f1)
  rm -rf "$P/t-$n"; cp -a "$t" "$P/t-$n"; rm -rf "$P/t-$n/.lake"
  INCR_TC=$TC bash "$FV/tools/incr/incr-reverify.sh" "$B" "$P/t-$n" "$CH" "$P/i-$n" --challenge-sha256 "$CS" --threads 4 \
    --comparator-sha256 "$(sha256sum < "$CH/comparator.json" | cut -c1-64)" \
    --packages "$P/ws" "$@" > "$P/i-$n.log" 2>&1; local rc=$?
  echo "$rc $(jf "$P/i-$n/summary.json" verdict)"
}
want_rej() {  # want_rej ROW "rc verdict ..." : REJECTED (exit 1)
  case "$2" in "1 REJECTED"*) ok "$1" "$2";; *) ko "$1" "$2 (want REJECTED)";; esac; }
want_acc() { case "$2" in "0 ACCEPTED"*) ok "$1" "$2";; *) ko "$1" "$2 (want ACCEPTED)";; esac; }
want_nv() { case "$2" in "2 NO"*) ok "$1" "$2";; *) ko "$1" "$2 (want NO VERDICT: the post-build verification)";; esac; }
# ctl P NAME TREE : the COLD control - bin/fastverify --preset sound on the tree itself -> "rc VERDICT"
ctl() {
  local P=$1 n=$2 t=$3; local pin; pin=$(awk '{print $1}' "$P/pinned/challenge.export.sha256")
  rm -rf "$P/c-$n" "$P/ctl-$n"; cp -a "$t" "$P/c-$n"; rm -rf "$P/c-$n/.lake"
  "$FV/bin/fastverify" "$P/c-$n" "$P/pinned" "$P/ctl-$n" --preset sound --threads 4 --packages "$P/ws" --challenge-sha256 "$pin" \
    --comparator-sha256 "$(sha256sum < "$P/pinned/comparator.json" | cut -c1-64)" \
    --export-dir none > "$P/ctl-$n.log" 2>&1; local rc=$?   # both pins required
  echo "$rc $(jf "$P/ctl-$n/result.json" verdict)"
}
# want_cold ROW RESULT CONTROL : the default path's exit + verdict equal the cold control's (NO-VERDICT = NO VERDICT)
want_cold() {
  local a b; a=$(printf '%s' "$2" | awk '{v=$2; if (v ~ /^NO/) v="NO"; print $1, v}'); b=$(printf '%s' "$3" | awk '{v=$2; if (v ~ /^NO/) v="NO"; print $1, v}')
  [ "$a" = "$b" ] && ok "$1" "$2 = cold $3" || ko "$1" "$2 != cold $3"; }
want_prov() {  # want_prov ROW "rc verdict" JSON KEY : NO VERDICT with "provisional": ACCEPTED (never a counted ACCEPTED)
  local pv; pv=$(jf "$3" provisional)
  case "$2|$pv" in "2 NO"*"|ACCEPTED") ok "$1" "$2, provisional $pv";; *) ko "$1" "$2, provisional $pv (want NO VERDICT, provisional ACCEPTED)";; esac; }
want_not_acc() { case "$2" in "0 "*|*" ACCEPTED"*) ko "$1" "$2 (ACCEPTED)";; *unparsable*|*" None"*|"") ko "$1" "$2 (no verifier answer)";; *) ok "$1" "$2";; esac; }
want_provrej() {  # experimental: a rejection is NO VERDICT + "provisional": REJECTED (never a counted verdict)
  local pv; pv=$(jf "$3" provisional)
  case "$2|$pv" in "2 NO"*"|REJECTED") ok "$1" "$2, provisional $pv";; *) ko "$1" "$2, provisional $pv (want NO VERDICT, provisional REJECTED)";; esac; }

# ------------------------------------------------------------------ srcDir = "./src"
P=$W/sd; mkdir -p "$P/chal_src/src"
mkproj "$P/chal_src" WarmSrcDir 'srcDir = "./src"\n'
printf 'theorem target_thm : %s := by sorry\n' "$FA" > "$P/chal_src/src/WarmSrcDir.lean"; cfgj "$P/chal_src" WarmSrcDir
cp -a "$P/chal_src" "$P/proj_good"; printf 'theorem target_thm : %s := fun n => Nat.add_zero n\n' "$FA" > "$P/proj_good/src/WarmSrcDir.lean"
cp -a "$P/proj_good" "$P/proj_cheat"; printf 'axiom fake_cheat : False\ntheorem target_thm : %s := fake_cheat.elim\n' "$FA" > "$P/proj_cheat/src/WarmSrcDir.lean"
cp -a "$P/proj_good" "$P/proj_edit"; printf 'theorem target_thm : %s := fun _ => rfl\n' "$FA" > "$P/proj_edit/src/WarmSrcDir.lean"
python3 -I -c 'import json,sys; json.dump({"src/WarmSrcDir.lean": open(sys.argv[2]).read()}, open(sys.argv[1], "w"))' \
  "$P/cheat.files" "$P/proj_cheat/src/WarmSrcDir.lean"
if setup "$P"; then
  want_rej fvwork/srcdir-cheat-rejected "$(fv "$P" cheat --tree "$P/proj_cheat")"
  want_rej fvwork/srcdir-cheat-files-rejected "$(fv "$P" cheatf --files "$P/cheat.files")"
  want_acc fvwork/srcdir-edit-accepted "$(fv "$P" edit --tree "$P/proj_edit")"
  want_rej incr/srcdir-cheat-rejected "$(ir "$P" cheat "$P/proj_cheat")"
  want_acc incr/srcdir-edit-accepted "$(ir "$P" edit "$P/proj_edit")"
  want_not_acc exp/incr-srcdir-cheat-not-accepted "$(ir "$P" xcheat "$P/proj_cheat" --experimental-incremental)"
else ko sd/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ include_str of a non-module .lean file
P=$W/inc; mkdir -p "$P/chal_src/WarmInc"
mkproj "$P/chal_src" WarmInc
printf 'ok' > "$P/chal_src/WarmInc/data.lean"
printf 'theorem target_thm : (include_str "WarmInc/data.lean") = "ok" := by sorry\n' > "$P/chal_src/WarmInc.lean"; cfgj "$P/chal_src" WarmInc
cp -a "$P/chal_src" "$P/proj_good"; printf 'theorem target_thm : (include_str "WarmInc/data.lean") = "ok" := rfl\n' > "$P/proj_good/WarmInc.lean"
cp -a "$P/proj_good" "$P/proj_bad"; printf 'BAD' > "$P/proj_bad/WarmInc/data.lean"
cp -a "$P/proj_good" "$P/proj_edit"; printf 'theorem target_thm : (include_str "WarmInc/data.lean") = "ok" := by rfl\n' > "$P/proj_edit/WarmInc.lean"
if setup "$P"; then
  want_not_acc fvwork/include-str-cheat-not-accepted "$(fv "$P" bad --tree "$P/proj_bad")"
  want_acc fvwork/include-str-edit-accepted "$(fv "$P" edit --tree "$P/proj_edit")"
  want_not_acc incr/include-str-cheat-not-accepted "$(ir "$P" bad "$P/proj_bad")"
  want_not_acc incr/include-str-cheat-optimistic-not-accepted "$(ir "$P" bado "$P/proj_bad" --optimistic)"
  want_acc incr/include-str-edit-accepted "$(ir "$P" edit "$P/proj_edit")"
else ko inc/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ include_str of ANOTHER module's source (not imported)
P=$W/rd; mkdir -p "$P/chal_src/WarmRd"
mkproj "$P/chal_src" WarmRd 'roots = ["WarmRd", "WarmRd.B"]\n'
printf -- '-- b\n' > "$P/chal_src/WarmRd/B.lean"
printf 'theorem target_thm : (include_str "WarmRd/B.lean") = "-- b\\n" := by sorry\n' > "$P/chal_src/WarmRd.lean"; cfgj "$P/chal_src" WarmRd
cp -a "$P/chal_src" "$P/proj_good"; printf 'theorem target_thm : (include_str "WarmRd/B.lean") = "-- b\\n" := rfl\n' > "$P/proj_good/WarmRd.lean"
cp -a "$P/proj_good" "$P/proj_bad"; printf -- '-- c\n' > "$P/proj_bad/WarmRd/B.lean"
if setup "$P"; then
  want_not_acc fvwork/reader-module-file-not-accepted "$(fv "$P" bad --tree "$P/proj_bad")"
  want_not_acc incr/reader-module-file-not-accepted "$(ir "$P" bad "$P/proj_bad")"
else ko rd/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ ordinary layout: the edit loop still works
P=$W/pl; mkdir -p "$P/chal_src/WarmPl"
mkproj "$P/chal_src" WarmPl
printf 'theorem h_lem : %s := fun n => Nat.add_zero n\n' "$FA" > "$P/chal_src/WarmPl/Helper.lean"
printf 'import WarmPl.Helper\ntheorem target_thm : %s := by sorry\n' "$FA" > "$P/chal_src/WarmPl.lean"; cfgj "$P/chal_src" WarmPl
cp -a "$P/chal_src" "$P/proj_good"; printf 'import WarmPl.Helper\ntheorem target_thm : %s := h_lem\n' "$FA" > "$P/proj_good/WarmPl.lean"
cp -a "$P/proj_good" "$P/proj_edit"; printf 'theorem h_lem : %s := fun _ => rfl\n' "$FA" > "$P/proj_edit/WarmPl/Helper.lean"
cp -a "$P/proj_good" "$P/proj_cheat"; printf 'import WarmPl.Helper\naxiom fake_cheat : False\ntheorem target_thm : %s := fake_cheat.elim\n' "$FA" > "$P/proj_cheat/WarmPl.lean"
# the build itself rewrites another module's source in the work tree (elaboration-time write): the compiled tree is no longer
# the submitted one -> the post-build verification answers no verdict
cp -a "$P/proj_good" "$P/proj_rw"; printf 'import WarmPl.Helper\ntheorem target_thm : %s := h_lem\n#eval IO.FS.writeFile "WarmPl/Helper.lean" "theorem h_lem : %s := fun n => Nat.add_zero n\\n-- rewritten during the build\\n"\n' "$FA" "$FA" > "$P/proj_rw/WarmPl.lean"
if setup "$P"; then
  r=$(fv "$P" edit --tree "$P/proj_edit"); want_acc fvwork/plain-edit-accepted "$r"
  want_rej fvwork/plain-cheat-rejected "$(fv "$P" cheat --tree "$P/proj_cheat")"
  want_acc incr/plain-edit-accepted "$(ir "$P" edit "$P/proj_edit")"
  want_rej incr/plain-cheat-rejected "$(ir "$P" cheat "$P/proj_cheat")"
  c_rw=$(ctl "$P" rw "$P/proj_rw")
  want_cold fvwork/build-rewrites-source-equals-cold "$(fv "$P" rw --tree "$P/proj_rw")" "$c_rw"
  want_cold incr/build-rewrites-source-equals-cold "$(ir "$P" rw "$P/proj_rw")" "$c_rw"
  # the default path IS the cold path: fvwork and incr-reverify answer from bin/fastverify on the submitted tree
  v=$(jf "$P/edit.json" mode attempts.0.mode); [ "$v" = "cold cold" ] && ok fvwork/default-path-cold "mode: $v" || ko fvwork/default-path-cold "$v"
  v=$(jf "$P/i-edit/summary.json" mode attempts); [ "$v" = "cold []" ] && ok incr/default-path-cold "mode: $v" || ko incr/default-path-cold "$v"
  r=$(ir "$P" opt "$P/proj_edit" --optimistic); v=$(jf "$P/i-opt/summary.json" mode ignored)
  case "$r|$v" in "0 ACCEPTED|cold ['--optimistic']") ok incr/incremental-options-ignored "$r / $v";; *) ko incr/incremental-options-ignored "$r / $v";; esac
  # the EXPERIMENTAL incremental machinery: never a counted ACCEPTED
  r=$(ir "$P" xedit "$P/proj_edit" --experimental-incremental); want_prov exp/incr-edit-not-counted "$r" "$P/i-xedit/summary.json"
  r=$(ir "$P" xcheat "$P/proj_cheat" --experimental-incremental); want_provrej exp/incr-cheat-not-counted "$r" "$P/i-xcheat/summary.json"
  r=$(ir "$P" xoo "$P/proj_edit" --experimental-incremental --optimistic-only); want_prov exp/incr-optimistic-only-not-counted "$r" "$P/i-xoo/summary.json"
  # (L1) a tree without lake-manifest.json: the base's is kept for Lake; a dropped manifest that lists packages counts
  # as a change (full build: a fresh build would see no manifest); one without packages is what Lake writes itself
  rm -rf "$P/proj_noman"; cp -a "$P/proj_edit" "$P/proj_noman"; rm -f "$P/proj_noman/lake-manifest.json"
  r=$(ir "$P" noman "$P/proj_noman")
  u=$(python3 -I - "$FV" "$W" <<'PY'
import importlib.util, json, os, sys
fv, w = sys.argv[1], sys.argv[2]
sp = importlib.util.spec_from_file_location("ib_l1", os.path.join(fv, "tools", "incr", "incr-build.py"))
m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m)
out = []
for name, txt in (("pkgs", json.dumps({"packages": [{"name": "mathlib"}]})), ("nopkgs", json.dumps({"packages": []})), ("garbage", "{")):
    p = os.path.join(w, "man-" + name + ".json"); open(p, "w").write(txt)
    out.append(str(m.manifest_has_packages(p)) if hasattr(m, "manifest_has_packages") else "missing")
print(" ".join(out))
PY
)
  case "$r|$u" in "0 ACCEPTED|True False True") ok incr/manifest-dropped-rule "$r; drop counts as a change: with packages / without / unparsable = $u";;
    *) ko incr/manifest-dropped-rule "$r / $u (want ACCEPTED; True False True)";; esac
  # (L2) --hardlink: a build that rewrites a source it did not write must not rewrite the base's (shared inode)
  h0=$(sha256sum < "$P/fvw/cold/work/proj/WarmPl/Helper.lean")
  r=$(ir "$P" rwh "$P/proj_rw" --hardlink); h1=$(sha256sum < "$P/fvw/cold/work/proj/WarmPl/Helper.lean")
  r2=$(ir "$P" rwhx "$P/proj_rw" --hardlink --experimental-incremental); h2=$(sha256sum < "$P/fvw/cold/work/proj/WarmPl/Helper.lean")
  [ "$h0" = "$h1" ] && [ "$h0" = "$h2" ] && ok incr/hardlink-base-sources-untouched "cold: $r; experimental --hardlink: $r2; base Helper.lean unchanged" \
    || ko incr/hardlink-base-sources-untouched "$r / $r2, base Helper.lean $( [ "$h0" = "$h1" ] && [ "$h0" = "$h2" ] && echo unchanged || echo REWRITTEN)"
  # fvwork: the incremental modes need --experimental-incremental; with it nothing is counted
  "${FW[@]}" stop --state "$P/fvw" > /dev/null 2>&1; for _ in $(seq 1 100); do [ -S "$P/fvw/sock" ] || break; sleep 0.2; done; sleep 1
  timeout 60 "${FW[@]}" serve --state "$P/fvw" --check frontier --jobs 1 --warm 0 --threads 4 > "$P/optin.log" 2>&1; grc=$?
  [ "$grc" = 2 ] && grep -q "EXPERIMENTAL" "$P/optin.log" && ok optin/fvwork-frontier-needs-flag "exit $grc" || ko optin/fvwork-frontier-needs-flag "exit $grc (want exactly 2): $(tail -c 200 "$P/optin.log")"
  "${FW[@]}" serve --state "$P/fvw" --check sound --jobs 1 --warm 0 --threads 4 --experimental-incremental > "$P/srvx.log" 2>&1 &
  PIDS+=($!); for _ in $(seq 1 600); do [ -S "$P/fvw/sock" ] && break; sleep 0.5; done
  r=$(fv "$P" xedit --tree "$P/proj_edit"); want_prov exp/fvwork-edit-not-counted "$r" "$P/xedit.json"
  r=$(fv "$P" xopt --tree "$P/proj_edit" --mode optimistic); want_prov exp/fvwork-optimistic-not-counted "$r" "$P/xopt.json"
  r=$(fv "$P" xcheat --tree "$P/proj_cheat"); want_provrej exp/fvwork-cheat-not-counted "$r" "$P/xcheat.json"
else ko pl/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ V1: a reader without any token of the earlier list
P=$W/v1; mkdir -p "$P/chal_src/WarmEv"
mkproj "$P/chal_src" WarmEv 'roots = ["WarmEv", "WarmEv.B"]\n'
printf -- '-- b\n' > "$P/chal_src/WarmEv/B.lean"
printf 'theorem target_thm : %s := by sorry\n' "$FA" > "$P/chal_src/WarmEv.lean"; cfgj "$P/chal_src" WarmEv
cp -a "$P/chal_src" "$P/proj_good"
cat > "$P/proj_good/WarmEv.lean" <<'LEAN'
import Lean
open Lean Elab Tactic
open IO FS in
elab "rd_tac" : tactic => do
  let ls ← lines "WarmEv/B.lean"
  if ls.any (fun l => (l.splitOn "cheat").length > 1) then
    evalTactic (← `(tactic| sorry))
  else
    evalTactic (← `(tactic| exact fun n => Nat.add_zero n))
theorem target_thm : ∀ n : Nat, n + 0 = n := by rd_tac
LEAN
cp -a "$P/proj_good" "$P/proj_bad"; printf -- '-- cheat\n' > "$P/proj_bad/WarmEv/B.lean"
if setup "$P"; then
  want_not_acc fvwork/v1-token-free-reader-not-accepted "$(fv "$P" bad --tree "$P/proj_bad")"
  want_not_acc incr/v1-token-free-reader-not-accepted "$(ir "$P" bad "$P/proj_bad")"
  want_not_acc exp/incr-v1-not-accepted "$(ir "$P" xbad "$P/proj_bad" --experimental-incremental)"
else ko v1/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ V2: an importer elaborated with the OLD macro
P=$W/v2; mkdir -p "$P/chal_src/WarmOp"
mkproj "$P/chal_src" WarmOp
printf 'theorem h0 : True := trivial\n' > "$P/chal_src/WarmOp/Helper.lean"
printf 'import WarmOp.Helper\ntheorem target_thm : %s := by sorry\n' "$FA" > "$P/chal_src/WarmOp.lean"; cfgj "$P/chal_src" WarmOp
cp -a "$P/chal_src" "$P/proj_good"
printf 'macro "solve_it" : tactic => `(tactic| exact fun n => Nat.add_zero n)\n' > "$P/proj_good/WarmOp/Helper.lean"
printf 'import WarmOp.Helper\ntheorem target_thm : %s := by solve_it\n' "$FA" > "$P/proj_good/WarmOp.lean"
cp -a "$P/proj_good" "$P/proj_sorry"; printf 'macro "solve_it" : tactic => `(tactic| sorry)\n' > "$P/proj_sorry/WarmOp/Helper.lean"
cp -a "$P/proj_good" "$P/proj_fail"; printf 'macro "solve_it" : tactic => `(tactic| fail "broken")\n' > "$P/proj_fail/WarmOp/Helper.lean"
cp -a "$P/proj_good" "$P/proj_ax"; printf 'axiom fake_cheat : False\nmacro "solve_it" : tactic => `(tactic| exact fake_cheat.elim)\n' > "$P/proj_ax/WarmOp/Helper.lean"
python3 -I -c 'import json,sys; json.dump({"WarmOp/Helper.lean": open(sys.argv[2]).read()}, open(sys.argv[1], "w"))' "$P/sorry.files" "$P/proj_sorry/WarmOp/Helper.lean"
if setup "$P"; then
  want_not_acc fvwork/v2-macro-sorry-not-accepted "$(fv "$P" sorry --tree "$P/proj_sorry")"
  want_not_acc fvwork/v2-macro-sorry-files-not-accepted "$(fv "$P" sorryf --files "$P/sorry.files")"
  want_not_acc fvwork/v2-macro-fail-not-accepted "$(fv "$P" fail --tree "$P/proj_fail")"
  want_not_acc fvwork/v2-macro-axiom-not-accepted "$(fv "$P" ax --tree "$P/proj_ax")"
  want_not_acc fvwork/v2-macro-sorry-optimistic-not-accepted "$(fv "$P" sorryo --tree "$P/proj_sorry" --mode optimistic)"
  want_not_acc incr/v2-macro-sorry-optimistic-not-accepted "$(ir "$P" sorryo "$P/proj_sorry" --optimistic)"
  want_not_acc incr/v2-macro-sorry-not-accepted "$(ir "$P" sorry "$P/proj_sorry")"
else ko v2/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ V3: a srcDir under .lake (base-build leftover)
P=$W/v3; mkdir -p "$P/chal_src"
mkproj "$P/chal_src" WarmLk
printf 'theorem target_thm : %s := by sorry\n' "$FA" > "$P/chal_src/WarmLk.lean"; cfgj "$P/chal_src" WarmLk
cp -a "$P/chal_src" "$P/proj_good"
printf 'theorem target_thm : %s := fun n => Nat.add_zero n\n#eval do IO.FS.createDirAll ".lake/gen"; IO.FS.writeFile ".lake/gen/Evil.lean" "theorem evil_lem : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n\\n"\n' "$FA" > "$P/proj_good/WarmLk.lean"
cp -a "$P/proj_good" "$P/proj_bad"
printf '[[lean_lib]]\nname = "Evil"\nsrcDir = ".lake/gen"\n' >> "$P/proj_bad/lakefile.toml"
printf 'import Evil\ntheorem target_thm : %s := evil_lem\n' "$FA" > "$P/proj_bad/WarmLk.lean"
if setup "$P"; then
  want_not_acc fvwork/v3-lake-srcdir-not-accepted "$(fv "$P" bad --tree "$P/proj_bad")"
  want_not_acc incr/v3-lake-srcdir-not-accepted "$(ir "$P" bad "$P/proj_bad")"
  want_not_acc exp/incr-v3-not-accepted "$(ir "$P" xbad "$P/proj_bad" --experimental-incremental)"
else ko v3/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ V4: a directory symlink retargeted
P=$W/v4; mkdir -p "$P/chal_src/data"
mkproj "$P/chal_src" WarmSy
printf 'ok' > "$P/chal_src/data/x.txt"
printf 'theorem target_thm : (include_str "data/x.txt") = "ok" := by sorry\n' > "$P/chal_src/WarmSy.lean"; cfgj "$P/chal_src" WarmSy
cp -a "$P/chal_src" "$P/proj_good"; rm -rf "$P/proj_good/data"; mkdir -p "$P/proj_good/d1" "$P/proj_good/d2"
printf 'ok' > "$P/proj_good/d1/x.txt"; printf 'BAD' > "$P/proj_good/d2/x.txt"; ln -s d1 "$P/proj_good/data"
printf 'theorem target_thm : (include_str "data/x.txt") = "ok" := rfl\n' > "$P/proj_good/WarmSy.lean"
cp -a "$P/proj_good" "$P/proj_bad"; ln -sfn d2 "$P/proj_bad/data"
if setup "$P"; then
  want_not_acc fvwork/v4-dirlink-retarget-not-accepted "$(fv "$P" bad --tree "$P/proj_bad")"
  want_not_acc incr/v4-dirlink-retarget-not-accepted "$(ir "$P" bad "$P/proj_bad")"
  want_cold incr/v4-equals-cold "$(ir "$P" bad2 "$P/proj_bad")" "$(ctl "$P" bad "$P/proj_bad")"
  want_not_acc exp/incr-v4-not-accepted "$(ir "$P" xbad "$P/proj_bad" --experimental-incremental)"
else ko v4/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ V5: the init build rewrites a source
P=$W/v5; mkdir -p "$P/chal_src/WarmDr"
mkproj "$P/chal_src" WarmDr
printf 'theorem h0 : True := trivial\n' > "$P/chal_src/WarmDr/Helper.lean"
printf 'import WarmDr.Helper\ntheorem target_thm : %s := by sorry\n' "$FA" > "$P/chal_src/WarmDr.lean"; cfgj "$P/chal_src" WarmDr
cp -a "$P/chal_src" "$P/proj_good"
printf 'axiom fake_cheat : False\ntheorem h_lem : %s := fake_cheat.elim\n' "$FA" > "$P/proj_good/WarmDr/Helper.lean"
printf 'import WarmDr.Helper\ntheorem target_thm : %s := h_lem\n#eval IO.FS.writeFile "WarmDr/Helper.lean" "theorem h_lem : %s := fun n => Nat.add_zero n\\n"\n' "$FA" "$FA" > "$P/proj_good/WarmDr.lean"
cp -a "$P/proj_good" "$P/proj_touch"; printf -- '-- touch\n' >> "$P/proj_touch/WarmDr.lean"
python3 -I -c 'import json,sys; json.dump({"WarmDr.lean": open(sys.argv[2]).read()}, open(sys.argv[1], "w"))' "$P/touch.files" "$P/proj_touch/WarmDr.lean"
if setup "$P"; then
  c=$(ctl "$P" touch "$P/proj_touch")
  r=$(fv "$P" touchf --files "$P/touch.files"); want_cold fvwork/v5-files-equals-cold "$r" "$c"; want_not_acc fvwork/v5-files-not-accepted "$r"
  want_cold fvwork/v5-tree-equals-cold "$(fv "$P" toucht --tree "$P/proj_touch")" "$c"
  want_cold incr/v5-equals-cold "$(ir "$P" touch "$P/proj_touch")" "$c"
else ko v5/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ V6c: simproc + Lake.computeFileHash
P=$W/v6c; mkdir -p "$P/chal_src/WarmSp"
mkproj "$P/chal_src" WarmSp 'roots = ["WarmSp", "WarmSp.B"]\n'
printf -- '-- b\n' > "$P/chal_src/WarmSp/B.lean"
printf 'theorem target_thm : %s := by sorry\n' "$FA" > "$P/chal_src/WarmSp.lean"; cfgj "$P/chal_src" WarmSp
cp -a "$P/chal_src" "$P/proj_good"; printf -- '-- b\n' > "$P/proj_good/WarmSp/ref.txt"
cat > "$P/proj_good/WarmSp.lean" <<'LEAN'
import Lake
simproc ↓ rdB ((_ : Nat) + 0) := fun _ => do
  if (← Lake.computeFileHash "WarmSp/B.lean") == (← Lake.computeFileHash "WarmSp/ref.txt") then
    return .continue
  else
    throwError "B changed"
theorem target_thm : ∀ n : Nat, n + 0 = n := by intro n; simp
LEAN
cp -a "$P/proj_good" "$P/proj_bad"; printf -- '-- cheat\n' > "$P/proj_bad/WarmSp/B.lean"
if setup "$P"; then
  c=$(ctl "$P" bad "$P/proj_bad")
  r=$(fv "$P" bad --tree "$P/proj_bad"); want_cold fvwork/v6c-equals-cold "$r" "$c"; want_not_acc fvwork/v6c-not-accepted "$r"
  r=$(ir "$P" bad "$P/proj_bad"); want_cold incr/v6c-equals-cold "$r" "$c"; want_not_acc incr/v6c-not-accepted "$r"
  want_not_acc exp/incr-v6c-not-accepted "$(ir "$P" xbad "$P/proj_bad" --experimental-incremental)"
else ko v6c/setup "$(tail -c 300 "$P/init.log" "$P/srv.log" 2>/dev/null | tr '\n' ' ')"; fi

# ------------------------------------------------------------------ (L3) memo digest: a symlink counts by its target content
U=$W/l3; mkdir -p "$U/pkg/check" "$U/pkg/config" "$U/pkg/lib" "$U/pkg/toolchains" "$U/tgt"
printf 'one' > "$U/tgt/f"; ln -s "$U/tgt/f" "$U/pkg/check/link"; mkdir -p "$U/tgt/d"; printf 'x' > "$U/tgt/d/g"; ln -s "$U/tgt/d" "$U/pkg/check/dlink"
v=$(python3 -I - "$FV" "$U" <<'PY'
import importlib.util, os, sys
fv, u = sys.argv[1], sys.argv[2]
sp = importlib.util.spec_from_file_location("fvw_l3", os.path.join(fv, "tools", "fvwork", "fvwork.py"))
m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m)
def dig():
    s = m.StatSha()
    return [(os.path.relpath(f, u), s(f)) for f in m.verdict_files(os.path.join(u, "pkg"))]
a = dig()
open(os.path.join(u, "tgt", "f"), "w").write("two")
open(os.path.join(u, "tgt", "d", "g"), "w").write("y")
b = dig()
print("files", len(a), "link-changed", a[0] != b[0] if a and b else None, "dir-descended", any("dlink" in x[0] for x in a),
      "dir-changed", [x for x in a if "dlink" in x[0]] != [x for x in b if "dlink" in x[0]])
PY
)
case "$v" in *"link-changed True dir-descended True dir-changed True") ok unit/memo-symlink-target "$v";; *) ko unit/memo-symlink-target "$v";; esac

# ------------------------------------------------------------------ memo after a release-table change
V=$W/M; mkdir -p "$V"
if [ -f "$W/pl/fvw/cold/result.json" ]; then
  # a private package copy whose check/xversion/releases.json can be changed (the package under test stays untouched)
  rsync -a --exclude=/tests --exclude=/bench --exclude=/check/notary --exclude='*.md' "$FV/" "$V/fv/"
  PIN=$(awk '{print $1}' "$W/pl/pinned/challenge.export.sha256")
  python3 -I -B "$V/fv/tools/fvwork/fvwork.py" init --state "$V/fvm" --project "$W/pl/proj_good" --challenge "$W/pl/pinned" \
    --comparator-sha256 "$(sha256sum < "$W/pl/pinned/comparator.json" | cut -c1-64)" \
    --challenge-sha256 "$PIN" --packages "$W/pl/ws" --threads 4 --fv "$V/fv" --tc "$TC" --adopt "$W/pl/fvw/cold" > "$V/init.log" 2>&1
  msv() { python3 -I -B "$V/fv/tools/fvwork/fvwork.py" serve --state "$V/fvm" --check sound --jobs 1 --warm 0 --threads 4 --reuse-identical > "$V/srv.log" 2>&1 &
    PIDS+=($!); for _ in $(seq 1 300); do [ -S "$V/fvm/sock" ] && break; sleep 0.2; done; }
  mask() { python3 -I -B "$V/fv/tools/fvwork/fvwork.py" verify --state "$V/fvm" --tree "$W/pl/proj_edit" --no-advance > "$V/$1.out" 2>&1; local rc=$?; tail -1 "$V/$1.out" > "$V/$1.json"; return $rc; }
  msv; mask m1; r1=$?; mask m2; r2=$?
  v1=$(jf "$V/m1.json" verdict attempts.-1.outcome); v2=$(jf "$V/m2.json" verdict attempts.-1.outcome)
  python3 -I -B "$V/fv/tools/fvwork/fvwork.py" stop --state "$V/fvm" > /dev/null 2>&1; sleep 2
  python3 -I - "$V/fv/check/xversion/releases.json" <<'PY'
import json, sys
p = sys.argv[1]; d = json.load(open(p))
d.setdefault("not_admitted", {})["4.33.1"] = dict(d["releases"].pop("4.33.1"), why="test: release revoked")
json.dump(d, open(p, "w"), indent=1, sort_keys=True)
PY
  msv; mask m3; r3=$?
  v3=$(jf "$V/m3.json" verdict attempts.-1.outcome)
  python3 -I -B "$V/fv/tools/fvwork/fvwork.py" stop --state "$V/fvm" > /dev/null 2>&1
  [ "$r1" = 0 ] && [ "$v1" = "ACCEPTED cold0" ] && [ "$v2" = "ACCEPTED cold0" ] && ok memo/cold-no-reuse "'$v1' then '$v2' (the cold path re-judges; no memo)" \
    || ko memo/cold-no-reuse "exit $r1 '$v1' / exit $r2 '$v2'"
  [ "$r3" != 0 ] && case "$v3" in *reused*) false;; ACCEPTED*) false;; *) true;; esac \
    && ok memo/after-release-change "release revoked: '$v3' (no reused ACCEPTED)" || ko memo/after-release-change "exit $r3 '$v3'"
else ko memo/setup "no base run of project pl"; fi
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
