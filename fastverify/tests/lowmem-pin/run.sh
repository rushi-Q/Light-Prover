#!/bin/bash
# tests/lowmem-pin/run.sh [WORKDIR] -- regression test: tools/lowmem/fv_lowmem.py never pins a challenge
# export by hashing it itself (HIGH, tools/lowmem/fv_lowmem.py): with a pre-existing CHALLENGE/challenge.export and no
# --challenge-sha256, fv_lowmem.py hashed that file itself and passed the self-hash to check-sound-lowmem.sh as the pin
# -> ACCEPTED (trust sound) for a replaced challenge export (Demo.lean states 0 = 1, challenge.export swapped), where
# bin/fastverify --preset sound REFUSES (exit 2). Reproduction inputs in data/.
# Rows: lowmem/unpinned-given-export-refused (exit 2, ERROR, the judge never ran), lowmem/bad-pin-format-refused,
#   lowmem/wrong-pin-refused, control/bin-fastverify-refuses (unchanged), control/pinned-runs (with the caller's pin the
#   judge runs and decides: exit 0 or 1, never a refusal); subcontract/* and judge/*:
#   tools/subcontract/mint.py without --challenge-sha256, merge.py on a manifest whose pin is not the caller's, and
#   tools/judge/judge.sh without CSHA are refused (exit 2); lowmem/unregistered-elan-toolchain-refused,
#   lowmem/unverified-toolchain-refused, lowmem/exporter-sha-mismatch-refused, lowmem/require-sorried-holes-reaches-judge,
#   control/no-switch-accepts-436-hole (unregistered / unverified toolchains and exporters); env/bashenv-unverified-lake,
#   env/path-tr-lean-path, env/ld-preload-not-in-stages, exporter/swap-after-check, exporter/unreadable-error,
#   lowmem/registered-official-id-wrong-tree, lowmem/require-sorried-holes-in-error-result (the caller's environment
#   never reaches a stage); lowmem/sources-in-436-honest-accepted, control/views-are-real-copies;
#   lowmem/exporter-copy-deleted-sha-recorded, signal/sigchld-ignored-still-refused, lowmem/out-mode-0700,
#   signal/sigterm-error-result-stages-killed; deps/436-sources-chal-accepted,
#   deps/436-pinned-chal-accepted, deps/4331-sources-chal-accepted, deps/4331-native-declines-pinned-accepted,
#   control/4331-native-really-declined, export/official-export-failure-is-error, out/inside-challenge-refused,
#   out/inside-project-refused (projects with a Lake dependency); umask/0277-honest-accepted,
#   umask/0777-refusal-exit-2, sigpipe/closed-stdout-exit-0, lowmem/integrity-cache-caller-dir-unused,
#   fd/stderr-closed-reexec-guard-exit-2, out/symlink-trailing-dot-refused, out/nonempty-mode-unchanged (process
#   environment edge cases); axioms/quoted-propext-accepted, axioms/never-widened-{quot-sound-one-component,
#   propext-x,quoted-sorryax,not-a-name} (permitted axioms compared as Lean names).
#   signal/nohup-sighup-survives (SIGHUP / SIGINT keep their inherited disposition, as bin/fastverify).
#   result/file-size-limit-exit-2-no-partial, out/dash-challenge-disjoint, axioms/s1-gate-before-build.
#   pin/comparator-missing-refused, pin/comparator-wrong-refused, pin/comparator-correct-honest-accepted,
#   pin/comparator-correct-cheat-rejected, judge/comparator-unpinned-refused, judge/autojudge3-comparator-pin-up-front
#   (--comparator-sha256 required wherever --challenge-sha256 is).
#   pin/source-challenge-pin-needs-comparator, cli/help-and-abbrev-no-verdict.
#   Exit 0 iff every row PASS. FV_ROOT=<package> for another copy (the package views then refer to that copy, read-only).
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/lowmem-pin.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
(cd "$HERE/data" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: SHA256SUMS mismatch"; echo "RESULT pass=0 fail=1"; exit 1; }
cp -a "$HERE/data/tampered_chal" "$HERE/data/solution.export" "$W/"; chmod -R u+w "$W"
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
FVL=$FV/tools/lowmem/fv_lowmem.py
cpin() { sha256sum "$1/comparator.json" | cut -d' ' -f1; }   # the comparator pin of a challenge dir
vj() { python3 -I -c 'import json,sys
try: j=json.load(open(sys.argv[1]))
except Exception: print("none"); sys.exit()
print(j.get("verdict"), j.get("trust"), str(j.get("reason",""))[:100].replace(" ","_"))' "$1"; }
python3 -I -B "$FVL" - "$W/tampered_chal" "$W/o1" --from-export "$W/solution.export" --threads 2 > "$W/o1.log" 2>&1; rc=$?
v=$(vj "$W/o1/result.json")
case "$rc:$v" in 2:ERROR*) ok lowmem/unpinned-given-export-refused "exit 2 ${v%% *}: $(echo "$v" | cut -d' ' -f3 | tr _ ' ' | cut -c1-90)";;
  *) ko lowmem/unpinned-given-export-refused "exit $rc '$v' (a given challenge export without the caller's pin)";; esac
python3 -I -B "$FVL" - "$W/tampered_chal" "$W/o2" --from-export "$W/solution.export" --threads 2 --challenge-sha256 XYZ > "$W/o2.log" 2>&1; rc=$?
[ "$rc" = 2 ] && ok lowmem/bad-pin-format-refused "exit 2" || ko lowmem/bad-pin-format-refused "exit $rc"
python3 -I -B "$FVL" - "$W/tampered_chal" "$W/o3" --from-export "$W/solution.export" --threads 2 \
  --challenge-sha256 0000000000000000000000000000000000000000000000000000000000000000 --comparator-sha256 "$(cpin "$W/tampered_chal")" > "$W/o3.log" 2>&1; rc=$?
[ "$rc" = 2 ] && ok lowmem/wrong-pin-refused "exit 2 ($(vj "$W/o3/result.json" | cut -d' ' -f1))" || ko lowmem/wrong-pin-refused "exit $rc"
"$FV/bin/fastverify" - "$W/tampered_chal" "$W/o4" --preset sound --export "$W/solution.export" > "$W/o4.log" 2>&1; rc=$?
[ "$rc" = 2 ] && ok control/bin-fastverify-refuses "exit 2 (GOAL S1(1))" || ko control/bin-fastverify-refuses "exit $rc"
CSHA=$(sha256sum "$W/tampered_chal/challenge.export" | cut -d' ' -f1)
python3 -I -B "$FVL" - "$W/tampered_chal" "$W/o5" --from-export "$W/solution.export" --threads 2 --challenge-sha256 "$CSHA" --comparator-sha256 "$(cpin "$W/tampered_chal")" > "$W/o5.log" 2>&1; rc=$?
v=$(vj "$W/o5/result.json")
case "$rc" in 0|1) ok control/pinned-runs "exit $rc ${v%% *} (the caller pinned this export: the judge decides)";;
  *) ko control/pinned-runs "exit $rc '$v'";; esac
# ---- tools/subcontract mint/merge and tools/judge/judge.sh need the caller's challenge pin ----
mkdir -p "$W/sc_proj"; cp "$W/tampered_chal/lakefile.toml" "$W/tampered_chal/lean-toolchain" "$W/sc_proj/" 2>/dev/null
python3 -I -B "$FV/tools/subcontract/mint.py" --experimental "$W/sc_proj" "$W/tampered_chal" "$W/sc_out" --threads 2 > "$W/sc.out" 2>&1; rc=$?
[ "$rc" = 2 ] && grep -q "challenge-sha256" "$W/sc.out" && ok subcontract/mint-unpinned-refused "exit 2: $(grep -o '"error": "[^"]*' "$W/sc.out" | cut -c11-100)" \
  || ko subcontract/mint-unpinned-refused "exit $rc $(tail -c 200 "$W/sc.out")"
mkdir -p "$W/sc_old"
python3 -I -c 'import json,sys; json.dump({"challenge_sha256": "a"*64, "subchallenges": []}, open(sys.argv[1], "w")); json.dump({}, open(sys.argv[2], "w")); json.dump({"lemma": "x"}, open(sys.argv[3], "w"))' \
  "$W/sc_old/manifest.json" "$W/sc_old/ledger.json" "$W/sc_old/sub.verified.json"
python3 -I -B "$FV/tools/subcontract/merge.py" --experimental "$W/sc_old/manifest.json" "$W/sc_old/sub.verified.json" > "$W/merge.out" 2>&1; rc=$?
[ "$rc" = 2 ] && grep -q "not pinned by the caller" "$W/merge.out" && ok subcontract/merge-old-manifest-refused "exit 2 (manifest pin not the caller's)" \
  || ko subcontract/merge-old-manifest-refused "exit $rc $(tail -c 200 "$W/merge.out")"
python3 -I -B "$FV/tools/subcontract/merge.py" --experimental "$W/sc_old/manifest.json" "$W/sc_old/sub.verified.json" --challenge-sha256 "$(printf 'b%.0s' $(seq 64))" > "$W/merge2.out" 2>&1; rc=$?
[ "$rc" = 2 ] && grep -q "!= the manifest" "$W/merge2.out" && ok subcontract/merge-pin-mismatch-refused "exit 2" \
  || ko subcontract/merge-pin-mismatch-refused "exit $rc $(tail -c 200 "$W/merge2.out")"
if [ -f "$FV/tools/judge/judge.sh" ] && [ -f "$FV/tools/judge/autojudge3.sh" ]; then   # tools/judge is not shipped in every tree
  CH="$W/tampered_chal/challenge.export" CJ="$W/tampered_chal/comparator.json" bash "$FV/tools/judge/judge.sh" t "local:$W/solution.export" "$W/judge" 2 2 > "$W/judge.out" 2>&1; rc=$?
  # no check ran: cs.json absent, or the ERROR record judge.sh writes before any refusal; no cs.out
  [ "$rc" = 2 ] && grep -q "CSHA" "$W/judge.out" && [ ! -e "$W/judge/t/cs.out" ] && { [ ! -e "$W/judge/t/cs.json" ] || grep -q '"verdict": "ERROR"' "$W/judge/t/cs.json"; } && ok judge/unpinned-refused "exit 2, no check ran" \
    || ko judge/unpinned-refused "exit $rc $(tail -c 200 "$W/judge.out")"
  ( unset CSHA CFGSHA; NRUN=/bin/false timeout 20 bash "$FV/tools/judge/autojudge3.sh" t 127.0.0.1 nonode "/nonexistent" > "$W/aj.out" 2>&1 ); rc=$?
  [ "$rc" = 2 ] && grep -q "CSHA" "$W/aj.out" && ok judge/autojudge3-pin-checked-up-front "exit 2 before any polling" \
    || ko judge/autojudge3-pin-checked-up-front "exit $rc $(tail -c 150 "$W/aj.out")"
else echo "SKIP judge/*: tools/judge is not shipped in this tree"; fi
# ---- only a registered toolchain whose whole tree verifies, the official exporter at its
# pinned sha256 (no ~/.elan / env/tools fallback), and --require-sorried-holes forwarded to the judge (as bin/fastverify) ----
# A package VIEW differing only in config/components.json (a real copy of fv_lowmem.py; the rest refers to $FV), and the
# Demo challenge as SOURCES (no challenge.export: fv_lowmem resolves the toolchain to build + export it officially)
VIEWBASE=
mkview() { # mkview NAME PY_EDIT -> prints the view root
  # a view is a REAL copy of the package parts fv_lowmem reads (~65 MB, copied once per run from
  # $FV, then hard-linked inside $W per view; the two files a view changes are written fresh): no symlink into $FV, so a
  # run from an installed (live) tree can never write through to it
  if [ -z "$VIEWBASE" ]; then
    VIEWBASE="$W/viewbase"; mkdir -p "$VIEWBASE/check" "$VIEWBASE/tools/lowmem" "$VIEWBASE/config"
    for d in bin build export lib schemas toolchains; do [ -e "$FV/$d" ] && cp -rL "$FV/$d" "$VIEWBASE/$d"; done
    for d in lowmem xversion; do cp -rL "$FV/check/$d" "$VIEWBASE/check/$d"; done
  fi
  local V="$W/view_$1"; cp -al "$VIEWBASE" "$V"
  cp "$FV/tools/lowmem/fv_lowmem.py" "$V/tools/lowmem/fv_lowmem.py"
  python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); t=c["lean_toolchains"]
exec(sys.argv[3])
json.dump(c, open(sys.argv[2], "w"), indent=2)' "$FV/config/components.json" "$V/config/components.json" "$2"
  echo "$V"; }
srcchal() { # srcchal NAME TOOLCHAIN_ID
  mkdir -p "$W/$1"; cp "$W/tampered_chal/Demo.lean" "$W/tampered_chal/lakefile.toml" "$W/tampered_chal/comparator.json" "$W/$1/"
  printf '%s\n' "$2" > "$W/$1/lean-toolchain"; }
Q4=$HERE/../definition-hole/x
lmrow() { # lmrow NAME VIEW CHAL WANT_REASON_SUBSTRING
  local tg=${1//\//_}
  timeout 1200 python3 -I -B "$2/tools/lowmem/fv_lowmem.py" - "$3" "$W/o_$tg" --from-export "$Q4/SolutionHonest.export" --threads 2 \
    > "$W/o_$tg.log" 2>&1; local rc=$?
  local r; r=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("reason",""))' "$W/o_$tg/result.json" 2>/dev/null)
  case "$rc|$r" in 2\|*"$4"*) ok "$1" "exit 2: $(echo "$r" | cut -c1-120)";;
    *) ko "$1" "exit $rc '$(echo "$r" | cut -c1-160)' (the toolchain / exporter was used without registration / verification / pin)";; esac; }
V1=$(mkview unreg 'del t["leanprover/lean4:v4.37.0-rc1"]'); srcchal chal_unreg leanprover/lean4:v4.37.0-rc1
lmrow lowmem/unregistered-elan-toolchain-refused "$V1" "$W/chal_unreg" "not a registered official toolchain"
V2=$(mkview unver 't["leanprover/lean4:v4.33.1-fvtest"] = dict(t["leanprover/lean4:v4.33.1"])'); srcchal chal_unver leanprover/lean4:v4.33.1-fvtest
lmrow lowmem/unverified-toolchain-refused "$V2" "$W/chal_unver" "does not verify"
V3=$(mkview badexp 't["leanprover/lean4:v4.36.0"]["official_lean4export"]["sha256"] = "0" * 64'); srcchal chal_badexp leanprover/lean4:v4.36.0
lmrow lowmem/exporter-sha-mismatch-refused "$V3" "$W/chal_badexp" "differs from its pin"
# --require-sorried-holes reaches the judge: the 4.36 challenge has a NON-sorried definition hole ('def hole : Nat := 0');
# 4.36 semantics accept the honest solution, the switch makes the judge DECLINE (tests/definition-hole fixtures)
mkdir -p "$W/q4chal"; cp "$Q4/Challenge.export" "$W/q4chal/challenge.export"; cp "$Q4/comparator.json" "$W/q4chal/"
Q4SHA=$(sha256sum "$W/q4chal/challenge.export" | cut -d' ' -f1)
python3 -I -B "$FVL" - "$W/q4chal" "$W/o_rsh0" --from-export "$Q4/SolutionHonest.export" --threads 2 --challenge-sha256 "$Q4SHA" --comparator-sha256 "$(cpin "$W/q4chal")" > "$W/o_rsh0.log" 2>&1; rc0=$?
v0=$(vj "$W/o_rsh0/result.json")
[ "$rc0" = 0 ] && ok control/no-switch-accepts-436-hole "exit 0 ${v0%% *} (official 4.36 semantics)" || ko control/no-switch-accepts-436-hole "exit $rc0 '$v0'"
python3 -I -B "$FVL" - "$W/q4chal" "$W/o_rsh1" --from-export "$Q4/SolutionHonest.export" --threads 2 --challenge-sha256 "$Q4SHA" --comparator-sha256 "$(cpin "$W/q4chal")" \
  --require-sorried-holes > "$W/o_rsh1.log" 2>&1; rc1=$?
r1=$(python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j.get("verdict"), j.get("require_sorried_holes"), "|", j.get("reason",""))' "$W/o_rsh1/result.json" 2>/dev/null)
case "$rc1|$r1" in "2|DECLINED True |"*"not sorried"*) ok lowmem/require-sorried-holes-reaches-judge "exit 2: $(echo "$r1" | cut -c1-130)";;
  *) ko lowmem/require-sorried-holes-reaches-judge "exit $rc1 '$(echo "$r1" | cut -c1-120)' $(tail -c 120 "$W/o_rsh1.log")";; esac
# ---- the caller's environment never reaches a stage, the exporter that runs is the
# one hashed, host failures are no verdict; variants (bash function, exporter swap, tr, unreadable exporter, mismatched release tree) + LD_PRELOAD ----
echo "(FV=$FV)"
TC36=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.36.0"]["prefix"])' "$FV/config/components.json")
res() { python3 -I -c 'import json,sys
try: j=json.load(open(sys.argv[1]))
except Exception: print("NO-RESULT-JSON"); sys.exit()
print(j.get("verdict"), j.get("trust"), j.get("require_sorried_holes"), "|", str(j.get("reason",""))[:160])' "$1"; }
# weak artifacts: an official export and a build of `Demo.thm : 0 = 0` (the challenge sources below state 0 = 1 := sorry)
mkdir -p "$W/weakchal"; cp "$W/tampered_chal/lakefile.toml" "$W/tampered_chal/comparator.json" "$W/weakchal/"
echo leanprover/lean4:v4.36.0 > "$W/weakchal/lean-toolchain"; printf 'namespace Demo\ntheorem thm : 0 = 0 := rfl\nend Demo\n' > "$W/weakchal/Demo.lean"
python3 -I -B "$FVL" - "$W/weakchal" "$W/o_weak" --from-export /nonexistent --threads 2 > "$W/o_weak.log" 2>&1
cp "$W/o_weak/challenge.export" "$W/weak.export" 2>/dev/null
cp -a "$W/weakchal" "$W/weakbuild"
"$FV/build/official-build.sh" "$W/weakbuild" /nonexistent "$TC36" --threads 2 --log "$W/weakbuild.log" > /dev/null 2>&1
if [ -f "$W/weak.export" ] && [ -f "$W/weakbuild/.lake/build/lib/lean/Demo.olean" ]; then
  # BASH_ENV defines a function `bash` that swaps the verified lake for a script copying the weak build
  srcchal chal_bashenv leanprover/lean4:v4.36.0
  mkdir -p "$W/faketc/bin"
  printf '#!/bin/sh\necho "UNVERIFIED-LAKE-RAN $*"\ncase "$1" in build) mkdir -p .lake && cp -a "%s" .lake/ && exit 0;; esac\nexit 3\n' "$W/weakbuild/.lake/build" > "$W/faketc/bin/lake"
  chmod +x "$W/faketc/bin/lake"
  cat > "$W/evil-bashenv.sh" <<EOF
bash() { local a=() x; for x in "\$@"; do case "\$x" in */bin/lake) a+=("$W/faketc/bin/lake");; *) a+=("\$x");; esac; done
  case " \$* " in *"/bin/lake build "*) ;; *) a=("\$@");; esac; command bash "\${a[@]}"; }
EOF
  BASH_ENV="$W/evil-bashenv.sh" timeout 1200 python3 -I -B "$FVL" - "$W/chal_bashenv" "$W/o_bashenv" --from-export "$W/weak.export" --threads 2 > "$W/o_bashenv.log" 2>&1; rc=$?
  r=$(res "$W/o_bashenv/result.json")
  case "$rc|$r" in "0|ACCEPTED"*) ko env/bashenv-unverified-lake "exit 0 ACCEPTED for a challenge stating 0 = 1 (BASH_ENV reached the build)";;
    *) ok env/bashenv-unverified-lake "exit $rc $r";; esac
  # a fake `tr` early in PATH rewrites the LEAN_PATH official-build.sh writes (challenge read from caller .oleans)
  mkdir -p "$W/pathbin"
  printf '#!/bin/sh\nif [ "$1" = -d ] && [ "$#" = 2 ]; then cat > /dev/null; printf "%%s" "%s"; exit 0; fi\nexec /usr/bin/tr "$@"\n' \
    "$W/weakbuild/.lake/build/lib/lean:$TC36/lib/lean" > "$W/pathbin/tr"; chmod +x "$W/pathbin/tr"
  srcchal chal_trpath leanprover/lean4:v4.36.0
  PATH="$W/pathbin:$PATH" timeout 1200 python3 -I -B "$FVL" - "$W/chal_trpath" "$W/o_trpath" --from-export "$W/weak.export" --threads 2 > "$W/o_trpath.log" 2>&1; rc=$?
  r=$(res "$W/o_trpath/result.json")
  case "$rc|$r" in "0|ACCEPTED"*) ko env/path-tr-lean-path "exit 0 ACCEPTED for a challenge stating 0 = 1 (PATH reached the build)";;
    *) ok env/path-tr-lean-path "exit $rc $r";; esac
  # the registered exporter is swapped for `cat weak.export` once the challenge build starts (after the sha check)
  mkdir -p "$W/exp"; cp "$TC36/bin/leanexport" "$W/exp/leanexport"
  V9=$(mkview expswap "t['leanprover/lean4:v4.36.0']['official_lean4export']['path'] = '$W/exp/leanexport'"); srcchal chal_expswap leanprover/lean4:v4.36.0
  printf '#!/bin/sh\necho FORGED-EXPORTER-RAN >&2\nexec cat %s\n' "$W/weak.export" > "$W/forged.sh"; chmod +x "$W/forged.sh"
  ( for i in $(seq 1 6000); do [ -d "$W/o_expswap/log-challenge-build" ] && { cp "$W/forged.sh" "$W/exp/.n" && mv -f "$W/exp/.n" "$W/exp/leanexport"; break; }; sleep 0.01; done ) &
  wp=$!
  timeout 1200 python3 -I -B "$V9/tools/lowmem/fv_lowmem.py" - "$W/chal_expswap" "$W/o_expswap" --from-export "$W/weak.export" --threads 2 > "$W/o_expswap.log" 2>&1; rc=$?
  wait $wp
  r=$(res "$W/o_expswap/result.json")
  case "$rc|$r" in "0|ACCEPTED"*) ko exporter/swap-after-check "exit 0 ACCEPTED: the exporter that ran was not the one hashed";;
    *) ok exporter/swap-after-check "exit $rc $r";; esac
else ko env/setup "weak artifacts not built: $(tail -c 300 "$W/o_weak.log")"; fi
# LD_PRELOAD: a library logging the name of every process that loads it; no stage process may load it
if command -v gcc > /dev/null; then
  printf '#include <stdio.h>\n__attribute__((constructor)) static void m(void){ char c[64]={0}; FILE*f=fopen("/proc/self/comm","r"); if(f){ if(!fgets(c,63,f)) c[0]=0; fclose(f);} FILE*o=fopen("%s","a"); if(o){ fputs(c,o); fclose(o);} }\n' "$W/preload.log" > "$W/mark.c"
  gcc -shared -fPIC -o "$W/mark.so" "$W/mark.c" 2>/dev/null
  srcchal chal_ld leanprover/lean4:v4.36.0
  LD_PRELOAD="$W/mark.so" timeout 1200 python3 -I -B "$FVL" - "$W/chal_ld" "$W/o_ld" --from-export "$Q4/SolutionHonest.export" --threads 2 > "$W/o_ld.log" 2>&1
  stages=$(grep -v -x -e python3 -e env -e timeout "$W/preload.log" 2>/dev/null | sort -u | tr '\n' ' ')   # launcher: timeout -> python3 -> env
  [ -s "$W/preload.log" ] && [ -z "$stages" ] && ok env/ld-preload-not-in-stages "only the launching process loaded it ($(sort -u "$W/preload.log" | tr '\n' ' '))" \
    || ko env/ld-preload-not-in-stages "stage processes loaded the caller's LD_PRELOAD: ${stages:-none recorded}"
else echo "SKIP env/ld-preload-not-in-stages: no gcc"; fi
# an unreadable registered exporter -> exit 2 ERROR with result.json (never a traceback / exit 1)
mkdir -p "$W/exp10"; printf 'x' > "$W/exp10/leanexport"; chmod 000 "$W/exp10/leanexport"
V10=$(mkview unreadable "t['leanprover/lean4:v4.36.0']['official_lean4export']['path'] = '$W/exp10/leanexport'"); srcchal chal_unreadable leanprover/lean4:v4.36.0
timeout 1200 python3 -I -B "$V10/tools/lowmem/fv_lowmem.py" - "$W/chal_unreadable" "$W/o_unreadable" --from-export "$Q4/SolutionHonest.export" --threads 2 > "$W/o_unreadable.log" 2>&1; rc=$?
r=$(res "$W/o_unreadable/result.json"); chmod 600 "$W/exp10/leanexport"
case "$rc|$r" in "2|ERROR"*) ok exporter/unreadable-error "exit 2 $r";; *) ko exporter/unreadable-error "exit $rc $r; $(tail -1 "$W/o_unreadable.log")";; esac
# a registered OFFICIAL id with a pinned manifest whose prefix holds another release's tree
V11=$(mkview wrongtree "t['leanprover/lean4:v4.36.0-rc1'] = dict(t['leanprover/lean4:v4.36.0'])"); srcchal chal_wrongtree leanprover/lean4:v4.36.0-rc1
timeout 1200 python3 -I -B "$V11/tools/lowmem/fv_lowmem.py" - "$W/chal_wrongtree" "$W/o_wrongtree" --from-export "$Q4/SolutionHonest.export" --threads 2 > "$W/o_wrongtree.log" 2>&1; rc=$?
r=$(res "$W/o_wrongtree/result.json")
if [ "$rc" = 2 ] && grep -q "does not verify" "$W/o_wrongtree/result.json" 2>/dev/null; then ok lowmem/registered-official-id-wrong-tree "exit 2 (does not verify against its pinned manifest)"
else ko lowmem/registered-official-id-wrong-tree "exit $rc $r"; fi
# --require-sorried-holes is recorded in ERROR results too
mkdir -p "$W/nocfg"
python3 -I -B "$FVL" - "$W/nocfg" "$W/o_rshe" --from-export "$Q4/SolutionHonest.export" --require-sorried-holes > "$W/o_rshe.log" 2>&1; rc=$?
r=$(res "$W/o_rshe/result.json")
case "$rc|$r" in "2|ERROR none True |"*) ok lowmem/require-sorried-holes-in-error-result "exit 2 $r";; *) ko lowmem/require-sorried-holes-in-error-result "exit $rc $r";; esac
# an honest Lean 4.36.0 SOURCES-IN project: the low-memory native exporter has no 4.36 entry, so
# the export falls back to the VERIFIED official exporter (earlier: export-lowmem.sh's own fallback -> ERROR)
srcchal chal_h436 leanprover/lean4:v4.36.0; printf 'namespace Demo\ntheorem thm : 1 + 1 = 2 := sorry\nend Demo\n' > "$W/chal_h436/Demo.lean"
mkdir -p "$W/proj_h436"; cp "$W/chal_h436/lakefile.toml" "$W/chal_h436/lean-toolchain" "$W/proj_h436/"
printf 'namespace Demo\ntheorem thm : 1 + 1 = 2 := rfl\nend Demo\n' > "$W/proj_h436/Demo.lean"
timeout 1800 python3 -I -B "$FVL" "$W/proj_h436" "$W/chal_h436" "$W/o_h436" --threads 2 > "$W/o_h436.log" 2>&1; rc=$?
r=$(res "$W/o_h436/result.json")
case "$rc|$r" in "0|ACCEPTED sound"*) ok lowmem/sources-in-436-honest-accepted "exit 0 $r";; *) ko lowmem/sources-in-436-honest-accepted "exit $rc $r";; esac
# the private exporter copies are deleted at the end; their source + sha256 stay in result.json
if [ ! -e "$W/o_h436/.exporter" ] && grep -q '"official_exporters"' "$W/o_h436/result.json" 2>/dev/null; then
  ok lowmem/exporter-copy-deleted-sha-recorded "no .exporter left, sha recorded"
else ko lowmem/exporter-copy-deleted-sha-recorded "copy left: $([ -e "$W/o_h436/.exporter" ] && echo yes || echo no), sha recorded: $(grep -c official_exporters "$W/o_h436/result.json" 2>/dev/null)"; fi
# started with SIGCHLD ignored (survives env -i): a tree that fails verification is still refused
srcchal chal_g1 leanprover/lean4:v4.36.0-rc1
timeout 300 python3 -I -c 'import os, signal, sys; signal.signal(signal.SIGCHLD, signal.SIG_IGN); os.execv("/usr/bin/python3", ["/usr/bin/python3", "-I"] + sys.argv[1:])' \
  "$V11/tools/lowmem/fv_lowmem.py" - "$W/chal_g1" "$W/o_g1" --from-export "$Q4/SolutionHonest.export" --threads 2 > "$W/o_g1.log" 2>&1; rc=$?
if [ "$rc" = 2 ] && grep -q "does not verify" "$W/o_g1/result.json" 2>/dev/null; then ok signal/sigchld-ignored-still-refused "exit 2 (does not verify)"
else ko signal/sigchld-ignored-still-refused "exit $rc $(res "$W/o_g1/result.json")"; fi
# an existing empty OUT created 0777 is made 0700 before use
mkdir -p "$W/o_g3"; chmod 0777 "$W/o_g3"
python3 -I -B "$FVL" - "$W/nocfg" "$W/o_g3" --from-export "$Q4/SolutionHonest.export" > /dev/null 2>&1
m=$(stat -c %a "$W/o_g3"); [ "$m" = 700 ] && ok lowmem/out-mode-0700 "OUT mode $m" || ko lowmem/out-mode-0700 "OUT mode $m"
# SIGTERM during a run: the stage tree is killed and an ERROR result.json is written
srcchal chal_g4 leanprover/lean4:v4.36.0
python3 -I -B "$FVL" - "$W/chal_g4" "$W/o_g4" --from-export "$Q4/SolutionHonest.export" --threads 2 > "$W/o_g4.log" 2>&1 &
gp=$!
for i in $(seq 1 600); do [ -e "$W/o_g4/work_challenge" ] && break; sleep 0.1; done; sleep 2
kill -TERM $gp 2>/dev/null; wait $gp; rc=$?; sleep 3
left=$(pgrep -f "o_g4/work_challenge" | wc -l)
if [ "$rc" = 2 ] && grep -q '"interrupted by signal' "$W/o_g4/result.json" 2>/dev/null && [ "$left" = 0 ]; then
  ok signal/sigterm-error-result-stages-killed "exit 2, ERROR result.json, 0 stage processes left"
else ko signal/sigterm-error-result-stages-killed "exit $rc, result: $(res "$W/o_g4/result.json"), stage processes left: $left"; pkill -KILL -f "o_g4/work_challenge" 2>/dev/null; fi
# ---- projects WITH a Lake dependency through the official exporter
# (E0: the challenge export, and the project export when the native low-memory exporter declines) -- earlier versions bound the
# empty mount point instead of the checkout (false REJECTED trust sound-lowmem); a failed export is ERROR, never REJECTED;
# OUT disjoint from PROJECT / CHALLENGE ----
TC33=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json")
depcase() { # depcase TAG TOOLCHAIN_ID TC_PREFIX MANIFEST_VERSION -> $W/ws_TAG (dep built), $W/dchal_TAG, $W/dproj_TAG
  local ws="$W/ws_$1" dep="$W/ws_$1/.lake/packages/dep" rev d
  mkdir -p "$dep"; printf '%s\n' "$2" > "$dep/lean-toolchain"
  printf 'name = "dep"\ndefaultTargets = ["Dep"]\n[[lean_lib]]\nname = "Dep"\n' > "$dep/lakefile.toml"
  printf 'theorem dep_thm : 1 + 1 = 2 := rfl\n' > "$dep/Dep.lean"
  ( cd "$dep" && env -i PATH=/usr/bin:/bin HOME="$W" git init -q && env -i PATH=/usr/bin:/bin HOME="$W" git add . \
    && env -i PATH=/usr/bin:/bin HOME="$W" git remote add origin https://example.invalid/dep.git \
    && env -i PATH=/usr/bin:/bin HOME="$W" git -c user.name=t -c user.email=t@t commit -q -m init ) || return 1
  rev=$(cd "$dep" && env -i PATH=/usr/bin:/bin HOME="$W" git rev-parse HEAD)
  env -i PATH=/usr/bin:/bin LANG=C.UTF-8 HOME="$W" "$FV/build/official-build.sh" "$dep" /nonexistent "$3" --threads 2 \
    --log "$W/log_dep_$1" > /dev/null 2>&1 || return 1
  python3 -I -c 'import json,sys
m = {"version": sys.argv[2], "name": "Demo", "packagesDir": ".lake/packages", "lakeDir": ".lake", "packages": [{
     "type": "git", "scope": "", "name": "dep", "manifestFile": "lake-manifest.json", "url": "https://example.invalid/dep.git",
     "rev": sys.argv[3], "inputRev": "main", "inherited": False, "configFile": "lakefile.toml", "subDir": None}]}
json.dump(m, open(sys.argv[1], "w"), indent=2)' "$ws/lake-manifest.json" "$4" "$rev"
  for d in "$W/dchal_$1" "$W/dproj_$1"; do
    mkdir -p "$d"; printf '%s\n' "$2" > "$d/lean-toolchain"; cp "$ws/lake-manifest.json" "$d/"
    printf 'name = "Demo"\ndefaultTargets = ["Demo"]\n[[lean_lib]]\nname = "Demo"\n[[require]]\nname = "dep"\ngit = "https://example.invalid/dep.git"\nrev = "main"\n' > "$d/lakefile.toml"
  done
  printf 'import Dep\ntheorem thm : 1 + 1 = 2 := sorry\n' > "$W/dchal_$1/Demo.lean"
  printf 'import Dep\ntheorem thm : 1 + 1 = 2 := dep_thm\n' > "$W/dproj_$1/Demo.lean"
  printf '{"challenge_module": "Demo", "solution_module": "Demo", "theorem_names": ["thm"], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}\n' > "$W/dchal_$1/comparator.json"; }
pinchal() { # pinchal SRC_CHAL OUT_WITH_EXPORT DST -> prints the sha256 of the pinned challenge export
  cp -a "$1" "$3"; cp "$2/challenge.export" "$3/challenge.export"; chmod u+w "$3/challenge.export"
  sha256sum "$3/challenge.export" | cut -d' ' -f1; }
deprow() { # deprow NAME FVL PROJ CHAL OUTTAG [extra args]
  local n=$1 f=$2 pj=$3 ch=$4 o="$W/o_$5"; shift 5
  timeout 1800 python3 -I -B "$f" "$pj" "$ch" "$o" "$@" --threads 2 > "$o.log" 2>&1; local rc=$?
  local r; r=$(res "$o/result.json")
  case "$rc|$r" in "0|ACCEPTED sound"*) ok "$n" "exit 0 $r";;
    *) ko "$n" "exit $rc $r; $(tail -c 200 "$o/export_official.log" "$o/challenge_export.log" 2>/dev/null | tr '\n' ' ' | cut -c1-220)";; esac; }
if depcase 436 leanprover/lean4:v4.36.0 "$TC36" 1.2.0; then
  deprow deps/436-sources-chal-accepted "$FVL" "$W/dproj_436" "$W/dchal_436" d436s --packages "$W/ws_436"
  if [ -f "$W/o_d436s/challenge.export" ]; then
    s=$(pinchal "$W/dchal_436" "$W/o_d436s" "$W/dchalp_436")
    deprow deps/436-pinned-chal-accepted "$FVL" "$W/dproj_436" "$W/dchalp_436" d436p --packages "$W/ws_436" --challenge-sha256 "$s" --comparator-sha256 "$(cpin "$W/dchalp_436")"
  else ko deps/436-pinned-chal-accepted "no official challenge export to pin (the sources-chal row failed)"; fi
else ko deps/436-sources-chal-accepted "fixture: the 4.36.0 dependency did not build"; fi
if depcase 4331 leanprover/lean4:v4.33.1 "$TC33" 1.1.0; then
  deprow deps/4331-sources-chal-accepted "$FVL" "$W/dproj_4331" "$W/dchal_4331" d4331s --packages "$W/ws_4331"
  # a package view whose low-memory native exporter is absent: export-lowmem.sh declines (exit 2), E0 exports
  VND=$(mkview nodecl 'pass'); rm -f "$VND/export/components-lowmem.json"
  python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c["native"]["path"]="/nonexistent/lean4export-lowmem"; c.pop("natives_other", None)
json.dump(c, open(sys.argv[2], "w"), indent=2)' "$FV/export/components-lowmem.json" "$VND/export/components-lowmem.json"
  if [ -f "$W/o_d4331s/challenge.export" ]; then
    s=$(pinchal "$W/dchal_4331" "$W/o_d4331s" "$W/dchalp_4331")
    deprow deps/4331-native-declines-pinned-accepted "$VND/tools/lowmem/fv_lowmem.py" "$W/dproj_4331" "$W/dchalp_4331" d4331n \
      --packages "$W/ws_4331" --challenge-sha256 "$s" --comparator-sha256 "$(cpin "$W/dchalp_4331")"
    grep -q '"exporter": "none"' "$W/o_d4331n/export.json" 2>/dev/null && ok control/4331-native-really-declined "export-lowmem.sh declined, E0 exported" \
      || ko control/4331-native-really-declined "$(head -c 200 "$W/o_d4331n/export.json" 2>/dev/null)"
  else ko deps/4331-native-declines-pinned-accepted "no official challenge export to pin (the sources-chal row failed)"; fi
else ko deps/4331-sources-chal-accepted "fixture: the 4.33.1 dependency did not build"; fi
# a project that builds but whose export fails officially (it does not declare the target theorem): ERROR, never REJECTED
if [ -f "$W/o_h436/challenge.export" ]; then
  s=$(pinchal "$W/chal_h436" "$W/o_h436" "$W/chalp_h436")
  mkdir -p "$W/proj_nothm"; cp "$W/chal_h436/lakefile.toml" "$W/chal_h436/lean-toolchain" "$W/proj_nothm/"
  printf 'namespace Demo\ntheorem other : 1 + 1 = 2 := rfl\nend Demo\n' > "$W/proj_nothm/Demo.lean"
  timeout 1800 python3 -I -B "$FVL" "$W/proj_nothm" "$W/chalp_h436" "$W/o_nothm" --challenge-sha256 "$s" --comparator-sha256 "$(cpin "$W/chalp_h436")" --threads 2 > "$W/o_nothm.log" 2>&1; rc=$?
  r=$(res "$W/o_nothm/result.json")
  case "$rc|$r" in "2|ERROR none"*"export"*) ok export/official-export-failure-is-error "exit 2 $r";;
    *) ko export/official-export-failure-is-error "exit $rc $r";; esac
else ko export/official-export-failure-is-error "no official challenge export to pin (lowmem/sources-in-436-honest-accepted failed)"; fi
# OUT inside CHALLENGE / inside PROJECT: refused before anything is created (as bin/fastverify)
cp -a "$W/tampered_chal" "$W/chal_nest"
python3 -I -B "$FVL" - "$W/chal_nest" "$W/chal_nest/sub_out" --from-export "$W/solution.export" --threads 2 > "$W/o_nest.log" 2>&1; rc=$?
[ "$rc" = 2 ] && [ ! -e "$W/chal_nest/sub_out" ] && grep -q "must not be inside CHALLENGE" "$W/o_nest.log" \
  && ok out/inside-challenge-refused "exit 2, nothing created in CHALLENGE" || ko out/inside-challenge-refused "exit $rc, created: $([ -e "$W/chal_nest/sub_out" ] && echo yes || echo no)"
cp -a "$W/proj_h436" "$W/proj_nest"
python3 -I -B "$FVL" "$W/proj_nest" "$W/chal_h436" "$W/proj_nest/sub_out" --threads 2 > "$W/o_nestp.log" 2>&1; rc=$?
[ "$rc" = 2 ] && [ ! -e "$W/proj_nest/sub_out" ] && grep -q "must not be inside PROJECT" "$W/o_nestp.log" \
  && ok out/inside-project-refused "exit 2, nothing created in PROJECT" || ko out/inside-project-refused "exit $rc, created: $([ -e "$W/proj_nest/sub_out" ] && echo yes || echo no)"
# ---- umask / closed fds / OUT spelling / SIGPIPE / --integrity-cache ----
if [ -f "$W/o_h436/challenge.export" ] && [ -f "$W/o_h436/solution.export" ]; then
  s=$(sha256sum "$W/chalp_h436/challenge.export" | cut -d' ' -f1)
  # a caller umask of 0277 (owner write masked) -> the run is unaffected (earlier: OUT 0500, handler crash, exit 1)
  ( umask 0277; timeout 1800 python3 -I -B "$FVL" "$W/proj_h436" "$W/chalp_h436" "$W/o_um" --challenge-sha256 "$s" --comparator-sha256 "$(cpin "$W/chalp_h436")" --threads 2 > "$W/o_um.log" 2>&1 ); rc=$?
  r=$(res "$W/o_um/result.json")
  case "$rc|$r" in "0|ACCEPTED sound"*) ok umask/0277-honest-accepted "exit 0 $r";; *) ko umask/0277-honest-accepted "exit $rc $r";; esac
  # umask 0777 on a refused input -> exit 2 with result.json (earlier: exit 1)
  ( umask 0777; python3 -I -B "$FVL" - "$W/tampered_chal" "$W/o_um7" --from-export "$W/solution.export" --threads 2 > "$W/o_um7.log" 2>&1 ); rc=$?
  r=$(res "$W/o_um7/result.json")
  case "$rc|$r" in "2|ERROR"*) ok umask/0777-refusal-exit-2 "exit 2 $r";; *) ko umask/0777-refusal-exit-2 "exit $rc $r";; esac
  # stdout a closed pipe -> still exit 0 (earlier: killed by SIGPIPE, 141, after ACCEPTED)
  python3 -I -B "$FVL" - "$W/chalp_h436" "$W/o_pipe" --from-export "$W/o_h436/solution.export" --challenge-sha256 "$s" --comparator-sha256 "$(cpin "$W/chalp_h436")" --threads 2 2> "$W/o_pipe.log" | head -c 0
  rc=${PIPESTATUS[0]}; r=$(res "$W/o_pipe/result.json")
  case "$rc|$r" in "0|ACCEPTED sound"*) ok sigpipe/closed-stdout-exit-0 "exit 0 $r";; *) ko sigpipe/closed-stdout-exit-0 "exit $rc $r";; esac
  # a caller --integrity-cache DIR is not used (bin/fastverify's private per-package directory instead)
  mkdir -m 700 "$W/ic_caller"
  python3 -I -B "$FVL" - "$W/chalp_h436" "$W/o_ic" --from-export "$W/o_h436/solution.export" --challenge-sha256 "$s" --comparator-sha256 "$(cpin "$W/chalp_h436")" --threads 2 \
    --integrity-cache "$W/ic_caller" > "$W/o_ic.log" 2>&1; rc=$?
  r=$(res "$W/o_ic/result.json"); n=$(ls -A "$W/ic_caller" | wc -l)
  case "$rc|$n|$r" in "0|0|ACCEPTED sound"*) ok lowmem/integrity-cache-caller-dir-unused "exit 0, caller dir untouched";;
    *) ko lowmem/integrity-cache-caller-dir-unused "exit $rc, $n entries in the caller dir, $r";; esac
else for n in umask/0277-honest-accepted umask/0777-refusal-exit-2 sigpipe/closed-stdout-exit-0 lowmem/integrity-cache-caller-dir-unused; do
  ko "$n" "no honest 4.36 run to reuse (lowmem/sources-in-436-honest-accepted failed)"; done; fi
# ---- as in bin/fastverify: permitted axioms compared as LEAN names (xvcheck.py
# parse_lean_name, the judges' String.toName): `«propext»` IS propext; the S1 set is never widened ----
if [ -f "$W/o_h436/solution.export" ] && [ -f "$W/chalp_h436/challenge.export" ]; then
  s=$(sha256sum "$W/chalp_h436/challenge.export" | cut -d' ' -f1)
  cfgax() { # cfgax DIR AXIOM...: a copy of the pinned 4.36 challenge whose comparator.json permits exactly these axioms
    cp -a "$W/chalp_h436" "$W/$1"; local d=$1; shift
    python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c["permitted_axioms"]=sys.argv[2:]; json.dump(c, open(sys.argv[1],"w"))' \
      "$W/$d/comparator.json" "$@"; }
  cfgax chalq_h436 "«propext»" "Quot.sound" "Classical.choice"
  timeout 1800 python3 -I -B "$FVL" - "$W/chalq_h436" "$W/o_qprop" --from-export "$W/o_h436/solution.export" --challenge-sha256 "$s" --comparator-sha256 "$(cpin "$W/chalq_h436")" \
    --threads 2 > "$W/o_qprop.log" 2>&1; rc=$?
  r=$(res "$W/o_qprop/result.json")
  case "$rc|$r" in "0|ACCEPTED sound"*) ok axioms/quoted-propext-accepted "exit 0 $r";; *) ko axioms/quoted-propext-accepted "exit $rc $r";; esac
  for c in "quot-sound-one-component:«Quot.sound»" "propext-x:propext.x" "quoted-sorryax:«sorryAx»" "not-a-name:pro pext"; do
    n=${c%%:*}; ax=${c#*:}
    cfgax "chalw_$n" "$ax" "Classical.choice"
    python3 -I -B "$FVL" - "$W/chalw_$n" "$W/o_w_$n" --from-export "$W/o_h436/solution.export" --challenge-sha256 "$s" --comparator-sha256 "$(cpin "$W/chalw_$n")" --threads 2 \
      > "$W/o_w_$n.log" 2>&1; rc=$?
    r=$(res "$W/o_w_$n/result.json")   # the reason is matched in the whole result.json (res truncates it)
    if [ "$rc" = 2 ] && grep -q '"verdict": "ERROR"' "$W/o_w_$n/result.json" 2>/dev/null \
       && grep -Eq 'outside GOAL S1|permits sorryAx' "$W/o_w_$n/result.json"; then ok "axioms/never-widened-$n" "exit 2 ($ax refused)"
    else ko "axioms/never-widened-$n" "exit $rc $r"; fi
  done
else for n in quoted-propext-accepted never-widened-quot-sound-one-component never-widened-propext-x never-widened-quoted-sorryax \
  never-widened-not-a-name; do ko "axioms/$n" "no honest 4.36 run to reuse (lowmem/sources-in-436-honest-accepted failed)"; done; fi
# ---- as in bin/fastverify: SIGHUP / SIGINT keep their inherited disposition: a nohup run
# (SIGHUP ignored) that gets SIGHUP mid-run still finishes with its verdict (earlier: ERROR "interrupted by signal 1") ----
if [ -f "$W/o_h436/solution.export" ] && [ -f "$W/chalp_h436/challenge.export" ]; then
  s=$(sha256sum "$W/chalp_h436/challenge.export" | cut -d' ' -f1)
  nohup python3 -I -B "$FVL" - "$W/chalp_h436" "$W/o_nohup" --from-export "$W/o_h436/solution.export" --challenge-sha256 "$s" --comparator-sha256 "$(cpin "$W/chalp_h436")" \
    --threads 2 > "$W/o_nohup.log" 2>&1 &
  np=$!
  for i in $(seq 1 600); do [ -e "$W/o_nohup/solution.export" ] && break; sleep 0.1; done; sleep 1
  kill -HUP "$np" 2>/dev/null && sent=yes || sent=no
  wait "$np"; rc=$?
  r=$(res "$W/o_nohup/result.json")
  case "$sent|$rc|$r" in "yes|0|ACCEPTED sound"*) ok signal/nohup-sighup-survives "SIGHUP sent mid-run, exit 0 $r";;
    *) ko signal/nohup-sighup-survives "SIGHUP sent: $sent, exit $rc $r";; esac
else ko signal/nohup-sighup-survives "no honest 4.36 run to reuse (lowmem/sources-in-436-honest-accepted failed)"; fi
# ---- result.json size limit, '-' challenge, S1 axiom check before the build ----
# a file-size limit while result.json is written: exit 2, result.json complete or absent (earlier: killed by SIGXFSZ, 153,
# or a partial "{" left)
python3 -I -c 'import os, resource, sys; resource.setrlimit(resource.RLIMIT_FSIZE, (1, 1)); os.execv("/usr/bin/python3", ["/usr/bin/python3", "-I"] + sys.argv[1:])' \
  "$FVL" - "$W/nocfg" "$W/o_fsz" --from-export "$Q4/SolutionHonest.export" > "$W/o_fsz.log" 2>&1; rc=$?
jok=$(python3 -I -c 'import json,sys,os
p=sys.argv[1]
if not os.path.exists(p): print("absent")
else:
    try: json.load(open(p)); print("complete")
    except Exception: print("partial")' "$W/o_fsz/result.json")
case "$rc|$jok" in "2|absent"|"2|complete") ok result/file-size-limit-exit-2-no-partial "exit 2, result.json $jok";;
  *) ko result/file-size-limit-exit-2-no-partial "exit $rc, result.json $jok";; esac
# the challenge spelled '-' is still a directory for the OUT disjointness check (earlier versions skipped it)
mkdir -p "$W/dashcase"; cp -a "$W/tampered_chal" "$W/dashcase/-"
( cd "$W/dashcase" && python3 -I -B "$FVL" - - ./-/sub_out --from-export "$W/solution.export" --threads 2 > "$W/o_dash.log" 2>&1 ); rc=$?
[ "$rc" = 2 ] && [ ! -e "$W/dashcase/-/sub_out" ] && grep -q "must not be inside CHALLENGE" "$W/o_dash.log" \
  && ok out/dash-challenge-disjoint "exit 2, nothing created in CHALLENGE '-'" \
  || ko out/dash-challenge-disjoint "exit $rc, created: $([ -e "$W/dashcase/-/sub_out" ] && echo yes || echo no)"
# a comparator outside S1(3) is no verdict even when the project fails to build (earlier: REJECTED trust sound-lowmem)
if [ -d "$W/chal_h436" ]; then
  cp -a "$W/chal_h436" "$W/chal_evil"
  python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c["permitted_axioms"]=["propext", "evilCustomAxiom"]; json.dump(c, open(sys.argv[1],"w"))' "$W/chal_evil/comparator.json"
  mkdir -p "$W/proj_broken"; cp "$W/chal_h436/lakefile.toml" "$W/chal_h436/lean-toolchain" "$W/proj_broken/"
  printf 'namespace Demo\ntheorem thm : 1 + 1 = 2 := by exact (\nend Demo\n' > "$W/proj_broken/Demo.lean"
  timeout 1800 python3 -I -B "$FVL" "$W/proj_broken" "$W/chal_evil" "$W/o_evil" --threads 2 > "$W/o_evil.log" 2>&1; rc=$?
  if [ "$rc" = 2 ] && grep -q "outside GOAL S1" "$W/o_evil/result.json" 2>/dev/null && [ ! -e "$W/o_evil/log-build" ]; then
    ok axioms/s1-gate-before-build "exit 2 ERROR before any build"
  else ko axioms/s1-gate-before-build "exit $rc $(res "$W/o_evil/result.json")"; fi
else ko axioms/s1-gate-before-build "fixture chal_h436 missing"; fi
# ---- wherever --challenge-sha256 is required (a given challenge
# export), --comparator-sha256 is required too and checked on the private copy; judge.sh / autojudge3.sh need CFGSHA ----
if [ -f "$W/o_h436/solution.export" ] && [ -f "$W/chalp_h436/challenge.export" ]; then
  s=$(sha256sum "$W/chalp_h436/challenge.export" | cut -d' ' -f1); cs=$(cpin "$W/chalp_h436")
  python3 -I -B "$FVL" - "$W/chalp_h436" "$W/o_cp0" --from-export "$W/o_h436/solution.export" --challenge-sha256 "$s" --threads 2 > "$W/o_cp0.log" 2>&1; rc=$?
  if [ "$rc" = 2 ] && grep -q "comparator-sha256" "$W/o_cp0/result.json" 2>/dev/null && [ ! -e "$W/o_cp0/check.json" ]; then
    ok pin/comparator-missing-refused "exit 2 ERROR, no check ran"; else ko pin/comparator-missing-refused "exit $rc $(res "$W/o_cp0/result.json")"; fi
  python3 -I -B "$FVL" - "$W/chalp_h436" "$W/o_cp1" --from-export "$W/o_h436/solution.export" --challenge-sha256 "$s" \
    --comparator-sha256 "$(printf 'c%.0s' $(seq 64))" --threads 2 > "$W/o_cp1.log" 2>&1; rc=$?
  if [ "$rc" = 2 ] && grep -q "comparator.json sha256 mismatch" "$W/o_cp1/result.json" 2>/dev/null && [ ! -e "$W/o_cp1/check.json" ]; then
    ok pin/comparator-wrong-refused "exit 2 ERROR (mismatch on the private copy), no check ran"; else ko pin/comparator-wrong-refused "exit $rc $(res "$W/o_cp1/result.json")"; fi
  python3 -I -B "$FVL" - "$W/chalp_h436" "$W/o_cp2" --from-export "$W/o_h436/solution.export" --challenge-sha256 "$s" \
    --comparator-sha256 "$cs" --threads 2 > "$W/o_cp2.log" 2>&1; rc=$?
  r=$(res "$W/o_cp2/result.json")
  if [ "$rc" = 0 ] && grep -q "\"comparator_sha256\": \"$cs\"" "$W/o_cp2/result.json"; then ok pin/comparator-correct-honest-accepted "exit 0 $r (pin recorded)"
  else ko pin/comparator-correct-honest-accepted "exit $rc $r"; fi
  mkdir -p "$W/proj_cheat"; cp "$W/chal_h436/lakefile.toml" "$W/chal_h436/lean-toolchain" "$W/proj_cheat/"
  printf 'namespace Demo\ntheorem thm : 1 + 1 = 2 := sorry\nend Demo\n' > "$W/proj_cheat/Demo.lean"
  timeout 1800 python3 -I -B "$FVL" "$W/proj_cheat" "$W/chalp_h436" "$W/o_cp3" --challenge-sha256 "$s" --comparator-sha256 "$cs" --threads 2 > "$W/o_cp3.log" 2>&1; rc=$?
  r=$(res "$W/o_cp3/result.json")
  case "$rc|$r" in "1|REJECTED"*) ok pin/comparator-correct-cheat-rejected "exit 1 $r";; *) ko pin/comparator-correct-cheat-rejected "exit $rc $r";; esac
else for n in comparator-missing-refused comparator-wrong-refused comparator-correct-honest-accepted comparator-correct-cheat-rejected; do
  ko "pin/$n" "no honest 4.36 run to reuse (lowmem/sources-in-436-honest-accepted failed)"; done; fi
if [ -f "$FV/tools/judge/judge.sh" ] && [ -f "$FV/tools/judge/autojudge3.sh" ]; then   # tools/judge is not shipped in every tree
  ( unset CFGSHA; CSHA=$(printf 'a%.0s' $(seq 64)) bash "$FV/tools/judge/judge.sh" t local:/nonexistent "$W/judge_cfg" > "$W/judge_cfg.out" 2>&1 ); rc=$?
  # no check ran: cs.json absent, or the ERROR record judge.sh writes before any refusal; no cs.out
  [ "$rc" = 2 ] && grep -q "CFGSHA" "$W/judge_cfg.out" && [ ! -e "$W/judge_cfg/t/cs.out" ] && { [ ! -e "$W/judge_cfg/t/cs.json" ] || grep -q '"verdict": "ERROR"' "$W/judge_cfg/t/cs.json"; } && ok judge/comparator-unpinned-refused "exit 2, no check ran" \
    || ko judge/comparator-unpinned-refused "exit $rc $(tail -c 200 "$W/judge_cfg.out")"
  ( unset CFGSHA; CSHA=$(printf 'a%.0s' $(seq 64)) NRUN=/bin/false timeout 20 bash "$FV/tools/judge/autojudge3.sh" t 127.0.0.1 nonode "/nonexistent" > "$W/aj_cfg.out" 2>&1 ); rc=$?
  [ "$rc" = 2 ] && grep -q "CFGSHA" "$W/aj_cfg.out" && ok judge/autojudge3-comparator-pin-up-front "exit 2 before any polling" \
    || ko judge/autojudge3-comparator-pin-up-front "exit $rc $(tail -c 200 "$W/aj_cfg.out")"
else echo "SKIP judge/comparator-*: tools/judge is not shipped in this tree"; fi
# ---- --challenge-sha256 with a SOURCE-only challenge needs the comparator
# pin too (the "given export" decision is made once); --help / an abbreviated option is no verdict (exit 2, not 0 = ACCEPTED) ----
if [ -d "$W/chal_h436" ]; then
  python3 -I -B "$FVL" "$W/proj_h436" "$W/chal_h436" "$W/o_srcpin" --challenge-sha256 "$(printf 'd%.0s' $(seq 64))" --threads 2 > "$W/o_srcpin.log" 2>&1; rc=$?
  [ "$rc" = 2 ] && grep -q "comparator-sha256" "$W/o_srcpin/result.json" 2>/dev/null && [ ! -e "$W/o_srcpin/log-challenge-build" ] \
    && ok pin/source-challenge-pin-needs-comparator "exit 2 before any build" || ko pin/source-challenge-pin-needs-comparator "exit $rc $(res "$W/o_srcpin/result.json")"
else ko pin/source-challenge-pin-needs-comparator "fixture chal_h436 missing"; fi
python3 -I -B "$FVL" --help > /dev/null 2>&1; rc1=$?
python3 -I -B "$FVL" - "$W/tampered_chal" "$W/o_abbr" --from-ex "$W/solution.export" > /dev/null 2>&1; rc2=$?
[ "$rc1" = 2 ] && [ "$rc2" = 2 ] && ok cli/help-and-abbrev-no-verdict "exit 2 / 2" || ko cli/help-and-abbrev-no-verdict "--help exit $rc1, --from-ex exit $rc2"
# fd 2 closed at the re-exec guard (dirty environment + --clean-env-reexec) -> exit 2 (earlier: AttributeError, exit 1)
env FV_DIRTY=1 /usr/bin/python3 -I "$FVL" --clean-env-reexec - "$W/tampered_chal" "$W/o_fd2" 2>&-; rc=$?
[ "$rc" = 2 ] && ok fd/stderr-closed-reexec-guard-exit-2 "exit 2" || ko fd/stderr-closed-reexec-guard-exit-2 "exit $rc"
# OUT spelled 'sym/.' (a symlink to a real empty directory) -> refused, nothing written through the link
mkdir "$W/real_out"; ln -s "$W/real_out" "$W/sym_out"
python3 -I -B "$FVL" - "$W/tampered_chal" "$W/sym_out/." --from-export "$W/solution.export" --threads 2 > "$W/o_symdot.log" 2>&1; rc=$?
n=$(ls -A "$W/real_out" | wc -l)
[ "$rc" = 2 ] && [ "$n" = 0 ] && ok out/symlink-trailing-dot-refused "exit 2, nothing written through the link" \
  || ko out/symlink-trailing-dot-refused "exit $rc, $n entries written through the link"
# an existing NON-empty 0755 directory as OUT -> refused with its mode unchanged
mkdir -m 755 "$W/full_out"; echo x > "$W/full_out/keep"
python3 -I -B "$FVL" - "$W/tampered_chal" "$W/full_out" --from-export "$W/solution.export" --threads 2 > "$W/o_full.log" 2>&1; rc=$?
m=$(stat -c %a "$W/full_out")
[ "$rc" = 2 ] && [ "$m" = 755 ] && ok out/nonempty-mode-unchanged "exit 2, mode $m" || ko out/nonempty-mode-unchanged "exit $rc, mode $m"
# no package view refers to $FV (real copies only)
nl=$(find "$W" -maxdepth 3 -type l -lname "$FV*" 2>/dev/null | wc -l)
[ "$nl" = 0 ] && ok control/views-are-real-copies "0 symlinks into $FV" || ko control/views-are-real-copies "$nl symlinks into $FV"
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
