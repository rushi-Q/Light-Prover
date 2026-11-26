#!/bin/bash
# check/checkB/test/run.sh [WORK]  -- component test of the check-B WRAPPER (check-b.sh / check_b.py): inputs, config
# handling, environment/cwd isolation, pinned binaries, resource/timeout behaviour. Every row prints
#   RESULT <case> expect=<e> got=<rc> PASS|FAIL
# and the script exits 0 iff every row passes. Small inputs from tests/026-*/x and tests/005-*/x; ~1-2 min.
# Verdict expectations: 0 = ACCEPTED, 1 = REJECTED, 2 = DECLINED; 'n1' = anything but 1 (no false reject), 'n0' = anything
# but 0 (never accept).
# (whole body in main(): bash parses it completely before running, so editing this file cannot corrupt a running copy)
main() {
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); CB=$H/../check-b.sh
X=$H/../../../tests; D26=$(ls -d $X/026-*/x); D05=$(ls -d $X/005-*/x)   # finding inputs: tests/NNN-*/x snapshots
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/fv-checkB-test.XXXXXX")}; mkdir -p "$W"; W=$(readlink -f "$W")
T=4; fails=0; n=0
row() { # name expect rc
  local ok=FAIL
  case $2 in n1) [ "$3" != 1 ] && ok=PASS;; n0) [ "$3" != 0 ] && ok=PASS;; *) [ "$3" = "$2" ] && ok=PASS;; esac
  n=$((n+1)); [ $ok = PASS ] || fails=$((fails+1)); echo "RESULT $1 expect=$2 got=$3 $ok"
}
cb() { bash "$CB" "$@" --threads $T > "$W/last.json" 2> "$W/last.err" < /dev/null; echo $?; }
lean_only() { python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("external_kernels",None); json.dump(c,open(sys.argv[2],"w"))' "$1" "$2"; }
mkcfg() { python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); exec(sys.argv[3]); json.dump(c,open(sys.argv[2],"w"))' "$D26/cfg.json" "$W/$1.json" "$2"; }
lean_only "$D26/cfg.json" "$W/leanonly.json"

# --- preflight, honest control, honest negative
bash "$CB" --preflight > /dev/null 2>&1; row preflight 0 $?
row control-nanoda-cfg 0 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$D26/cfg.json")"
row control-leanonly 0 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json")"
row sorry-solution 1 "$(cb "$D05/Challenge.export" "$D05/Challenge.export" "$W/leanonly.json")"
row wrong-statement 1 "$(cb "$D05/Main.export" "$D05/Challenge.export" "$W/leanonly.json")"
# --- no path-dependent branch (findings 002/005): the comparison runs for any path
mkdir -p "$W/p/arena/suite" "$W/q/inputs/suitex"; cp "$D05/Main.export" "$W/p/arena/suite/s.export"; cp "$D05/Main.export" "$W/q/inputs/suitex/s.export"
row path-arena-suite 1 "$(cb "$W/p/arena/suite/s.export" "$D05/Challenge.export" "$W/leanonly.json")"
row path-suitex 1 "$(cb "$W/q/inputs/suitex/s.export" "$D05/Challenge.export" "$W/leanonly.json")"
# --- environment pollution (finding 016): verdict-relevant knobs of every tool must have no effect
row env-pollution-sorry 1 "$(env KC_AXIOMS=propext,Quot.sound,Classical.choice,sorryAx KC_THEOREMS=x GRUSZKA=/bin/true SUSZ=/bin/true \
  NL_STEPS=1 SK_ORDER=file GZ_SEQ_LOAD=1 K02_TIMES=1 GRUSZKA_STACK_MB=1 LEAN_ABORT_ON_PANIC=0 PATH=/nonexistent:$PATH \
  bash "$CB" "$D05/Challenge.export" "$D05/Challenge.export" "$W/leanonly.json" --threads $T > /dev/null 2>&1 < /dev/null; echo $?)"
row env-pollution-control 0 "$(env GRUSZKA_STACK_MB=1 NL_STEPS=1 bash "$CB" "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --threads $T > /dev/null 2>&1 < /dev/null; echo $?)"
# --- the caller's cwd must not matter (finding 049: nl-fast reads ./nano-lean.toml)
mkdir -p "$W/cwd"; printf 'steps = 1\narena_mib = 1\nthreads = 1\n' > "$W/cwd/nano-lean.toml"
row cwd-nano-lean-toml 0 "$(cd "$W/cwd" && bash "$CB" "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --threads $T > /dev/null 2>&1 < /dev/null; echo $?)"
# --- inputs must be regular files (finding 009 class)
rm -f "$W/fifo"; mkfifo "$W/fifo"; ( cat "$D26/Main.export" > "$W/fifo" & ) 2>/dev/null
row fifo-export 2 "$(timeout 60 bash "$CB" "$W/fifo" "$D26/Challenge.export" "$W/leanonly.json" --threads $T > /dev/null 2>&1 < /dev/null; echo $?)"
cat "$W/fifo" > /dev/null 2>&1 & sleep 0.2; kill %1 2>/dev/null
row devnull-export 2 "$(cb /dev/null "$D26/Challenge.export" "$W/leanonly.json")"
row dir-export 2 "$(cb "$W" "$D26/Challenge.export" "$W/leanonly.json")"
row missing-export 2 "$(cb "$W/nonexistent" "$D26/Challenge.export" "$W/leanonly.json")"
row empty-export n0 "$(: > "$W/empty.export"; cb "$W/empty.export" "$D26/Challenge.export" "$W/leanonly.json")"
# --- config handling (mirror of Lake.Check.Config; refuse what check B cannot reproduce)
# definition_names (v4, kcompare patch 02 = Lean 4.36 definition holes); expected values = the OFFICIAL comparator's verdicts
# on the same inputs (check/official/check.sh): 0 0 1 1 1
mkcfg defs 'c["definition_names"]=["Nat.add"]';            row cfg-definition-names 0 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/defs.json")"
mkcfg defsonly 'c["theorem_names"]=[]; c["definition_names"]=["Nat.add"]'; row cfg-definitions-only 0 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/defsonly.json")"
mkcfg defthm 'c["definition_names"]=["main_thm"]';          row cfg-definition-is-theorem 1 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/defthm.json")"
mkcfg defmiss 'c["definition_names"]=["no_such_def"]';      row cfg-definition-missing 1 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/defmiss.json")"
mkcfg defind 'c["definition_names"]=["Nat"]';               row cfg-definition-is-inductive 1 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/defind.json")"
mkcfg defcomma 'c["definition_names"]=["a,b"]';             row cfg-definition-name-with-comma 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/defcomma.json")"
mkcfg paranoid 'c["external_kernels"]={"Lean paranoid":["leanchecker-paranoid","--silent","--from-export"]}'
row cfg-unknown-kernel 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/paranoid.json")"
mkcfg both 'c["enable_nanoda"]=True'                       ; row cfg-enable-nanoda-and-kernels 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/both.json")"
mkcfg nanodaargs 'c["external_kernels"]={"nanoda":["nanoda_bin","--x"]}'; row cfg-nanoda-extra-args 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/nanodaargs.json")"
mkcfg enable 'c.pop("external_kernels"); c["enable_nanoda"]=True'; row cfg-enable-nanoda 0 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/enable.json")"
mkcfg nothms 'c.pop("theorem_names")'                       ; row cfg-no-theorem-names 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/nothms.json")"
mkcfg emptythms 'c["theorem_names"]=[]'                     ; row cfg-empty-theorem-names 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/emptythms.json")"
mkcfg comma 'c["theorem_names"]=["main_thm,foo"]'           ; row cfg-name-with-comma 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/comma.json")"
# names Lean's String.toName does not read as a plain dotted identifier ("main-thm" -> `.anonymous`: the official comparator
# rejects 'Const not found in challenge: [anonymous]' even when the exports contain «main-thm» - check B before the name check ACCEPTED
# such a pair) -> DECLINED; numeric component ("foo.1" = Name.num) -> DECLINED
mkcfg hyph 'c["theorem_names"]=["main-thm"]'                ; row cfg-name-not-identifier 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/hyph.json")"
mkcfg numc 'c["theorem_names"]=["main_thm.1"]'              ; row cfg-name-numeric-component 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/numc.json")"
mkcfg axhyph 'c["permitted_axioms"]=["propext","Quot.sound","Classical-choice"]'; row cfg-axiom-not-identifier 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/axhyph.json")"
mkcfg wrongthm 'c["theorem_names"]=["no_such_thm"]'         ; row cfg-missing-theorem n0 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/wrongthm.json")"
# a config that permits sorryAx: the official comparator accepts; check B's legs accept too but `sorry` carries a string
# literal (its unique tag) -> prechk order_strlit -> DECLINED. Requirement here: no false reject.
mkcfg sorryax 'c["permitted_axioms"]=c["permitted_axioms"]+["sorryAx"]'; row cfg-project-permits-sorry n1 "$(cb "$D05/Challenge.export" "$D05/Challenge.export" "$W/sorryax.json")"
printf '{not json' > "$W/bad.json"                          ; row cfg-not-json 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/bad.json")"
# JSON that Python accepts but Lean.Json.parse refuses (official comparator: 'malformed configuration', exit 2 = cannot run,
# checked): NaN, a duplicate key -> DECLINED; an unknown field is ignored by Lean's FromJson -> verdict 0
python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("external_kernels",None); s=json.dumps(c); open(sys.argv[2],"w").write(s[:-1]+",\"extra\":NaN}"); open(sys.argv[3],"w").write("{\"theorem_names\":[\"no_such_thm\"],"+s[1:]); open(sys.argv[4],"w").write(s[:-1]+",\"unknown_field\":1}")' "$D26/cfg.json" "$W/nan.json" "$W/dup.json" "$W/unk.json"
row cfg-nan 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/nan.json")"
row cfg-duplicate-key 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/dup.json")"
row cfg-unknown-field 0 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/unk.json")"
# --- arguments
row bad-threads 2 "$(bash "$CB" "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --threads abc > /dev/null 2>&1 < /dev/null; echo $?)"
row bad-mode 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --mode quad)"
row unknown-option 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --no-prechk)"
row too-few-args 2 "$(bash "$CB" "$D26/Main.export" > /dev/null 2>&1 < /dev/null; echo $?)"
row mode-single 0 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --mode single)"
row option-C4-single 0 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --single)"
row option-C4-single-sorry 1 "$(cb "$D05/Challenge.export" "$D05/Challenge.export" "$W/leanonly.json" --single)"
row unsafe-unknown 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --unsafe skip-everything)"
# --unsafe ignore-order: the permits-sorry case (string literal -> order_strlit) is then ACCEPTED and marked UNSAFE
row unsafe-ignore-order 0 "$(cb "$D05/Challenge.export" "$D05/Challenge.export" "$W/sorryax.json" --unsafe ignore-order)"
row unsafe-recorded 0 "$(python3 -I -c 'import json,sys; r=json.loads(open(sys.argv[1]).read().strip().splitlines()[-1]); sys.exit(0 if r.get("unsafe")==["ignore-order"] and r["trust"].startswith("UNSAFE") else 1)' "$W/last.json"; echo $?)"
# --- pinned binaries: a substituted binary (right name, wrong sha256) is refused, never run
B=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["bin_dir"])' "$H/../components.json")
mkdir -p "$W/fakebin"; cp "$B/gruszka" "$B/kcompare" "$W/fakebin/"; printf '#!/bin/sh\nexit 0\n' > "$W/fakebin/nl-fast"; chmod +x "$W/fakebin/nl-fast"
row tampered-binary 2 "$(cb "$D05/Challenge.export" "$D05/Challenge.export" "$W/leanonly.json" --bin "$W/fakebin")"
# --- resources: timeout -> decline; an address-space limit must never turn into a (false) reject
row timeout 2 "$(cb "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --timeout 0.01)"
row rlimit-as-8G-control n1 "$(bash -c "ulimit -v 8388608; bash '$CB' '$D26/Main.export' '$D26/Challenge.export' '$W/leanonly.json' --threads $T" > /dev/null 2>&1 < /dev/null; echo $?)"
row rlimit-as-8G-sorry n0 "$(bash -c "ulimit -v 8388608; bash '$CB' '$D05/Challenge.export' '$D05/Challenge.export' '$W/leanonly.json' --threads $T" > /dev/null 2>&1 < /dev/null; echo $?)"
# --- output contract: exactly one JSON object on stdout with checker/verdict/exit
cb "$D26/Main.export" "$D26/Challenge.export" "$W/leanonly.json" --json "$W/out.json" > /dev/null
row json-contract 0 "$(python3 -I -c 'import json,sys; a=open(sys.argv[1]).read().strip().splitlines(); b=json.load(open(sys.argv[2]))
r=json.loads(a[-1]); sys.exit(0 if len(a)==1 and r==b and r["checker"]=="checkB" and r["verdict"]=="ACCEPTED" and r["exit"]==0 and set(r["legs"])>={"kcompare","gruszka","nl-fast","prechk"} else 1)' "$W/last.json" "$W/out.json"; echo $?)"
echo "SUMMARY checkB wrapper test: $((n-fails))/$n PASS (work $W)"
[ $fails = 0 ]
}
main "$@"; exit $?
