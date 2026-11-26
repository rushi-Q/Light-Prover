#!/bin/bash
# tests/config-types/run.sh [FASTVERIFY_ROOT]  -- regression test of comparator.json field types:
# a comparator.json whose optional fields have the wrong JSON type ("enable_nanoda": "false", "external_kernels": []) is a
# CONFIGURATION ERROR for the official 4.36 `lake comparator` (exit 2, no verdict), so every judge must give DECLINED (exit 2),
# never ACCEPTED. The judges validate the ORIGINAL config with the notary's validator (the config block of check/notary/check-notary.sh,
# copied verbatim into the other five judges) before inspecting or rewriting it.
#   Part A  official-vs-validator table: data/mkvariants.py writes 90 config variants; data/official-4.36.tsv records the
#           official 4.36 comparator's exit status for each (rc 2 = configuration error). Each judge's config block must
#           refuse with the official configuration error exactly for the rc-2 variants and pass the others (blocks before the
#           common version refused a lone surrogate escape, which Lean reads as U+FFFD: accepted as such). If the 4.36 toolchain is
#           installed, the official comparator is re-run on every variant and must match the recorded table.
#   Part B  full judge runs on all six judges (check-sound.sh, -svc, check-sound-lowmem.sh, -ultralowmem.sh, check-frontier.sh,
#           check-notary.sh): nanoda-type and kernels-type -> DECLINED exit 2 with the official configuration error; the
#           unmodified config (good) -> ACCEPTED (control). Inputs: official 4.36 exports (sha256 in
#           data/SHA256SUMS).
#   Part C  (not in check-notary.sh): weight-1e309 an ignored annotation
#           "weight": 1e309 (official: accepted) -> ACCEPTED on the other five judges (was DECLINED: Python wrote Infinity
#           into the private config); empty-last-arg --keep-config-kernels with a kept kernel command whose LAST argument is empty
#           (official runs it and accepts) -> ACCEPTED (was DECLINED); cr-label a kept kernel named "release\rreplay" -> ACCEPTED
#           with its leg records (lean, k2, kept-0 with the exact name) in the result (were dropped: "legs": null).
#   Part D  --workdir through a symbolic link and a relative --workdir -> the
#           honest input is ACCEPTED on the five judges (the work dir is realpath'd right after mktemp; before, the
#           kernel wrappers compared the export path with the unresolved "$W/solution.export" and the run had no verdict).
# Prints PASS/FAIL rows + RESULT line.
set -u
FV=$(readlink -f "${1:-$(dirname "$(readlink -f "$0")")/../..}")
D=$(cd "$(dirname "$(readlink -f "$0")")/data" && pwd)
( cd "$D" && sha256sum -c --quiet SHA256SUMS ) || { echo "FAIL inputs: data/SHA256SUMS"; echo "RESULT pass=0 fail=1"; exit 1; }
WB=; for d in ${F2_TEST_WORKDIR:-} /scratch /var/tmp; do [ -d "$d" ] && [ -w "$d" ] && { WB=$d; break; }; done
[ -n "$WB" ] || { echo "FAIL setup: no writable /scratch or /var/tmp"; echo "RESULT pass=0 fail=1"; exit 1; }
W=$(mktemp -d "$WB/config-types.XXXXXX"); trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok() { echo "PASS $1"; pass=$((pass+1)); }
no() { echo "FAIL $1: $2"; fail=$((fail+1)); }
OFFMSG='official comparator configuration error|a string with a surrogate code point'
# in check-frontier.sh / check-notary.sh the cross-version gate (check/xversion/xvcheck.py) can
# refuse such a config first, with its own wording; either decline text counts in Part B (the verdict is what matters)
OFFMSG_B="$OFFMSG|comparator config refused, as by the official comparator's config decoding"
declare -A J=( [check-sound]=check/sound/check-sound.sh [check-sound-svc]=check/sound/check-sound-svc.sh
  [check-sound-lowmem]=check/lowmem/check-sound-lowmem.sh [check-sound-ultralowmem]=check/lowmem/check-sound-ultralowmem.sh
  [check-frontier]=check/frontier/check-frontier.sh [check-notary]=check/notary/check-notary.sh )
ORDER="check-sound check-sound-svc check-sound-lowmem check-sound-ultralowmem check-frontier check-notary"

# ---------- Part A ----------
/usr/bin/python3 -I "$D/mkvariants.py" "$W/cfg" > /dev/null || { no "A/variants" "mkvariants.py failed"; }
nv=$(ls "$W/cfg" | wc -l); nt=$(grep -vc '^#' "$D/official-4.36.tsv")
[ "$nv" = "$nt" ] && ok "A/variants ($nv variants = recorded official table)" || no "A/variants" "$nv variants, $nt table rows"
while read -r n rc sh; do
  case "$n" in '#'*) continue;; esac
  [ "$(sha256sum < "$W/cfg/$n.json" | cut -c1-16)" = "$sh" ] || no "A/variant-bytes/$n" "variant bytes differ from the recorded table"
done < "$D/official-4.36.tsv"
TC36=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
if [ -x "$TC36/bin/lake" ] && [ -x /usr/bin/bwrap ]; then
  mkdir -p "$W/off/run" "$W/off/home"; cp "$D/challenge.export" "$D/solution.export" "$W/off/"; bad=
  while read -r n rc sh; do
    case "$n" in '#'*) continue;; esac
    /usr/bin/bwrap --die-with-parent --unshare-all --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp --bind "$W" "$W" \
      --chdir "$W/off/run" --clearenv --setenv PATH "$TC36/bin:/usr/bin:/bin" --setenv LANG C.UTF-8 --setenv HOME "$W/off/home" \
      "$TC36/bin/lake" comparator --config "$W/cfg/$n.json" --challenge-from-export "$W/off/challenge.export" \
      --solution-from-export "$W/off/solution.export" > "$W/off/$n.log" 2>&1
    r=$?; [ "$r" = "$rc" ] || bad="$bad $n(rc=$r,recorded=$rc)"
  done < "$D/official-4.36.tsv"
  [ -z "$bad" ] && ok "A/official-4.36-rerun (all $nt variants match the recorded exit status)" || no "A/official-4.36-rerun" "$bad"
else
  echo "SKIP A/official-4.36-rerun: 4.36 toolchain lake or bwrap missing (recorded table used)"
fi
# block NAME VARIANT -> runs the judge's config Python block alone on the variant; prints OFFERR / pass / judge-refuse
block() {
  local j=$1 n=$2 v; v=$(mktemp -d "$W/blk.XXXXXX"); mkdir -p "$v/bin" "$v/tmp"; : > "$v/extra"
  case "$j" in
    check-frontier) cp "$W/cfg/$n.json" "$v/comparator.orig.json"; /usr/bin/python3 -I "$W/$j.block.py" "$v" > "$v/log" 2>&1;;
    check-notary) /usr/bin/python3 -I "$W/$j.block.py" "$W/cfg/$n.json" "$v/out.json" "$v" 0 1 0 0 0 4 "$TC36" > "$v/log" 2>&1;;   # newer notary blocks take TC36 too
    check-sound-lowmem|check-sound-ultralowmem) /usr/bin/python3 -I "$W/$j.block.py" "$W/cfg/$n.json" "$v/out.json" "$v/bin/gk" 0 "$v" > "$v/log" 2>&1;;
    *) /usr/bin/python3 -I "$W/$j.block.py" "$W/cfg/$n.json" "$v/out.json" "$v/bin/gk" 0 "$v" "$v/extra" > "$v/log" 2>&1;;
  esac
  local r=$?
  if [ $r = 0 ]; then echo pass; elif grep -qE "$OFFMSG" "$v/log"; then echo OFFERR; else echo "judge-refuse"; fi
}
for j in $ORDER; do
  s=$FV/${J[$j]}
  [ -f "$s" ] || { no "A/$j" "missing $s"; continue; }
  l=$(grep -n '^CFGMSG=$(/usr/bin/python3 -I - ' "$s" | head -n 1 | cut -d: -f1)
  [ -n "$l" ] || { no "A/$j" "no config block found"; continue; }
  l=$(awk -v s="$l" 'NR>=s && index($0, "<<'"'"'PY'"'"'") {print NR; exit}' "$s")   # the heredoc starts after its <<'PY' line
  awk -v s="$l" 'NR>s && /^PY$/ {exit} NR>s {print}' "$s" > "$W/$j.block.py"
  grep -q '^# before anything is checked or rewritten, the file is read EXACTLY' "$W/$j.block.py" || { no "A/$j" "config block does not carry the notary validator"; continue; }
  bad=
  while read -r n rc sh; do
    case "$n" in '#'*) continue;; esac
    got=$(block "$j" "$n")
    # the lone-surrogate row: blocks before the common version (no lean_str) refused it (documented stricter case);
    # the common block normalizes it to U+FFFD like Lean (official: accepted)
    if [ "$rc" = 2 ]; then want=OFFERR; elif [ "$n" = lone-surrogate ] && ! grep -q '^def lean_str' "$W/$j.block.py"; then want=OFFERR; else want=notOFFERR; fi
    case "$want:$got" in OFFERR:OFFERR|notOFFERR:pass|notOFFERR:judge-refuse) ;; *) bad="$bad $n(official rc=$rc, judge $got)";; esac
  done < "$D/official-4.36.tsv"
  [ -z "$bad" ] && ok "A/$j (config block = official on all $nt variants; older blocks: lone surrogate refused, documented)" || no "A/$j" "$bad"
done

# ---------- Part B ----------
# the verdict JSON comes from the --json file (newer judges log a verdict line to stderr AFTER the stdout JSON)
lastjs() { { [ -s "$1.json" ] && cat "$1.json" || tail -n 1 "$1"; } | /usr/bin/python3 -I -c 'import json,sys
try: d=json.loads(sys.stdin.read())
except Exception: print("BADJSON -"); sys.exit()
print(d.get("exit"), d.get("verdict"))'; }
for j in $ORDER; do
  s=$FV/${J[$j]}
  ex=(); [ "$j" = check-sound-svc ] && { mkdir -p -m 700 "$W/cache"; ex=(--integrity-cache "$W/cache"); }
  for c in nanoda-type kernels-type good; do
    o=$W/$j.$c.out; mkdir -p "$W/wd"
    "$s" "$D/solution.export" "$D/challenge.export" "$D/$c.json" --threads 4 --json "$o.json" --workdir "$W/wd" "${ex[@]}" > "$o" 2>&1; rc=$?
    read -r jrc jv < <(lastjs "$o")
    if [ "$c" = good ]; then
      [ "$rc" = 0 ] && [ "$jrc" = 0 ] && [ "$jv" = ACCEPTED ] && ok "B/$j/good ACCEPTED (control)" \
        || no "B/$j/good" "rc=$rc json=($jrc $jv): $(tail -n 1 "$o" | cut -c1-200)"
    else
      [ "$rc" = 2 ] && [ "$jrc" = 2 ] && [ "$jv" = DECLINED ] && { [ -s "$o.json" ] && cat "$o.json" || tail -n 1 "$o"; } | grep -qE "$OFFMSG_B" && ok "B/$j/$c DECLINED (exit 2, official configuration error)" \
        || no "B/$j/$c" "rc=$rc json=($jrc $jv): $(tail -n 1 "$o" | cut -c1-200)"
    fi
  done
done
# ---------- Part C ----------
LC=$TC36/bin/leanchecker
/usr/bin/python3 -I - "$D/good.json" "$W" "$LC" <<'PYC'
import json, sys
g = json.load(open(sys.argv[1])); W, lc = sys.argv[2], sys.argv[3]
def w(n, extra_raw=None, **kw):
    x = dict(g); x.update(kw); t = json.dumps(x)
    if extra_raw: t = t[:-1] + extra_raw + "}"
    open("%s/%s.json" % (W, n), "w").write(t)
w("weight-1e309", extra_raw=', "weight": 1e309')
w("empty-last-arg", external_kernels={"replay": ["/bin/sh", "-c", 'exec %s --from-export "$1"' % lc, ""]})
w("cr-label", external_kernels={"release\rreplay": [lc, "--from-export"]})
PYC
lastleg() { { [ -s "$1.json" ] && cat "$1.json" || tail -n 1 "$1"; } | /usr/bin/python3 -I -c 'import json,sys
try: d=json.loads(sys.stdin.read())
except Exception: print("BADJSON - -"); sys.exit()
L=d.get("legs") or {}
k=[v.get("name") for n, v in L.items() if n.startswith("kept-")]
print(d.get("exit"), d.get("verdict"), json.dumps(sorted(L)) .replace(" ", ""), json.dumps(k).replace(" ", ""))'; }
for j in check-sound check-sound-svc check-sound-lowmem check-sound-ultralowmem check-frontier; do
  s=$FV/${J[$j]}
  ex=(); [ "$j" = check-sound-svc ] && ex=(--integrity-cache "$W/cache")
  o=$W/$j.weight-1e309.out
  "$s" "$D/solution.export" "$D/challenge.export" "$W/weight-1e309.json" --threads 4 --json "$o.json" --workdir "$W/wd" "${ex[@]}" > "$o" 2>&1; rc=$?
  read -r jrc jv _ _ < <(lastleg "$o")
  [ "$rc" = 0 ] && [ "$jv" = ACCEPTED ] && ok "C/$j/weight-1e309 ignored annotation 1e309 ACCEPTED (official: accepted)" || no "C/$j/weight-1e309" "rc=$rc json=($jrc $jv): $(tail -n 1 "$o" | cut -c1-200)"
  [ "$j" = check-frontier ] && continue
  o=$W/$j.empty-last-arg.out
  "$s" "$D/solution.export" "$D/challenge.export" "$W/empty-last-arg.json" --threads 4 --json "$o.json" --workdir "$W/wd" --keep-config-kernels "${ex[@]}" > "$o" 2>&1; rc=$?
  read -r jrc jv legs kn < <(lastleg "$o")
  [ "$rc" = 0 ] && [ "$jv" = ACCEPTED ] && [ "$kn" = '["replay"]' ] && ok "C/$j/empty-last-arg kept kernel with an empty last argument ACCEPTED" || no "C/$j/empty-last-arg" "rc=$rc json=($jrc $jv $kn): $(tail -n 1 "$o" | cut -c1-200)"
  o=$W/$j.cr-label.out
  "$s" "$D/solution.export" "$D/challenge.export" "$W/cr-label.json" --threads 4 --json "$o.json" --workdir "$W/wd" --keep-config-kernels "${ex[@]}" > "$o" 2>&1; rc=$?
  read -r jrc jv legs kn < <(lastleg "$o")
  [ "$rc" = 0 ] && [ "$jv" = ACCEPTED ] && [ "$legs" = '["k2","kept-0","lean"]' ] && [ "$kn" = '["release\rreplay"]' ] && ok "C/$j/cr-label CR in a kept kernel's name: ACCEPTED with lean/k2/kept-0 records" || no "C/$j/cr-label" "rc=$rc json=($jrc $jv $legs $kn): $(tail -n 1 "$o" | cut -c1-200)"
done
# ---------- Part D (symlinked / relative --workdir) ----------
mkdir -p "$W/wdreal" "$W/rel/wd"; ln -s "$W/wdreal" "$W/wdlink"
for j in check-sound check-sound-svc check-sound-lowmem check-sound-ultralowmem check-frontier; do
  s=$FV/${J[$j]}
  ex=(); [ "$j" = check-sound-svc ] && ex=(--integrity-cache "$W/cache")
  o=$W/$j.symwd.out
  "$s" "$D/solution.export" "$D/challenge.export" "$D/good.json" --threads 4 --json "$o.json" --workdir "$W/wdlink" "${ex[@]}" > "$o" 2>&1; rc=$?
  read -r jrc jv < <(lastjs "$o")
  [ "$rc" = 0 ] && [ "$jv" = ACCEPTED ] && ok "D/$j/workdir-through-symlink ACCEPTED" || no "D/$j/workdir-through-symlink" "rc=$rc json=($jrc $jv): $(tail -n 1 "$o" | cut -c1-200)"
  o=$W/$j.relwd.out
  ( cd "$W/rel" && "$s" "$D/solution.export" "$D/challenge.export" "$D/good.json" --threads 4 --json "$o.json" --workdir wd "${ex[@]}" ) > "$o" 2>&1; rc=$?
  read -r jrc jv < <(lastjs "$o")
  [ "$rc" = 0 ] && [ "$jv" = ACCEPTED ] && ok "D/$j/relative-workdir ACCEPTED" || no "D/$j/relative-workdir" "rc=$rc json=($jrc $jv): $(tail -n 1 "$o" | cut -c1-200)"
done
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]; exit $?
