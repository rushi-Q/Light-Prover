#!/bin/bash
# tests/subcontract-paths/run.sh [PKGROOT] - regression test: subcontract merge never writes outside the tree (HIGH):
# tools/subcontract/merge.py took the source path of a splice from the (caller-supplied) subproof JSON instead of the
# minting manifest, without confinement, and wrote it before compiling / checking / honouring --dry-run:
#   part1  rel_file = an absolute path outside the tree, --dry-run   -> the outside file was overwritten
#   part2  rel_file = ../../../manifest.json, --dry-run               -> OUT/manifest.json replaced (pins of a fake challenge),
#          then a merge proving only fake_ok returned a final ACCEPTED for a project whose target_thm : False is unproved
#   symlink  a source file in the base tree that is a symlink to an outside file -> written through
#   compile  subverify.compile_single_module_sandboxed made / removed host files outside the tree (absolute rel_file,
#          symlinked .lake/build/lib/lean)
#   pins   merge.py / subverify.py / mint.py did not forward --challenge-sha256 / --comparator-sha256 to the judges
# Fixed: every such merge is refused (exit 2) BEFORE anything is written, nothing outside the tree changes, the honest merge
# still works (CONDITIONAL, then the remaining lemma stays open). Built with the official Lean 4.36 toolchain (bwrap, no net).
# Rows 'PASS|FAIL name: ...'; last line 'RESULT pass=N fail=M'; exit 0 iff all PASS. (On the pre-fix tree the bug rows FAIL.)
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(cd "${1:-$HERE/../..}" && pwd)
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.36.0"]["prefix"])' "$FV/config/components.json")
W=$(mktemp -d "${SCRATCH:-${TMPDIR:-/tmp}}/subcontract-paths-test-XXXXXX"); trap 'chmod -R u+w "$W" 2>/dev/null; [ "${KEEP_WORK:-0}" = 1 ] || rm -rf "$W"' EXIT
# (no "." in W: the absolute-path compile row must name the real victim file; SCRATCH should not contain "." either)
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
cd "$W"
mkdir -p ParentChal ParentProj FakeChal
for d in ParentChal ParentProj FakeChal; do echo "leanprover/lean4:v4.36.0" > "$d/lean-toolchain"; done
printf 'name = "ParentChal"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\n' > ParentChal/lakefile.toml
printf 'theorem target_thm : False := sorry\n' > ParentChal/Main.lean
CFGJ='{"challenge_module": "Main", "solution_module": "Main", "theorem_names": ["%s"], "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": false}\n'
printf "$CFGJ" target_thm > ParentChal/comparator.json
printf 'name = "ParentProj"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Helper"\n[[lean_lib]]\nname = "Main"\n' > ParentProj/lakefile.toml
printf 'theorem helper_lem : False := by sorry\ntheorem easy_lem : 1 + 1 = 2 := by sorry\n' > ParentProj/Helper.lean
printf 'import Helper\ntheorem target_thm : False := (fun _ => helper_lem) easy_lem\n' > ParentProj/Main.lean
cp ParentChal/comparator.json ParentProj/
printf 'name = "FakeChal"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\n' > FakeChal/lakefile.toml
printf 'theorem fake_ok : True := trivial\n' > FakeChal/Main.lean
printf "$CFGJ" fake_ok > FakeChal/comparator.json
PRIMS="propext Quot.sound Classical.choice Quot Quot.mk Quot.lift Quot.ind Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
for d in ParentChal FakeChal; do
  t=$( [ "$d" = ParentChal ] && echo target_thm || echo fake_ok )
  "$FV/build/official-build.sh" "$W/$d" "$W/$d" "$TC" --threads 4 > "$W/build_$d.log" 2>&1 || { ko setup "official build of $d failed"; echo "RESULT pass=$pass fail=$fail"; exit 1; }
  /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dev /dev --proc /proc --ro-bind "$TC" "$TC" --ro-bind "$W/$d" "$W/$d" --clearenv --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_PATH "$W/$d/.lake/build/lib/lean:$TC/lib/lean" --setenv LANG C.UTF-8 --setenv LEAN_ABORT_ON_PANIC 1 --chdir "$W/$d" -- \
    "$TC/bin/leanexport" Main -- "$t" $PRIMS > "$W/$d/challenge.export" || { ko setup "export of $d failed"; echo "RESULT pass=$pass fail=$fail"; exit 1; }
done
PIN=$(sha256sum "$W/ParentChal/challenge.export" | cut -d' ' -f1)
CPIN=$(sha256sum "$W/ParentChal/comparator.json" | cut -d' ' -f1)   # comparator pin required with the challenge pin
# mint without / with a wrong comparator pin: refused before anything runs
python3 -I "$FV/tools/subcontract/mint.py" --experimental "$W/ParentProj" "$W/ParentChal" "$W/OUT0" --challenge-sha256 "$PIN" --packages "$W/ParentChal" --fv "$FV" --threads 4 > "$W/mint0.out" 2>&1; rc=$?
[ $rc = 2 ] && grep -q 'comparator-sha256' "$W/mint0.out" && [ ! -e "$W/OUT0/base" ] && ok pin/mint-missing-comparator-pin "exit 2, nothing built" || ko pin/mint-missing-comparator-pin "exit $rc $(tail -c 200 "$W/mint0.out")"
# a cached check-frontier receipt is never reused (not bound to this run's inputs): refused
echo '{"verdict": "ACCEPTED", "frontier": []}' > "$W/receipt.json"
python3 -I "$FV/tools/subcontract/mint.py" --experimental "$W/ParentProj" "$W/ParentChal" "$W/OUT2" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --frontier-json "$W/receipt.json" --packages "$W/ParentChal" --fv "$FV" --threads 4 > "$W/mint2.out" 2>&1; rc=$?
[ $rc = 2 ] && grep -q 'frontier-json is not accepted' "$W/mint2.out" && [ ! -e "$W/OUT2/manifest.json" ] && [ ! -e "$W/OUT2/base" ] && ok pin/mint-cached-receipt-refused "exit 2, nothing built, no manifest" || ko pin/mint-cached-receipt-refused "exit $rc $(tail -c 200 "$W/mint2.out")"
python3 -I "$FV/tools/subcontract/mint.py" --experimental "$W/ParentProj" "$W/ParentChal" "$W/OUT1" --challenge-sha256 "$PIN" --comparator-sha256 0000000000000000000000000000000000000000000000000000000000000000 --packages "$W/ParentChal" --fv "$FV" --threads 4 > "$W/mint1.out" 2>&1; rc=$?
[ $rc = 2 ] && grep -q 'comparator.json sha256 mismatch' "$W/mint1.out" && ok pin/mint-wrong-comparator-pin "exit 2" || ko pin/mint-wrong-comparator-pin "exit $rc $(tail -c 200 "$W/mint1.out")"
python3 -I "$FV/tools/subcontract/mint.py" --experimental "$W/ParentProj" "$W/ParentChal" "$W/OUT" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --packages "$W/ParentChal" --fv "$FV" --threads 4 --exporter E0 > "$W/mint.out" 2> "$W/mint.err"
mrc=$?
[ $mrc = 0 ] && grep -q '"verdict": "CONDITIONAL"' "$W/mint.out" && ok mint "exit 0, CONDITIONAL parent" || { ko mint "exit $mrc $(tail -c 300 "$W/mint.out") $(tail -c 300 "$W/mint.err")"; echo "RESULT pass=$pass fail=$fail"; exit 1; }
# the subcontract engine is EXPERIMENTAL: without --experimental every CLI is refused (exit 2)
for t in mint.py merge.py subverify.py; do
  python3 -I "$FV/tools/subcontract/$t" "$W/OUT/manifest.json" x y > "$W/gate-$t.out" 2>&1; rc=$?
  [ $rc = 2 ] && grep -q 'EXPERIMENTAL in v0.1' "$W/gate-$t.out" && ok "gate/$t-needs-experimental" "exit 2" || ko "gate/$t-needs-experimental" "exit $rc $(tail -c 200 "$W/gate-$t.out")"
done
# a mint retry in the SAME OUT never reads the earlier run's parent receipt: (B) the target is
# now `sorry` and the old OUT/base/frontier.json is read-only -> REJECTED exit 1 (earlier: exit 0 with the old CONDITIONAL);
# (C) this run's check writes no JSON (a stand-in check-frontier.sh, e.g. killed) -> exit 2; (D) its exit does not match its
# verdict -> exit 2 (each in a copy of the honest OUT)
cp -a "$W/ParentProj" "$W/ParentProjSorry"; printf 'import Helper\ntheorem target_thm : False := sorry\n' > "$W/ParentProjSorry/Main.lean"
cp -a "$W/OUT" "$W/OUTB"; chmod 0444 "$W/OUTB/base/frontier.json"
python3 -I "$FV/tools/subcontract/mint.py" --experimental "$W/ParentProjSorry" "$W/ParentChal" "$W/OUTB" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --packages "$W/ParentChal" --fv "$FV" --threads 4 --exporter E0 > "$W/mintB.out" 2>&1; rc=$?
mv=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$W/OUTB/manifest.json" 2>/dev/null)
[ $rc = 1 ] && [ "$mv" = REJECTED ] && ok mint/retry-same-out-old-receipt-not-read "exit 1 REJECTED (this run's check)" || ko mint/retry-same-out-old-receipt-not-read "exit $rc manifest verdict $mv $(tail -c 200 "$W/mintB.out")"
FK=$W/fakefv; mkdir -p "$FK/check/frontier"
for x in "$FV"/*; do [ "$(basename "$x")" = check ] || ln -s "$x" "$FK/"; done
for x in "$FV"/check/*; do [ "$(basename "$x")" = frontier ] || ln -s "$x" "$FK/check/"; done
for x in "$FV"/check/frontier/*; do [ "$(basename "$x")" = check-frontier.sh ] || ln -s "$x" "$FK/check/frontier/"; done
cat > "$FK/check/frontier/check-frontier.sh" <<'EOS'
#!/bin/bash
# stand-in parent check for this test: FAKE_MODE=nojson -> writes nothing, exit 3; FAKE_MODE=mismatch -> CONDITIONAL JSON, exit 2
J=; while [ $# -gt 0 ]; do [ "$1" = --json ] && J=$2; shift; done
[ "${FAKE_MODE:-}" = mismatch ] && printf '{"verdict": "CONDITIONAL", "frontier": [], "frontier_size": 0}\n' > "$J" && exit 2
exit 3
EOS
chmod +x "$FK/check/frontier/check-frontier.sh"
# SIGTERM while mint's parent check runs: NO_VERDICT exit 2 (not 143), no check-frontier.sh left
cp -a "$W/OUT" "$W/OUT-sig"
python3 -I "$FV/tools/subcontract/mint.py" --experimental "$W/ParentProj" "$W/ParentChal" "$W/OUT-sig" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --packages "$W/ParentChal" --fv "$FV" --threads 4 --exporter E0 > "$W/mint-sig.out" 2>&1 &
MSP=$!
for _ in $(seq 1 3000); do pgrep -f "check-frontier.sh.*$W/OUT-sig/base" > /dev/null && break; kill -0 $MSP 2>/dev/null || break; sleep 0.1; done
kill -TERM $MSP 2>/dev/null; wait $MSP; rc=$?; sleep 1
left=$(pgrep -f "$W/OUT-sig" | wc -l)
[ $rc = 2 ] && grep -q 'interrupted (signal 15)' "$W/mint-sig.out" && [ "$left" = 0 ] && ok mint/sigterm-is-no-verdict "exit 2, nothing left" || ko mint/sigterm-is-no-verdict "exit $rc left $left $(tail -c 200 "$W/mint-sig.out")"
for m in nojson mismatch; do
  cp -a "$W/OUT" "$W/OUT-$m"
  FAKE_MODE=$m python3 -I "$FV/tools/subcontract/mint.py" --experimental "$W/ParentProj" "$W/ParentChal" "$W/OUT-$m" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --packages "$W/ParentChal" --fv "$FK" --threads 4 --exporter E0 > "$W/mint-$m.out" 2>&1; rc=$?
  [ $rc = 2 ] && [ ! -e "$W/OUT-$m/manifest.json" ] && ok "mint/retry-same-out-check-$m" "exit 2, no manifest (old receipt not used)" || ko "mint/retry-same-out-check-$m" "exit $rc $(tail -c 200 "$W/mint-$m.out")"
done
python3 -I - "$W" "$FV" > "$W/rows.txt" 2>"$W/rows.err" <<'PY'
import hashlib, json, os, shutil, subprocess, sys
W, fv = sys.argv[1], sys.argv[2]
mp = os.path.join(W, "OUT", "manifest.json")
m = json.load(open(mp))
sc = {x["lemma"]: x for x in m["subchallenges"]}
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
res = []
def row(name, good, msg):
    print(("PASS " if good else "FAIL ") + name + ": " + msg)
def merge(sp, *extra):
    p = os.path.join(W, "sp-%d.json" % (len(res)))
    json.dump(sp, open(p, "w"))
    r = subprocess.run(["python3", "-I", os.path.join(fv, "tools/subcontract/merge.py"), "--experimental", mp, p, "--fv", fv, "--threads", "4",
                        "--exporter", "E0"] + list(extra), capture_output=True, text=True)
    res.append(r)
    return r.returncode, (r.stdout.strip().splitlines() or [""])[-1][:300]
def sp_for(ln, rel, text, module):
    s = sc[ln]
    return {"schema": "fv-verified-subproof-v1", "lemma": ln, "id": s["id"], "sketch_subgoal": False, "agent": "attack",
            "rel_file": rel, "module": module, "subchallenge_sha256": s["subchallenge_sha256"], "mode_used": "full-file",
            "full_module_text": text, "proof_sha256": "0" * 64}
man0 = sha(mp)
# part1: absolute outside path, --dry-run
marker = os.path.join(W, "outside_marker.txt"); open(marker, "w").write("UNMODIFIED_OUTSIDE_FILE\n")
rc, out = merge(sp_for("helper_lem", marker, "OVERWRITTEN_BY_MERGE_DRY_RUN\n", "Helper"), "--dry-run")
row("part1/absolute-path-dry-run", open(marker).read() == "UNMODIFIED_OUTSIDE_FILE\n" and rc == 2,
    "rc=%d marker=%r %s" % (rc, open(marker).read(), out))
# part2: ../../../manifest.json, --dry-run, then a merge of a fake proof
pm = dict(m)
pm["challenge"] = os.path.join(W, "FakeChal"); pm["challenge_export"] = os.path.join(W, "FakeChal", "challenge.export")
pm["challenge_sha256"] = sha(pm["challenge_export"]); pm["comparator_config"] = os.path.join(W, "FakeChal", "comparator.json")
pm["comparator_sha256"] = sha(pm["comparator_config"]); pm["parent_theorems"] = ["fake_ok"]
rc, out = merge(sp_for("helper_lem", "../../../manifest.json", json.dumps(pm, indent=2) + "\n", "Helper"), "--dry-run")
row("part2/relative-traversal-dry-run", sha(mp) == man0 and rc == 2, "rc=%d manifest %s %s" % (rc, "unchanged" if sha(mp) == man0 else "REPLACED", out))
rc, out = merge(sp_for("helper_lem", "Main.lean", "theorem fake_ok : True := trivial\n", "Main"))
row("part2/no-day100-for-fake", rc != 0 and '"day100_complete": true' not in out, "rc=%d %s" % (rc, out))
row("part2/foreign-rel-file-refused", rc == 2 and "names source file" in out, "rc=%d %s" % (rc, out))
# symlink: the base tree's Helper.lean is a symlink to an outside file (as a sandboxed build could leave it)
bt = m["base_build_tree"]; h = os.path.join(bt, "Helper.lean"); keep = open(h).read()
victim = os.path.join(W, "victim.lean"); open(victim, "w").write(keep)
os.rename(h, h + ".orig"); os.symlink(victim, h)
rc, out = merge(sp_for("easy_lem", "Helper.lean", keep.replace("1 + 1 = 2 := by sorry", "1 + 1 = 2 := rfl"), "Helper"), "--dry-run")
row("symlink/source-not-followed", open(victim).read() == keep and rc != 0, "rc=%d victim %s %s" % (rc, "unchanged" if open(victim).read() == keep else "WRITTEN", out))
os.unlink(h); os.rename(h + ".orig", h)
# compile helper: host-side outputs confined (absolute rel_file; symlinked .lake/build/lib/lean)
sys.path.insert(0, os.path.join(fv, "tools", "subcontract"))
import subverify as SV
t = os.path.join(W, "ctree"); os.makedirs(os.path.join(t, ".lake", "build", "lib", "lean")); open(os.path.join(t, "A.lean"), "w").write("theorem a : True := trivial\n")
vd = os.path.join(W, "vdir"); os.makedirs(vd); open(os.path.join(vd, "marker.olean"), "w").write("keep")
open(os.path.join(vd, "marker.lean"), "w").write("theorem m : True := trivial\n")
absrel = os.path.join(vd, "marker.lean")
try:
    r = SV.compile_single_module_sandboxed(t, absrel, absrel[:-5].replace(os.sep, "."), m["packages_workspace"], m["toolchain_prefix"], timeout_s=60)
except Exception as e:
    r = ("exception", str(e))
row("compile/absolute-rel-file", os.path.exists(os.path.join(vd, "marker.olean")) and not r[0], "result %s, outside olean %s" % (str(r)[:120], "kept" if os.path.exists(os.path.join(vd, "marker.olean")) else "REMOVED"))
shutil.rmtree(os.path.join(t, ".lake", "build", "lib", "lean")); os.symlink(vd, os.path.join(t, ".lake", "build", "lib", "lean"))
open(os.path.join(vd, "A.olean"), "w").write("keep")
try:
    r = SV.compile_single_module_sandboxed(t, "A.lean", "A", m["packages_workspace"], m["toolchain_prefix"], timeout_s=60)
except Exception as e:
    r = ("exception", str(e))
kept = os.path.isfile(os.path.join(vd, "A.olean")) and open(os.path.join(vd, "A.olean")).read() == "keep"
row("compile/symlinked-lib-dir", kept and not r[0], "result %s, outside olean %s" % (str(r)[:160], "kept" if kept else "REMOVED/CHANGED"))
# honest path: subverify easy_lem (rfl), merge -> CONDITIONAL with helper_lem remaining; manifest pins forwarded (static)
sub = os.path.join(W, "easy.lean"); open(sub, "w").write("theorem easy_lem : 1 + 1 = 2 := rfl\n")
r = subprocess.run(["python3", "-I", os.path.join(fv, "tools/subcontract/subverify.py"), "--experimental", mp, "easy_lem", sub, "--fv", fv,
                    "--exporter", "E0", "--threads", "4"], capture_output=True, text=True)
vj = os.path.join(W, "OUT", "verified_subproofs", sc["easy_lem"]["id"] + ".verified.json")
row("honest/subverify", r.returncode == 0 and os.path.isfile(vj), "rc=%d %s" % (r.returncode, (r.stdout.strip().splitlines() or [""])[-1][:200]))
if os.path.isfile(vj):
    p = subprocess.run(["python3", "-I", os.path.join(fv, "tools/subcontract/merge.py"), "--experimental", mp, vj, "--fv", fv, "--threads", "4", "--exporter", "E0"],
                       capture_output=True, text=True)
    j = json.loads((p.stdout.strip().splitlines() or ["{}"])[-1] or "{}")
    row("honest/merge", p.returncode == 3 and j.get("parent_verdict") == "CONDITIONAL" and j.get("remaining_lemmas") == ["helper_lem"],
        "rc=%d %s" % (p.returncode, p.stdout.strip()[-250:]))
src = {n: open(os.path.join(fv, "tools/subcontract", n)).read() for n in ("merge.py", "subverify.py", "mint.py")}
row("pins/merge-forwards", '"--challenge-sha256", chal_sha' in src["merge.py"] and '"--comparator-sha256", comp_cfg_pin' in src["merge.py"], "check-frontier.sh gets the manifest pins")
row("pins/subverify-forwards", '"--challenge-sha256", sub_exp_pin' in src["subverify.py"] and '"--comparator-sha256", sub_comp_pin' in src["subverify.py"], "check-sound gets the subchallenge pins")
# merge with a manifest that lacks the comparator pin flag (an older mint) and no --comparator-sha256: refused
mo = dict(m); mo.pop("comparator_sha256_pinned_by_caller", None)
mop = os.path.join(W, "OUT", "manifest-old.json"); json.dump(mo, open(mop, "w"))
rr = subprocess.run(["python3", "-I", os.path.join(fv, "tools/subcontract/merge.py"), "--experimental", mop, vj if os.path.isfile(vj) else mp, "--fv", fv,
                     "--threads", "4", "--exporter", "E0", "--dry-run"], capture_output=True, text=True)
row("pins/merge-old-manifest-needs-comparator-pin", rr.returncode == 2 and "comparator" in rr.stdout, "rc=%d %s" % (rr.returncode, rr.stdout.strip()[-160:]))
rr = subprocess.run(["python3", "-I", os.path.join(fv, "tools/subcontract/merge.py"), "--experimental", mp, vj if os.path.isfile(vj) else mp, "--fv", fv,
                     "--threads", "4", "--exporter", "E0", "--dry-run", "--comparator-sha256", "0" * 64], capture_output=True, text=True)
row("pins/merge-wrong-comparator-pin", rr.returncode == 2 and "comparator" in rr.stdout, "rc=%d %s" % (rr.returncode, rr.stdout.strip()[-160:]))
row("pins/mint-records-comparator-pin", m.get("comparator_sha256_pinned_by_caller") is True and len(str(m.get("comparator_sha256") or "")) == 64, "manifest flag + pin")
row("pins/mint-forwards", '"--challenge-sha256", chal_sha, "--comparator-sha256", comp_cfg_sha' in src["mint.py"], "check-frontier.sh gets the parent pins")
# a declined parent check (unavailable integrity cache) is merge exit 2, not 1
if os.path.isfile(vj):
    rr = subprocess.run(["python3", "-I", os.path.join(fv, "tools/subcontract/merge.py"), "--experimental", mp, vj, "--fv", fv, "--threads", "4",
                         "--exporter", "E0", "--dry-run", "--integrity-cache", os.path.join(W, "no-such-dir", "icache")],
                        capture_output=True, text=True)
    jj = json.loads((rr.stdout.strip().splitlines() or ["{}"])[-1] or "{}")
    row("exit/merge-declined-check-is-2", rr.returncode == 2 and jj.get("verdict") not in ("REJECTED", "ACCEPTED", "CONDITIONAL"),
        "rc=%d verdict %s" % (rr.returncode, jj.get("verdict")))
# a task without its comparator fields is NO_VERDICT exit 2 (was KeyError, exit 1)
t0 = json.load(open(sc["easy_lem"]["task_json"]))
t0.pop("comparator_json", None); t0.pop("comparator_sha256", None)
tp = os.path.join(W, "OUT", "task-nocomp.json"); json.dump(t0, open(tp, "w"))
m2 = json.loads(json.dumps(m))
for x in m2["subchallenges"]:
    if x["lemma"] == "easy_lem":
        x["task_json"] = tp
m2p = os.path.join(W, "OUT", "manifest-nocomp.json"); json.dump(m2, open(m2p, "w"))
rr = subprocess.run(["python3", "-I", os.path.join(fv, "tools/subcontract/subverify.py"), "--experimental", m2p, "easy_lem", sub, "--fv", fv,
                     "--exporter", "E0", "--threads", "4"], capture_output=True, text=True)
jj = json.loads((rr.stdout.strip().splitlines() or ["{}"])[-1] or "{}")
row("exit/subverify-task-without-comparator-fields", rr.returncode == 2 and jj.get("verdict") == "NO_VERDICT" and "Traceback" not in rr.stderr,
    "rc=%d %s %s" % (rr.returncode, jj.get("category"), str(jj.get("reason"))[:100]))
PY
cat "$W/rows.txt"; [ -s "$W/rows.err" ] && tail -5 "$W/rows.err"
pass=$((pass + $(grep -c '^PASS ' "$W/rows.txt"))); fail=$((fail + $(grep -c '^FAIL ' "$W/rows.txt")))
[ "$(grep -c '^\(PASS\|FAIL\) ' "$W/rows.txt")" -ge 17 ] || { echo "FAIL rows: the row script stopped early"; fail=$((fail+1)); }
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
