#!/usr/bin/env python3
"""apply.py PROJ MODREL SRC_ROOT RESULTS.jsonl OUT_DIR [--prefer t1;t2;...] [--exclude t,...] [--rounds N] [--no-verify]
                [--leaf-only | --leaf-or-hinted] [--edits EDITS.tsv] [--lean-opts "-Dk=v ..."]

Apply the successful TryAt replacements of one module and verify the result by elaborating the edited module with the
official lean inside bwrap (blean.sh) against build tree PROJ. Replacements whose edit produces an error are reverted
(the latest replacement at or before the error line), up to N rounds; the original module is elaborated too (time
baseline; it must have no error). Writes OUT_DIR/<MODREL> (the edited module, only if every remaining replacement
verifies) and prints one JSON summary line. Untrusted: the verdict on the edited tree is the trusted check's.
"""
import json, os, re, subprocess, sys, time

# structural steps a human reader uses to follow a proof; --leaf-only never replaces a block that contains one
STRUCT = re.compile(r"(^|\s)(have|obtain|suffices|calc|show|rcases|by_cases|induction|cases|match|refine)\b")

T = os.path.dirname(os.path.realpath(__file__))


def elab(proj, wd, rel_in_wd, modname):
    extra = []
    if modname.startswith("GroundTheory.LocalFields") or modname.startswith("GroundTheory.GlobalFields"):
        extra = ["-DsynthInstance.maxHeartbeats=400000"]
    t0 = time.time()
    r0 = os.times()
    p = subprocess.run([f"{T}/blean.sh", proj, wd, rel_in_wd, "--json"] + extra, capture_output=True, text=True)
    r1 = os.times()
    wall = time.time() - t0
    cpu = (r1.children_user - r0.children_user) + (r1.children_system - r0.children_system)
    msgs = []
    for ln in p.stdout.splitlines():
        try:
            msgs.append(json.loads(ln))
        except Exception:
            pass
    errs = [m for m in msgs if m.get("severity") == "error"]
    if p.returncode != 0 and not errs:
        errs = [{"severity": "error", "pos": {"line": 0}, "data": "lean rc=%d: %s" % (p.returncode, p.stderr[-300:])}]
    sorry = [m for m in msgs if "declaration uses 'sorry'" in m.get("data", "")]
    return dict(rc=p.returncode, wall=round(wall, 2), cpu=round(cpu, 2), errs=errs + sorry, nmsg=len(msgs),
                stderr=p.stderr[-500:])


def main():
    a = sys.argv[1:]
    proj, modrel, src, resf, outd = a[:5]
    opt = lambda k, d=None: a[a.index(k) + 1] if k in a else d
    pl = opt("--prefer") or "rfl;simp;simp [$H];omega;linarith;positivity;ring;norm_num;simp_all;simp_all [$H];linarith [$P];tauto;grind;grind [$G];aesop"
    prefer = pl.split(";") if ";" in pl else pl.split(",")
    exclude = set((opt("--exclude") or "").split(",")) - {""}
    rounds = int(opt("--rounds", "4"))
    if opt("--lean-opts"):   # project options for the re-elaboration (lean -D flags); default: RH's (blean.sh)
        os.environ["BLEAN_OPTS"] = opt("--lean-opts")
    # --leaf-only: never replace a block with a structural step (have/obtain/calc/cases/...): the proof skeleton stays;
    # --leaf-or-hinted: such a block may be replaced only by a HINTED closer (it names the facts the block used)
    leaf_only = "--leaf-only" in a
    leaf_or_hinted = "--leaf-or-hinted" in a
    edits_f = opt("--edits")
    modname = modrel[:-5].replace("/", ".")
    data = open(os.path.join(src, modrel), "rb").read()
    rank = {t: i for i, t in enumerate(prefer)}
    best = {}
    for ln in open(resf):
        r = json.loads(ln)
        if not r["ok"] or r.get("tmpl", r["tac"]) in exclude:
            continue
        # proof read by an attribute (@[to_additive]/@[to_dual] translate the proof term): never edited
        bs = data.rfind(b"\n\n", 0, r["spos"])
        if b"to_additive" in data[bs:r["spos"]] or b"to_dual" in data[bs:r["spos"]]:
            continue
        if (leaf_only or (leaf_or_hinted and "$" not in r.get("tmpl", ""))) and \
                STRUCT.search(data[r["spos"]:r["epos"]].decode("utf-8", "replace")):
            continue
        k = (r["spos"], r["epos"])
        tk = lambda x: rank.get(x.get("tmpl", x["tac"]), 99)
        if k not in best or tk(r) < tk(best[k]):
            best[k] = r
    # non-overlapping, longest first
    cands = sorted(best.values(), key=lambda r: -(r["epos"] - r["spos"]))
    chosen = []
    for r in cands:
        if all(r["epos"] <= c["spos"] or c["epos"] <= r["spos"] for c in chosen):
            chosen.append(r)
    chosen.sort(key=lambda r: r["spos"])

    def render(sel):
        out, last = [], 0
        newstarts = []
        for r in sel:
            out.append(data[last:r["spos"]])
            txt = r["tac"] if r["ngoals"] == 1 else f"all_goals ({r['tac']})"
            nl = b"".join(out).count(b"\n") + 1
            newstarts.append((nl, r))
            out.append(txt.encode())
            last = r["epos"]
        out.append(data[last:])
        return b"".join(out), newstarts

    wd = os.path.abspath(os.path.join(outd.rstrip("/") + ".wd", modrel.replace("/", "__")[:-5]))  # outside the tree
    os.makedirs(wd, exist_ok=True)
    summ = dict(module=modrel, cands=len(best), chosen=len(chosen))
    verify = "--no-verify" not in a
    if verify:
        open(os.path.join(wd, "orig.lean"), "wb").write(data)
        base = elab(proj, wd, "orig.lean", modname)
        summ["orig"] = dict(wall=base["wall"], cpu=base["cpu"], errs=len(base["errs"]))
        if base["errs"]:
            summ["status"] = "orig-has-errors"
            print(json.dumps(summ)); return
    sel = list(chosen)
    reverted = []
    for rnd in range(rounds + 1):
        new, starts = render(sel)
        if not sel or not verify:
            break
        open(os.path.join(wd, "new.lean"), "wb").write(new)
        res = elab(proj, wd, "new.lean", modname)
        if not res["errs"]:
            summ["new"] = dict(wall=res["wall"], cpu=res["cpu"])
            break
        bad = set()
        for e in res["errs"]:
            el = e.get("pos", {}).get("line", 0)
            prev = [r for (nl, r) in starts if nl <= el]
            if prev:
                bad.add(id(prev[-1]))
            else:
                bad.update(id(r) for r in sel)  # cannot attribute: revert everything
        reverted += [r for r in sel if id(r) in bad]
        sel = [r for r in sel if id(r) not in bad]
    else:
        sel = []
    new, _ = render(sel)
    if verify and sel and "new" not in summ:
        sel = []
        new = data
    summ.update(applied=len(sel), reverted=len(reverted),
                lines0=data.count(b"\n"), lines1=new.count(b"\n"), chars0=len(data), chars1=len(new),
                tacs={t: sum(1 for r in sel if r["tac"] == t) for t in set(r["tac"] for r in sel)},
                status="ok")
    if edits_f and sel:
        esc = lambda t: t.replace("\\", "\\\\").replace("\n", "\\n")  # P03 format: tabs stay literal (split maxsplit=5)
        with open(edits_f, "a") as ef:
            for r in sel:
                ls = data.rfind(b"\n", 0, r["spos"]) + 1
                le = data.find(b"\n", r["epos"]); le = len(data) if le < 0 else le
                l0 = data.count(b"\n", 0, r["spos"]) + 1; l1 = data.count(b"\n", 0, r["epos"]) + 1
                txt = r["tac"] if r["ngoals"] == 1 else f"all_goals ({r['tac']})"
                rep = (data[ls:r["spos"]] + txt.encode() + data[r["epos"]:le]).decode()
                ef.write(f"{modname}\t{l0}\t{l1}\treplace\tP06\t{esc(rep)}\n")   # team format: module NAME
                with open(edits_f + ".deps", "a") as df:
                    df.write(json.dumps({"module": modname, "l0": l0, "l1": l1, "decl": r["decl"],
                                         "deps": r.get("deps")}) + "\n")
    op = os.path.join(outd, modrel)
    os.makedirs(os.path.dirname(op), exist_ok=True)
    open(op, "wb").write(new)
    json.dump(dict(applied=[{k: r[k] for k in ("decl", "line", "eline", "spos", "epos", "tac", "ngoals")} for r in sel],
                   reverted=[{k: r[k] for k in ("decl", "line", "eline", "tac")} for r in reverted]),
              open(os.path.join(wd, "applied.json"), "w"))
    print(json.dumps(summ))


if __name__ == "__main__":
    main()
