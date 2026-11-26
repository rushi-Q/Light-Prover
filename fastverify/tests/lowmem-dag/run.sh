#!/bin/bash
# tests/lowmem-dag/run.sh — regression suite for the lowmem checkAxioms BFS dense-DAG
# mark-on-push bound and for duplicate Name / duplicate declaration rejection.
# Runs read-only against $FV_ROOT (writes exclusively inside a private mktemp workdir).
set -euo pipefail
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
W=$(mktemp -d "${TMPDIR:-/tmp}/fv-lowmem-dag.XXXXXX")
trap 'rm -rf "$W"' EXIT

python3 -I - "$FV" "$W" <<'PY'
import hashlib, json, os, shutil, subprocess, sys

fv, w = sys.argv[1], sys.argv[2]
chk_lm = os.path.join(fv, "check", "lowmem", "check-sound-lowmem.sh")
selftest = "/scratch/fastverify-next/selftest"
assert os.path.isfile(chk_lm), f"missing {chk_lm}"
assert os.path.isdir(selftest), f"missing {selftest}"

def sha256_file(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()

lines_good = [ln for ln in open(os.path.join(selftest, "good.export"), encoding="utf-8").read().splitlines() if ln.strip()]
lines_chal = [ln for ln in open(os.path.join(selftest, "challenge.export"), encoding="utf-8").read().splitlines() if ln.strip()]
hdr = lines_good[0]
cfg_base = json.load(open(os.path.join(selftest, "comparator.json"), encoding="utf-8"))

def max_indices(items):
    mi = ml = 0
    me = -1
    for o in items:
        if "in" in o: mi = max(mi, o["in"])
        elif "il" in o: ml = max(ml, o["il"])
        elif "ie" in o: me = max(me, o["ie"])
    return mi, ml, me

def build_dense_dag(base_lines, n_lemmas=74, illegal_root=False):
    items = [json.loads(x) for x in base_lines[1:]]
    mi, ml, me = max_indices(items)

    def add_name(s):
        nonlocal mi
        mi += 1
        items.append({"in": mi, "str": {"pre": 0, "str": s}})
        return mi

    def add_expr(d):
        nonlocal me
        me += 1
        obj = {"ie": me}; obj.update(d)
        items.append(obj)
        return me

    s0 = add_expr({"sort": 0})
    np, nx, nu = add_name("p"), add_name("x"), add_name("_u")
    b0, b1 = add_expr({"bvar": 0}), add_expr({"bvar": 1})
    ty_id = add_expr({"forallE": {"name": np, "type": s0, "body": add_expr({"forallE": {"name": nx, "type": b0, "body": b1, "binderInfo": "default"}}), "binderInfo": "default"}})
    val_id = add_expr({"lam": {"name": np, "type": s0, "body": add_expr({"lam": {"name": nx, "type": b0, "body": b0, "binderInfo": "default"}}), "binderInfo": "default"}})

    bad_ax_const = None
    if illegal_root:
        n_bad = add_name("dagIllegalRootAx")
        items.append({"axiom": {"name": n_bad, "levelParams": [], "type": ty_id, "isUnsafe": False}})
        bad_ax_const = add_expr({"const": {"name": n_bad, "us": []}})

    lemma_consts = []
    for i in range(n_lemmas):
        nm = add_name(f"dagL_{i}")
        if i == 0 and illegal_root:
            body = bad_ax_const
        else:
            body = val_id
            # Reference every prior lemma 0..i-1 via non-dependent letE chain (~2,775 edges for n=74 > n_decls+1024!)
            for prev_c in lemma_consts:
                body = add_expr({"letE": {"name": nu, "type": ty_id, "value": prev_c, "body": body, "nondep": True}})
        items.append({"thm": {"name": nm, "levelParams": [], "type": ty_id, "value": body, "all": [nm]}})
        lemma_consts.append(add_expr({"const": {"name": nm, "us": []}}))

    n_tgt = add_name("dagTarget")
    items.append({"thm": {"name": n_tgt, "levelParams": [], "type": ty_id, "value": lemma_consts[-1], "all": [n_tgt]}})
    return hdr + "\n" + "\n".join(json.dumps(o, separators=(",", ":"), sort_keys=True) for o in items) + "\n", ty_id

# Challenge export with dagTarget := sorryAx
chal_items = [json.loads(x) for x in lines_chal[1:]]
mi_c, ml_c, me_c = max_indices(chal_items)
nmap_c = {0: ""}
for o in chal_items:
    if "in" in o and "str" in o:
        p = nmap_c.get(o["str"]["pre"], "")
        nmap_c[o["in"]] = f"{p}.{o['str']['str']}" if p else o["str"]["str"]
nsorry_c = next(k for k, v in nmap_c.items() if v == "sorryAx")
nfalse_c = next(k for k, v in nmap_c.items() if v == "Bool.false")

def c_name(s):
    global mi_c
    mi_c += 1
    chal_items.append({"in": mi_c, "str": {"pre": 0, "str": s}})
    return mi_c

def c_expr(d):
    global me_c
    me_c += 1
    obj = {"ie": me_c}; obj.update(d)
    chal_items.append(obj)
    return me_c

s0_c = c_expr({"sort": 0})
np_c, nx_c = c_name("p"), c_name("x")
b0_c, b1_c = c_expr({"bvar": 0}), c_expr({"bvar": 1})
ty_id_c = c_expr({"forallE": {"name": np_c, "type": s0_c, "body": c_expr({"forallE": {"name": nx_c, "type": b0_c, "body": b1_c, "binderInfo": "default"}}), "binderInfo": "default"}})
sorry_c = c_expr({"const": {"name": nsorry_c, "us": [0]}})
bfalse_c = c_expr({"const": {"name": nfalse_c, "us": []}})
sval_c = c_expr({"app": {"fn": c_expr({"app": {"fn": sorry_c, "arg": ty_id_c}}), "arg": bfalse_c}})
ntgt_c = c_name("dagTarget")
chal_items.append({"thm": {"name": ntgt_c, "levelParams": [], "type": ty_id_c, "value": sval_c, "all": [ntgt_c]}})

chal_p = os.path.join(w, "dag_chal.export")
open(chal_p, "w", encoding="utf-8").write(hdr + "\n" + "\n".join(json.dumps(o, separators=(",", ":"), sort_keys=True) for o in chal_items) + "\n")
cfg_p = os.path.join(w, "dag_cfg.json")
cfg_dag = dict(cfg_base)
cfg_dag["theorem_names"] = list(cfg_base["theorem_names"]) + ["dagTarget"]
json.dump(cfg_dag, open(cfg_p, "w", encoding="utf-8"))

sol_ok_txt, _ = build_dense_dag(lines_good, n_lemmas=74, illegal_root=False)
sol_ok_p = os.path.join(w, "dag74_valid.export")
open(sol_ok_p, "w", encoding="utf-8").write(sol_ok_txt)

sol_bad_txt, _ = build_dense_dag(lines_good, n_lemmas=74, illegal_root=True)
sol_bad_p = os.path.join(w, "dag74_illegal_root.export")
open(sol_bad_p, "w", encoding="utf-8").write(sol_bad_txt)

def run_lm(sol, chal, cfg, tag):
    wd = os.path.join(w, f"wd_{tag}")
    jsf = os.path.join(w, f"{tag}.json")
    cmd = [chk_lm, sol, chal, cfg, "--threads", "4", "--workdir", wd, "--json", jsf]
    if "--challenge-sha256)" in open(chk_lm, encoding="utf-8", errors="replace").read():
        cmd += ["--challenge-sha256", sha256_file(chal), "--comparator-sha256", sha256_file(cfg)]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    shutil.rmtree(wd, ignore_errors=True)
    j = json.load(open(jsf, encoding="utf-8")) if os.path.isfile(jsf) else {}
    return p.returncode, j

# 1. BFS bound: 74-lemma valid dense DAG (> n_decls + 1024 edges) -> ACCEPTED (rc=0)
rc1, j1 = run_lm(sol_ok_p, chal_p, cfg_p, "dag74_ok")
assert rc1 == 0 and j1.get("verdict") == "ACCEPTED", (rc1, j1)
print("PASS [1/3] 74-lemma valid dense DAG accepted without BFS stack overflow (rc=0)")

# 2. BFS bound, soundness control: 74-lemma dense DAG with illegal axiom at root L_0 -> REJECTED (rc=1)
rc2, j2 = run_lm(sol_bad_p, chal_p, cfg_p, "dag74_bad")
assert rc2 == 1 and j2.get("verdict") == "REJECTED" and "dagIllegalRootAx" in j2.get("reason", ""), (rc2, j2)
print("PASS [2/3] control: 74-lemma dense DAG with root illegal axiom rejected (rc=1)")

# 3. Duplicate declaration via distinct `in` indices for `dagTarget`
#    First decl uses illegal axiom, second decl has wrong type `Prop -> Prop` or valid proof -> kernel legs REJECT!
dup_items = [json.loads(x) for x in sol_bad_txt.splitlines()[1:] if x.strip()]
mi_d, _, me_d = max_indices(dup_items)
mi_d += 1
dup_items.append({"in": mi_d, "str": {"pre": 0, "str": "dagTarget"}})
# Find ty_id and val_id by adding clean closed `∀ (p : Prop) (x : p), p`
me_d += 1; s0_d = me_d; dup_items.append({"ie": s0_d, "sort": 0})
mi_d += 1; np_d = mi_d; dup_items.append({"in": np_d, "str": {"pre": 0, "str": "p"}})
mi_d += 1; nx_d = mi_d; dup_items.append({"in": nx_d, "str": {"pre": 0, "str": "x"}})
me_d += 1; b0_d = me_d; dup_items.append({"ie": b0_d, "bvar": 0})
me_d += 1; b1_d = me_d; dup_items.append({"ie": b1_d, "bvar": 1})
me_d += 1; inner_t = me_d; dup_items.append({"ie": inner_t, "forallE": {"name": nx_d, "type": b0_d, "body": b1_d, "binderInfo": "default"}})
me_d += 1; ty_d = me_d; dup_items.append({"ie": ty_d, "forallE": {"name": np_d, "type": s0_d, "body": inner_t, "binderInfo": "default"}})
me_d += 1; inner_v = me_d; dup_items.append({"ie": inner_v, "lam": {"name": nx_d, "type": b0_d, "body": b0_d, "binderInfo": "default"}})
me_d += 1; val_d = me_d; dup_items.append({"ie": val_d, "lam": {"name": np_d, "type": s0_d, "body": inner_v, "binderInfo": "default"}})
dup_items.append({"thm": {"name": mi_d - 2, "levelParams": [], "type": ty_d, "value": val_d, "all": [mi_d - 2]}})
dup_p = os.path.join(w, "dup_decl_forgery.export")
open(dup_p, "w", encoding="utf-8").write(hdr + "\n" + "\n".join(json.dumps(o, separators=(",", ":"), sort_keys=True) for o in dup_items) + "\n")

rc3, j3 = run_lm(dup_p, chal_p, cfg_p, "dup_decl")
assert rc3 != 0 and j3.get("verdict") != "ACCEPTED", (rc3, j3)
print(f"PASS [3/3] duplicate-Name shadowed declaration rejected ({j3.get('verdict')}, rc={rc3})")
PY
echo "RESULT PASS"
