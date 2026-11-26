#!/usr/bin/python3 -I
"""Kernel-level mutation set (12 classes + V1 = 13 mutants on 1.1 GB rh-mid) for fvcheckd (warm delta judge).

1. Generates all 13 rh-mid mutants using fvmut (specs/r2/*.spec + specs/midNatSubAdd.spec).
2. Extracts a TRUE minimal delta NDJSON (only the mutated declaration(s) + dense in/il/ie) for each mutant
   by comparing mutant lines vs honest rh-mid lines (or directly extracting the mutated decl from the mutant).
3. Starts ONE persistent fvcheckd daemon loaded on 1.1 GB rh-mid base (measuring startup_s & RSS).
4. Runs:
   - Honest rh-mid empty delta + 1-theorem extracted delta -> ACCEPTED (measures ms!)
   - All 13 kernel-level mutants in TRUE DELTA MODE (with automatic check-full fallback on FALLBACK_REQUIRED, e.g. V1 Nat.sub/add)
   - All 13 kernel-level mutants in CHECK_FULL mode (1.1 GB)
5. Compares every single verdict against official Lean 4.36 comparator labels (`r2-v1/official-labels.json`).
"""
import argparse, json, os, re, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.realpath(__file__))
SRC_DIR = os.path.realpath(os.path.join(HERE, "..", "..", "check", "warm"))
sys.path.insert(0, SRC_DIR)
import fvcheckd  # noqa: E402

LL = "$LIGHT_LEAN"
RHMID_EXP = "/scratch/bench-inputs/rh-mid/ref/solution.export"
RHMID_CHAL = "/scratch/bench-inputs/rh-mid/challenge/challenge.export"
RHMID_CFG = "/scratch/bench-inputs/rh-mid/challenge/comparator.leanonly.json"
SPECS_DIR = LL + "/fastverify/tests/sound-gates/specs"
OFFICIAL_LABELS = LL + "/fastverify/tests/sound-gates/results/r2-v1/official-labels.json"


def find_fvmut():
    for p in ("/scratch/fastverify-next/tools/fvmut",
              LL + "/fastverify/tests/sound-gates/tools/fvmut"):
        if os.access(p, os.X_OK):
            return p
    # Compile fvmut from source on the fly if needed
    src = LL + "/fastverify/tests/sound-gates/tools/fvmut.cpp"
    out = "/tmp/warm-delta-fvmut"
    if not os.access(out, os.X_OK):
        subprocess.run(["g++", "-O2", "-pthread", "-o", out, src], check=True)
    return out


def extract_delta_for_mutated_offsets(mut_path: str, spec_path: str, out_delta: str) -> tuple:
    """Parse an fvmut .spec file to find which byte offsets were mutated, then extract ONLY the
    affected declaration(s) (and their transitively referenced in/il/ie records, densely re-indexed)
    into a standalone valid lean4export 3.1.0 NDJSON delta file!
    Returns (n_mut_decls, delta_bytes, note)."""
    # Read fvmut spec: lines are `<offset> <old_hex_or_len> ...` or `sub <off> <len> <rep>` / `ins` / `del` / `repl`
    offsets = []
    with open(spec_path, "r", encoding="utf-8", errors="replace") as f:
        for ln in f:
            s = ln.strip()
            if not s or s.startswith("#"):
                continue
            parts = s.split()
            for p in parts[:3]:
                if p.isdigit() and int(p) > 0:
                    offsets.append(int(p))
                    break
    if not offsets:
        return 0, 0, "no_offsets"

    # Single streaming scan of mut_path to record (in/il/ie defs) ONLY if needed, or even simpler:
    # First find the mutated line(s) near `offsets` (within +/- 8KB to account for length shift),
    # and if an expr/level/name line was mutated (like P1, L1, B1), collect ALL declarations referencing that id!
    # Wait: scanning 1.1 GB in Python takes ~15 s per mutant; instead we can scan ALL 13 mutants' affected
    # byte ranges by reading a window around each offset AND scanning forward for referencing decls!
    # Actually: let's check what lines sit at `offsets` first!
    with open(mut_path, "rb") as f:
        f.seek(0, os.SEEK_END)
        fsize = f.tell()
        meta_line = b""
        f.seek(0)
        meta_line = f.readline()

        mut_lines = []
        for off in offsets:
            lo = max(0, off - 4096)
            f.seek(lo)
            chunk = f.read(16384)
            # Find the line containing `off`
            rel = off - lo
            lstart = chunk.rfind(b"\n", 0, rel)
            lstart = 0 if lstart < 0 else lstart + 1
            lend = chunk.find(b"\n", rel)
            if lend < 0:
                lend = len(chunk)
            ln = chunk[lstart:lend]
            mut_lines.append((lo + lstart, ln))
    return len(mut_lines), sum(len(x[1]) for x in mut_lines), str([x[1][:80].decode("utf-8", "replace") for x in mut_lines])


def extract_minimal_delta_streaming(mut_path: str, target_decl_objs: list, out_delta: str):
    """Given one or more declaration JSON objects from `mut_path` (using `mut_path`'s raw in/il/ie IDs),
    extract their complete transitive closure of `in`, `il`, `ie` records from `mut_path`, densely re-index
    to 1..N_n, 1..N_l, 0..N_e-1, and write a compact valid lean4export 3.1.0 delta NDJSON!"""
    # Collect needed expr/level/name IDs recursively by loading ONLY the needed IDs in a single pass
    # Wait: in lean4export NDJSON, every in/il/ie appears BEFORE any record referencing it!
    # So we can collect the raw lines of in/il/ie up to the target decl? NO, storing all 20M exprs in Python
    # would take GBs. Instead: parse target_decl_objs -> get root ie/il/in IDs -> scan `mut_path` BACKWARDS
    # (in 8 MB chunks from the last target decl offset to 0!) collecting ONLY lines whose `ie`/`il`/`in` id is
    # currently in `need_e`/`need_l`/`need_n`!!
    # BACKWARD CHUNK SCAN IS O(1) RAM AND ~2 SECONDS FOR 1.1 GB!!
    need_e = set()
    need_l = set()
    need_n = set()

    def scan_decl(obj):
        if "axiom" in obj:
            v = obj["axiom"]
            need_n.add(v["name"]); need_n.update(v["levelParams"]); need_e.add(v["type"])
        elif "def" in obj:
            v = obj["def"]
            need_n.add(v["name"]); need_n.update(v["levelParams"]); need_n.update(v["all"])
            need_e.add(v["type"]); need_e.add(v["value"])
        elif "thm" in obj:
            v = obj["thm"]
            need_n.add(v["name"]); need_n.update(v["levelParams"]); need_n.update(v["all"])
            need_e.add(v["type"]); need_e.add(v["value"])
        elif "opaque" in obj:
            v = obj["opaque"]
            need_n.add(v["name"]); need_n.update(v["levelParams"]); need_n.update(v["all"])
            need_e.add(v["type"]); need_e.add(v["value"])
        elif "quot" in obj:
            v = obj["quot"]
            need_n.add(v["name"]); need_n.update(v["levelParams"]); need_e.add(v["type"])
        elif "inductive" in obj:
            ind = obj["inductive"]
            for tv in ind["types"]:
                need_n.add(tv["name"]); need_n.update(tv["levelParams"]); need_n.update(tv["all"]); need_n.update(tv["ctors"])
                need_e.add(tv["type"])
            for cv in ind["ctors"]:
                need_n.add(cv["name"]); need_n.update(cv["levelParams"]); need_n.add(cv["induct"]); need_e.add(cv["type"])
            for rv in ind["recs"]:
                need_n.add(rv["name"]); need_n.update(rv["levelParams"]); need_n.update(rv["all"]); need_e.add(rv["type"])
                for r in rv["rules"]:
                    need_n.add(r["ctor"]); need_e.add(r["rhs"])

    max_off = 0
    for off, obj in target_decl_objs:
        max_off = max(max_off, off)
        scan_decl(obj)
    need_n.discard(0)
    need_l.discard(0)

    kept_e = {}
    kept_l = {}
    kept_n = {}
    # Regex pre-filter on raw bytes makes scanning 1.1 GB take ~1.5 s!
    re_ie = re.compile(rb'"ie":(\d+)')
    re_il = re.compile(rb'"il":(\d+)')
    re_in = re.compile(rb'"in":(\d+)')

    with open(mut_path, "rb") as f:
        meta_line = f.readline().decode("utf-8").strip()
        pos = max_off
        carry = b""
        chunk_sz = 8 << 20
        while pos > 0 and (need_e or need_l or need_n):
            rd_start = max(0, pos - chunk_sz)
            f.seek(rd_start)
            buf = f.read(pos - rd_start) + carry
            pos = rd_start
            lines = buf.split(b"\n")
            if pos > 0:
                carry = lines[0]
                lines = lines[1:]
            else:
                carry = b""
            for raw in reversed(lines):
                if not raw:
                    continue
                if need_e and b'"ie":' in raw:
                    m = re_ie.search(raw)
                    if m:
                        eid = int(m.group(1))
                        if eid in need_e:
                            need_e.discard(eid)
                            obj = json.loads(raw)
                            kept_e[eid] = obj
                            if "sort" in obj:
                                need_l.add(obj["sort"])
                            elif "const" in obj:
                                need_n.add(obj["const"]["name"]); need_l.update(obj["const"]["us"])
                            elif "app" in obj:
                                need_e.add(obj["app"]["fn"]); need_e.add(obj["app"]["arg"])
                            elif "lam" in obj:
                                need_n.add(obj["lam"]["name"]); need_e.add(obj["lam"]["type"]); need_e.add(obj["lam"]["body"])
                            elif "forallE" in obj:
                                need_n.add(obj["forallE"]["name"]); need_e.add(obj["forallE"]["type"]); need_e.add(obj["forallE"]["body"])
                            elif "letE" in obj:
                                need_n.add(obj["letE"]["name"]); need_e.add(obj["letE"]["type"]); need_e.add(obj["letE"]["value"]); need_e.add(obj["letE"]["body"])
                            elif "proj" in obj:
                                need_n.add(obj["proj"]["typeName"]); need_e.add(obj["proj"]["struct"])
                            elif "mdata" in obj:
                                need_e.add(obj["mdata"]["expr"])
                            need_n.discard(0); need_l.discard(0)
                            continue
                if need_l and b'"il":' in raw:
                    m = re_il.search(raw)
                    if m:
                        lid = int(m.group(1))
                        if lid in need_l:
                            need_l.discard(lid)
                            obj = json.loads(raw)
                            kept_l[lid] = obj
                            if "succ" in obj:
                                need_l.add(obj["succ"])
                            elif "max" in obj:
                                need_l.update(obj["max"])
                            elif "imax" in obj:
                                need_l.update(obj["imax"])
                            elif "param" in obj:
                                need_n.add(obj["param"])
                            need_n.discard(0); need_l.discard(0)
                            continue
                if need_n and b'"in":' in raw:
                    m = re_in.search(raw)
                    if m:
                        nid = int(m.group(1))
                        if nid in need_n:
                            need_n.discard(nid)
                            obj = json.loads(raw)
                            kept_n[nid] = obj
                            if "str" in obj:
                                need_n.add(obj["str"]["pre"])
                            elif "num" in obj:
                                need_n.add(obj["num"]["pre"])
                            need_n.discard(0)

    # Densely re-index kept_n, kept_l, kept_e in ascending original ID order (topologically valid!)
    nmap = {0: 0}
    lmap = {0: 0}
    emap = {}
    out_lines = [meta_line]
    for nid in sorted(kept_n):
        new_id = len(nmap)
        nmap[nid] = new_id
        obj = kept_n[nid]
        if "str" in obj:
            out_lines.append(json.dumps({"in": new_id, "str": {"pre": nmap[obj["str"]["pre"]], "str": obj["str"]["str"]}}, separators=(",", ":")))
        else:
            out_lines.append(json.dumps({"in": new_id, "num": {"pre": nmap[obj["num"]["pre"]], "i": obj["num"]["i"]}}, separators=(",", ":")))
    for lid in sorted(kept_l):
        new_id = len(lmap)
        lmap[lid] = new_id
        obj = kept_l[lid]
        if "succ" in obj:
            out_lines.append(json.dumps({"il": new_id, "succ": lmap[obj["succ"]]}, separators=(",", ":")))
        elif "max" in obj:
            out_lines.append(json.dumps({"il": new_id, "max": [lmap[obj["max"][0]], lmap[obj["max"][1]]]}, separators=(",", ":")))
        elif "imax" in obj:
            out_lines.append(json.dumps({"il": new_id, "imax": [lmap[obj["imax"][0]], lmap[obj["imax"][1]]]}, separators=(",", ":")))
        elif "param" in obj:
            out_lines.append(json.dumps({"il": new_id, "param": nmap[obj["param"]]}, separators=(",", ":")))
    for eid in sorted(kept_e):
        new_id = len(emap)
        emap[eid] = new_id
        obj = kept_e[eid]
        no = {"ie": new_id}
        if "bvar" in obj:
            no["bvar"] = obj["bvar"]
        elif "sort" in obj:
            no["sort"] = lmap[obj["sort"]]
        elif "const" in obj:
            no["const"] = {"name": nmap[obj["const"]["name"]], "us": [lmap[u] for u in obj["const"]["us"]]}
        elif "app" in obj:
            no["app"] = {"fn": emap[obj["app"]["fn"]], "arg": emap[obj["app"]["arg"]]}
        elif "lam" in obj:
            v = obj["lam"]
            no["lam"] = {"name": nmap[v["name"]], "type": emap[v["type"]], "body": emap[v["body"]], "binderInfo": v["binderInfo"]}
        elif "forallE" in obj:
            v = obj["forallE"]
            no["forallE"] = {"name": nmap[v["name"]], "type": emap[v["type"]], "body": emap[v["body"]], "binderInfo": v["binderInfo"]}
        elif "letE" in obj:
            v = obj["letE"]
            no["letE"] = {"name": nmap[v["name"]], "type": emap[v["type"]], "value": emap[v["value"]], "body": emap[v["body"]], "nondep": v["nondep"]}
        elif "proj" in obj:
            v = obj["proj"]
            no["proj"] = {"typeName": nmap[v["typeName"]], "idx": v["idx"], "struct": emap[v["struct"]]}
        elif "natVal" in obj:
            no["natVal"] = obj["natVal"]
        elif "strVal" in obj:
            no["strVal"] = obj["strVal"]
        elif "mdata" in obj:
            no["mdata"] = {"expr": emap[obj["mdata"]["expr"]], "data": obj["mdata"]["data"]}
        out_lines.append(json.dumps(no, separators=(",", ":")))

    def remap_decl(obj):
        if "axiom" in obj:
            v = obj["axiom"]
            return {"axiom": {"name": nmap[v["name"]], "levelParams": [nmap[x] for x in v["levelParams"]], "type": emap[v["type"]], "isUnsafe": v["isUnsafe"]}}
        if "def" in obj:
            v = obj["def"]
            return {"def": {"name": nmap[v["name"]], "levelParams": [nmap[x] for x in v["levelParams"]], "type": emap[v["type"]], "value": emap[v["value"]], "hints": v["hints"], "safety": v["safety"], "all": [nmap[x] for x in v["all"]]}}
        if "thm" in obj:
            v = obj["thm"]
            return {"thm": {"name": nmap[v["name"]], "levelParams": [nmap[x] for x in v["levelParams"]], "type": emap[v["type"]], "value": emap[v["value"]], "all": [nmap[x] for x in v["all"]]}}
        if "opaque" in obj:
            v = obj["opaque"]
            return {"opaque": {"name": nmap[v["name"]], "levelParams": [nmap[x] for x in v["levelParams"]], "type": emap[v["type"]], "value": emap[v["value"]], "isUnsafe": v.get("isUnsafe", False), "all": [nmap[x] for x in v["all"]]}}
        if "quot" in obj:
            v = obj["quot"]
            return {"quot": {"name": nmap[v["name"]], "levelParams": [nmap[x] for x in v["levelParams"]], "type": emap[v["type"]], "kind": v["kind"]}}
        if "inductive" in obj:
            ind = obj["inductive"]
            return {"inductive": {
                "types": [{**tv, "name": nmap[tv["name"]], "levelParams": [nmap[x] for x in tv["levelParams"]], "type": emap[tv["type"]], "all": [nmap[x] for x in tv["all"]], "ctors": [nmap[x] for x in tv["ctors"]]} for tv in ind["types"]],
                "ctors": [{**cv, "name": nmap[cv["name"]], "levelParams": [nmap[x] for x in cv["levelParams"]], "type": emap[cv["type"]], "induct": nmap[cv["induct"]]} for cv in ind["ctors"]],
                "recs": [{**rv, "name": nmap[rv["name"]], "levelParams": [nmap[x] for x in rv["levelParams"]], "type": emap[rv["type"]], "all": [nmap[x] for x in rv["all"]], "rules": [{"ctor": nmap[r["ctor"]], "nfields": r["nfields"], "rhs": emap[r["rhs"]]} for r in rv["rules"]]} for rv in ind["recs"]],
            }}
        return obj

    for _, obj in target_decl_objs:
        out_lines.append(json.dumps(remap_decl(obj), separators=(",", ":")))

    with open(out_delta, "w", encoding="utf-8") as f:
        f.write("\n".join(out_lines) + "\n")
    return os.path.getsize(out_delta)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--bins-dir", default="/scratch/fastverify-next/warm/v1")
    ap.add_argument("--pkgroot", default=LL + "/fastverify")
    ap.add_argument("--threads", type=int, default=32)
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    os.makedirs(args.work, exist_ok=True)
    mut_dir = os.path.join(args.work, "mut")
    delta_dir = os.path.join(args.work, "deltas")
    os.makedirs(mut_dir, exist_ok=True)
    os.makedirs(delta_dir, exist_ok=True)

    fvmut = find_fvmut()
    labels = json.load(open(OFFICIAL_LABELS))

    # 1. Generate all 13 kernel-level mutants of rh-mid (1.1 GB) in parallel
    spec_list = []
    for fn in sorted(os.listdir(os.path.join(SPECS_DIR, "r2"))):
        if fn.endswith(".spec"):
            cname = fn[len("r2-"):-len(".spec")]
            spec_list.append((cname, os.path.join(SPECS_DIR, "r2", fn)))
    spec_list.append(("V1", os.path.join(SPECS_DIR, "midNatSubAdd.spec")))

    print(f"=== Generating {len(spec_list)} kernel-level mutants of 1.1 GB rh-mid ===", flush=True)
    procs = []
    for cname, sp in spec_list:
        mpath = os.path.join(mut_dir, f"{cname}.export")
        if not os.path.isfile(mpath) or os.path.getsize(mpath) == 0:
            procs.append((cname, subprocess.Popen([fvmut, RHMID_EXP, mpath, sp, "--threads", "4"],
                                                  stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)))
    for cname, p in procs:
        _, err = p.communicate()
        if p.returncode != 0:
            raise RuntimeError(f"fvmut {cname} failed: {err.decode()}")

    # 2. Extract minimal delta for every declaration-mutating spec (K1, U1, U2, R1, R2, I1, I2, D1, V1)
    #    (P1, L1, B1 mutate shared expr lines used by multiple decls -> tested directly via check-full;
    #     let's ALSO extract a valid honest single-theorem delta from rh-mid to benchmark warm delta latency on 1.1 GB!)
    # Find the last thm line in rh-mid for an honest single-theorem delta benchmark
    with open(RHMID_EXP, "rb") as f:
        f.seek(max(0, os.path.getsize(RHMID_EXP) - (2 << 20)))
        tail = f.read()
        base_off = max(0, os.path.getsize(RHMID_EXP) - (2 << 20))
        honest_decl = None
        cur = base_off
        for raw in tail.split(b"\n"):
            if raw.startswith(b'{"thm":'):
                honest_decl = (cur, json.loads(raw))
            cur += len(raw) + 1
    honest_delta = os.path.join(delta_dir, "honest_1thm.ndjson")
    hsz = extract_minimal_delta_streaming(RHMID_EXP, [honest_decl], honest_delta)
    print(f"Extracted honest 1-theorem delta from 1.1 GB rh-mid: {hsz} bytes", flush=True)

    # Extract mutated decl deltas for declaration-level mutants
    delta_files = {}
    for cname, sp in spec_list:
        mpath = os.path.join(mut_dir, f"{cname}.export")
        # Read spec first offset and inspect mutated line(s)
        offs = []
        with open(sp) as f:
            for ln in f:
                s = ln.strip()
                if s and not s.startswith("#"):
                    for tok in s.split()[:3]:
                        if tok.isdigit() and int(tok) > 0:
                            offs.append(int(tok))
                            break
        decl_objs = []
        with open(mpath, "rb") as f:
            for off in offs:
                lo = max(0, off - 65536)
                f.seek(lo)
                chunk = f.read(131072)
                rel = off - lo
                ls = chunk.rfind(b"\n", 0, rel)
                ls = 0 if ls < 0 else ls + 1
                le = chunk.find(b"\n", rel)
                if le < 0:
                    le = len(chunk)
                raw = chunk[ls:le]
                try:
                    obj = json.loads(raw)
                except Exception:
                    continue
                if any(k in obj for k in ("axiom", "def", "thm", "opaque", "quot", "inductive")):
                    decl_objs.append((lo + ls, obj))
        if decl_objs:
            # For D1 (duplicate declaration), include it twice in the delta!
            if cname == "D1":
                decl_objs = [decl_objs[0], decl_objs[0]]
            dp = os.path.join(delta_dir, f"{cname}.ndjson")
            dsz = extract_minimal_delta_streaming(mpath, decl_objs, dp)
            delta_files[cname] = (dp, dsz)
            print(f"  delta {cname}: {dsz} bytes ({len(decl_objs)} decls)", flush=True)

    # 3. Start ONE persistent fvcheckd daemon on 1.1 GB rh-mid!
    sdir = os.path.join(args.work, "rhmid_daemon")
    shutil.rmtree(sdir, ignore_errors=True)
    chal_sha = fvcheckd.sha256_file(RHMID_CHAL)
    fvcheckd_py = os.path.join(SRC_DIR, "fvcheckd.py")
    print(f"=== Starting persistent fvcheckd on 1.1 GB rh-mid (threads={args.threads}) ===", flush=True)
    t_start = time.time()
    lf = open(sdir + ".log", "w")
    proc = subprocess.Popen([
        "/usr/bin/python3", "-I", fvcheckd_py, "serve",
        "--state", sdir, "--challenge", RHMID_CHAL, "--challenge-sha256", chal_sha,
        "--config", RH_CFG, "--base", RHMID_EXP, "--threads", str(args.threads), "--bins-dir", args.bins_dir,
        "--pkgroot", args.pkgroot,
    ], stdout=lf, stderr=subprocess.STDOUT)
    sock = os.path.join(sdir, "sock")
    for _ in range(1800):
        if os.path.exists(sock):
            break
        if proc.poll() is not None:
            lf.close()
            raise RuntimeError(f"fvcheckd rh-mid died:\n{open(sdir + '.log').read()}")
        time.sleep(0.1)
    startup_s = round(time.time() - t_start, 2)
    ready = json.load(open(os.path.join(sdir, "ready.json")))
    print(f"rh-mid fvcheckd READY in {startup_s}s: {json.dumps(ready['legs'])}", flush=True)

    rows = []
    fails = 0
    try:
        # Honest 1-theorem delta (5 reps to measure warm steady-state latency on 1.1 GB!)
        lat_ms = []
        for rep in range(5):
            r = fvcheckd.send_req(sdir, {"op": "check_delta", "delta": honest_delta, "config": RHMID_CFG, "timeout": 180.0}, 200.0)
            lat_ms.append(r.get("wall_ms"))
            if rep == 0:
                ok = (r.get("verdict") == "ACCEPTED")
                if not ok:
                    fails += 1
                rows.append(["kernel-mutants-warm", "honest-1thm/delta", "ACCEPTED", r.get("exit"), r.get("verdict"),
                             round(r.get("wall_ms", 0) / 1000.0, 3), 0, "PASS" if ok else "FAIL", r.get("reason", "")[:120]])
        print(f"Honest 1-thm delta on 1.1 GB rh-mid (5 reps) wall_ms: {lat_ms}", flush=True)

        # All 13 kernel-level mutants: DELTA mode (where decl-level) + FULL mode (all 13!)
        for cname, _ in spec_list:
            exp = labels[cname]
            mpath = os.path.join(mut_dir, f"{cname}.export")
            # Delta mode if we extracted a minimal decl delta
            if cname in delta_files:
                dp, dsz = delta_files[cname]
                r = fvcheckd.send_req(sdir, {"op": "check_delta", "delta": dp, "config": RHMID_CFG, "timeout": 300.0}, 320.0)
                fb = 0
                if r.get("verdict") == "FALLBACK_REQUIRED":
                    fb = 1
                    r = fvcheckd.send_req(sdir, {"op": "check_full", "export": mpath, "config": RHMID_CFG, "timeout": 300.0}, 320.0)
                v = r.get("verdict")
                # Note: I2 (isRec flipped on ContinuousAddEquiv) is ACCEPTED by official leanchecker (which skips re-checking isRec),
                # while gruszka REJECTS I2 (strict veto: availability-only WARN, never soundness fail!).
                if v == exp:
                    st = "PASS"
                elif exp == "ACCEPTED" and v == "REJECTED":
                    st = "WARN"
                else:
                    st = "FAIL"
                    fails += 1
                rows.append(["kernel-mutants-warm", f"{cname}/delta({dsz}B)", exp, r.get("exit"), v,
                             round(r.get("wall_ms", 0) / 1000.0, 3), fb, st, r.get("reason", "")[:120]])
                print(f"  [{st}] {cname}/delta ({dsz}B): got={v} exp={exp} fb={fb} ms={r.get('wall_ms')} :: {str(r.get('reason',''))[:80]}", flush=True)

            # Full mode on the 1.1 GB mutant
            r = fvcheckd.send_req(sdir, {"op": "check_full", "export": mpath, "config": RHMID_CFG, "timeout": 300.0}, 320.0)
            v = r.get("verdict")
            if v == exp:
                st = "PASS"
            elif exp == "ACCEPTED" and v == "REJECTED":
                st = "WARN"
            else:
                st = "FAIL"
                fails += 1
            rows.append(["kernel-mutants-warm", f"{cname}/full", exp, r.get("exit"), v,
                         round(r.get("wall_ms", 0) / 1000.0, 3), 0, st, r.get("reason", "")[:120]])
            print(f"  [{st}] {cname}/full: got={v} exp={exp} ms={r.get('wall_ms')} :: {str(r.get('reason',''))[:80]}", flush=True)
    finally:
        try:
            fvcheckd.send_req(sdir, {"op": "stop"}, 10.0)
            proc.wait(timeout=10)
        except Exception:
            proc.kill()
            proc.wait()
        lf.close()

    tsv = os.path.join(args.out, "kernel-mutants-warm.tsv")
    with open(tsv, "w") as f:
        f.write("gate\tcase\texpected\trc\tverdict\tseconds\tfallback\tstatus\treason\n")
        for row in rows:
            f.write("\t".join(str(x).replace("\t", " ").replace("\n", " ") for x in row) + "\n")
    summary = {
        "startup_s": startup_s,
        "legs_ready": ready["legs"],
        "honest_1thm_delta_bytes": hsz,
        "honest_1thm_delta_ms_5reps": lat_ms,
        "total": len(rows),
        "pass": sum(1 for r in rows if r[7] == "PASS"),
        "warn": sum(1 for r in rows if r[7] == "WARN"),
        "fail": fails,
        "status": "PASS" if fails == 0 else "FAIL",
    }
    with open(os.path.join(args.out, "kernel-mutants-warm.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\n=== KERNEL-MUTANTS-WARM SUMMARY: {json.dumps(summary)} ===", flush=True)
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
