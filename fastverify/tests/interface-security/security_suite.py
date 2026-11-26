#!/usr/bin/python3 -I
"""security_suite.py — adversarial security and reward-hacking test suite for the service front ends:
  * HTTP API (fvapi.py): auth bypass, missing/invalid/chunked Content-Length, oversized payload bomb,
    slowloris socket timeout, NaN/Infinity JSON injection, batch-size bomb, 429 concurrency flood,
    path/theorem-name traversal & null-byte injection, backend-down fail-closed (NO-VERDICT -> reward=0.0),
    proof cheats (sorry, custom axiom, native_decide, debug.skipKernelTC, #eval host write, statement drift)
  * MCP server (fastverify-mcp): --allow-root path traversal, symlink escape outside allowed root,
    oversized JSON-RPC line & Content-Length bomb, malformed JSON, unknown tool/method,
    challenge_sha256 pin mismatch, proof cheats through fv_verify_attempt
  * Triage (triage.py): sandbox escape attempt via #eval IO.FS.writeFile inside a sub-lemma
  * CLI (bin/fv): missing/wrong --challenge-sha256 fail-closed

Exit 0 iff ALL adversarial tests pass with 0 false accepts and 0 sandbox/path escapes.
"""
import concurrent.futures as cf
import json
import os
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.realpath(__file__))
FV_ROOT = os.path.realpath(os.path.join(HERE, "..", ".."))
TC = os.environ.get("TC433", "$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1")
THREADS = int(os.environ.get("EVAL_THREADS", "8"))


def raw_http(host, port, raw_bytes, timeout=10.0):
    s = socket.create_connection((host, port), timeout=timeout)
    s.settimeout(timeout)
    s.sendall(raw_bytes)
    chunks = []
    try:
        while True:
            b = s.recv(4096)
            if not b:
                break
            chunks.append(b)
            if b"\r\n\r\n" in b"".join(chunks):
                hdr, rest = b"".join(chunks).split(b"\r\n\r\n", 1)
                cl = 0
                for line in hdr.split(b"\r\n")[1:]:
                    if line.lower().startswith(b"content-length:"):
                        cl = int(line.split(b":", 1)[1].strip())
                if len(rest) >= cl:
                    break
    except socket.timeout:
        pass
    finally:
        s.close()
    resp = b"".join(chunks)
    status_line = resp.split(b"\r\n", 1)[0].decode("latin1")
    code = int(status_line.split()[1]) if len(status_line.split()) >= 2 else 0
    return code, resp


def run_all():
    w = tempfile.mkdtemp(prefix="interface-security.")
    bad = 0
    svc_p = None
    api_p = None

    def ok(msg):
        print(f"PASS {msg}", flush=True)

    def fail(msg):
        nonlocal bad
        print(f"FAIL {msg}", flush=True)
        bad = 1

    try:
        # Prepare minimal official pinned challenge (Init-only)
        chal_src = os.path.join(w, "chal_src")
        os.makedirs(chal_src)
        open(os.path.join(chal_src, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
        open(os.path.join(chal_src, "lakefile.toml"), "w").write(
            'name = "RT"\ndefaultTargets = ["RT"]\n[[lean_lib]]\nname = "RT"\n'
        )
        open(os.path.join(chal_src, "lake-manifest.json"), "w").write(
            '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n'
        )
        open(os.path.join(chal_src, "RT.lean"), "w").write(
            "theorem rt_thm : ∀ n : Nat, n + 0 = n := by sorry\n"
        )
        open(os.path.join(chal_src, "comparator.json"), "w").write(json.dumps({
            "challenge_module": "RT",
            "solution_module": "RT",
            "theorem_names": ["rt_thm"],
            "definition_names": [],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        }))
        pinned = os.path.join(w, "pinned")
        p = subprocess.run([os.path.join(FV_ROOT, "bin", "fv"), "init-challenge", chal_src, pinned,
                            "--threads", str(THREADS), "--json"], capture_output=True, text=True, timeout=180)
        init_d = json.loads(p.stdout)
        assert init_d["ok"], init_d
        pin = init_d["challenge_sha256"]

        # Start fvserve
        empty_ws = os.path.join(w, "empty_ws")
        os.makedirs(os.path.join(empty_ws, ".lake", "packages"))
        svc_state = os.path.join(w, "svc")
        svc_log = os.path.join(w, "svc.log")
        svc_p = subprocess.Popen([
            "/usr/bin/python3", "-I", os.path.join(FV_ROOT, "tools", "fvserve", "fvserve.py"), "serve",
            "--state", svc_state, "--pset", f"rt={pinned}:{pin}",
            "--packages", empty_ws, "--toolchain", TC, "--fv", FV_ROOT,
            "--snapshot-header", "import Init", "--threads", str(THREADS), "--svc-check",
        ], stdout=open(svc_log, "wb"), stderr=subprocess.STDOUT)
        for _ in range(120):
            if os.path.isfile(svc_log) and b'"ready"' in open(svc_log, "rb").read():
                break
            time.sleep(0.5)
        assert b'"ready"' in open(svc_log, "rb").read(), open(svc_log).read()

        # Start fvapi with Bearer auth, tight limits (max_body=32KiB, max_batch=4, max_concurrent=2, socket_timeout=1.5s)
        key_file = os.path.join(w, "api.key")
        open(key_file, "w").write("secret-test-token-xyz\n")
        api_log = os.path.join(w, "api.log")
        api_p = subprocess.Popen([
            "/usr/bin/python3", "-I", os.path.join(FV_ROOT, "tools", "http", "fvapi.py"),
            "--fvserve-state", svc_state, "--default-pset", "rt",
            "--host", "127.0.0.1", "--port", "0",
            "--api-key-file", key_file,
            "--max-body-bytes", "32768", "--max-batch", "4",
            "--max-concurrent", "2", "--socket-timeout", "1.5",
        ], stdout=open(api_log, "wb"), stderr=subprocess.STDOUT)
        for _ in range(60):
            if os.path.isfile(api_log) and b'"ready"' in open(api_log, "rb").read():
                break
            time.sleep(0.2)
        api_info = json.loads(open(api_log).read().splitlines()[0])
        host, port = api_info["host"], api_info["port"]
        auth_hdr = "Authorization: Bearer secret-test-token-xyz\r\n"

        # ---- HTTP check 1: Auth enforcement (missing / wrong token -> 401)
        c1, _ = raw_http(host, port, b"POST /v1/verify HTTP/1.1\r\nHost: x\r\nContent-Length: 2\r\n\r\n{}")
        c2, _ = raw_http(host, port, b"POST /v1/verify HTTP/1.1\r\nHost: x\r\nAuthorization: Bearer wrong\r\nContent-Length: 2\r\n\r\n{}")
        c3, _ = raw_http(host, port, b"GET /metrics HTTP/1.1\r\nHost: x\r\n\r\n")
        if (c1, c2, c3) == (401, 401, 401):
            ok("HTTP auth: missing/wrong token rejected (401)")
        else:
            fail(f"HTTP auth bypass: got {(c1, c2, c3)}")

        # ---- HTTP check 2: Missing Content-Length & chunked transfer smuggling -> 411
        c_nocl, _ = raw_http(host, port, f"POST /v1/verify HTTP/1.1\r\nHost: x\r\n{auth_hdr}\r\n".encode())
        c_chk, _ = raw_http(host, port, f"POST /v1/verify HTTP/1.1\r\nHost: x\r\n{auth_hdr}Transfer-Encoding: chunked\r\n\r\n0\r\n\r\n".encode())
        if (c_nocl, c_chk) == (411, 411):
            ok("HTTP framing: missing Content-Length and chunked transfer rejected (411)")
        else:
            fail(f"HTTP framing: expected (411,411), got {(c_nocl, c_chk)}")

        # ---- HTTP check 3: Oversized body bomb -> 413
        c_big, _ = raw_http(host, port, f"POST /v1/verify HTTP/1.1\r\nHost: x\r\n{auth_hdr}Content-Length: 9999999\r\n\r\n".encode())
        if c_big == 413:
            ok("HTTP body bomb (>32 KiB) rejected before read (413)")
        else:
            fail(f"HTTP body bomb: expected 413, got {c_big}")

        # ---- HTTP check 4: Slowloris partial body -> 408 timeout
        t_sl = time.time()
        c_sl, _ = raw_http(host, port, f"POST /v1/verify HTTP/1.1\r\nHost: x\r\n{auth_hdr}Content-Length: 100\r\n\r\npartial".encode(), timeout=5.0)
        dt_sl = time.time() - t_sl
        if c_sl == 408 and dt_sl < 4.5:
            ok(f"HTTP slowloris timed out cleanly (408 in {dt_sl:.2f}s)")
        else:
            fail(f"HTTP slowloris: code={c_sl} dt={dt_sl:.2f}s")

        # ---- HTTP check 5: NaN/Infinity JSON injection & batch-size bomb -> 400
        nan_body = b'{"theorem":"rt_thm","source":"x","timeout":NaN}'
        c_nan, _ = raw_http(host, port, f"POST /v1/verify HTTP/1.1\r\nHost: x\r\n{auth_hdr}Content-Length: {len(nan_body)}\r\n\r\n".encode() + nan_body)
        bomb_body = json.dumps({"codes": [{"proof": "x", "theorem": "rt_thm"}] * 10}).encode()
        c_bomb, _ = raw_http(host, port, f"POST /verify HTTP/1.1\r\nHost: x\r\n{auth_hdr}Content-Length: {len(bomb_body)}\r\n\r\n".encode() + bomb_body)
        if (c_nan, c_bomb) == (400, 400):
            ok("HTTP strict JSON (NaN) and batch-size bomb (>4) rejected (400)")
        else:
            fail(f"HTTP JSON/batch bomb: got {(c_nan, c_bomb)}")

        # ---- HTTP check 5b: Concurrency flood (>max_concurrent=2) -> at least one 429 + Retry-After
        def slow_req(_i):
            body = json.dumps({
                "theorem": "rt_thm",
                "source": "import Init\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n",
            }).encode()
            return raw_http(host, port, f"POST /v1/verify HTTP/1.1\r\nHost: x\r\n{auth_hdr}Content-Length: {len(body)}\r\n\r\n".encode() + body, timeout=30.0)
        with cf.ThreadPoolExecutor(max_workers=6) as ex:
            flood_res = list(ex.map(slow_req, range(6)))
        codes_429 = [resp for code, resp in flood_res if code == 429]
        if codes_429 and all(b"Retry-After:" in r for r in codes_429):
            ok(f"HTTP concurrency flood (6 > max_concurrent=2): {len(codes_429)} requests cleanly throttled with 429 + Retry-After")
        else:
            fail(f"HTTP concurrency flood: expected >=1 429, got {[c for c, _ in flood_res]}")

        # ---- HTTP check 6: Proof cheats + path/theorem traversal + #eval host write through HTTP
        pwn_marker_tmp = os.path.join(w, "HTTP_PWNED_TMP")
        ro_base = "/scratch" if os.path.isdir("/scratch") else "/var"
        pwn_marker_ro = os.path.join(ro_base, f"iface_pwn_{os.getpid()}")
        cheats = [
            ("sorry", "rt_thm", "import Init\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by sorry\n", True),
            ("custom_axiom", "rt_thm", "import Init\naxiom evil : ∀ n : Nat, n + 0 = n\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := evil\n", True),
            ("skipKernelTC", "rt_thm", "import Init\nset_option debug.skipKernelTC true in\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by decide +kernel\n", True),
            ("weakened_stmt", "rt_thm", "import Init\ntheorem rt_thm : True := trivial\n", True),
            # Writing into host /tmp lands in sandbox ephemeral tmpfs (no host write; honest proof still valid!)
            ("eval_tmp_sandboxed", "rt_thm", f'import Init\n#eval show IO Unit from IO.FS.writeFile "{pwn_marker_tmp}" "x"\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n', False),
            # Writing into read-only service dir raises EROFS inside bwrap -> REJECTED + no host file
            ("eval_svc_write", "rt_thm", f'import Init\n#eval show IO Unit from IO.FS.writeFile "{pwn_marker_ro}" "x"\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n', True),
            ("path_traversal_thm", "../../etc/passwd", "import Init\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n", True),
            ("null_byte_thm", "rt_thm\x00evil", "import Init\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n", True),
        ]
        cheat_fails = []
        for label, thm, src, must_reject in cheats:
            req = urllib.request.Request(
                f"http://{host}:{port}/v1/verify",
                data=json.dumps({"theorem": thm, "source": src}).encode(),
                headers={"Content-Type": "application/json", "Authorization": "Bearer secret-test-token-xyz"},
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=60) as r:
                d = json.loads(r.read().decode())
            if must_reject and (d.get("accepted") is True or d.get("verdict") == "ACCEPTED" or d.get("reward") != 0.0):
                cheat_fails.append((label, d))
        if not cheat_fails and not os.path.exists(pwn_marker_tmp) and not os.path.exists(pwn_marker_ro):
            ok(f"HTTP cheat/injection suite: 0/{sum(1 for x in cheats if x[3])} false accepts, 0 host writes")
        else:
            fail(f"CRITICAL HTTP cheat failure: {cheat_fails}, tmp={os.path.exists(pwn_marker_tmp)}, ro={os.path.exists(pwn_marker_ro)}")

        # ---- HTTP check 6b: Cross-problem theorem-inference reward hacking defense
        # 1) Default fvapi MUST refuse omitted 'theorem' (cannot infer 'rt_thm' for custom_id 'hard_other')
        req_no_thm = urllib.request.Request(
            f"http://{host}:{port}/api/check",
            data=json.dumps({
                "pset": "rt",
                "codes": [{
                    "custom_id": "hard_other",
                    "proof": "import Init\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n",
                }],
            }).encode(),
            headers={"Content-Type": "application/json", "Authorization": "Bearer secret-test-token-xyz"},
            method="POST",
        )
        with urllib.request.urlopen(req_no_thm, timeout=30) as r:
            d_nt = json.loads(r.read().decode())
        item_nt = d_nt["results"][0]
        # 2) Test --experimental-theorem-inference (formerly --allow-theorem-inference) refuses multi-theorem snippets as NO-VERDICT ('ambiguous')
        #    and --custom-id-is-theorem binds theorem:=custom_id (rejecting renamed easy proof!)
        api_inf_log = os.path.join(w, "api_inf.log")
        api_inf_p = subprocess.Popen(
            ["/usr/bin/python3", "-I", os.path.join(FV_ROOT, "tools", "http", "fvapi.py"),
             "--fvserve-state", svc_state, "--default-pset", "rt",
             "--host", "127.0.0.1", "--port", "0", "--experimental-theorem-inference"],   # (renamed, EXPERIMENTAL)
            stdout=open(api_inf_log, "wb"), stderr=subprocess.STDOUT,
        )
        api_cid_log = os.path.join(w, "api_cid.log")
        api_cid_p = subprocess.Popen(
            ["/usr/bin/python3", "-I", os.path.join(FV_ROOT, "tools", "http", "fvapi.py"),
             "--fvserve-state", svc_state, "--default-pset", "rt",
             "--host", "127.0.0.1", "--port", "0", "--custom-id-is-theorem"],
            stdout=open(api_cid_log, "wb"), stderr=subprocess.STDOUT,
        )
        try:
            for lg in (api_inf_log, api_cid_log):
                for _ in range(40):
                    if os.path.isfile(lg) and b'"ready"' in open(lg, "rb").read():
                        break
                    time.sleep(0.1)
            inf_url = json.loads(open(api_inf_log).read().splitlines()[0])["url"]
            cid_url = json.loads(open(api_cid_log).read().splitlines()[0])["url"]
            # Ambiguous 2-theorem snippet under --allow-theorem-inference -> NO-VERDICT, reward=0.0
            r_amb = json.loads(urllib.request.urlopen(urllib.request.Request(
                inf_url + "/api/check",
                data=json.dumps({"pset": "rt", "codes": [{
                    "custom_id": "amb1",
                    "proof": "import Init\ntheorem helper_x : True := trivial\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n",
                }]}).encode(),
                headers={"Content-Type": "application/json"}, method="POST",
            ), timeout=30).read().decode())["results"][0]
            # Wrong custom_id under --custom-id-is-theorem -> REJECTED, reward=0.0 (never verifies rt_thm!)
            r_cid_bad = json.loads(urllib.request.urlopen(urllib.request.Request(
                cid_url + "/api/check",
                data=json.dumps({"pset": "rt", "codes": [{
                    "custom_id": "hard_other",
                    "proof": "import Init\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n",
                }]}).encode(),
                headers={"Content-Type": "application/json"}, method="POST",
            ), timeout=30).read().decode())["results"][0]
            # Matching custom_id under --custom-id-is-theorem -> ACCEPTED, echoes theorem='rt_thm'
            r_cid_ok = json.loads(urllib.request.urlopen(urllib.request.Request(
                cid_url + "/api/check",
                data=json.dumps({"pset": "rt", "codes": [{
                    "custom_id": "rt_thm",
                    "proof": "import Init\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n",
                }]}).encode(),
                headers={"Content-Type": "application/json"}, method="POST",
            ), timeout=30).read().decode())["results"][0]
            f2_conds = [
                # an unresolved target is NO-VERDICT with trust 'none' (no check ran), never
                # REJECTED with the 'sound' label
                item_nt["is_pass"] is False and item_nt["reward"] == 0.0 and item_nt["verdict"] == "NO-VERDICT" and item_nt["trust"] == "none",
                r_amb["is_pass"] is False and r_amb["reward"] == 0.0 and r_amb["verdict"] == "NO-VERDICT" and "ambiguous" in r_amb["reason"],
                r_cid_bad["is_pass"] is False and r_cid_bad["reward"] == 0.0 and r_cid_bad["theorem"] == "hard_other",
                r_cid_ok["is_pass"] is True and r_cid_ok["reward"] == 1.0 and r_cid_ok["theorem"] == "rt_thm",
            ]
            if all(f2_conds):
                ok("HTTP theorem-binding: default refuses omitted theorem, --custom-id-is-theorem blocks cross-problem reward hack, --allow-theorem-inference refuses ambiguous multi-theorem")
            else:
                fail(f"HTTP theorem-binding failed: {f2_conds} -> {(item_nt, r_amb, r_cid_bad, r_cid_ok)}")
        finally:
            for p_x in (api_inf_p, api_cid_p):
                p_x.terminate()
                try:
                    p_x.wait(3)
                except Exception:
                    p_x.kill()

        # ---- MCP check 7: --allow-root path traversal & symlink escape
        allowed_dir = os.path.join(w, "allowed")
        secret_dir = os.path.join(w, "outside_secret")
        os.makedirs(allowed_dir); os.makedirs(secret_dir)
        secret_file = os.path.join(secret_dir, "secret.lean")
        open(secret_file, "w").write("theorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n")
        symlink_escape = os.path.join(allowed_dir, "escape.lean")
        os.symlink(secret_file, symlink_escape)

        mcp_bin = os.path.join(FV_ROOT, "tools", "mcp", "fastverify-mcp")
        mcp_reqs = [
            {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
            {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_verify_attempt", "arguments": {"theorem": "rt_thm", "source_file": os.path.join(allowed_dir, "..", "outside_secret", "secret.lean")}}},
            {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "fv_verify_attempt", "arguments": {"theorem": "rt_thm", "source_file": symlink_escape}}},
            {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
                "export_file": os.path.join(pinned, "challenge.export"),
                "challenge_export": os.path.join(pinned, "challenge.export"),
                "comparator_json": os.path.join(pinned, "comparator.json"),
                "challenge_sha256": "0" * 64,
            }}},
            {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {"name": "nonexistent_tool", "arguments": {}}},
            {"jsonrpc": "2.0", "id": 6, "method": "bogus/method", "params": {}},
        ]
        raw_in = "".join(json.dumps(r) + "\n" for r in mcp_reqs).encode() + b"{broken json line\n"
        mp = subprocess.run([mcp_bin, "--fvserve-state", svc_state, "--default-pset", "rt",
                             "--allow-root", allowed_dir, "--allow-root", pinned],
                            input=raw_in, capture_output=True, timeout=60)
        lines = [json.loads(l) for l in mp.stdout.decode().splitlines() if l.strip()]
        by_id = {r.get("id"): r for r in lines if r.get("id") is not None}
        parse_errs = [r for r in lines if r.get("error", {}).get("code") == -32700]
        conds = [
            by_id[2]["result"]["isError"] is True and "outside allowed" in json.dumps(by_id[2]),
            by_id[3]["result"]["isError"] is True and "outside allowed" in json.dumps(by_id[3]),
            by_id[4]["result"]["structuredContent"]["verdict"] == "ERROR" and by_id[4]["result"]["structuredContent"]["reward"] == 0.0,
            by_id[5]["error"]["code"] == -32602,
            by_id[6]["error"]["code"] == -32601,
            len(parse_errs) == 1,
        ]
        if all(conds):
            ok("MCP path and pin checks: traversal refused, symlink escape refused, wrong pin ERROR, unknown tool/method/JSON errors")
        else:
            fail(f"MCP path and pin checks failed: {conds} -> {lines}")

        # ---- MCP check 7b: fv_verify_project timeout kills entire process tree (0 orphans!)
        import hashlib
        cfg_pin = hashlib.sha256(open(os.path.join(pinned, "comparator.json"), "rb").read()).hexdigest()
        slow_proj = os.path.join(w, f"slow_proj_d07f5_{os.getpid()}")
        shutil.copytree(chal_src, slow_proj)
        mcp_tmo_reqs = [
            {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
            {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_verify_project", "arguments": {
                "project_dir": slow_proj, "challenge_dir": pinned, "challenge_sha256": pin,
                "comparator_sha256": cfg_pin, "build_option": "B0", "timeout": 1.0,
            }}},
        ]
        mp_tmo = subprocess.run(
            [mcp_bin, "--allow-root", w],
            input="".join(json.dumps(r) + "\n" for r in mcp_tmo_reqs).encode(),
            capture_output=True, timeout=30,
        )
        tmo_lines = [json.loads(l) for l in mp_tmo.stdout.decode().splitlines() if l.strip()]
        tmo_sc = next((r["result"]["structuredContent"] for r in tmo_lines if r.get("id") == 2), {})
        time.sleep(1.5)
        orphans = []
        for pid_s in os.listdir("/proc"):
            if not pid_s.isdigit():
                continue
            try:
                cl = open(f"/proc/{pid_s}/cmdline", "rb").read().replace(b"\0", b" ").decode(errors="replace")
            except OSError:
                continue
            if slow_proj in cl and int(pid_s) != os.getpid():
                orphans.append((int(pid_s), cl[:100]))
        if tmo_sc.get("verdict") == "NO-VERDICT" and tmo_sc.get("reward") == 0.0 and not orphans:
            ok("MCP timeout containment: fv_verify_project returned NO-VERDICT (reward=0.0) with 0 orphaned descendants")
        else:
            fail(f"MCP timeout containment failed: sc={tmo_sc}, orphans={orphans}")

        # ---- MCP check 7c: forged comparator.json (adding sorryAx to permitted_axioms) MUST NOT get ACCEPTED!
        forged_dir = os.path.join(allowed_dir, "forged_chal")
        os.makedirs(forged_dir, exist_ok=True)
        shutil.copyfile(os.path.join(pinned, "challenge.export"), os.path.join(forged_dir, "challenge.export"))
        forged_cfg = json.load(open(os.path.join(pinned, "comparator.json"), encoding="utf-8"))
        forged_cfg["permitted_axioms"] = list(forged_cfg.get("permitted_axioms") or []) + ["sorryAx"]
        forged_cfg_p = os.path.join(forged_dir, "comparator.json")
        open(forged_cfg_p, "w", encoding="utf-8").write(json.dumps(forged_cfg, indent=2) + "\n")
        # Attempt 1: fv_check_export with real challenge_sha256 + forged comparator.json + NO comparator_sha256 -> ERROR!
        # Attempt 2: fv_check_export with real challenge_sha256 + real comparator_sha256 + forged comparator.json -> ERROR!
        # Attempt 3: fv_verify_project with forged challenge_dir + real challenge_sha256 + NO comparator_sha256 -> ERROR!
        # Attempt 4: operator-registered --challenge rt=<pinned> rejects sorry export (challenge.export itself has sorryAx!)
        forged_reqs = [
            {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
            {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
                "export_file": os.path.join(forged_dir, "challenge.export"),
                "challenge_export": os.path.join(forged_dir, "challenge.export"),
                "comparator_json": forged_cfg_p,
                "challenge_sha256": pin,
            }}},
            {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
                "export_file": os.path.join(forged_dir, "challenge.export"),
                "challenge_export": os.path.join(forged_dir, "challenge.export"),
                "comparator_json": forged_cfg_p,
                "challenge_sha256": pin,
                "comparator_sha256": cfg_pin,
            }}},
            {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {"name": "fv_verify_project", "arguments": {
                "project_dir": chal_src,
                "challenge_dir": forged_dir,
                "challenge_sha256": pin,
            }}},
            {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
                "export_file": os.path.join(forged_dir, "challenge.export"),
                "challenge_id": "rt_pinned",
            }}},
        ]
        mp_d06 = subprocess.run(
            [mcp_bin, "--allow-root", w, "--challenge", f"rt_pinned={pinned}:{pin}:{cfg_pin}"],
            input="".join(json.dumps(r) + "\n" for r in forged_reqs).encode(),
            capture_output=True, timeout=60,
        )
        forged_by = {r.get("id"): r["result"]["structuredContent"]
                  for r in (json.loads(l) for l in mp_d06.stdout.decode().splitlines() if l.strip())
                  if r.get("id") in (2, 3, 4, 5)}
        forged_conds = [
            forged_by.get(2, {}).get("verdict") == "ERROR" and forged_by.get(2, {}).get("reward") == 0.0 and "comparator_sha256" in forged_by.get(2, {}).get("reason", ""),
            forged_by.get(3, {}).get("verdict") == "ERROR" and forged_by.get(3, {}).get("reward") == 0.0 and "mismatch" in forged_by.get(3, {}).get("reason", ""),
            forged_by.get(4, {}).get("verdict") == "ERROR" and forged_by.get(4, {}).get("reward") == 0.0 and "comparator_sha256" in forged_by.get(4, {}).get("reason", ""),
            forged_by.get(5, {}).get("verdict") == "REJECTED" and forged_by.get(5, {}).get("accepted") is False and forged_by.get(5, {}).get("reward") == 0.0,
        ]
        if all(forged_conds):
            ok("MCP forged comparator.json defense: unpinned/mismatched comparator refused (ERROR, reward=0.0) and --challenge registry rejects sorryAx")
        else:
            fail(f"MCP forged comparator.json defense failed: conds={forged_conds} -> {forged_by}")

        # ---- MCP check 7d: arbitrary caller-supplied pins file rejected in BOTH fv_check_export and fv_verify_project
        evil_pins = os.path.join(allowed_dir, "evil.env")
        open(evil_pins, "w").write("PIN ccmp 0000 /bin/true\n")
        b4_reqs = [
            {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
            {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
                "export_file": os.path.join(forged_dir, "challenge.export"),
                "challenge_id": "rt_pinned",
                "pins": evil_pins,
            }}},
            {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "fv_verify_project", "arguments": {
                "project_dir": chal_src,
                "challenge_id": "rt_pinned",
                "pins": evil_pins,
            }}},
        ]
        mp_b4 = subprocess.run(
            [mcp_bin, "--allow-root", w, "--challenge", f"rt_pinned={pinned}:{pin}:{cfg_pin}"],
            input="".join(json.dumps(r) + "\n" for r in b4_reqs).encode(),
            capture_output=True, timeout=30,
        )
        b4_by = {r.get("id"): r["result"] for r in (json.loads(l) for l in mp_b4.stdout.decode().splitlines() if l.strip()) if r.get("id") in (2, 3)}
        b4_sc2 = (b4_by.get(2) or {}).get("structuredContent") or {}
        b4_sc3 = (b4_by.get(3) or {}).get("structuredContent") or {}
        if (b4_sc2.get("verdict") == "ERROR" and b4_sc2.get("reward") == 0.0 and "B4" in b4_sc2.get("reason", "")
                and b4_sc3.get("verdict") == "ERROR" and b4_sc3.get("reward") == 0.0 and "B4" in b4_sc3.get("reason", "")):
            ok("MCP pins defense: caller-supplied arbitrary pins path refused in fv_check_export & fv_verify_project (ERROR, reward=0.0)")
        else:
            fail(f"MCP pins defense failed: {b4_by}")

        # ---- HTTP check 7e: unauthenticated half-open TCP socket flood bounded by --max-connections
        f4_p = subprocess.Popen(
            ["/usr/bin/python3", "-I", os.path.join(FV_ROOT, "tools", "http", "fvapi.py"),
             "--fvserve-state", svc_state, "--default-pset", "rt",
             "--host", "127.0.0.1", "--port", "0", "--max-concurrent", "4", "--max-connections", "10",
             "--socket-timeout", "1.5"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        f4_socks = []
        try:
            f4_ready = json.loads(f4_p.stdout.readline())
            f4_port = f4_ready["port"]
            got_503 = 0
            for _ in range(50):
                s = socket.create_connection(("127.0.0.1", f4_port), timeout=2.0)
                f4_socks.append(s)
            time.sleep(0.3)
            threads_n = 0
            for ln in open(f"/proc/{f4_p.pid}/status"):
                if ln.startswith("Threads:"):
                    threads_n = int(ln.split()[1])
            for s in f4_socks:
                s.settimeout(0.1)
                try:
                    buf = s.recv(256)
                    if b"503 Service Unavailable" in buf:
                        got_503 += 1
                except (socket.timeout, OSError):
                    pass
            for s in f4_socks:
                try:
                    s.close()
                except OSError:
                    pass
            f4_socks.clear()
            time.sleep(0.3)
            hc, hb = raw_http("127.0.0.1", f4_port, b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n")
            if threads_n <= 24 and got_503 >= 30 and hc == 200:
                ok(f"HTTP connection cap: 50 half-open sockets -> Threads={threads_n} (<=24), 503-dropped={got_503}, recovered /health=200")
            else:
                fail(f"HTTP connection cap failed: threads={threads_n}, got_503={got_503}, health={hc} {hb[:120]}")
        finally:
            for s in f4_socks:
                try:
                    s.close()
                except OSError:
                    pass
            f4_p.terminate()
            try:
                f4_p.wait(3)
            except Exception:
                f4_p.kill()

        # ---- HTTP check 7f: Trickle-byte header & body slowloris cannot pin --max-connections slots
        f12_log = os.path.join(w, "api_f12.log")
        f12_p = subprocess.Popen(
            ["/usr/bin/python3", "-I", os.path.join(FV_ROOT, "tools", "http", "fvapi.py"),
             "--fvserve-state", svc_state, "--default-pset", "rt",
             "--host", "127.0.0.1", "--port", "0", "--max-concurrent", "4",
             "--max-connections", "8", "--socket-timeout", "10",
             "--header-timeout", "1.5", "--body-timeout", "1.5"],
            stdout=open(f12_log, "wb"), stderr=subprocess.STDOUT,
        )
        f12_socks = []
        try:
            for _ in range(40):
                if os.path.isfile(f12_log) and b'"ready"' in open(f12_log, "rb").read():
                    break
                time.sleep(0.1)
            f12_port = json.loads(open(f12_log).read().splitlines()[0])["port"]
            # Open 10 trickling-header sockets (exceeds --max-connections=8) sending 1 byte every 0.4s (< socket-timeout=10s)
            for _ in range(10):
                s = socket.create_connection(("127.0.0.1", f12_port), timeout=2.0)
                s.sendall(b"G")
                f12_socks.append(s)
            # Keep trickling past --header-timeout=1.5s without closing sockets
            t_start = time.time()
            while time.time() - t_start < 2.6:
                for s in f12_socks:
                    try:
                        s.sendall(b"E")
                    except OSError:
                        pass
                time.sleep(0.4)
            # Even while attacker holds all 10 sockets open, header_timeout MUST have evicted them -> /health=200!
            hc_hdr, hb_hdr = raw_http("127.0.0.1", f12_port, b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n")
            # Also verify trickle-body slowloris is evicted by --body-timeout=1.5s
            b_socks = []
            for _ in range(10):
                s = socket.create_connection(("127.0.0.1", f12_port), timeout=2.0)
                s.sendall(b"POST /v1/verify HTTP/1.1\r\nHost: x\r\nContent-Length: 500\r\n\r\n{")
                b_socks.append(s)
            t_b = time.time()
            while time.time() - t_b < 2.6:
                for s in b_socks:
                    try:
                        s.sendall(b" ")
                    except OSError:
                        pass
                time.sleep(0.4)
            hc_body, hb_body = raw_http("127.0.0.1", f12_port, b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n")
            f12_socks.extend(b_socks)
            if hc_hdr == 200 and hc_body == 200:
                ok("HTTP slowloris total deadlines: 10 trickle-header & 10 trickle-body sockets evicted within 1.5s -> /health=200")
            else:
                fail(f"HTTP slowloris total deadlines failed: hc_hdr={hc_hdr} ({hb_hdr[:80]}), hc_body={hc_body} ({hb_body[:80]})")
        finally:
            for s in f12_socks:
                try:
                    s.close()
                except OSError:
                    pass
            f12_p.terminate()
            try:
                f12_p.wait(3)
            except Exception:
                f12_p.kill()

        # ---- Triage check 8: hostile #eval IO.FS.writeFile inside sub-lemma cannot escape bwrap
        triage_pwn = os.path.join(w, "TRIAGE_PWNED")
        hostile_sub = os.path.join(w, "hostile_sub.lean")
        open(hostile_sub, "w").write(
            f'#eval show IO Unit from IO.FS.writeFile "{triage_pwn}" "pwned"\n'
            f"theorem good_sub (n : Nat) : n + 0 = n := by sorry\n"
        )
        subprocess.run([os.path.join(FV_ROOT, "bin", "fv"), "triage", hostile_sub,
                        "--toolchain", TC, "--packages", empty_ws, "--json"],
                       capture_output=True, text=True, timeout=60)
        if not os.path.exists(triage_pwn):
            ok("Triage sandbox: hostile #eval write blocked by bwrap")
        else:
            fail("CRITICAL: triage sandbox escape!")

        # ---- HTTP check 9: backend dead -> fail-closed NO-VERDICT + reward=0.0 (never ACCEPTED!)
        subprocess.run(["/usr/bin/python3", "-I", os.path.join(FV_ROOT, "tools", "fvserve", "fvserve.py"),
                        "stop", "--state", svc_state], capture_output=True, timeout=15)
        time.sleep(1.5)
        req = urllib.request.Request(
            f"http://{host}:{port}/v1/verify",
            data=json.dumps({"theorem": "rt_thm", "source": "import Init\ntheorem rt_thm : ∀ n : Nat, n + 0 = n := by intro n; exact Nat.add_zero n\n"}).encode(),
            headers={"Content-Type": "application/json", "Authorization": "Bearer secret-test-token-xyz"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=15) as r:
            dead_d = json.loads(r.read().decode())
        # Also verify /health reports 503 degraded
        h_code, _ = raw_http(host, port, b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n")
        if dead_d["verdict"] == "NO-VERDICT" and dead_d["accepted"] is False and dead_d["reward"] == 0.0 and h_code == 503:
            ok("HTTP backend-down fail-closed: NO-VERDICT, accepted=False, reward=0.0, /health=503")
        else:
            fail(f"HTTP backend-down unexpected: {dead_d}, health={h_code}")

    finally:
        for p in (api_p, svc_p):
            if p is not None:
                try:
                    p.terminate()
                    p.wait(5)
                except Exception:
                    try:
                        p.kill()
                    except Exception:
                        pass
        shutil.rmtree(w, ignore_errors=True)

    print("RESULT PASS" if bad == 0 else "RESULT FAIL")
    return bad


if __name__ == "__main__":
    sys.exit(run_all())
