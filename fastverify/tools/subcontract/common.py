#!/usr/bin/python3 -I
"""Shared utilities for fastverify/tools/subcontract.

Zero-trust Day 1-99 collaboration primitives:
  - sandboxed bwrap command builders (S4: untrusted code never runs unsandboxed or with network)
  - Lean 4 declaration locator & safe proof-body splicer
  - atomic JSON persistence & SHA-256 helpers
  - progress ledger schema helpers
"""
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import tempfile
import time

FASTVERIFY_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
BWRAP = "/usr/bin/bwrap"
PY = "/usr/bin/python3"

# Lean 4.36 Lake/CLI/Check.lean primitiveTargets (verbatim order)
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
    "Nat", "String", "String.mk", "Char", "optParam", "autoParam",
    "semiOutParam", "outParam",
]


def now_iso():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 20)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def sha256_str(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def atomic_write_json(path, obj):
    os.makedirs(os.path.dirname(os.path.realpath(path)), exist_ok=True)
    tmp = f"{path}.tmp.{os.getpid()}.{time.time_ns()}"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2, ensure_ascii=False)
        f.write("\n")
    os.replace(tmp, path)


# ---------------------------------------------------------------------------------------------------------------------
# paths inside a work tree. A source path comes ONLY from the dispatcher's manifest (never from a
# subproof / submission JSON); it is a relative path whose components are not empty / '.' / '..' and hold no control
# character, opened component by component from the tree root with O_NOFOLLOW (no symlink anywhere below the root, none
# followed if swapped in later), and written by an atomic rename inside its own directory (never through a symlink or a
# hard link). A module file's path and its module name determine each other (no '.' inside a component).
# ---------------------------------------------------------------------------------------------------------------------
_CTRL_RE = re.compile(r"[\x00-\x1f\x7f]")
_DIR_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC


class PathRefused(ValueError):
    """a path outside the confinement rules above (no file was read or written)"""


def safe_relpath(rel):
    """components of a confined relative path, or PathRefused"""
    if not isinstance(rel, str) or not rel or rel.startswith("/") or _CTRL_RE.search(rel):
        raise PathRefused("path %r is not a relative path without control characters" % (rel,))
    try:
        rel.encode("utf-8")
    except UnicodeEncodeError:
        raise PathRefused("path %r is not valid UTF-8 (lone surrogate)" % (rel,))
    comps = rel.split("/")
    if any(c in ("", ".", "..") for c in comps):
        raise PathRefused("path %r has an empty, '.' or '..' component" % (rel,))
    return comps


def module_of_relpath(rel):
    """the Lean module of a module file path (A/B/C.lean -> A.B.C), or PathRefused"""
    comps = safe_relpath(rel)
    if not comps[-1].endswith(".lean"):
        raise PathRefused("path %r is not a .lean module file" % (rel,))
    stem = comps[:-1] + [comps[-1][:-5]]
    if any(not c or "." in c for c in stem):
        raise PathRefused("path %r does not name a module (empty or dotted component)" % (rel,))
    return ".".join(stem)


def open_dir_nofollow(root, comps, create=False):
    """fd of root/comps[0]/.../comps[-1]: every directory opened with O_NOFOLLOW below the real directory `root` (itself
    not a symlink); with create=True missing directories are made (0755). The caller closes the fd."""
    try:
        fd = os.open(root, _DIR_FLAGS)
    except OSError as e:
        raise PathRefused("tree root %r is not a real directory: %s" % (root, e))
    try:
        for c in comps:
            if c in ("", ".", "..") or "/" in c or _CTRL_RE.search(c):
                raise PathRefused("bad path component %r" % (c,))
            try:
                nfd = os.open(c, _DIR_FLAGS, dir_fd=fd)
            except FileNotFoundError:
                if not create:
                    raise PathRefused("directory %r missing below %r" % (c, root))
                try:
                    os.mkdir(c, 0o755, dir_fd=fd)
                    nfd = os.open(c, _DIR_FLAGS, dir_fd=fd)
                except OSError as e:   # (r2) a race / a non-directory swapped in: refused, never a raw error
                    raise PathRefused("cannot create the directory %r below %r: %s" % (c, root, e))
            except OSError as e:   # ELOOP / ENOTDIR: a symlink or a non-directory
                raise PathRefused("%r below %r is not a real directory: %s" % (c, root, e))
            os.close(fd)
            fd = nfd
        return fd
    except BaseException:
        os.close(fd)
        raise


def read_text_under(root, rel, max_bytes=1 << 26):
    """UTF-8 text of root/rel: a regular file reached without following any symlink"""
    comps = safe_relpath(rel)
    dfd = open_dir_nofollow(root, comps[:-1])
    try:
        try:
            fd = os.open(comps[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC, dir_fd=dfd)
        except OSError as e:
            raise PathRefused("cannot open %r without following a symlink: %s" % (rel, e))
        try:   # (r2) checked on the fd BEFORE fdopen: a directory / FIFO is a refusal (fd closed), never a raw error
            if not stat.S_ISREG(os.fstat(fd).st_mode):
                raise PathRefused("%r is not a regular file" % (rel,))
            f = os.fdopen(fd, "rb")
        except BaseException:
            os.close(fd)
            raise
        with f:
            try:
                data = f.read(max_bytes + 1)
            except OSError as e:
                raise PathRefused("cannot read %r: %s" % (rel, e))
    finally:
        os.close(dfd)
    if len(data) > max_bytes:
        raise PathRefused("%r is larger than %d bytes" % (rel, max_bytes))
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        raise PathRefused("%r is not UTF-8 text" % (rel,))


def write_text_under(root, rel, text, create_dirs=False):
    """replace root/rel by `text` atomically: a fresh temp file (O_EXCL|O_NOFOLLOW) in the same no-symlink directory,
    renamed over the entry, which may only be absent or a regular file. Never writes through a symlink or a hard link."""
    comps = safe_relpath(rel)
    if not isinstance(text, str):
        raise PathRefused("content for %r is not text" % (rel,))
    try:
        data = text.encode("utf-8")
    except UnicodeEncodeError:
        raise PathRefused("content for %r is not valid UTF-8 (lone surrogate)" % (rel,))
    dfd = open_dir_nofollow(root, comps[:-1], create=create_dirs)
    try:
        mode = 0o644
        try:
            st = os.stat(comps[-1], dir_fd=dfd, follow_symlinks=False)
            if not stat.S_ISREG(st.st_mode):
                raise PathRefused("%r exists and is not a regular file" % (rel,))
            mode = stat.S_IMODE(st.st_mode)
        except FileNotFoundError:
            pass
        tmp = ".fv-subcontract-%d-%d.tmp" % (os.getpid(), time.time_ns())
        fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600, dir_fd=dfd)
        try:
            with os.fdopen(fd, "wb") as f:
                f.write(data)
                os.fchmod(f.fileno(), mode)
            os.rename(tmp, comps[-1], src_dir_fd=dfd, dst_dir_fd=dfd)
        except BaseException:
            try:
                os.unlink(tmp, dir_fd=dfd)
            except OSError:
                pass
            raise
    finally:
        os.close(dfd)


def safe_id(name):
    """Turn a Lean constant name into a safe, collision-free filesystem directory name."""
    s = re.sub(r"[^A-Za-z0-9._-]", "_", name)
    if not s or s in (".", ".."):
        s = "decl"
    if s != name:
        s = f"{s[:100]}_{sha256_str(name)[:8]}"
    elif len(s) > 120:
        s = s[:100] + "_" + sha256_str(name)[:12]
    return s


def load_components(fv_root=FASTVERIFY_ROOT):
    cfg_path = os.path.join(fv_root, "config", "components.json")
    with open(cfg_path, encoding="utf-8") as f:
        return json.load(f)


def resolve_toolchain_for_project(project_dir, fv_root=FASTVERIFY_ROOT):
    """only a toolchain registered in config/components.json, verified like bin/fastverify does
    (lib/toolchain.py verify: the whole tree against its pinned manifest); no unverified ~/.elan fallback"""
    tc_file = os.path.join(project_dir, "lean-toolchain")
    tc_spec = open(tc_file, encoding="utf-8").read().strip() if os.path.exists(tc_file) else "leanprover/lean4:v4.33.1"
    cfg = load_components(fv_root)
    tcs = cfg.get("lean_toolchains") or {}
    prefix = None
    if tc_spec in tcs and os.path.isdir(tcs[tc_spec].get("prefix", "")):
        prefix = tcs[tc_spec]["prefix"]
    elif tc_spec == cfg.get("comparator", {}).get("id") and os.path.isdir(cfg["comparator"].get("prefix", "")):
        prefix = cfg["comparator"]["prefix"]
    if prefix is None:
        raise RuntimeError(f"toolchain {tc_spec!r} is not a registered official toolchain (config/components.json)")
    r = subprocess.run(["/usr/bin/python3", "-I", os.path.join(fv_root, "lib", "toolchain.py"), "verify", prefix, tc_spec],
                       capture_output=True, text=True, env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"}, timeout=900)
    if r.returncode != 0:
        raise RuntimeError(f"toolchain {tc_spec} at {prefix} does not verify against its pinned manifest: "
                           f"{(r.stderr or r.stdout).strip()[-300:]}")
    return prefix, tc_spec


def resolve_official_exporter(tc_spec, tc_prefix, fv_root=FASTVERIFY_ROOT):
    """only the registered official exporter whose sha256 matches config/components.json"""
    cfg = load_components(fv_root)
    tcs = cfg.get("lean_toolchains") or {}
    e = (tcs.get(tc_spec) or {}).get("official_lean4export") or {}
    p, want = e.get("path"), e.get("sha256")
    if not p or not want or not os.path.isfile(p):
        raise RuntimeError(f"no registered official exporter for {tc_spec} (config/components.json official_lean4export)")
    if sha256_file(p) != want:
        raise RuntimeError(f"official exporter {p} sha256 differs from config/components.json")
    return p


def collect_lean_path(build_tree, packages_ws=None):
    """Build LEAN_PATH from a compiled Lake build tree + trusted packages workspace."""
    roots = []
    proj_lib = os.path.join(build_tree, ".lake", "build", "lib", "lean")
    if os.path.isdir(proj_lib):
        roots.append(proj_lib)
    proj_lib_old = os.path.join(build_tree, ".lake", "build", "lib")
    if os.path.isdir(proj_lib_old) and proj_lib_old not in roots:
        roots.append(proj_lib_old)
    if packages_ws:
        pkg_root = os.path.join(packages_ws, ".lake", "packages")
        if os.path.isdir(pkg_root):
            for name in sorted(os.listdir(pkg_root)):
                p = os.path.join(pkg_root, name)
                for sub in (".lake/build/lib/lean", ".lake/build/lib", "build/lib/lean", "build/lib"):
                    cand = os.path.join(p, sub)
                    if os.path.isdir(cand) and cand not in roots:
                        roots.append(cand)
                        break
    return ":".join(roots)


def run_bwrap(argv, ro_binds=(), rw_binds=(), env_extra=None, cwd=None, timeout=120):
    """Run argv inside a network-less bwrap sandbox (S4 compliant)."""
    cmd = [
        BWRAP, "--unshare-all", "--die-with-parent", "--new-session",
        "--ro-bind", "/", "/",
        "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/run", "--tmpfs", "/tmp",
        "--dev", "/dev", "--proc", "/proc",
    ]
    seen_ro = set()
    for p in ro_binds:
        if not p:
            continue
        rp = os.path.realpath(p)
        if rp not in seen_ro:
            cmd += ["--ro-bind", rp, rp]
            if p != rp and os.path.exists(p):
                cmd += ["--ro-bind", p, p]
            seen_ro.add(rp)
    seen_rw = set()
    for p in rw_binds:
        if not p:
            continue
        rp = os.path.realpath(p)
        if rp not in seen_rw:
            cmd += ["--bind", rp, rp]
            if p != rp and os.path.exists(p):
                cmd += ["--bind", p, p]
            seen_rw.add(rp)
    if cwd:
        cmd += ["--chdir", cwd]
    cmd += [
        "--clearenv",
        "--setenv", "LANG", "C.UTF-8",
        "--setenv", "LEAN_ABORT_ON_PANIC", "1",
    ]
    if env_extra:
        for k, v in env_extra.items():
            cmd += ["--setenv", k, str(v)]
    cmd += ["--"] + list(argv)
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
        return p.returncode, p.stdout.decode("utf-8", errors="replace"), p.stderr.decode("utf-8", errors="replace"), round(time.monotonic() - t0, 3)
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode("utf-8", errors="replace")
        err = (e.stderr or b"").decode("utf-8", errors="replace")
        return 124, out, err + f"\n[timeout after {timeout}s]", round(time.monotonic() - t0, 3)


def strip_comments_preserving_lines(src):
    """Replace Lean comments (-- ... and /- ... -/) with spaces, preserving newlines & byte offsets."""
    out = list(src)
    n = len(src)
    i = 0
    depth = 0
    in_str = False
    while i < n:
        c = src[i]
        if depth > 0:
            if c == "/" and i + 1 < n and src[i + 1] == "-":
                out[i] = " "; out[i + 1] = " "
                depth += 1; i += 2
            elif c == "-" and i + 1 < n and src[i + 1] == "/":
                out[i] = " "; out[i + 1] = " "
                depth -= 1; i += 2
            else:
                if c != "\n":
                    out[i] = " "
                i += 1
        elif in_str:
            if c == "\\" and i + 1 < n:
                i += 2
            elif c == '"':
                in_str = False; i += 1
            else:
                i += 1
        else:
            if c == '"':
                in_str = True; i += 1
            elif c == "-" and i + 1 < n and src[i + 1] == "-":
                while i < n and src[i] != "\n":
                    out[i] = " "; i += 1
            elif c == "/" and i + 1 < n and src[i + 1] == "-":
                out[i] = " "; out[i + 1] = " "
                depth = 1; i += 2
            else:
                i += 1
    return "".join(out)


# Unicode-aware Lean 4 identifier pattern (handles Greek letters, subscripts ₀..₉, superscripts, primes, «guillemets»)
_LEAN_IDENT_PART = r"(?:«[^»]+»|[^\W\d][\w'\u00b2\u00b3\u00b9\u2070-\u209f\u1d62-\u1d6a]*)"
LEAN_IDENT_RE_STR = rf"{_LEAN_IDENT_PART}(?:\.{_LEAN_IDENT_PART})*"

# Top-level declaration starter pattern (at column 0, ignoring leading attributes/modifiers)
_DECL_START_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example|namespace|section|end)\b"
)
_NS_RE = re.compile(rf"^namespace\s+({LEAN_IDENT_RE_STR})")
_END_RE = re.compile(rf"^end(?:\s+({LEAN_IDENT_RE_STR}))?(?:\s|$)")
_THM_NAME_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    rf"(theorem|lemma)\s+({LEAN_IDENT_RE_STR})"
)


def scan_lean_declarations(src):
    """Scan a Lean file into declaration spans, tracking namespace stack.
    Returns list of dicts:
      {kind, short_name, full_name, start_line, end_line, start_idx, end_idx, ns_stack}
    Lines are 1-indexed, end_line inclusive.
    """
    clean = strip_comments_preserving_lines(src)
    lines = src.splitlines(keepends=True)
    clean_lines = clean.splitlines(keepends=True)
    offsets = []
    pos = 0
    for ln in lines:
        offsets.append(pos)
        pos += len(ln)
    offsets.append(pos)

    ns_stack = []
    decls = []
    i = 0
    n = len(lines)
    while i < n:
        cl = clean_lines[i]
        # Track namespace / end
        m_ns = _NS_RE.match(cl)
        if m_ns:
            parts = m_ns.group(1).split(".")
            ns_stack.append(parts)
            i += 1
            continue
        m_end = _END_RE.match(cl)
        if m_end:
            target = m_end.group(1)
            if target and ns_stack:
                tparts = target.split(".")
                if ns_stack[-1] == tparts:
                    ns_stack.pop()
                else:
                    # pop matching suffix if any
                    for k in range(len(ns_stack) - 1, -1, -1):
                        if ns_stack[k] == tparts:
                            del ns_stack[k]
                            break
            elif not target and ns_stack:
                ns_stack.pop()
            i += 1
            continue

        m_thm = _THM_NAME_RE.match(cl)
        if m_thm:
            kind = m_thm.group(1)
            raw_name = m_thm.group(2).replace("«", "").replace("»", "")
            prefix = ".".join(p for grp in ns_stack for p in grp)
            full_name = f"{prefix}.{raw_name}" if prefix else raw_name
            start_i = i
            # Walk back over immediately preceding @[...] attribute lines on own lines
            j = i - 1
            while j >= 0 and clean_lines[j].strip().startswith("@["):
                start_i = j
                j -= 1
            # Find end of declaration: next non-indented top-level command/decl/namespace/end/section/import/open/variable/attribute/set_option/#
            k = i + 1
            while k < n:
                ck = clean_lines[k]
                if ck and not ck[0].isspace():
                    if _DECL_START_RE.match(ck) or re.match(
                        r"^(?:import|open|variable|universe|attribute|set_option|section|end|namespace|#|/--|@\[)",
                        ck,
                    ):
                        break
                k += 1
            # Trim trailing blank lines from decl span
            end_i = k - 1
            while end_i > i and lines[end_i].strip() == "":
                end_i -= 1
            decls.append({
                "kind": kind,
                "short_name": raw_name,
                "full_name": full_name,
                "ns_prefix": prefix,
                "start_line": start_i + 1,
                "end_line": end_i + 1,
                "start_idx": offsets[start_i],
                "end_idx": offsets[end_i + 1],
            })
            i = k
            continue
        i += 1
    return decls


def locate_lemma_in_project(project_dir, full_name):
    """Find the .lean file and declaration span defining `full_name`."""
    candidates = []
    for root, dirs, files in os.walk(project_dir):
        dirs[:] = sorted(d for d in dirs if d not in (".lake", ".git", "__pycache__"))
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            fpath = os.path.join(root, fn)
            rel = os.path.relpath(fpath, project_dir)
            try:
                src = open(fpath, encoding="utf-8").read()
            except OSError:
                continue
            if full_name.split(".")[-1] not in src:
                continue
            for d in scan_lean_declarations(src):
                if d["full_name"] == full_name:
                    d["rel_file"] = rel
                    d["abs_file"] = fpath
                    d["module"] = rel[:-5].replace(os.sep, ".")
                    d["source_text"] = src[d["start_idx"]:d["end_idx"]]
                    d["context_before"] = src[:d["start_idx"]]
                    candidates.append(d)
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        # Prefer exact module prefix match
        for c in candidates:
            if full_name.startswith(c["module"] + "."):
                return c
        return candidates[0]
    return None


def split_theorem_header_and_proof(decl_text):
    """Split a Lean theorem/lemma text into (header_before_assign, proof_rhs) at top-level `:=`.
    Respects parentheses, brackets, braces, strings, comments, and `let ... := ...;` inside types.
    Returns (header, proof) or (None, None) if no top-level `:=` is found.
    """
    clean = strip_comments_preserving_lines(decl_text)
    depth = 0
    in_str = False
    n = len(clean)
    i = 0
    top_assigns = []
    while i < n:
        c = clean[i]
        if in_str:
            if c == "\\" and i + 1 < n:
                i += 2; continue
            if c == '"':
                in_str = False
            i += 1; continue
        if c == '"':
            in_str = True; i += 1; continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and c == ":" and i + 1 < n and clean[i + 1] == "=":
            top_assigns.append(i)
            i += 2; continue
        i += 1
    if not top_assigns:
        return None, None
    # Skip any `:=` that belongs to a `let ... := ...;` inside the theorem's type signature
    for pos in top_assigns:
        before = clean[:pos]
        if re.search(r"\blet\s+[^;]*$", before):
            # Only treat as let-binding inside type if a later `:=` exists after a `;`
            if any(p > pos for p in top_assigns):
                continue
        return decl_text[:pos].rstrip(), decl_text[pos + 2:].strip()
    pos = top_assigns[0]
    return decl_text[:pos].rstrip(), decl_text[pos + 2:].strip()


def extract_lemma_proof_from_submission(submission_text, full_name, short_name=None):
    """Extract the replacement declaration text (plus any auxiliary helper declarations preceding it)
    for `full_name` from a model/agent submission.
    Accepts:
      1. A full Lean file containing `theorem <short_name> ... := ...`
      2. A declaration block (optionally preceded by helper `private lemma`/`def`/`abbrev`/`macro` decls)
      3. Just a proof body starting with `by ...` or `:= ...` (returned with kind='body')
    """
    short = short_name or full_name.split(".")[-1]
    # Try scanning as Lean declarations first
    decls = scan_lean_declarations(submission_text)
    for d in decls:
        if d["full_name"] == full_name or d["short_name"] == short:
            txt = submission_text[d["start_idx"]:d["end_idx"]]
            hdr, prf = split_theorem_header_and_proof(txt)
            if hdr is not None:
                prefix_raw = submission_text[:d["start_idx"]].strip()
                # Preserve auxiliary helper declarations (private lemma/def/abbrev/macro/etc.) before the lemma
                # when the submission is a snippet without `import` statements.
                prefix_block = ""
                if prefix_raw and not re.search(r"^\s*import\s+", submission_text, re.M):
                    clean_pre = strip_comments_preserving_lines(prefix_raw).strip()
                    if clean_pre:
                        # Strip bare leading `namespace ...` / `open ...` only if there is nothing else; keep real helpers
                        pre_lines = [ln for ln in prefix_raw.splitlines() if not re.match(r"^\s*(?:namespace|end)\b", ln)]
                        cand_pre = "\n".join(pre_lines).strip()
                        if strip_comments_preserving_lines(cand_pre).strip():
                            prefix_block = cand_pre
                block_text = f"{prefix_block}\n\n{txt}" if prefix_block else txt
                return {
                    "kind": "decl",
                    "decl_text": txt,
                    "prefix_block": prefix_block,
                    "block_text": block_text,
                    "header": hdr,
                    "proof": prf,
                }
    # Check if submission is a raw proof body
    stripped = submission_text.strip()
    if stripped.startswith(":="):
        return {"kind": "body", "proof": stripped[2:].strip()}
    if stripped.startswith("by ") or stripped.startswith("by\n"):
        return {"kind": "body", "proof": stripped}
    return None


def find_sorry_spans_in_decl(decl_text):
    """Find all `sorry` keyword spans inside the proof body of `decl_text` (ignoring comments/strings).
    Returns list of dicts: {index (1-based), start_idx, end_idx, is_tactic_mode} relative to `decl_text`.
    """
    hdr, _ = split_theorem_header_and_proof(decl_text)
    if hdr is None:
        return []
    clean = strip_comments_preserving_lines(decl_text)
    assign_pos = clean.find(":=", len(hdr))
    if assign_pos == -1:
        return []
    body_start = assign_pos + 2
    body_clean = clean[body_start:]
    # Mask string literals so "sorry" inside strings is ignored
    body_nostr = re.sub(r'"(?:\\.|[^"\\])*"', lambda m: " " * len(m.group(0)), body_clean)
    spans = []
    for k, m in enumerate(re.finditer(r"(?<![\w'.])sorry(?![\w'.])", body_nostr), 1):
        before = body_nostr[:m.start()]
        # Heuristic: inside `by` block if `\bby\b` appears before this sorry after the most recent `:=` or at top of proof
        last_assign = before.rfind(":=")
        seg = before[last_assign + 2:] if last_assign != -1 else before
        is_tactic = bool(re.search(r"\bby\b", seg)) or bool(re.search(r"\bby\b", before[:40]))
        spans.append({
            "index": k,
            "start_idx": body_start + m.start(),
            "end_idx": body_start + m.end(),
            "is_tactic_mode": is_tactic,
        })
    return spans


def _parse_trace_state_block(block_text):
    """Parse Lean 4 `trace_state` output lines into (binders_list, goal_str).
    Each binder in binders_list is a string like `(n : Nat)` or `(h : n < myBound)`.
    """
    raw_lines = [ln.rstrip() for ln in block_text.splitlines() if ln.strip()]
    # Join indented continuation lines onto previous entry
    logical = []
    for ln in raw_lines:
        if ln.startswith("case "):
            continue
        if ln.startswith(" ") and logical:
            logical[-1] += " " + ln.strip()
        else:
            logical.append(ln.strip())

    binders = []
    goal = None
    anon_idx = 0
    for ln in logical:
        if ln.startswith("⊢"):
            goal = ln[1:].strip()
            break
        if " : " not in ln:
            continue
        lhs, rhs = ln.split(" : ", 1)
        # Drop `:= val` on `let` context entries so it binds cleanly as a hypothesis/value
        if " := " in rhs:
            rhs = rhs.split(" := ", 1)[0].strip()
        # Sanitize inaccessible `✝` names into valid binder identifiers
        clean_names = []
        for nm in lhs.strip().split():
            if "✝" in nm or not re.match(rf"^{_LEAN_IDENT_PART}$", nm):
                anon_idx += 1
                clean_names.append(f"_h{anon_idx}")
            else:
                clean_names.append(nm)
        if clean_names and rhs.strip():
            binders.append(f"({' '.join(clean_names)} : {rhs.strip()})")
    return binders, goal


def extract_sketch_subgoals_via_lean(file_src, decl_info, base_tree, packages_ws, tc_prefix, timeout_s=45):
    """Extract clean surface Lean 4 local-context binders + goal for every inline `sorry` inside
    `decl_info` by running Lean `trace_state; sorry` inside a network-less `bwrap --unshare-all`
    sandbox (S4).
    Returns dict keyed by 1-based source order:
      {1: {"binders": [...], "goal": "...", "is_tactic_mode": bool, "line": int, "col": int}, ...}.
    """
    decl_text = file_src[decl_info["start_idx"]:decl_info["end_idx"]]
    spans = find_sorry_spans_in_decl(decl_text)
    if not spans:
        return {}
    # Replace each sorry bottom-to-top with `trace_state; sorry` (no `trace` channel interleaving issues)
    inst_decl = decl_text
    for sp in reversed(spans):
        if sp["is_tactic_mode"]:
            rep = "(trace_state; sorry)"
        else:
            rep = "(by trace_state; sorry)"
        inst_decl = inst_decl[:sp["start_idx"]] + rep + inst_decl[sp["end_idx"]:]
    probe_src = file_src[:decl_info["start_idx"]] + inst_decl + file_src[decl_info["end_idx"]:]

    lean_bin = os.path.join(tc_prefix, "bin", "lean")
    lean_path = collect_lean_path(base_tree, packages_ws)
    with tempfile.TemporaryDirectory(prefix="fv-sketch-pp-") as td:
        pfile = os.path.join(td, "SketchProbe.lean")
        with open(pfile, "w", encoding="utf-8") as f:
            f.write(probe_src)
        rc, out, err, _ = run_bwrap(
            [lean_bin, "-j", "1", pfile],
            ro_binds=[base_tree, packages_ws, tc_prefix, td],
            rw_binds=[],
            env_extra={"PATH": f"{tc_prefix}/bin:/usr/bin:/bin", "LEAN_PATH": lean_path, "HOME": "/tmp", "TMPDIR": "/tmp"},
            cwd=base_tree, timeout=timeout_s,
        )
    combined = out + "\n" + err
    span_by_k = {sp["index"]: sp for sp in spans}

    # Primary parser: Lean emits `/.../SketchProbe.lean:LINE:COL: info:\n<context>\n⊢ <goal>`
    # Sort all `info:` blocks containing `⊢` by (line, col) to recover exact source order 1..K.
    diag_re = re.compile(r"(?m)^(?P<path>/[^:\n]+):(?P<line>\d+):(?P<col>\d+):\s*(?P<sev>[a-z]+):[ \t]*")
    matches = list(diag_re.finditer(combined))
    located = []
    for idx, m in enumerate(matches):
        if m.group("sev") != "info":
            continue
        start = m.end()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(combined)
        body = combined[start:end]
        if "⊢" not in body:
            continue
        binders, goal = _parse_trace_state_block(body)
        if goal:
            located.append((int(m.group("line")), int(m.group("col")), binders, goal))
    located.sort(key=lambda t: (t[0], t[1]))

    res = {}
    if located:
        for k, (ln, col, binders, goal) in enumerate(located, 1):
            res[k] = {
                "binders": binders,
                "goal": goal,
                "line": ln,
                "col": col,
                "is_tactic_mode": span_by_k.get(k, {}).get("is_tactic_mode", True),
            }
        return res

    # Fallback parser: split raw output at each `⊢ ...` line when no file:line:col headers are present
    cur_lines = []
    k = 0
    for ln in combined.splitlines():
        if re.match(r"^/[^:]+:\d+:\d+:", ln):
            cur_lines = []
            continue
        cur_lines.append(ln)
        if ln.lstrip().startswith("⊢"):
            binders, goal = _parse_trace_state_block("\n".join(cur_lines))
            cur_lines = []
            if goal:
                k += 1
                res[k] = {
                    "binders": binders,
                    "goal": goal,
                    "is_tactic_mode": span_by_k.get(k, {}).get("is_tactic_mode", True),
                }
    return res


def match_sketch_subgoal_pp(pp_map, ltype, sorry_idx, used_keys):
    """Match a frontier inline subgoal (`ltype`, `_fv_sorry_<sorry_idx>`) to its extracted
    `trace_state` entry in `pp_map` (immune to AST traversal order like `App fn arg` reversing `have`s!).
    """
    if not pp_map:
        return None
    avail = [(k, v) for k, v in pp_map.items() if k not in used_keys and v.get("goal")]
    if not avail:
        avail = [(k, v) for k, v in pp_map.items() if v.get("goal")]
    if not avail:
        return None
    if len(avail) == 1:
        k, v = avail[0]
        used_keys.add(k)
        out = dict(v)
        out["source_index"] = k
        return out

    # Count expanded binders (e.g. `(a b c : ℝ)` -> 3 binders) and compare against ltype's binder/conclusion tokens
    def _count_pp_binders(binders):
        tot = 0
        for b in binders:
            m = re.match(r"^\(([^:]+):", b.strip())
            tot += len(m.group(1).split()) if m else 1
        return tot

    def _tokens(s):
        return set(re.findall(r"[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_'α-ωΑ-Ω₀-₉]*|\d+", s or ""))

    lt = (ltype or "").strip()
    # Count ∀/→ binders in ltype (fvfrontier-prep prints `∀ (x : T), ...` or `A → B`)
    ltype_forall_n = len(re.findall(r"∀\s*\([^)]+\)\s*,", lt))
    # Extract conclusion after last `), ` or `→ `
    parts = re.split(r"\),\s*|→\s*", lt)
    ltype_concl = parts[-1].strip() if parts else lt
    lt_toks = _tokens(ltype_concl)
    lt_all_toks = _tokens(lt)

    best_k, best_v, best_score = None, None, -10**9
    for k, v in avail:
        g_toks = _tokens(v["goal"])
        b_all = " ".join(v.get("binders") or [])
        all_toks = g_toks | _tokens(b_all)
        # Overlap between conclusion tokens (strong signal) + binder count proximity + exact index tie-breaker
        concl_overlap = len(lt_toks & g_toks)
        concl_extra = len(g_toks - lt_toks)
        all_overlap = len(lt_all_toks & all_toks)
        nb = _count_pp_binders(v.get("binders") or [])
        binder_diff = abs(nb - ltype_forall_n) if ltype_forall_n > 0 else 0
        score = concl_overlap * 10 - concl_extra * 3 + all_overlap * 2 - binder_diff * 4 + (1 if k == sorry_idx else 0)
        if score > best_score:
            best_score = score
            best_k, best_v = k, v
    if best_k is not None:
        used_keys.add(best_k)
        out = dict(best_v)
        out["source_index"] = best_k
        return out
    fb = pp_map.get(sorry_idx)
    if fb is not None:
        out = dict(fb)
        out["source_index"] = sorry_idx
        return out
    return None


# ---------------------------------------------------------------- interruption = no verdict, exit 2
def _descendants(root):
    """live (non-zombie) descendants of `root` from /proc (the tool is a child subreaper, so orphans stay below it)"""
    kids = {}
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % d, "rb") as f:
                st = f.read()
            rest = st[st.rindex(b")") + 2:].split()
            if rest[0] == b"Z":
                continue
            kids.setdefault(int(rest[1]), []).append(int(d))
        except (OSError, ValueError, IndexError):
            continue
    out, todo = [], [root]
    while todo:
        for c in kids.get(todo.pop(), []):
            out.append(c)
            todo.append(c)
    return out


def _kill_tree(grace=5.0):
    import signal as _sg
    me = os.getpid()
    for p in _descendants(me):
        try:
            os.kill(p, _sg.SIGTERM)
        except OSError:
            pass
    t_end = time.time() + grace
    while time.time() < t_end and _descendants(me):
        try:
            while os.waitpid(-1, os.WNOHANG)[0] > 0:
                pass
        except ChildProcessError:
            pass
        time.sleep(0.05)
    for p in _descendants(me):
        try:
            os.kill(p, _sg.SIGKILL)
        except OSError:
            pass


def install_interrupt_handler(tool):
    """SIGTERM / SIGINT / SIGHUP during mint / subverify / merge: handled ONCE (all three
    ignored from then on), the whole descendant tree (check-frontier.sh / check-sound.sh / builds) is killed (TERM, KILL after
    5 s), one NO_VERDICT JSON line is printed and the tool exits 2 (not 130 / 143)."""
    import signal as _sg
    try:
        import ctypes
        ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0)   # PR_SET_CHILD_SUBREAPER
    except Exception:   # noqa: BLE001
        pass

    def _h(signum, _frame):
        for sg in (_sg.SIGTERM, _sg.SIGINT, _sg.SIGHUP):
            _sg.signal(sg, _sg.SIG_IGN)
        _kill_tree()
        try:
            import sys as _sys
            _sys.stdout.write(json.dumps({"ok": False, "verdict": "NO_VERDICT", "exit": 2,
                                          "error": "%s interrupted (signal %d): no verdict" % (tool, signum)}) + "\n")
            _sys.stdout.flush()
        finally:
            os._exit(2)
    for sg in (_sg.SIGTERM, _sg.SIGINT, _sg.SIGHUP):
        _sg.signal(sg, _h)
