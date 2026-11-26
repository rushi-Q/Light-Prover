#!/usr/bin/python3 -I
"""fv_cli.py — Ergonomic daily production CLI for fastverify (`bin/fv`).

Zero external dependencies (Python 3.10+ stdlib only). Additive wrapper over the unchanged
trusted verifier (bin/fastverify, check/sound/check-sound.sh, tools/incr, tools/fvserve,
tools/http/fvapi.py, tools/triage/triage.py, tools/ci-action).

Subcommands:
  fv verify         Verify a Lean project against a challenge (auto temp OUT, incremental/cold, JSON/SARIF)
  fv check          Standalone sound check of an .export file against a SHA-256-pinned official challenge
  fv attempt        Verify a single proof attempt via fvserve or fvapi (0.6-3 s sound verdict)
  fv triage         Pre-proving sandboxed triage of a sorry sub-lemma (refutation/vacuity/hazards/dups)
  fv mint           Mint SHA-256-pinned standalone sub-challenges from open sorry frontier lemmas
  fv init-challenge Build and SHA-256-pin an official challenge export (B0+E0) from challenge sources
  fv audit          Audit a challenge directory (comparator.json, pins, optional tools/audit)
  fv doctor         Inspect host/cgroup/sandbox/toolchain readiness and recommend preset/threads
  fv watch          Editor/LSP-friendly continuous watch loop emitting VS Code diagnostics + LSP JSON + SARIF
  fv serve          Manage fvserve + fvapi HTTP REST API
  fv ci             Run the GitHub/GitLab CI Action runner locally
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import urllib.request

HERE = os.path.dirname(os.path.realpath(__file__))
FV_ROOT = os.path.realpath(os.path.join(HERE, "..", ".."))

def _default_toolchain():
    """Default official Lean 4.33.1 toolchain: the one registered in config/components.json (tools/configure.py),
    else ${ELAN_HOME:-~/.elan}/toolchains/leanprover--lean4---v4.33.1."""
    try:
        with open(os.path.join(FV_ROOT, "config", "components.json"), encoding="utf-8") as f:
            p = json.load(f)["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"]
        if p:
            return p
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return os.path.join(os.environ.get("ELAN_HOME") or os.path.expanduser("~/.elan"), "toolchains",
                        "leanprover--lean4---v4.33.1")


def _default_packages():
    """Default trusted Lake workspace of bin/fv: <repository root>/verify/challenge if it exists, else None (pass
    --packages WS)."""
    p = os.path.join(os.path.dirname(FV_ROOT), "verify", "challenge")
    return p if os.path.isdir(p) else None

sys.path.insert(0, os.path.join(FV_ROOT, "schemas"))
sys.path.insert(0, os.path.join(FV_ROOT, "tools", "mcp"))
sys.path.insert(0, os.path.join(FV_ROOT, "tools", "fvserve"))
sys.path.insert(0, os.path.join(FV_ROOT, "tools", "triage"))
import fv_schema   # noqa: E402
import mcp_server  # noqa: E402
import fvserve     # noqa: E402
import triage      # noqa: E402


# ---- ONE local path policy for every bin/fv input and output --------------------------
# A path given to bin/fv is never resolved: it is made absolute and normalized lexically ('..' removed without stepping
# back through a link), mapped onto the longest anchor of mcp_server.cli_roots() (the resolved current directory,
# FV_CLI_ROOTS, '/'), and every component below the anchor is walked with O_NOFOLLOW. Inputs are then read / copied
# privately from the opened fds (regular single-link files, trees without symlink / special file / hard link); outputs
# are created inside their directory opened without following links (temp file + rename: a planted symlink is replaced,
# never written through). Calling os.path.realpath on these paths first would follow every link before any check.
class CliRefused(Exception):
    pass


def cli_path(path, what, must_exist=True, want_dir=None):
    """the canonical form of a local path (see above); CliRefused if a component is a symlink / missing / of the wrong
    kind"""
    try:
        return mcp_server.client_abspath(path, mcp_server.cli_roots(), must_exist=must_exist, expect_dir=want_dir,
                                         allow_dotdot=True)
    except (mcp_server.ClientPathError, OSError) as e:
        raise CliRefused(f"{what} {path}: {e}")


def cli_read(path, what, max_bytes=64 << 20):
    """the bytes of a local regular single-link file, read without following any link"""
    roots = mcp_server.cli_roots()
    try:
        return mcp_server.read_client_file(mcp_server.local_path_under(path, roots), roots, max_bytes=max_bytes)
    except (mcp_server.ClientPathError, OSError) as e:
        raise CliRefused(f"{what} {path}: {e}")


def cli_copy_file(path, dst, what):
    """a private copy (dst, mode 0444) of a local regular single-link file, opened without following any link"""
    roots = mcp_server.cli_roots()
    try:
        mcp_server.copy_client_file(mcp_server.local_path_under(path, roots), dst, roots)
    except (mcp_server.ClientPathError, OSError) as e:
        raise CliRefused(f"{what} {path}: {e}")
    return dst


def cli_copy_tree(path, dst, what, file_filter=None):
    """a private copy of a local directory (no symlink / special file / hard link anywhere; .lake/.git skipped)"""
    roots = mcp_server.cli_roots()
    try:
        fd = mcp_server.open_nofollow_under(mcp_server.local_path_under(path, roots), roots, want_dir=True)
        try:
            mcp_server.copy_client_tree(fd, dst, file_filter=file_filter)
        finally:
            os.close(fd)
    except (mcp_server.ClientPathError, OSError, RecursionError, MemoryError) as e:   # never a traceback
        shutil.rmtree(dst, ignore_errors=True)
        raise CliRefused(f"{what} {path}: {e}")
    return dst


def cli_write(path, data, what, mode=0o644):
    """create / replace a local output file without following any link (its directory is created if missing)"""
    roots = mcp_server.cli_roots()
    try:
        canon = mcp_server.local_path_under(path, roots)
        dfd = mcp_server.open_nofollow_under(os.path.dirname(canon), roots, want_dir=True, create=True)
        try:
            mcp_server.write_file_at(dfd, os.path.basename(canon), data, mode=mode)
        finally:
            os.close(dfd)
    except (mcp_server.ClientPathError, OSError) as e:
        raise CliRefused(f"{what} {path}: {e}")


CLI_SCAN_MAX = 10 ** 7   # entries of a cache / build tree scanned for links (Mathlib-size trees fit)


def cli_scan_no_links(path, what, create=False):
    """the canonical path of a local directory reached without following links,
    owned by the caller, with NO symlink / special file anywhere below it (every entry walked with O_NOFOLLOW relative to
    its parent fd); create: made (no-follow) if missing. CliRefused otherwise (also on a permission error: no traceback)"""
    roots = mcp_server.cli_roots()
    try:
        canon = mcp_server.local_path_under(path, roots)
        fd = mcp_server.open_nofollow_under(canon, roots, want_dir=True, create=create)
        try:
            if os.fstat(fd).st_uid != os.getuid():
                raise CliRefused(f"{what} {path}: not owned by the caller")
            mcp_server.scan_client_tree(fd, ignore=(), single_link=False, max_entries=CLI_SCAN_MAX)
            _check_private_tree(fd, f"{what} {path}")
            _check_parents(canon)
        finally:
            os.close(fd)
    except (mcp_server.ClientPathError, OSError, RecursionError, MemoryError) as e:
        raise CliRefused(f"{what} {path}: {e}")
    return canon


def _own_private_group():
    """the caller's primary gid if it is a user-private group (no member but the caller), else None"""
    try:
        import grp
        import pwd
        g = grp.getgrgid(os.getgid())
        me = pwd.getpwuid(os.getuid()).pw_name
        if not set(g.gr_mem) <= {me}:
            return None
        # primary-group members are not listed in gr_mem: no OTHER account may have
        # this gid as its primary group either
        if any(pw.pw_gid == os.getgid() and pw.pw_uid != os.getuid() for pw in pwd.getpwall()):
            return None
        return os.getgid()
    except (KeyError, ImportError, OSError):
        return None


def _check_parents(canon):
    """no parent of a checked tree that another account could rename it
    out of: not writable by others or by a foreign group, and owned by root or the caller - unless the sticky bit is set"""
    upg, par = _own_private_group(), os.path.dirname(canon)
    while True:
        stp = os.lstat(par)
        # the sticky bit exempts only the WRITE bits (shared directories like /tmp): the
        # OWNER of a directory can always rename / remove its entries, so a parent owned by another account (not root) is
        # refused even when sticky
        if stp.st_uid not in (0, os.getuid()) or (not stp.st_mode & stat.S_ISVTX and (
                stp.st_mode & 0o002 or (stp.st_mode & 0o020 and stp.st_gid != upg))):
            raise mcp_server.ClientPathError(f"parent directory {par} can be changed by another account (owned by another "
                                             "account, or group / others write without the sticky bit)")
        if par == "/":
            break
        par = os.path.dirname(par)


def _check_private_tree(dir_fd, what):
    """a tree the incremental tools keep using after this check must be controlled by the
    caller alone: every entry (the top included) owned by the caller, never writable by others, and writable by the group
    only when that group is the caller's own private group (umask 002 setups). A scan alone was a point-in-time check: an
    owned but group/other-writable tree could be swapped by another account afterwards. Walked with O_NOFOLLOW (the tree
    has no link: scan_client_tree ran first)."""
    upg = _own_private_group()
    uid = os.getuid()

    def bad(st, rel):
        if stat.S_ISLNK(st.st_mode):   # a link's own mode is always 0777 and it can only be replaced through its directory
            return None
        if st.st_uid != uid:
            return f"{rel or '.'!r} is not owned by the caller"
        if st.st_mode & 0o002:
            return f"{rel or '.'!r} is writable by others"
        if st.st_mode & 0o020 and st.st_gid != upg:
            return f"{rel or '.'!r} is writable by its group"
        return None
    why = bad(os.fstat(dir_fd), "")
    if why:
        raise mcp_server.ClientPathError(why + " (refused: the tree must be controlled by the caller alone)")
    # os.fwalk keeps only the fds of the current path open (the depth is bounded by the scan) and never follows a link
    for dpath, dnames, fnames, dfd in os.fwalk(".", dir_fd=dir_fd, follow_symlinks=False):
        for n in dnames + fnames:
            r = os.path.normpath(os.path.join(dpath, n))
            why = bad(os.stat(n, dir_fd=dfd, follow_symlinks=False), r)
            if why:
                raise mcp_server.ClientPathError(why + " (refused: the tree must be controlled by the caller alone)")


def cli_packages(path, what="--packages"):
    """a packages workspace given to bin/fv: its path checked (cli_path), then what
    lib/manifest.py and the build use from it, without following links: lake-manifest.json a regular file; .lake and
    .lake/packages real directories; every package entry a real directory (a symlinked entry would be resolved on the host by
    manifest.py and its target - any repository - bound into the build); in each package, .git a real directory
    (manifest.py runs git there: a `.git` file / link would read another repository) and .lake/build a real directory tree
    without any symlink or special file. Symlinks a package's own source tree carries (git-tracked, e.g. Mathlib's scripts)
    stay allowed: they resolve inside the build sandbox only. A missing .lake/packages is fine (manifest.py refuses a needed
    dependency)."""
    ws = cli_path(path, what, want_dir=True)
    roots = mcp_server.cli_roots()

    def kind(dfd, name):
        try:
            return os.stat(name, dir_fd=dfd, follow_symlinks=False).st_mode
        except FileNotFoundError:
            return None

    def opendir(dfd, name, rel):
        try:
            return os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=dfd)
        except OSError as e:
            raise mcp_server.ClientPathError(f"{rel!r}: not a directory reachable without following a symlink ({e.strerror})")
    fds = []
    try:
        wfd = mcp_server.open_nofollow_under(ws, roots, want_dir=True)
        fds.append(wfd)
        m = kind(wfd, "lake-manifest.json")
        if m is not None and not stat.S_ISREG(m):
            raise mcp_server.ClientPathError("'lake-manifest.json' is not a regular file (symlink / special refused)")
        # the packages directory is the one lib/manifest.py uses: the workspace manifest's
        # `packagesDir` (default .lake/packages), read here without following links; it must be a plain relative path
        # inside the workspace, every component a real directory (checking only .lake/packages is not enough: `"packagesDir":
        # "vendor"` with vendor/dep a link would bind an outside repository)
        # EVERY packages directory a consumer may read is checked: Lake's (the
        # manifest's packagesDir, else the lakefile's packagesDir, else .lake/packages - lib/manifest.py), AND .lake/packages
        # itself (tools/triage and tools/dupfind always read it); a lakefile.lean that sets packagesDir cannot be read here
        mpdir = None
        if m is not None:
            mfd = os.open("lake-manifest.json", os.O_RDONLY | os.O_NOFOLLOW, dir_fd=wfd)
            try:   # the WHOLE file (not only its first 4 MiB)
                chunks, total = [], 0
                while True:
                    c = os.read(mfd, 1 << 20)
                    if not c:
                        break
                    total += len(c)
                    if total > (64 << 20):
                        raise mcp_server.ClientPathError("lake-manifest.json is larger than 64 MiB (refused)")
                    chunks.append(c)
                raw = b"".join(chunks)
            finally:
                os.close(mfd)
            try:
                wman = json.loads(raw.decode("utf-8"))
            except (ValueError, UnicodeDecodeError) as e:
                raise mcp_server.ClientPathError(f"lake-manifest.json is not valid JSON ({e})")
            if not isinstance(wman, dict):
                raise mcp_server.ClientPathError("lake-manifest.json is not a JSON object")
            mpdir = wman.get("packagesDir")
            if "packagesDir" in wman and (not isinstance(mpdir, str) or mpdir.strip() in ("", ".", "./")):
                raise mcp_server.ClientPathError(f"lake-manifest.json: packagesDir {mpdir!r} is not a usable relative path")
        lpdir = None
        for lf in ("lakefile.toml", "lakefile.lean"):
            lk = kind(wfd, lf)
            if lk is None:
                continue
            if not stat.S_ISREG(lk):
                raise mcp_server.ClientPathError(f"{lf} is not a regular file")
            lfd = os.open(lf, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=wfd)
            try:
                ltxt = os.read(lfd, 4 << 20).decode("utf-8", "replace")
            finally:
                os.close(lfd)
            if "packagesDir" in ltxt:
                mm = re.search(r'(?m)^\s*packagesDir\s*=\s*"([^"\\]*)"\s*(#.*)?$', ltxt) if lf == "lakefile.toml" else None
                if not mm:
                    raise mcp_server.ClientPathError(f"{lf}: a packagesDir setting that cannot be read exactly here (refused)")
                lpdir = mm.group(1)
        cands = []
        for pdir in (mpdir or lpdir or ".lake/packages", ".lake/packages"):
            pd2 = pdir[2:] if pdir.startswith("./") else pdir
            if pd2.rstrip("/") not in [c.rstrip("/") for c in cands]:
                cands.append(pd2)
        for pd2 in cands:
            _check_one_pkgdir(pd2, wfd, kind, opendir, fds)
        _check_parents(ws)   # no other account can swap the workspace after this check
        return ws
    except (mcp_server.ClientPathError, OSError, RecursionError, MemoryError) as e:
        raise CliRefused(f"{what} {path}: {e}")
    finally:
        for fd in fds:
            try:
                os.close(fd)
            except OSError:
                pass


def _check_one_pkgdir(pd2, wfd, kind, opendir, fds):
    """one packages directory of the workspace open at wfd: a plain relative path inside it,
    every component a real directory; each entry a real directory with its own .git (no indirection, no link) and a
    link-free .lake/build"""
    if True:
        comps = pd2.rstrip("/").split("/")
        if pd2.startswith("/") or any(c in ("", ".", "..") for c in comps) or "\x00" in pd2:
            raise mcp_server.ClientPathError(f"packagesDir {pd2!r} is not a plain relative path inside the workspace")
        cur = wfd
        for i, c in enumerate(comps):
            if kind(cur, c) is None:
                return
            cur = opendir(cur, c, "/".join(comps[:i + 1]))
            fds.append(cur)
        # the packages tree is bound into builds after this check: only the caller may be
        # able to change it (owned, not writable by others or a foreign group)
        _check_private_tree(cur, pd2)
        pfd = cur
        for n in sorted(os.listdir(pfd)):
            rel = pd2.rstrip("/") + "/" + n
            m = kind(pfd, n)
            if m is None or stat.S_ISREG(m):
                continue
            if not stat.S_ISDIR(m):
                raise mcp_server.ClientPathError(f"package entry {rel!r} is a symlink / special file (refused: the workspace "
                                                 "is bound into the build as it is)")
            efd = opendir(pfd, n, rel)
            try:
                g = kind(efd, ".git")
                if g is None:   # git would resolve HEAD in the ENCLOSING repository instead
                    raise mcp_server.ClientPathError(f"package entry {rel!r} has no .git directory of its own (a Lake git "
                                                     "checkout is expected)")
                if g is not None and not stat.S_ISDIR(g):
                    raise mcp_server.ClientPathError(f"{rel + '/.git'!r} is not a real directory (a `.git` file / link "
                                                     "would make git read another repository)")
                if g is not None:   # no indirection to another repository inside .git
                    gfd = opendir(efd, ".git", rel + "/.git")
                    try:
                        # a real repository: HEAD a regular file, objects a directory (an EMPTY
                        # .git made git walk up to the enclosing repository and report ITS HEAD)
                        hk, ok_ = kind(gfd, "HEAD"), kind(gfd, "objects")
                        if hk is None or not stat.S_ISREG(hk) or ok_ is None or not stat.S_ISDIR(ok_):
                            raise mcp_server.ClientPathError(f"{rel}/.git is not a git repository of its own (HEAD / objects missing)")
                        for ind in ("commondir", "gitdir", "objects/info/alternates", "objects/info/http-alternates"):
                            dfd2, parts = gfd, ind.split("/")
                            for pi, part in enumerate(parts):
                                km = kind(dfd2, part)
                                if km is None:
                                    break
                                if pi == len(parts) - 1:
                                    raise mcp_server.ClientPathError(f"{rel}/.git/{ind} refused (it points git at another "
                                                                     "repository)")
                                nfd = opendir(dfd2, part, f"{rel}/.git/{'/'.join(parts[:pi + 1])}")
                                if dfd2 != gfd:
                                    os.close(dfd2)
                                dfd2 = nfd
                            if dfd2 != gfd:
                                os.close(dfd2)
                        try:   # and no link / special file anywhere in .git (HEAD, refs ...)
                            mcp_server.scan_client_tree(gfd, ignore=(), single_link=False, max_entries=CLI_SCAN_MAX)
                        except mcp_server.ClientPathError as e:
                            raise mcp_server.ClientPathError(f"{rel}/.git: {e}")
                    finally:
                        os.close(gfd)
                if kind(efd, ".lake") is not None:
                    pl = opendir(efd, ".lake", rel + "/.lake")
                    try:
                        if kind(pl, "build") is not None:
                            bfd = opendir(pl, "build", rel + "/.lake/build")
                            try:
                                mcp_server.scan_client_tree(bfd, ignore=(), single_link=False, max_entries=CLI_SCAN_MAX)
                            except mcp_server.ClientPathError as e:
                                raise mcp_server.ClientPathError(f"{rel}/.lake/build: {e}")
                            finally:
                                os.close(bfd)
                    finally:
                        os.close(pl)
            finally:
                os.close(efd)


def write_optional_outputs(env, json_out=None, sarif_out=None, lsp_out=None):
    """every output file is written without following links (cli_write)"""
    if json_out:
        cli_write(json_out, json.dumps(env, indent=2), "--json-out")
    if sarif_out:
        cli_write(sarif_out, json.dumps(fv_schema.to_sarif_210(env), indent=2), "--sarif")
    if lsp_out:
        cli_write(lsp_out, json.dumps(fv_schema.to_lsp_diagnostics(env), indent=2), "--lsp-out")


def print_human_envelope(env):
    v = env["verdict"]
    trust = env["trust"]
    t_s = env["timing"].get("total_s", 0.0)
    tag = "OK" if env["accepted"] else ("CONDITIONAL" if v in ("CONDITIONAL", "ACCEPTED_MODULO_FRONTIER") else "FAIL")
    print(f"[{tag}] verdict={v} trust={trust} reward={env['reward']} time={t_s:.2f}s")
    if env.get("verdict_basis"):
        print(f"  basis: {env['verdict_basis']}")
    parts = []
    for k in ("preflight_s", "build_s", "export_s", "check_s"):
        if env["timing"].get(k) is not None:
            parts.append(f"{k[:-2]}={env['timing'][k]:.2f}s")
    if parts:
        print("  stages: " + "  ".join(parts))
    for d in (env.get("diagnostics") or [])[:20]:
        loc = f"{d['file']}:{d['line']}:{d['column']}: " if d.get("file") and d.get("line") else ""
        print(f"  {loc}{d['severity']} [{d['rule_id']}]: {d['message'].splitlines()[0]}")
    fr = env.get("frontier")
    if isinstance(fr, dict):
        items = fr.get("frontier") or []
        if isinstance(items, list) and items:
            rw = f" [rewrite={fr['rewrite']}]" if fr.get("rewrite") else ""
            print(f"  open frontier ({len(items)}){rw}:")
            for e in items[:15]:
                if not isinstance(e, dict):
                    continue
                nm = e.get("name") or "?"
                ax = e.get("axiom")
                ax_tag = f" [axiom={ax}]" if ax and ax != nm else ""
                srcs = e.get("source")
                if isinstance(srcs, list) and srcs and isinstance(srcs[0], dict):
                    s0 = srcs[0]
                    loc = f"{s0.get('file')}:{s0.get('line')}"
                    stmt = " ".join(str(s0.get("statement_as_written") or "").split())[:140]
                    print(f"    - {nm}{ax_tag} ({loc}): {stmt}")
                else:
                    print(f"    - {nm}{ax_tag}")


def resolve_challenge_pin(challenge_dir, explicit_pin, trust_pin_file=False):
    if explicit_pin is not None:   # an explicitly empty pin (`--challenge-sha256=`) is malformed, not absent
        if not fv_schema.validate_sha256(explicit_pin):
            raise SystemExit("fv: --challenge-sha256 must be 64 lowercase hex digits")
        return explicit_pin
    if trust_pin_file:
        p = cli_path(os.path.join(challenge_dir, "challenge.export.sha256"), "challenge.export.sha256", must_exist=False)
        if os.path.lexists(p):   # present: read without following a link (a symlink is refused, not "no pin")
            toks = cli_read(p, "challenge.export.sha256", 4096).decode("utf-8", "replace").strip().split()
            if toks and fv_schema.validate_sha256(toks[0]):
                return toks[0]
            # an empty / malformed pin file the caller asked to trust is an input error (exit 2), not
            # a silently unpinned run
            raise SystemExit(f"fv: --trust-challenge-sha256-file: {p} is empty or does not start with a 64-hex SHA-256")
        # the named trust source is missing: refused, never a silently unpinned run
        raise SystemExit(f"fv: --trust-challenge-sha256-file: {p} does not exist")
    return None


def wrap_with_guard(cmd, guard_spec, guard_json_path):
    """Wrap cmd with tools/guard/fvguard.py when --guard SPEC is passed.
    Example SPEC: 'mem=8G,wall=300,procs=128'."""
    if not guard_spec:
        return cmd
    gp = os.path.join(FV_ROOT, "tools", "guard", "fvguard.py")
    if not os.path.isfile(gp):
        raise SystemExit("fv: --guard requested but tools/guard/fvguard.py is not present")
    gcmd = ["/usr/bin/python3", "-I", gp, "--json", guard_json_path]
    for part in guard_spec.split(","):
        part = part.strip()
        if not part:
            continue
        k, _, v = part.partition("=")
        k = k.strip().replace("_", "-")
        if not k or not v:
            raise SystemExit(f"fv: invalid --guard item {part!r} (expected key=value)")
        gcmd += [f"--{k}", v.strip()]
    gcmd.append("--")
    return gcmd + cmd


def check_guard_violation(guard_json_path, mode, total_s, target=None):
    """Return a fail-closed NO-VERDICT envelope if fvguard killed the command due to a resource violation."""
    if not guard_json_path or not os.path.isfile(guard_json_path):
        return None
    try:
        gj = json.load(open(guard_json_path, encoding="utf-8"))
    except Exception:
        return None
    viol = gj.get("violation")
    if viol:
        detail = gj.get("detail") or f"resource guard limit exceeded: {viol}"
        return fv_schema.make_envelope(
            mode=mode,
            verdict="NO-VERDICT",
            trust="sound",
            verdict_basis=f"fvguard resource violation ({viol}): {detail} (fail-closed, never a verdict)",
            total_s=total_s,
            reason=f"resource_limit:{viol}: {detail}",
            target=target,
            diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", detail),
            raw={"fvguard": gj},
        )
    return None


# --------------------------------------------------------------------------- subcommands
class PinsRefused(Exception):
    """--pins outside the package's own pins*.env files: no verdict (ERROR envelope, exit 2)"""


def _resolve_pins_arg(pins_arg, ctx="fv", lowmem=False):
    """Boundary B4: --pins names a pins*.env file directly inside THIS package's check/sound/ (check/lowmem/
    for --low-mem), exactly as bin/fastverify, fvserve, fv_lowmem, fvcheckd and fastverify-mcp confine it: a caller path
    (also via a symlink) would let the judge verify its binaries against the caller's own hashes"""
    if pins_arg is None:
        return None
    if not str(pins_arg).strip():   # an explicitly empty profile is malformed, never "the default"
        raise PinsRefused(f"{ctx}: --pins must not be empty")
    sub = ("check", "lowmem") if lowmem else ("check", "sound")
    d = os.path.realpath(os.path.join(FV_ROOT, *sub))
    if pins_arg in ("436", "default"):
        pins_p = os.path.join(d, "pins.env")
    elif pins_arg in ("437", "4.37", "4.37.0-rc1"):
        pins_p = os.path.join(d, "pins-437.env")
    else:
        # every component checked without resolving (cli_path: a symlinked or bounce path is refused,
        # never followed) before the containment check; relative = against the cwd, then against this package
        cands = []
        for c0 in ([pins_arg] if os.path.isabs(pins_arg) else [pins_arg, os.path.join(FV_ROOT, pins_arg)]):
            try:
                cands.append(mcp_server.client_abspath(c0, mcp_server.cli_roots(), must_exist=True, expect_dir=False,
                                                       allow_dotdot=True))
            except (mcp_server.ClientPathError, OSError):
                continue
        if not cands:
            raise PinsRefused(f"refused: {ctx} --pins {pins_arg}: not a regular file reachable without following a symlink "
                              f"(Boundary B4)")
        pins_p = next((c for c in cands if os.path.dirname(c) == d), cands[0])
    pins_p = os.path.realpath(pins_p)
    if os.path.dirname(pins_p) != d or not os.path.basename(pins_p).startswith("pins") or not pins_p.endswith(".env"):
        raise PinsRefused(f"refused: {ctx} --pins {pins_arg}: must name a pins*.env file in {d} (Boundary B4)")
    if not os.path.isfile(pins_p):
        raise PinsRefused(f"refused: {ctx} --pins: pins file not found: {pins_p} (Boundary B4)")
    return pins_p


# `fv verify` runs the sound family by default; options of bin/fastverify that would replace the deciding
# check of a sound preset are refused (argparse prefix abbreviations included), and the result must show that the requested
# sound check really decided. A non-sound preset needs --allow-unsound-presets and never counts (fv_schema ACCEPTING_TRUST).
SOUND_FAMILY_PRESETS = ("sound", "sound-auto", "notary")
# ALLOW-list of bin/fastverify options that --extra-arg may carry: they only touch the untrusted build / export,
# scheduling, or make the trusted check stricter. Everything else is refused - in particular what is judged and against
# what (--from-export, --export, --comparator-config, --challenge-sha256, --pins, --packages, --modulo-frontier,
# --frontier-*, --reference-export), the deciding check (--preset, --check, --fast-*), and anything that weakens or
# replaces kernels or judge inputs (--skip-extra-kernel, --notary-kernels, --check-hide, --check-hints, --unsafe,
# --overlap-targets). An option must be spelled exactly (no argparse abbreviation); a value may follow as '=V' or as the
# next token (a token that does not start with '-').
EXTRA_ARG_ALLOWED = frozenset({
    # no path-valued option here: --export-dir / --build-cache would reach bin/fastverify unchecked
    # (bcache made directories through intermediate symlinks); fv verify has its own --export-dir / --build-cache, checked
    "--threads", "--build", "--official-timeout", "--extra-kernel", "--require-kernel",
    "--parallel-checks", "--sequential-checks", "--no-confirm-build-failure", "--confirm-build-failure-full",
    "--no-build-fallback", "--require-fast", "--no-integrity-cache", "--keep-work", "--overlap", "--overlap-targeted",
    "--require-sorried-holes", "--confirm-reject",
})


EXTRA_ARG_TAKES_VALUE = frozenset({"--threads", "--build", "--official-timeout", "--extra-kernel", "--require-kernel"})


def unsafe_extra_args(extra_args, allowed=EXTRA_ARG_ALLOWED):
    """the --extra-arg tokens that are not an exactly spelled allowed option (any token starting with '-' must be one).
    A token without '-' is accepted only as the value of the preceding value-taking option (`--threads 8`)."""
    bad = []
    want_value = False
    for tok in extra_args or []:
        if not isinstance(tok, str):
            bad.append(repr(tok))
            want_value = False
            continue
        if want_value and not tok.startswith("-"):
            want_value = False
            continue
        want_value = False
        if tok.startswith("-"):
            name = tok.split("=", 1)[0]
            if tok == "--" or name not in allowed:
                bad.append(tok)
            elif name in EXTRA_ARG_TAKES_VALUE and "=" not in tok:
                want_value = True
        else:
            bad.append(tok)
    return bad


def sound_preset_ran(preset, res):
    """did bin/fastverify's result come from the requested sound-family preset's trusted check?"""
    mode = res.get("mode") if isinstance(res, dict) and isinstance(res.get("mode"), dict) else {}
    checks = mode.get("check") if isinstance(mode.get("check"), list) else []
    if mode.get("preset") != preset:
        return False
    if preset == "notary":
        return "CN" in checks
    return mode.get("sound") is True and "CS" in checks


def result_input_mismatch(res, chal_pin, cfg_sha):
    """None if bin/fastverify's result judged the PROJECT (no given export) against the challenge export with
    sha256 chal_pin (when given) and the comparator config with sha256 cfg_sha (when known); else the reason"""
    if not isinstance(res, dict):
        return "no result"
    mode = res.get("mode") if isinstance(res.get("mode"), dict) else {}
    if mode.get("export_given") is not False:
        return "the result judged a given export (export_given %r)" % (mode.get("export_given"),)
    ins = res.get("inputs") if isinstance(res.get("inputs"), dict) else {}
    got_c = (ins.get("challenge_export") or {}).get("sha256") if isinstance(ins.get("challenge_export"), dict) else None
    got_f = (ins.get("comparator_config") or {}).get("sha256") if isinstance(ins.get("comparator_config"), dict) else None
    if chal_pin and got_c != chal_pin:
        return "challenge export sha256 %s != the pin %s" % (got_c, chal_pin)
    if cfg_sha and got_f != cfg_sha:
        return "comparator config sha256 %s != %s" % (got_f, cfg_sha)
    return None


def _emit_refusal(a, mode, msg, t0, target=None):
    env = fv_schema.from_error(mode, msg, time.time() - t0, target=target)
    write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
    if a.json:
        print(json.dumps(env, indent=2))
    elif not a.quiet:
        print_human_envelope(env)
    return env["exit_code"]


def _incr_toolchain(proj, chal):
    """the official toolchain prefix for `fv verify --incr-base`, resolved as bin/fastverify does: the
    release the project's AND the challenge's lean-toolchain name (equal), registered in config/components.json; passed to
    incr-reverify.sh explicitly (--toolchain), which verifies the tree (lib/toolchain.py verify) before using it. Returns
    (prefix, None), or (None, why) when the project must be judged by the cold path instead: unreadable / different
    lean-toolchain files, an unregistered release, or a release with its own trusted check (check/sound/pins-*.env with that
    TC_VERSION: sound-auto selects it, the incremental path can only run the default check)."""
    try:
        want = open(os.path.join(proj, "lean-toolchain"), encoding="utf-8").read().strip()
        cwant = open(os.path.join(chal, "lean-toolchain"), encoding="utf-8").read().strip()
    except OSError as e:
        return None, f"no lean-toolchain ({e})"
    if want != cwant:
        return None, f"project toolchain {want} != challenge toolchain {cwant}"
    try:
        reg = json.load(open(os.path.join(FV_ROOT, "config", "components.json"), encoding="utf-8"))["lean_toolchains"]
    except (OSError, ValueError, KeyError) as e:
        return None, f"config/components.json unreadable ({e})"
    if want not in reg or not reg[want].get("prefix"):
        return None, f"lean-toolchain {want} is not registered in config/components.json"
    import glob
    for f in sorted(glob.glob(os.path.join(FV_ROOT, "check", "sound", "pins-*.env"))):
        try:
            tv = [ln.split("=", 1)[1].strip() for ln in open(f, encoding="utf-8") if ln.startswith("TC_VERSION=")]
        except OSError:
            continue
        if tv and tv[0] == want:
            return None, f"{want} has its own trusted check ({os.path.basename(f)}), which the incremental path cannot select"
    return reg[want]["prefix"], None


# `fv verify --incr-base` takes the cold path: the same verification as without it,
# with a warning. The incremental implementation (below) is not reachable from bin/fv in v0.1; tools/incr/incr-reverify.sh
# has its own explicit experimental flag and its results are never counted.
_INCR_IN_BIN_FV = False
_INCR_V01_NOTE = "incremental mode is experimental in v0.1 and was not used"


def _incr_unsupported(a):
    """options the cold path honours and the incremental path cannot (it builds, exports and checks
    with its own fixed stages): with any of them the project is judged by the cold path, never silently without them"""
    opts = [] if a.preset in ("sound", "sound-auto") else [f"--preset {a.preset}"]
    for k, flag in (("pins", "--pins"), ("build", "--build"), ("export_dir", "--export-dir"),
                    ("confirm_reject", "--confirm-reject"), ("no_integrity_cache", "--no-integrity-cache"),
                    ("modulo_frontier", "--modulo-frontier"), ("frontier_pin", "--frontier-pin"),
                    ("frontier_base", "--frontier-base"), ("extra_args", "--extra-arg"), ("build_cache", "--build-cache")):
        if getattr(a, k, None):
            opts.append(flag)
    return f"{', '.join(opts)} cannot be honoured by the incremental path" if opts else None


def cmd_verify(a):
    # the project and the challenge are judged as PRIVATE no-follow copies (as on MCP):
    # bin/fastverify / incr-reverify never see the caller's paths, and lib/autotune.py (sound-auto) only walks a copy whose
    # lakefile paths stay inside it
    proj_disp = cli_path(a.project, "project", want_dir=True)
    chal_disp = cli_path(a.challenge, "--challenge", want_dir=True)
    in_tmp = tempfile.mkdtemp(prefix="fv-verify-in.")
    try:
        proj = cli_copy_tree(a.project, os.path.join(in_tmp, "project"), "project")
        chal = cli_copy_tree(a.challenge, os.path.join(in_tmp, "challenge"), "--challenge")
        for what, d in (("project", proj), ("--challenge", chal)):
            lerr = mcp_server.lake_config_confined(d)
            if lerr:
                raise CliRefused(f"{what}: {lerr}")
        return _cmd_verify(a, proj, chal, proj_disp, chal_disp)
    finally:
        shutil.rmtree(in_tmp, ignore_errors=True)


def _ws_has_packages(path):
    """True iff the workspace at path has a packages directory reached without links: Lake's
    (the manifest's packagesDir, else .lake/packages) - looking only for the literal .lake/packages would make a challenge
    whose manifest names another packagesDir lose its dependencies"""
    roots = mcp_server.cli_roots()
    cands = [(".lake", "packages")]
    try:
        man = json.loads(cli_read(os.path.join(path, "lake-manifest.json"), "lake-manifest.json", 64 << 20).decode("utf-8"))
        pd = man.get("packagesDir") if isinstance(man, dict) else None
        if isinstance(pd, str) and pd.strip():
            pd = pd[2:] if pd.startswith("./") else pd
            comps = tuple(pd.rstrip("/").split("/"))
            if all(c not in ("", ".", "..") for c in comps):
                cands.insert(0, comps)
    except (CliRefused, ValueError, UnicodeDecodeError, AttributeError):
        pass
    return any(mcp_server._real_dir_at(path, roots, c) for c in cands)


def _packages_arg(a, chal_disp):
    """the packages workspace for bin/fastverify: --packages (checked, no link at any component), else -
    as bin/fastverify's own default and the documented challenge layout - the caller's challenge directory itself when its
    .lake/packages is a real directory reached without following any link (the private challenge copy has no .lake, so it alone
    would lose the dependencies). The workspace is used in place (lib/manifest.py binds its checkouts read-only), never copied."""
    if a.packages:
        return cli_packages(a.packages)
    if _ws_has_packages(chal_disp):   # Lake's packages directory, not only the literal .lake/packages
        return cli_packages(chal_disp, "--challenge (its packages directory)")
    return None


def _cmd_verify(a, proj, chal, proj_disp, chal_disp):
    t0 = time.time()
    sound_preset = a.preset in SOUND_FAMILY_PRESETS
    if not sound_preset and not getattr(a, "allow_unsound_presets", False):
        return _emit_refusal(a, "project", f"refused: --preset {a.preset} is not a sound preset ({', '.join(SOUND_FAMILY_PRESETS)}); "
                             "pass --allow-unsound-presets to run it anyway (its verdict never counts: accepted=false, "
                             "reward=0.0)", t0, target={"project": proj_disp, "challenge": chal_disp})
    bad_x = unsafe_extra_args(getattr(a, "extra_args", None))
    if bad_x:
        return _emit_refusal(a, "project", f"refused: --extra-arg {bad_x}: only these bin/fastverify options may be forwarded: "
                             f"{' '.join(sorted(EXTRA_ARG_ALLOWED))} (what is judged, the pins and the deciding check come from "
                             "fv verify's own options)", t0, target={"project": proj_disp, "challenge": chal_disp})
    try:   # the comparator config fv verify vouches for: the result must report exactly this file's sha256
        cfg_sha_here = fv_schema.sha256_file(os.path.join(chal, "comparator.json"))
    except OSError:
        cfg_sha_here = None
    pin = resolve_challenge_pin(chal, a.challenge_sha256, a.trust_challenge_sha256_file)
    cfg_pin = getattr(a, "comparator_sha256", None)
    if cfg_pin is None and (pin is not None or a.challenge_sha256 is not None or getattr(a, "trust_challenge_sha256_file", False)
                            or os.path.isfile(os.path.join(chal, "challenge.export"))):
        # a pinned challenge needs the pin of its comparator.json too
        return _emit_refusal(a, "project", "refused: --comparator-sha256 HEX is required with a pinned challenge "
                             "(--challenge-sha256 / challenge.export): the sha256 of the challenge's comparator.json",
                             t0, target={"project": proj, "challenge": chal})
    if cfg_pin is not None:   # `--comparator-sha256=` is malformed, not absent
        if not fv_schema.validate_sha256(cfg_pin):
            raise SystemExit("fv verify: --comparator-sha256 must be 64 lowercase hex digits")
        cfg_file = os.path.join(chal, "comparator.json")
        if not os.path.isfile(cfg_file) or fv_schema.sha256_file(cfg_file) != cfg_pin:
            env = fv_schema.from_error("project", f"comparator.json sha256 mismatch (pinned {cfg_pin})", time.time() - t0)
            write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
            if a.json:
                print(json.dumps(env, indent=2))
            elif not a.quiet:
                print_human_envelope(env)
            return env["exit_code"]
    temp_out = None
    out_dir = cli_path(a.out, "--out", must_exist=False, want_dir=True) if a.out else None   # no link followed
    if out_dir and os.path.lexists(out_dir) and not (os.path.isdir(out_dir) and not os.path.islink(out_dir)
                                                     and not os.listdir(out_dir)):
        # a used --out holds an earlier run's verdict files: refused before either route starts (as
        # bin/fastverify refuses it, finding 067), never filled with a second, contradicting verdict
        return _emit_refusal(a, "project", f"refused: --out {a.out} exists and is not an empty directory (an output "
                             "directory is never reused)", t0, target={"project": proj_disp, "challenge": chal_disp})
    if not out_dir:
        temp_out = tempfile.mkdtemp(prefix="fv-run.")
        out_dir = os.path.join(temp_out, "out")
    guard_js = os.path.join(tempfile.gettempdir(), f"fv-guard-{os.getpid()}-{int(t0*1000)}.json") if a.guard else None
    try:
        # the incremental path runs only with the project's verified official toolchain, and anything
        # but a verdict of its trusted check (a failed untrusted incremental build / export, a refused toolchain) sends the
        # project to the cold path below: it is never reported as REJECTED (the cold path confirms build failures officially)
        incr_tc, incr_note = (None, _incr_unsupported(a)) if a.incr_base else (None, None)
        if a.incr_base and not _INCR_IN_BIN_FV:   # incremental mode is experimental: unused
            # the given base path obeys the path policy (no link at any component); its CONTENTS are never read
            # in v0.1 (a real --keep-work base holds links: a whole-tree scan refused every real base)
            cli_path(a.incr_base, "--incr-base", want_dir=True)
            incr_note = _INCR_V01_NOTE
        if a.incr_base and not incr_note:
            incr_tc, incr_note = _incr_toolchain(proj, chal)
        if a.incr_base and not incr_note:
            if getattr(a, "pins", None):
                raise SystemExit("fv verify --pins is not yet supported with --incr-base (omit --incr-base to use bin/fastverify --pins)")
            if not pin:
                raise SystemExit("fv verify --incr-base requires --challenge-sha256 HEX (or --trust-challenge-sha256-file)")
            os.makedirs(out_dir, exist_ok=True)
            cmd = [os.path.join(FV_ROOT, "tools", "incr", "incr-reverify.sh"),
                   cli_scan_no_links(a.incr_base, "--incr-base"), proj, chal, out_dir,   # no link in the base
                   "--challenge-sha256", pin]
            if not cfg_pin:   # incr-reverify requires the caller's comparator pin (scheme 2)
                raise SystemExit("fv verify --incr-base requires --comparator-sha256 HEX (forwarded to incr-reverify)")
            cmd += ["--comparator-sha256", cfg_pin]
            if a.threads:
                cmd += ["--threads", str(a.threads)]
            cmd += ["--toolchain", incr_tc]   # explicit: bin/fv's env -i drops INCR_TC
            pk = _packages_arg(a, chal_disp)
            if pk:
                cmd += ["--packages", pk]
            if a.optimistic:
                cmd.append("--optimistic")
            if a.closure_only:
                cmd.append("--closure-only")
            if a.integrity_cache:
                cmd += ["--integrity-cache", cli_path(a.integrity_cache, "--integrity-cache", must_exist=False)]
            cmd = wrap_with_guard(cmd, a.guard, guard_js)
            p = subprocess.run(cmd, capture_output=a.json or a.quiet, text=True)   # --quiet: no terminal output
            gv = check_guard_violation(guard_js, "project_incremental", time.time() - t0, {"project": proj_disp, "challenge": chal_disp})
            sp = os.path.join(out_dir, "summary.json")
            if gv is not None:
                env = gv
            elif os.path.isfile(sp):
                try:
                    summ_obj = json.load(open(sp, encoding="utf-8"))
                except (OSError, ValueError) as e:
                    env = fv_schema.from_error("project_incremental", f"malformed incr summary.json: {e}", time.time() - t0)
                else:
                    env = fv_schema.enforce_process_exit(
                        fv_schema.from_incr_summary(summ_obj, proj_disp, chal_disp, pin,
                                                    total_s=time.time() - t0, include_raw=a.include_raw),
                        p.returncode, "project_incremental", time.time() - t0,
                    )
            else:
                env = fv_schema.from_error("project_incremental", f"incr-reverify exited {p.returncode}", time.time() - t0)
            if gv is None and env.get("verdict") not in ("ACCEPTED", "REJECTED", "CONDITIONAL"):
                try:
                    outc = ",".join(str(x.get("outcome")) for x in json.load(open(sp, encoding="utf-8")).get("attempts") or [])
                except (OSError, ValueError, AttributeError):
                    outc = f"incr-reverify exit {p.returncode}"
                incr_note = f"the incremental re-verification gave no verdict ({outc or env.get('verdict')})"
        if not a.incr_base or incr_note:
            if a.incr_base and not a.quiet and not a.json:
                print(f"fv verify: warning: {incr_note}; judging the project by the cold path", file=sys.stderr)
            if a.incr_base and os.path.isdir(out_dir) and os.listdir(out_dir):
                # an incremental attempt of this invocation ran in OUT: the cold path gets its own empty OUT below it
                os.makedirs(out_dir, exist_ok=True)
                if os.path.isfile(os.path.join(out_dir, "summary.json")):   # this invocation's no-verdict attempt:
                    os.replace(os.path.join(out_dir, "summary.json"),       # no top-level summary.json besides the verdict
                               os.path.join(out_dir, "incremental-attempt-no-verdict.json"))
                out_dir = tempfile.mkdtemp(prefix="cold-fallback.", dir=out_dir)
            cmd = [os.path.join(FV_ROOT, "bin", "fastverify"), proj, chal, out_dir, "--preset", a.preset]
            if pin:
                cmd += ["--challenge-sha256", pin]
            if cfg_pin:   # the comparator pin is forwarded: bin/fastverify checks its private copy
                cmd += ["--comparator-sha256", cfg_pin]
            if a.threads:
                cmd += ["--threads", str(a.threads)]
            pk = _packages_arg(a, chal_disp)
            if pk:
                cmd += ["--packages", pk]
            if a.build:
                cmd += ["--build", a.build]
            if a.export_dir:
                cmd += ["--export-dir", a.export_dir if a.export_dir == "none" else cli_path(a.export_dir, "--export-dir", want_dir=True)]
            if getattr(a, "build_cache", None):   # checked here (no link at any component), never via --extra-arg
                cmd += ["--build-cache", a.build_cache if a.build_cache == "none"
                        else cli_path(a.build_cache, "--build-cache", must_exist=False, want_dir=True)]
            if a.keep_work:
                cmd.append("--keep-work")
            if a.confirm_reject:
                cmd.append("--confirm-reject")
            if getattr(a, "no_integrity_cache", False):
                cmd.append("--no-integrity-cache")
            try:
                pins_p = _resolve_pins_arg(getattr(a, "pins", None), ctx="fv verify")
            except PinsRefused as e:
                return _emit_refusal(a, "project", str(e), t0, target={"project": proj_disp, "challenge": chal_disp})
            if pins_p:
                cmd += ["--pins", pins_p]
            if getattr(a, "modulo_frontier", None):
                mf = a.modulo_frontier
                if mf != "auto":   # a private no-follow copy, as on MCP (never the raw path)
                    a._mf_disp = cli_path(mf, "--modulo-frontier", want_dir=False)
                    mf = a._mf_priv = cli_copy_file(mf, os.path.join(os.path.dirname(proj), "modulo_frontier.txt"),
                                                    "--modulo-frontier")
                cmd += ["--modulo-frontier", mf]
            if getattr(a, "frontier_pin", None):
                cmd += ["--frontier-pin", cli_copy_tree(a.frontier_pin, os.path.join(os.path.dirname(proj), "frontier_pin"), "--frontier-pin")]
            if getattr(a, "frontier_base", None):
                cmd += ["--frontier-base", cli_copy_file(a.frontier_base, os.path.join(os.path.dirname(proj), "frontier_base.json"), "--frontier-base")]
            if a.extra_args:
                cmd.extend(a.extra_args)
            cmd = wrap_with_guard(cmd, a.guard, guard_js)
            p = subprocess.run(cmd, capture_output=a.json or a.quiet, text=True)   # --quiet: no terminal output
            gv = check_guard_violation(guard_js, "project", time.time() - t0, {"project": proj_disp, "challenge": chal_disp})
            rp = os.path.join(out_dir, "result.json")
            if gv is not None:
                env = gv
            elif os.path.isfile(rp):
                try:
                    res_obj = json.load(open(rp, encoding="utf-8"))
                except (OSError, ValueError) as e:
                    env = fv_schema.from_error("project", f"malformed result.json: {e}", time.time() - t0)
                else:
                    env = fv_schema.enforce_process_exit(
                        fv_schema.from_fastverify_result(res_obj, total_s=time.time() - t0, project_dir=proj_disp,
                                                         include_raw=a.include_raw),
                        p.returncode, "project", time.time() - t0,
                    )
                    if sound_preset and env.get("verdict") in ("ACCEPTED", "CONDITIONAL") and not sound_preset_ran(a.preset, res_obj):
                        # a verdict that does not come from the requested sound check is no verdict
                        env = fv_schema.from_error("project", f"result does not come from the requested --preset {a.preset} "
                                                   f"trusted check (mode {res_obj.get('mode')!r}, trust {res_obj.get('trust')!r})",
                                                   time.time() - t0, target={"project": proj_disp, "challenge": chal_disp})
                    if env.get("verdict") in ("ACCEPTED", "CONDITIONAL"):
                        # ... and about exactly what fv verify was asked to judge, against its own pins
                        why = result_input_mismatch(res_obj, pin, cfg_pin or cfg_sha_here)
                        if why:
                            env = fv_schema.from_error("project", "result does not match fv verify's inputs: " + why,
                                                       time.time() - t0, target={"project": proj_disp, "challenge": chal_disp})
            else:
                msg = (p.stderr or p.stdout or f"fastverify exited {p.returncode}")[-400:] if (a.json or a.quiet) else f"fastverify exited {p.returncode}"
                env = fv_schema.from_error("project", msg, time.time() - t0)
        # diagnostics name files of the private copies: report them under the caller's paths
        env = json.loads(json.dumps(env).replace(json.dumps(proj)[1:-1], json.dumps(proj_disp)[1:-1])
                         .replace(json.dumps(chal)[1:-1], json.dumps(chal_disp)[1:-1])
                         .replace(json.dumps(getattr(a, "_mf_priv", "\x00"))[1:-1], json.dumps(getattr(a, "_mf_disp", ""))[1:-1]))
        if a.incr_base and incr_note and isinstance(env, dict):   # say which path judged it
            env["verdict_basis"] = (f"{env.get('verdict_basis') or ''} [fv verify --incr-base: {incr_note}; judged by the "
                                    "cold path]").strip()
            if isinstance(env.get("warnings"), list):   # and warn
                env["warnings"].append(f"fv verify --incr-base: {incr_note}")
        write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
        if a.json:
            print(json.dumps(env, indent=2))
        elif not a.quiet:
            print_human_envelope(env)
        return env["exit_code"]
    finally:
        if guard_js and os.path.exists(guard_js):
            try:
                os.unlink(guard_js)
            except OSError:
                pass
        if temp_out and not a.keep_work:
            shutil.rmtree(temp_out, ignore_errors=True)


def _release_pins_shorthand(chx):
    """the check/sound/pins-<X>.env whose TC_VERSION is the challenge export's Lean release (its meta line), as its
    shorthand '<X>' for --pins; None = the default judge (pins.env). An unreadable meta line: None (the cross-version gate
    decides what the default judge may judge)."""
    import glob
    try:
        with open(chx, "rb") as f:
            first = f.readline(1 << 20)
        ver = (json.loads(first).get("meta") or {}).get("lean", {}).get("version")
    except (OSError, ValueError, AttributeError):
        return None
    if not isinstance(ver, str) or not ver:
        return None
    want = "leanprover/lean4:v" + ver
    for f in sorted(glob.glob(os.path.join(FV_ROOT, "check", "sound", "pins-*.env"))):
        try:
            tv = [ln.split("=", 1)[1].strip() for ln in open(f, encoding="utf-8") if ln.startswith("TC_VERSION=")]
        except OSError:
            continue
        if tv and tv[0] == want:
            return os.path.basename(f)[len("pins-"):-len(".env")]
    return None


def cmd_check(a):
    """every input is checked without resolving it and judged / hashed as a private copy
    made from the opened fd (hashing the caller's paths through a symlink would be an sha256 oracle)"""
    if not fv_schema.validate_sha256(a.challenge_sha256):
        raise SystemExit("fv check: --challenge-sha256 must be 64 lowercase hex digits")
    if a.frontier and getattr(a, "notary", False):   # two different judges: never a silent choice
        raise SystemExit("fv check: --frontier and --notary are different judges: choose one")
    if a.challenge:
        cdir = cli_path(a.challenge, "--challenge", want_dir=True)
        chx_a = a.challenge_export or os.path.join(cdir, "challenge.export")
        cfg_a = a.comparator_json or os.path.join(cdir, "comparator.json")
    else:
        if not a.challenge_export or not a.comparator_json:
            raise SystemExit("fv check: provide --challenge DIR or both --challenge-export and --comparator-json")
        chx_a, cfg_a = a.challenge_export, a.comparator_json
    in_tmp = tempfile.mkdtemp(prefix="fv-check-in.")
    try:
        exp = cli_path(a.export_file, "export_file", must_exist=False, want_dir=False)
        chx = cli_path(chx_a, "challenge_export", must_exist=False, want_dir=False)
        cfg = cli_path(cfg_a, "comparator_json", must_exist=False, want_dir=False)
        priv = {}
        for k, src, fn in (("exp", exp, "solution.export"), ("chx", chx, "challenge.export"), ("cfg", cfg, "comparator.json")):
            if os.path.lexists(src):
                priv[k] = cli_copy_file(src, os.path.join(in_tmp, fn), k)
        return _cmd_check(a, exp, priv.get("exp"), priv.get("chx"), priv.get("cfg"), chx, cfg, in_tmp)
    finally:
        shutil.rmtree(in_tmp, ignore_errors=True)


def _cmd_check(a, exp, priv_exp_in, chx, cfg, chx_disp, cfg_disp, in_tmp):
    t0 = time.time()
    if not priv_exp_in:
        env = fv_schema.from_error("export_in", f"export_file not found: {a.export_file}", time.time() - t0)
        write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
        if a.json:
            print(json.dumps(env, indent=2))
        elif not a.quiet:
            print_human_envelope(env)
        return env["exit_code"]
    if not chx or not cfg:
        env = fv_schema.from_error("export_in", f"challenge_export or comparator_json not found ({chx_disp}, {cfg_disp})", time.time() - t0)
        write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
        if a.json:
            print(json.dumps(env, indent=2))
        elif not a.quiet:
            print_human_envelope(env)
        return env["exit_code"]
    got = fv_schema.sha256_file(chx)
    cfg_pin = getattr(a, "comparator_sha256", None)
    if cfg_pin is not None and not fv_schema.validate_sha256(cfg_pin):   # an empty value is malformed too
        raise SystemExit("fv check: --comparator-sha256 must be 64 lowercase hex digits")
    got_cfg = fv_schema.sha256_file(cfg)
    if got != a.challenge_sha256:
        env = fv_schema.from_error("export_in", f"challenge_export sha256 mismatch (got {got}, pinned {a.challenge_sha256})",
                                   time.time() - t0)
    elif cfg_pin and got_cfg != cfg_pin:
        env = fv_schema.from_error("export_in", f"comparator_json sha256 mismatch (got {got_cfg}, pinned {cfg_pin})",
                                   time.time() - t0)
    else:
        tmpd = tempfile.mkdtemp(prefix="fv-chk.")
        try:
            priv_exp = priv_exp_in   # the private no-follow copy made by cmd_check
            jsf = os.path.join(tmpd, "check.json")
            logf = os.path.join(tmpd, "check.log")
            rel = _release_pins_shorthand(chx)   # the challenge release's own judge, one rule everywhere
            if getattr(a, "pins", None) is None and not getattr(a, "notary", False):
                a.pins = rel
            try:
                pins_p = _resolve_pins_arg(getattr(a, "pins", None), ctx="fv check",
                                           lowmem=bool(getattr(a, "low_mem", False) and not a.frontier and not getattr(a, "notary", False)))
            except PinsRefused as e:
                return _emit_refusal(a, "frontier" if a.frontier else "export_in", str(e), t0, target={"export_path": exp})
            ax_err = mcp_server.validate_s1_comparator_axioms(cfg)
            if ax_err:
                env = fv_schema.from_error("frontier" if a.frontier else "export_in", ax_err, time.time() - t0,
                                           target={"export_path": exp})
                write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
                if a.json:
                    print(json.dumps(env, indent=2))
                elif not a.quiet:
                    print_human_envelope(env)
                return env["exit_code"]
            xv_rc, xv_reason = mcp_server.run_xversion_gate(FV_ROOT, chx, cfg)
            if xv_rc == 1:
                trust_lbl = "notary" if getattr(a, "notary", False) else "sound"
                env = fv_schema.make_envelope(
                    mode="frontier" if a.frontier else "export_in",
                    verdict="REJECTED",
                    trust=trust_lbl,
                    verdict_basis=f"{trust_lbl.upper()}: rejected by challenge release comparator rule (check/xversion): {xv_reason}",
                    total_s=time.time() - t0,
                    reason=xv_reason,
                    target={"export_path": exp, "challenge_sha256": a.challenge_sha256},
                    diagnostics=fv_schema.classify_verdict_diagnostic("REJECTED", xv_reason),
                )
                write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
                if a.json:
                    print(json.dumps(env, indent=2))
                elif not a.quiet:
                    print_human_envelope(env)
                return env["exit_code"]
            elif xv_rc != 0:
                env = fv_schema.from_error("frontier" if a.frontier else "export_in",
                                           f"cross-version gate: {xv_reason}", time.time() - t0,
                                           target={"export_path": exp})
                write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
                if a.json:
                    print(json.dumps(env, indent=2))
                elif not a.quiet:
                    print_human_envelope(env)
                return env["exit_code"]
            if (getattr(a, "pins", None) is None and getattr(a, "notary", False) and not a.frontier
                    and rel is not None):   # one release rule: after the release check, notary has no judge for it
                return _emit_refusal(a, "export_in", f"refused: --notary has no judge for this challenge's release (pins-{rel}.env "
                                     "is its trusted check) in v0.1; run without --notary", t0, target={"export_path": exp})
            if getattr(a, "notary", False) and not getattr(a, "experimental", False):
                # the notary judge is EXPERIMENTAL in v0.1 (bin/fastverify gates its notary preset the
                # same way); after the release check, so a release-check REJECTED stays REJECTED
                return _emit_refusal(a, "export_in", "refused: --notary is EXPERIMENTAL in fastverify v0.1 (the notary judge is not "
                                     "release grade): pass --experimental to run it", t0, target={"export_path": exp})
            if not getattr(a, "notary", False):
                # one release rule, as bin/fastverify: an explicit --pins (436, default,
                # a path) is used only when it IS the challenge release's own judge; another release's judge is refused
                sub_ = "lowmem" if (getattr(a, "low_mem", False) and not a.frontier) else "sound"
                want_ = os.path.realpath(os.path.join(FV_ROOT, "check", sub_, f"pins-{rel}.env" if rel else "pins.env"))
                got_ = os.path.realpath(pins_p) if pins_p else os.path.realpath(os.path.join(FV_ROOT, "check", sub_, "pins.env"))
                if got_ != want_:
                    return _emit_refusal(a, "frontier" if a.frontier else "export_in",
                                         f"refused: --pins selects {os.path.basename(got_)}, but this challenge's release is "
                                         f"judged only by its own trusted check {os.path.basename(want_)} (never another "
                                         "release's judge); run without --pins", t0, target={"export_path": exp})
            if a.frontier:
                chk_sh = os.path.join(FV_ROOT, "check", "frontier", "check-frontier.sh")
                cmd = [chk_sh, priv_exp, chx, cfg, "--json", jsf, "--log", logf]
                if a.allowed_frontier:   # private no-follow copies
                    cmd += ["--allowed", cli_copy_file(a.allowed_frontier, os.path.join(in_tmp, "allowed"), "--allowed-frontier")]
                if getattr(a, "frontier_axioms", None):
                    cmd += ["--axioms", cli_copy_file(a.frontier_axioms, os.path.join(in_tmp, "axioms"), "--frontier-axioms")]
                if a.frontier_pinned:
                    cmd += ["--pinned", cli_copy_tree(a.frontier_pinned, os.path.join(in_tmp, "pinned"), "--frontier-pinned")]
                if getattr(a, "frontier_base", None):
                    cmd += ["--base", cli_copy_file(a.frontier_base, os.path.join(in_tmp, "base.json"), "--frontier-base")]
                if pins_p:
                    cmd += ["--pins", pins_p]
            else:
                if getattr(a, "notary", False):
                    if pins_p:
                        raise SystemExit("fv check: --pins cannot be combined with --notary")
                    chk_sh = os.path.join(FV_ROOT, "check", "notary", "check-notary.sh")
                    if not os.path.isfile(chk_sh):
                        raise SystemExit("fv check --notary: check/notary/check-notary.sh not installed")
                    cmd = [chk_sh, priv_exp, chx, cfg, "--json", jsf, "--log", logf]
                    if getattr(a, "notary_kernels", None):
                        cmd += ["--kernels", a.notary_kernels]
                elif getattr(a, "low_mem", False):
                    chk_sh = os.path.join(FV_ROOT, "check", "lowmem", "check-sound-lowmem.sh")
                    if not os.path.isfile(chk_sh):
                        raise SystemExit("fv check --low-mem: check/lowmem/check-sound-lowmem.sh not installed")
                    cmd = [chk_sh, priv_exp, chx, cfg, "--json", jsf, "--log", logf]
                    if pins_p:
                        cmd += ["--pins", pins_p]
                else:
                    chk_sh = os.path.join(FV_ROOT, "check", "sound", "check-sound.sh")
                    cmd = [chk_sh, priv_exp, chx, cfg, "--json", jsf, "--log", logf]
                    if pins_p:
                        cmd += ["--pins", pins_p]
            if a.threads:
                cmd += ["--threads", str(a.threads)]
            if a.timeout:
                cmd += ["--timeout", str(a.timeout)]
            try:
                if "--challenge-sha256)" in open(chk_sh, encoding="utf-8", errors="replace").read():
                    cmd += ["--challenge-sha256", a.challenge_sha256, "--comparator-sha256", got_cfg]
            except OSError:
                pass
            guard_js = os.path.join(tmpd, "guard.json") if a.guard else None
            cmd = wrap_with_guard(cmd, a.guard, guard_js)
            p = subprocess.run(cmd, capture_output=True, text=True)
            gv = check_guard_violation(guard_js, "frontier" if a.frontier else "export_in", time.time() - t0, {"export_path": exp})
            chk_mode = "frontier" if a.frontier else "export_in"
            if gv is not None:
                env = gv
            elif os.path.isfile(jsf):
                try:
                    raw_js = json.load(open(jsf, encoding="utf-8"))
                except (OSError, ValueError) as e:
                    env = fv_schema.from_error(chk_mode, f"malformed check.json: {e}", time.time() - t0)
                else:
                    if a.frontier:
                        env = fv_schema.from_check_frontier_result(raw_js, exp, a.challenge_sha256,
                                                                   total_s=time.time() - t0, include_raw=a.include_raw)
                    else:
                        env = fv_schema.from_check_sound_result(raw_js, exp, a.challenge_sha256,
                                                                total_s=time.time() - t0, include_raw=a.include_raw)
                    env = fv_schema.enforce_process_exit(env, p.returncode, chk_mode, time.time() - t0)
            else:
                env = fv_schema.from_error("frontier" if a.frontier else "export_in",
                                           f"checker exited {p.returncode}: {(p.stderr or p.stdout)[-300:]}",
                                           time.time() - t0)
        finally:
            shutil.rmtree(tmpd, ignore_errors=True)
    write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
    if a.json:
        print(json.dumps(env, indent=2))
    elif not a.quiet:
        print_human_envelope(env)
    return env["exit_code"]


def cmd_attempt(a):
    t0 = time.time()
    # the attempt file is read without following any link (single-link regular file)
    src = sys.stdin.read() if a.file == "-" else cli_read(a.file, "file", 16 << 20).decode("utf-8", "replace")
    sfile = None if a.file == "-" else cli_path(a.file, "file", want_dir=False)
    if a.http:
        url = a.http.rstrip("/") + "/v1/verify"
        body = json.dumps({"pset": a.pset, "theorem": a.theorem, "source": src}).encode("utf-8")
        headers = {"Content-Type": "application/json"}
        if a.api_key:
            headers["Authorization"] = f"Bearer {a.api_key}"
        req = urllib.request.Request(url, data=body, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=a.timeout) as r:
                env = json.loads(r.read().decode("utf-8"))
        except (OSError, ValueError) as e:   # no verdict was received: ERROR, exit 2
            raise SystemExit(f"fv attempt: fvapi at {a.http} unavailable or gave no verdict ({type(e).__name__}: {e}); "
                             "the attempt was not judged")
        bad = fv_schema.validate_v1(env) if isinstance(env, dict) else ["not a JSON object"]
        if not bad and env.get("mode") != "attempt":   # a single attempt, never a batch summary or other mode
            bad = [f"mode {env.get('mode')!r} is not a single-attempt result"]
        if bad:   # nothing is published from a response that is not one complete, consistent v1 envelope
            raise SystemExit(f"fv attempt: fvapi at {a.http} returned no valid result envelope ({'; '.join(bad[:3])}); "
                             "no verdict")
    elif a.state:
        st_dir = cli_path(a.state, "--state", want_dir=True)   # no link at any component
        try:
            raw = fvserve.request(st_dir, {"op": "verify", "pset": a.pset, "theorem": a.theorem, "source": src},
                                  timeout=a.timeout)
        except (OSError, ValueError) as e:   # e.g. no daemon socket: ERROR, exit 2, not a rejection
            raise SystemExit(f"fv attempt: fvserve daemon at --state {a.state} unavailable or gave no verdict "
                             f"({type(e).__name__}: {e}); the attempt was not judged")
        env = fv_schema.from_fvserve_result(raw, pset=a.pset, theorem=a.theorem, source_file=sfile,
                                            include_raw=a.include_raw)
    else:
        raise SystemExit("fv attempt: provide either --state DIR (fvserve) or --http URL (fvapi)")
    env["timing"]["cli_wall_s"] = round(time.time() - t0, 4)
    if sfile and a.http:   # on the fvapi path: the service's private Attempt/<theorem>.lean -> the
        att = "Attempt/" + str(a.theorem or "").replace(".", "/") + ".lean"   # caller's source file
        for d in env.get("diagnostics") or []:
            f = d.get("file") if isinstance(d, dict) else None
            if isinstance(f, str) and (f == att or f.endswith("/" + att)):
                d["file"] = sfile
    write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
    if a.json:
        print(json.dumps(env, indent=2))
    elif not a.quiet:
        print_human_envelope(env)
    return env["exit_code"]


def _resolve_repo_toolchain(explicit_tc, repo_dir):
    if explicit_tc:   # an explicit toolchain dir: no link at any component
        return cli_path(explicit_tc, "--toolchain", want_dir=True)
    if repo_dir:
        # lean-toolchain read without following a link (repo_dir: a private copy or a checked local path)
        tcf = cli_path(os.path.join(repo_dir, "lean-toolchain"), "lean-toolchain", must_exist=False)
        comp_p = os.path.join(FV_ROOT, "config", "components.json")
        if os.path.lexists(tcf) and os.path.isfile(comp_p):
            try:
                want = cli_read(tcf, "lean-toolchain", 256).decode("utf-8", "replace").strip()
                pref = (json.load(open(comp_p, encoding="utf-8")).get("lean_toolchains") or {}).get(want, {}).get("prefix")
                if pref and os.path.isdir(pref):
                    return pref
            except Exception:
                pass
    return _default_toolchain()


def _lean_cannot_start(tc):
    """True if the toolchain's lean cannot even print its version (a missing interpreter / loader, a broken file)"""
    try:   # inside bwrap (no network, read-only filesystem, private /tmp), as the probe itself
        r = subprocess.run(["/usr/bin/bwrap", "--die-with-parent", "--unshare-all", "--ro-bind", "/", "/", "--dev", "/dev",
                            "--proc", "/proc", "--tmpfs", "/tmp", "--ro-bind", os.path.realpath(tc), os.path.realpath(tc),
                            "--clearenv", "--setenv", "PATH", "/usr/bin:/bin",   # a toolchain under /tmp too
                            "--setenv", "HOME", "/tmp", "--setenv", "LANG", "C.UTF-8",
                            os.path.join(os.path.realpath(tc), "bin", "lean"), "--version"], capture_output=True, text=True,
                           timeout=30)
        return r.returncode != 0 or "Lean" not in (r.stdout or "")
    except (OSError, subprocess.SubprocessError):
        return True


def _experimental_gate(a, name):
    """fv watch / fv triage ship EXPERIMENTAL: refused (exit 2) unless --experimental"""
    if not getattr(a, "experimental", False):
        raise SystemExit(f"fv {name} is EXPERIMENTAL in fastverify v0.1 (not release grade): pass --experimental to run it")


def cmd_triage(a):
    _experimental_gate(a, "triage")
    # the file is read without following links; --repo is scanned as a private no-follow copy of its .lean
    # files (+ lean-toolchain), as on MCP; --packages / --snapshot-dir are checked paths (no link at any component)
    src = sys.stdin.read() if a.file == "-" else cli_read(a.file, "file", 16 << 20).decode("utf-8", "replace")
    rtmp = tempfile.mkdtemp(prefix="fv-triage-in.") if a.repo else None
    try:
        repo = cli_copy_tree(a.repo, os.path.join(rtmp, "repo"), "--repo",
                             file_filter=lambda n: n.endswith(".lean") or n == "lean-toolchain") if a.repo else None
        tc_t = _resolve_repo_toolchain(a.toolchain, repo)
        if not a.static_only and not (os.path.isfile(os.path.join(tc_t, "bin", "lean")) and   # a regular executable
                                      os.access(os.path.join(tc_t, "bin", "lean"), os.X_OK)):
            # a Lean probe that cannot start (its output has no Lean diagnostic, which triage
            # would read as "the negation elaborated" = REFUTED, exit 1) is an input error: exit 2
            raise SystemExit(f"fv triage: toolchain {tc_t}: bin/lean is not an executable file (pass --toolchain DIR or "
                             "--static-only)")
        if not a.static_only and _lean_cannot_start(tc_t):   # positive evidence that the probe can start
            raise SystemExit(f"fv triage: toolchain {tc_t}: bin/lean does not start (`lean --version` failed); no triage")
        ws_t = cli_packages(a.packages) if a.packages else None
        snap_t = cli_path(a.snapshot_dir, "--snapshot-dir", want_dir=True) if a.snapshot_dir else None
        try:
            res = triage.triage_sublemma(src, decl_name=a.theorem, tc=tc_t, ws=ws_t, snap_dir=snap_t, repo_dir=repo,
                                         run_lean_probes=(not a.static_only), timeout=a.timeout)
        except (OSError, RuntimeError, ValueError, UnicodeError) as e:   # no evidence: UNCLEAR, exit 2
            res = {"api_version": fv_schema.API_VERSION, "status": "UNCLEAR", "dispatch_recommended": False,
                   "statement": None, "probe": {"ran": False}, "duplicates": [],
                   "findings": [{"kind": "probe_incomplete", "severity": "error",
                                 "message": "triage could not run: %s (UNCLEAR)" % fv_schema.sanitize_single_line(e, 200)}],
                   "total_s": 0.0}
    finally:
        if rtmp:
            shutil.rmtree(rtmp, ignore_errors=True)
    if a.json:
        print(json.dumps(res, indent=2))
    else:
        print(f"[TRIAGE {res['status']}] dispatch={res['dispatch_recommended']} time={res['total_s']}s")
        for f in res["findings"]:
            print(f"  {f['severity'].upper()} ({f['kind']}): {f['message']}")
    # exit 0 = dispatch, 1 = a finding against the statement, 2 = no evidence either way (UNCLEAR)
    return 0 if res["dispatch_recommended"] else (2 if res["status"] == "UNCLEAR" else 1)


def cmd_init_challenge(a):
    t0 = time.time()
    # the paths are passed as given: init_official_challenge walks them from cli_roots() with
    # O_NOFOLLOW (os.path.realpath here would follow a symlinked challenge / out dir before any check)
    res = mcp_server.init_official_challenge(
        FV_ROOT, a.challenge, a.out,
        packages_dir=cli_packages(a.packages) if a.packages else None,
        threads=a.threads, timeout=a.timeout,
    )
    res["elapsed_s"] = round(time.time() - t0, 3)
    if a.json:
        print(json.dumps(res, indent=2))
    else:
        if res.get("ok"):
            print(f"[OK] official challenge pinned: {res['challenge_export']}")
            print(f"  sha256: {res['challenge_sha256']}  ({res['size_bytes']} bytes)")
        else:
            print(f"[ERROR] {res.get('error')}", file=sys.stderr)
    return 0 if res.get("ok") else 2


def cmd_mint(a):
    """Mint standalone SHA-256-pinned official sub-challenges from open `sorry` theorems in a Lean project.
    Each minted sub-challenge is exported by the OFFICIAL Lean (B0+E0) so untrusted prover agents
    cannot weaken statements or move the goalposts."""
    t0 = time.time()
    # the project is read and copied WITHOUT following anything (symlink / special file / hard link
    # anywhere: refused), the official source copy lives in a private temp dir, and every output is created inside the
    # out dir without following links (mcp_server's no-follow helpers)
    proj_roots = mcp_server.local_roots(a.project)   # = cli_roots(): nothing of the path is resolved
    out_roots = mcp_server.local_roots(a.out)
    try:
        proj = mcp_server.local_path_under(a.project, proj_roots)
        out_root = mcp_server.local_path_under(a.out, out_roots)
    except mcp_server.ClientPathError as e:
        raise CliRefused(str(e))
    work_tmp = tempfile.mkdtemp(prefix="fv-mint.")
    try:
        return _cmd_mint(a, t0, proj, proj_roots, out_root, out_roots, work_tmp)
    finally:
        shutil.rmtree(work_tmp, ignore_errors=True)


def _cmd_mint(a, t0, proj_given, proj_roots, out_root, out_roots, work_tmp):
    def fail(msg):
        res = {"ok": False, "error": msg}
        print(json.dumps(res, indent=2) if a.json else f"[ERROR] {res['error']}")
        return 2
    proj = os.path.join(work_tmp, "proj")
    try:
        pfd = mcp_server.open_nofollow_under(proj_given, proj_roots, want_dir=True)
        try:
            mcp_server.copy_client_tree(pfd, proj)
        finally:
            os.close(pfd)
        out_fd = mcp_server.open_nofollow_under(out_root, out_roots, want_dir=True, create=True)
    except (mcp_server.ClientPathError, OSError) as e:
        return fail(f"refused: {e}")
    try:
        return _cmd_mint_in(a, t0, proj_given, proj, out_root, out_fd, work_tmp, fail)
    finally:
        os.close(out_fd)


def _cmd_mint_in(a, t0, proj_given, proj, out_root, out_fd, work_tmp, fail):
    # Discover target sorry theorems if --theorems not explicitly passed
    targets = list(a.theorem or [])
    if a.frontier_file:   # read without following links
        for ln in cli_read(a.frontier_file, "--frontier-file", 4 << 20).decode("utf-8", "replace").splitlines():
            s = ln.strip()
            if s and not s.startswith("#"):
                targets.append(s)
    if not targets:
        # Auto-discover theorems containing `sorry` in project .lean files
        for r, ds, fs in os.walk(proj):
            ds[:] = [d for d in ds if not d.startswith(".") and d != ".lake"]
            for fn in sorted(fs):
                if not fn.endswith(".lean"):
                    continue
                txt = open(os.path.join(r, fn), encoding="utf-8", errors="replace").read()
                for m in re.finditer(r"^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b.*?:\s*.*?:=[^\n]*\bsorry\b", txt, re.M | re.S):
                    if m.group(1) not in targets:
                        targets.append(m.group(1))
    if not targets:
        res = {"ok": False, "error": "no frontier theorems specified or discovered"}
        print(json.dumps(res, indent=2) if a.json else f"[ERROR] {res['error']}")
        return 2

    # First build ONE official challenge export containing all frontier theorems via B0+E0
    mod = a.module
    if not mod:
        # Detect root library module from lakefile or .lean files
        lf = os.path.join(proj, "lakefile.toml")
        if os.path.isfile(lf):
            m = re.search(r'name\s*=\s*"([^"]+)"', open(lf).read())
            if m:
                mod = m.group(1)
        if not mod:
            mod = "Challenge"
    permitted = a.permitted_axioms.split(",") if a.permitted_axioms else ["propext", "Quot.sound", "Classical.choice"]
    base_dir = proj   # the private no-follow copy (work_tmp/proj): nothing is written into the user's project or out dir
    base_cfg = {
        "challenge_module": mod,
        "solution_module": mod,
        "theorem_names": targets,
        "definition_names": [],
        "permitted_axioms": permitted,
    }
    with open(os.path.join(base_dir, "comparator.json"), "w", encoding="utf-8") as f:
        json.dump(base_cfg, f, indent=2)

    all_out = os.path.join(out_root, "_all_frontier")
    # a packages workspace is trusted input: used only when given explicitly with --packages (never the
    # project's own .lake/packages, which the no-follow copy does not even read)
    if not a.packages and mcp_server._real_dir_at(proj_given, mcp_server.cli_roots(), (".lake", "packages")):
        return fail("the project has its own .lake/packages: pass the packages workspace explicitly with --packages DIR "
                    "(a workspace is trusted input)")
    pkgs = cli_packages(a.packages) if a.packages else None
    init_res = mcp_server.init_official_challenge(
        FV_ROOT, base_dir, os.path.join(work_tmp, "all_frontier"),
        packages_dir=pkgs, threads=a.threads, timeout=a.timeout,
    )
    if not init_res.get("ok"):
        print(json.dumps(init_res, indent=2) if a.json else f"[ERROR] {init_res.get('error')}")
        return 2
    try:
        afd = mcp_server.subdir_at(out_fd, "_all_frontier")
        try:
            mcp_server.export_tree_to(os.path.join(work_tmp, "all_frontier"), afd)
        finally:
            os.close(afd)
    except (mcp_server.ClientPathError, OSError) as e:
        return fail(f"cannot write {all_out} without following links: {e}")

    # Mint one pinned sub-challenge directory per frontier theorem (each gets its own comparator.json
    # listing ONLY that theorem + a verified copy of the official challenge.export + sha256 pin)
    minted = []
    sha = init_res["challenge_sha256"]
    for thm in targets:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", thm):
            return fail(f"invalid theorem name {thm!r}")
        sdir = os.path.join(out_root, f"sub_{thm}")
        scfg = {
            "challenge_module": mod,
            "solution_module": f"Attempt.{thm}" if a.for_fvserve else mod,
            "theorem_names": [thm],
            "definition_names": [],
            "permitted_axioms": permitted,
        }
        try:
            sfd = mcp_server.subdir_at(out_fd, f"sub_{thm}")
            try:
                xfd = os.open(init_res["challenge_export"], os.O_RDONLY)
                try:
                    mcp_server.write_file_at(sfd, "challenge.export", src_fd=xfd, mode=0o444)
                finally:
                    os.close(xfd)
                mcp_server.write_file_at(sfd, "challenge.export.sha256", f"{sha}  challenge.export\n")
                mcp_server.write_file_at(sfd, "comparator.json", json.dumps(scfg, indent=2))
            finally:
                os.close(sfd)
        except (mcp_server.ClientPathError, OSError) as e:
            return fail(f"cannot write {sdir} without following links: {e}")
        minted.append({"theorem": thm, "dir": sdir, "challenge_sha256": sha})

    manifest = {
        "ok": True,
        "api_version": fv_schema.API_VERSION,
        "project": proj_given,
        "module": mod,
        "count": len(minted),
        "challenge_sha256": sha,
        "batch_pset_dir": all_out,
        "subchallenges": minted,
        "elapsed_s": round(time.time() - t0, 3),
    }
    try:
        mcp_server.write_file_at(out_fd, "mint-manifest.json", json.dumps(manifest, indent=2))
    except (mcp_server.ClientPathError, OSError) as e:
        return fail(f"cannot write the manifest without following links: {e}")
    if a.json:
        print(json.dumps(manifest, indent=2))
    else:
        print(f"[OK] minted {len(minted)} officially-pinned sub-challenge(s) in {manifest['elapsed_s']}s")
        print(f"  batch pset (fvserve): {all_out}  sha256={sha}")
        for m in minted:
            print(f"  - {m['theorem']}: {m['dir']}")
    return 0


def cmd_audit(a):
    if a.challenge_sha256 is not None and not fv_schema.validate_sha256(a.challenge_sha256):   # input error: exit 2
        raise SystemExit("fv audit: --challenge-sha256 must be 64 lowercase hex digits")
    # the challenge (dir or file), --config and --reading-set are passed as given:
    # audit_challenge_dir copies the inputs privately walking from cli_roots() with O_NOFOLLOW before anything is read or
    # hashed, and writes the reading set without following links (never realpath + leaf-only lstat + host pre-hash)
    res = mcp_server.audit_challenge_dir(
        FV_ROOT, a.challenge,
        expected_sha256=a.challenge_sha256,
        probe=bool(getattr(a, "probe", False)),
        packages_dir=cli_packages(a.packages) if getattr(a, "packages", None) else None,
        reading_set_out=getattr(a, "reading_set", None),
        conjecture_mode=bool(getattr(a, "conjecture_mode", False)),
        solution_mode=bool(getattr(a, "solution_mode", False)),
        config_path=getattr(a, "config", None),
    )
    deep = res.get("deep_audit") if isinstance(res.get("deep_audit"), dict) else None
    if deep is None and not res.get("error") and os.path.isfile(os.path.join(FV_ROOT, "tools", "audit", "audit.py")):
        # the installed deep audit engine ran but left no result (e.g. audit.py exit 2 without --json)
        deep = res["deep_audit"] = {"status": "ERROR", "error": "tools/audit/audit.py produced no result"}
    # the audit could not run - a missing / unreadable comparator config or input, a refused
    # input, the deep audit engine reporting ERROR or failing - is an ERROR (exit 2), never ok (0) or a finding (1)
    audit_err = res.get("error") or (deep is not None and (str(deep.get("status") or "").upper() == "ERROR"
                                                         or deep.get("error")) and
                                     "deep audit: " + str(deep.get("error") or deep.get("status")))
    if audit_err:
        res["ok"] = False
        res["error"] = str(audit_err)
    if a.json:
        print(json.dumps(res, indent=2))
    else:
        deep_st = f"  deep_audit={deep.get('status')}" if deep and deep.get("status") else ""
        print(f"[AUDIT {'ERROR: ' + res['error'] if audit_err else 'OK' if res.get('ok') else 'WARN/ERROR'}] "
              f"theorems={res.get('theorem_count')} "
              f"def_holes={res.get('definition_names_count')} axioms={res.get('permitted_axioms')}{deep_st}")
        for f in res.get("findings") or []:
            print(f"  {f['severity'].upper()} [{f['rule_id']}]: {f['message']}")
        if deep:
            rs = deep.get("reading_set")
            if isinstance(rs, dict) and rs.get("total_decls") is not None:
                print(f"  reading_set: {rs.get('non_mathlib_decls', '?')}/{rs.get('total_decls')} non-Mathlib decls")
            for df in (deep.get("findings") or [])[:20]:
                if isinstance(df, dict):
                    sev = str(df.get("severity") or "INFO").upper()
                    code = df.get("code") or df.get("rule") or "AUDIT"
                    decl = f" ({df['decl']})" if df.get("decl") else ""
                    msg = df.get("message") or df.get("detail") or ""
                    print(f"  {sev} [{code}]{decl}: {msg}")
    # the audit could not run (audit_err), or failed without an error finding: exit 2
    if audit_err or (not res.get("ok") and (res.get("error") or not any(isinstance(f, dict) and f.get("severity") == "error"
                                                                        for f in res.get("findings") or []))):
        return 2
    return 0 if res.get("ok") else 1


def cmd_doctor(a):
    # the doctor (and lib/autotune.py) only ever sees a private no-follow copy of
    # --project, as on MCP; autotune runs only if that copy's lakefile paths stay inside it
    if a.project:
        proj_disp = cli_path(a.project, "--project", want_dir=True)
        dtmp = tempfile.mkdtemp(prefix="fv-doctor-in.")
        try:
            priv = cli_copy_tree(a.project, os.path.join(dtmp, "proj"), "--project")
            res = mcp_server.run_host_doctor(FV_ROOT, priv)
            res = json.loads(json.dumps(res).replace(json.dumps(priv)[1:-1], json.dumps(proj_disp)[1:-1]))
        finally:
            shutil.rmtree(dtmp, ignore_errors=True)
    else:
        res = mcp_server.run_host_doctor(FV_ROOT, None)
    if a.json:
        print(json.dumps(res, indent=2))
    else:
        print(f"[DOCTOR {'OK' if res['ok'] else 'ISSUES'}]")
        r = res["checks"]["resources"]
        sp = res["checks"]["sound_pins"]   # readiness = the REQUIRED pins; optional ones are warnings
        sp_txt = (f"required={sp['required_present']}" + (f" optional_missing={','.join(sp['optional_missing'])}"
                                                          if sp.get("optional_missing") else "")
                  if "required_present" in sp else str(sp.get("all_present")))
        print(f"  bwrap={res['checks']['bwrap']['ok']}  sound_pins={sp_txt}  "
              f"cpus={r['affinity_cpus']}  mem_avail={r['mem_avail_gb']}GB  shm_free={r['shm_free_gb']}GB  "
              f"max_map_count={res['checks']['vm_max_map_count']['value']}")
        rec = res["recommendation"]
        print(f"  recommended: --preset {rec['preset']} --threads {rec['threads']} --export-dir {rec['export_dir']}"
              + (f" --build {rec['build_override']}" if rec.get("build_override") else ""))
        for n in rec.get("notes") or []:
            print(f"  tip: {n}")
        for w in res.get("warnings") or []:
            print(f"  WARNING: {w}")
    return 0 if res["ok"] else 2


def snapshot_lean_tree(root):
    snap = {}
    for r, ds, fs in os.walk(root):
        ds[:] = [d for d in ds if not d.startswith(".") and d != ".lake"]
        for fn in fs:
            if fn.endswith(".lean") or fn in ("lakefile.toml", "lakefile.lean", "lean-toolchain"):
                p = os.path.join(r, fn)
                try:
                    st = os.stat(p, follow_symlinks=False)   # metadata only, never through a link
                    snap[os.path.relpath(p, root)] = (st.st_mtime_ns, st.st_size)
                except OSError:
                    pass
    return snap


_WATCH_FVWORK_V01 = False   # daemon-backed project watch refused


def cmd_watch(a):
    """Editor/LSP-friendly continuous watch loop: detects saved .lean edits, runs sound verification
    (via fvserve for single-file attempt mode, or tools/incr / bin/fastverify for project mode),
    emits VS Code problem-matcher diagnostics + LSP JSON + SARIF 2.1.0."""
    _experimental_gate(a, "watch")
    # `fv watch | head`: the watch ends at its first failed stdout write (checked at the write site
    # below); a broken stderr stays diagnostics-only (SIGPIPE is set to its default for the whole process)
    # checked without resolving (no link at any component); file content read without following links
    target = cli_path(a.path, "path", must_exist=False)
    if not os.path.lexists(target):
        raise SystemExit(f"fv watch: path does not exist: {target}")
    is_file = os.path.isfile(target)
    if is_file and (a.challenge or a.challenge_sha256 or getattr(a, "comparator_sha256", None) or a.trust_challenge_sha256_file):
        # (experimental surface) the file-attempt watch is judged by the fvserve daemon's own problem set:
        # a caller's challenge identity is never silently ignored
        raise SystemExit("fv watch FILE (attempt mode) is judged against the fvserve daemon's problem set (--pset / --theorem); "
                         "--challenge / --challenge-sha256 / --comparator-sha256 apply to project watch (a directory) only: refused")
    pin = resolve_challenge_pin(cli_path(a.challenge, "--challenge", want_dir=True), a.challenge_sha256,
                                a.trust_challenge_sha256_file) if a.challenge else None
    last_snap = None
    iterations = 0
    print(f"[fv watch] watching {target} (interval={a.interval}s)", flush=True)
    if _CLI_STATE["stdout_failed"]:   # nobody reads the watch any more: end it (exit 2, output error)
        return 2
    if not is_file and a.fvwork_state and not _WATCH_FVWORK_V01:
        # the edit loop is COLD: a fvwork-daemon-backed project watch (its default is
        # incremental / optimistic, and it cannot check the caller's challenge pins) is not offered in v0.1
        raise SystemExit("fv watch: --fvwork-state (daemon-backed project watch) is experimental and not available in v0.1; "
                         "use `fv watch DIR --challenge DIR --challenge-sha256 HEX --comparator-sha256 HEX` (cold path)")
    if not is_file and a.challenge and not a.fvwork_state:   # the comparator-pin rule, once, before the loop
        cpin = getattr(a, "comparator_sha256", None)
        cdir = cli_path(a.challenge, "--challenge", want_dir=True)   # no link followed
        if cpin is None and (pin is not None or a.challenge_sha256 is not None or a.trust_challenge_sha256_file
                             or os.path.isfile(os.path.join(cdir, "challenge.export"))):
            raise SystemExit("fv watch: --comparator-sha256 HEX is required with a pinned challenge (--challenge-sha256 / "
                             "challenge.export)")
        if cpin is not None and (not fv_schema.validate_sha256(cpin) or not os.path.isfile(os.path.join(cdir, "comparator.json"))
                                 or fv_schema.sha256_file(os.path.join(cdir, "comparator.json")) != cpin):
            raise SystemExit(f"fv watch: --comparator-sha256 {cpin} is malformed or does not match the challenge's comparator.json")
    while True:
        if is_file:
            st = os.stat(target, follow_symlinks=False)
            cur_snap = {os.path.basename(target): (st.st_mtime_ns, st.st_size)}
        else:
            cur_snap = snapshot_lean_tree(target)
        if cur_snap != last_snap:
            changed = sorted(k for k in set(cur_snap) | set(last_snap or {}) if cur_snap.get(k) != (last_snap or {}).get(k))
            last_snap = cur_snap
            iterations += 1
            t0 = time.time()
            if is_file and a.fvserve_state and a.pset and a.theorem:
                raw = fvserve.request(cli_path(a.fvserve_state, "--fvserve-state", want_dir=True), {
                    "op": "verify", "pset": a.pset, "theorem": a.theorem,
                    "source": cli_read(target, "path", 16 << 20).decode("utf-8", "replace"),
                }, timeout=a.timeout)
                env = fv_schema.from_fvserve_result(raw, pset=a.pset, theorem=a.theorem, source_file=target, include_raw=False)
            elif not is_file and a.fvwork_state and _WATCH_FVWORK_V01:
                # fvwork gets a PRIVATE no-follow copy of the tree (as MCP fv_verify_patch), whose
                # lakefile paths stay inside it - never the caller's directory (fvwork rsyncs it, links and all)
                wtmp = tempfile.mkdtemp(prefix="fv-watch-tree.")
                try:
                    priv = cli_copy_tree(target, os.path.join(wtmp, "tree"), "path")
                    lerr = mcp_server.lake_config_confined(priv)
                    if lerr:
                        raise CliRefused(f"path: {lerr}")
                    raw = fvserve.request(cli_path(a.fvwork_state, "--fvwork-state", want_dir=True), {
                        "op": "verify", "tree": priv, "advance": not a.no_advance, "stream": False,
                    }, timeout=a.timeout)
                    raw = json.loads(json.dumps(raw).replace(json.dumps(priv)[1:-1], json.dumps(target)[1:-1]))
                finally:
                    shutil.rmtree(wtmp, ignore_errors=True)
                env = fv_schema.from_fvwork_result(raw, project_dir=target, total_s=time.time() - t0, include_raw=False)
            elif not is_file and a.challenge:
                sub = argparse.Namespace(
                    project=target, challenge=a.challenge, challenge_sha256=a.challenge_sha256,   # raw: same checks
                    comparator_sha256=getattr(a, "comparator_sha256", None),   # forwarded
                    trust_challenge_sha256_file=a.trust_challenge_sha256_file, out=None, incr_base=a.incr_base,
                    optimistic=True, closure_only=a.closure_only, integrity_cache=a.integrity_cache,
                    preset=a.preset, no_integrity_cache=a.no_integrity_cache, build=a.build, threads=a.threads, packages=a.packages,
                    export_dir=a.export_dir, keep_work=False, confirm_reject=False, extra_args=[], guard=None,
                    json=False, quiet=True, include_raw=False, json_out=a.json_out,
                    sarif=a.sarif, lsp_out=a.lsp_out,
                )
                # Run quietly and capture envelope directly
                tmp = tempfile.mkdtemp(prefix="fv-watch.")
                try:
                    js = os.path.join(tmp, "v1.json")
                    sub.json_out = js
                    cmd_verify(sub)
                    env = json.load(open(js, encoding="utf-8"))
                finally:
                    shutil.rmtree(tmp, ignore_errors=True)
            else:
                raise SystemExit("fv watch: for a file pass --fvserve-state/--pset/--theorem; for a project pass --fvwork-state or --challenge")
            write_optional_outputs(env, a.json_out, a.sarif, a.lsp_out)
            # Emit VS Code problem-matcher lines + compact summary
            print(f"[fv watch #{iterations}] changed={changed[:5]} verdict={env['verdict']} trust={env['trust']} "
                  f"wall={round(time.time() - t0, 2)}s", flush=True)
            for d in env.get("diagnostics") or []:
                fp = d.get("file") or target
                ln = d.get("line") or 1
                col = d.get("column") or 1
                print(f"{fp}:{ln}:{col}: {d['severity']}: [{d['rule_id']}] {d['message'].splitlines()[0]}", flush=True)
            fr = env.get("frontier")
            if isinstance(fr, dict) and isinstance(fr.get("frontier"), list):
                for e in fr["frontier"][:10]:
                    if isinstance(e, dict) and e.get("name"):
                        srcs = e.get("source")
                        if isinstance(srcs, list) and srcs and isinstance(srcs[0], dict):
                            print(f"{srcs[0].get('file')}:{srcs[0].get('line')}:1: warning: [FV005] open frontier lemma {e['name']}", flush=True)
                        else:
                            print(f"{target}:1:1: warning: [FV005] open frontier lemma {e['name']}", flush=True)
            if _CLI_STATE["stdout_failed"]:   # `fv watch | head`: the reader is gone - end the watch (exit 2)
                return 2
            if a.once or (a.max_runs and iterations >= a.max_runs):
                return env["exit_code"]
        time.sleep(a.interval)


def cmd_lookup(a):
    """Duplicate-lemma lookup via tools/dupfind/dupfind.py (kernel exphash)."""
    df_py = os.path.join(FV_ROOT, "tools", "dupfind", "dupfind.py")
    if not os.path.isfile(df_py):
        raise SystemExit("fv lookup: tools/dupfind/dupfind.py not installed")
    # the query file and every index's index.sqlite are private no-follow copies (as on MCP); --packages /
    # --snapshot are checked paths (no link at any component)
    ltmp = tempfile.mkdtemp(prefix="fv-lookup-in.")
    try:
        idxs = []
        for i, ix in enumerate(a.index):
            d = os.path.join(ltmp, "ix%d" % i)
            os.makedirs(d)
            cli_copy_file(os.path.join(cli_path(ix, "--index", want_dir=True), "index.sqlite"), os.path.join(d, "index.sqlite"),
                          "--index")
            idxs.append(d)
        if a.file:
            fdisp = cli_path(a.file, "file", want_dir=False)
            qf = cli_copy_file(a.file, os.path.join(ltmp, os.path.basename(fdisp)), "file")
            tc = _resolve_repo_toolchain(a.toolchain, os.path.dirname(fdisp))
            cmd = ["/usr/bin/python3", "-I", df_py, "query", qf, "--fast-export",
                   "--toolchain", tc, "--packages", cli_packages(a.packages), "--fv", FV_ROOT]
            for ix in idxs:
                cmd += ["--index", ix]
            if a.targets:
                cmd += ["--targets", a.targets]
            if a.snapshot:
                cmd += ["--snapshot", cli_path(a.snapshot, "--snapshot", want_dir=True)]
            if a.threads:
                cmd += ["--threads", str(a.threads)]
            if a.json:
                cmd.append("--json")
        else:
            cmd = ["/usr/bin/python3", "-I", df_py, "lookup"]
            for ix in idxs:
                cmd += ["--index", ix]
            for n in (a.name or []):
                cmd += ["--name", n]
            for h in (a.hash or []):
                cmd += ["--hash", h]
            if a.json:
                cmd.append("--json")
        return subprocess.run(cmd).returncode
    finally:
        shutil.rmtree(ltmp, ignore_errors=True)


def cmd_diff(a):
    """Diagnostic kernel-term diff of two .export files via tools/compress/expdiff (never a verdict)."""
    # both exports (and a --targets file) are private no-follow copies (as on MCP)
    old_c = cli_path(a.old_export, "old_export", must_exist=False, want_dir=False)
    new_c = cli_path(a.new_export, "new_export", must_exist=False, want_dir=False)
    if not os.path.lexists(old_c) or not os.path.lexists(new_c):
        err = {"ok": False, "analysis_only": True, "error": "old_export or new_export file not found"}
        print(json.dumps(err, indent=2) if a.json else f"[ERROR] {err['error']}", file=sys.stderr if not a.json else sys.stdout)
        return 2
    dtmp = tempfile.mkdtemp(prefix="fv-diff-in.")
    try:
        old_p = cli_copy_file(old_c, os.path.join(dtmp, "old.export"), "old_export")
        new_p = cli_copy_file(new_c, os.path.join(dtmp, "new.export"), "new_export")
        targets = a.targets
        if targets and ("/" in targets or os.path.lexists(targets)) and os.path.lexists(
                cli_path(targets, "--targets", must_exist=False)):
            targets = cli_copy_file(targets, os.path.join(dtmp, "targets.txt"), "--targets")
        return _cmd_diff(a, old_p, new_p, targets)
    finally:
        shutil.rmtree(dtmp, ignore_errors=True)


def _cmd_diff(a, old_p, new_p, targets):
    res = mcp_server.run_expdiff_diff(
        FV_ROOT, old_p, new_p,
        targets=targets, explain=a.explain,
        dead_lets=a.dead_lets, private_modulo=a.private_modulo,
        threads=a.threads or min(16, os.cpu_count() or 4),
        timeout=a.timeout,
    )
    if a.json:
        print(json.dumps(res, indent=2))
    else:
        if not res.get("ok"):
            print(f"[DIFF ERROR] {res.get('error')}", file=sys.stderr)
            return 2
        sc = res.get("statement_changed_count", 0)
        tag = "DRIFT" if sc else "CLEAN"
        print(f"[DIFF {tag}] {res.get('result')}  (analysis only, wall={res.get('wall_s')}s)")
        for st_name, cnt in sorted((res.get("statuses") or {}).items()):
            if cnt:
                print(f"  {st_name}: {cnt}")
        if res.get("statement_changed"):
            print("  STATEMENT-CHANGED: " + ", ".join(res["statement_changed"][:20]))
        for ex in (res.get("explanations") or [])[:15]:
            print(f"  explain [{ex['status']}] {ex['decl']}: {ex['detail'][:240]}")
    return 0 if res.get("ok") else 2


_GROUP_GUARD = r"""
import os, signal, subprocess, sys, time
# bin/fv's direct child for a process TREE (fv ci -> fv-ci.sh -> guard -> orchestrator): it runs in its own
# process group (start_new_session) with PR_SET_PDEATHSIG = SIGTERM (bin/fv's preexec hook). On SIGTERM / SIGINT / SIGHUP -
# forwarded by bin/fv, or sent by the kernel when bin/fv dies (even by SIGKILL) - the WHOLE group gets the signal (the
# orchestrator records the interruption), then whatever is left after the grace period gets SIGKILL.
def members():   # every live descendant of the guard (fvguard starts its own session) + its own group
    me, pg, par, grp = os.getpid(), os.getpgrp(), {}, {}
    for d in os.listdir("/proc"):
        if d.isdigit():
            try:
                st = open("/proc/%s/stat" % d, "rb").read()
                f = st[st.rindex(b")") + 2:].split()
                if f[0] != b"Z":
                    par[int(d)] = int(f[1]); grp[int(d)] = int(f[2])
            except (OSError, ValueError, IndexError):
                pass
    out = []
    for pid in par:
        if pid == me:
            continue
        q, hops = pid, 0
        while q in par and q != me and hops < 64:
            q, hops = par[q], hops + 1
        if q == me or grp.get(pid) == pg:
            out.append(pid)
    return out
child = None
def stop(signum, frame):
    for s_ in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(s_, signal.SIG_IGN)
    try:
        os.killpg(0, signum)
    except OSError:
        pass
    for pid in members():   # descendants in other sessions (fvguard's) get it too
        try:
            os.kill(pid, signum)
        except OSError:
            pass
    end = time.time() + 50   # shorter than bin/fv's 60 s: this sweep runs before bin/fv's own SIGKILL
    while time.time() < end and members():
        if child is not None:
            child.poll()
        time.sleep(0.1)
    for pid in members():
        try:
            os.kill(pid, signal.SIGKILL)
        except OSError:
            pass
    if child is not None:
        child.poll()
    os._exit(128 + signum)
# the handlers are installed BEFORE the tree is started: a signal in between can no longer orphan it
for s_ in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
    signal.signal(s_, stop)
def _pds():   # the tree's root (fv-ci.sh) gets SIGTERM when this guard dies (even by SIGKILL)
    try:
        import ctypes
        ok = ctypes.CDLL(None, use_errno=True).prctl(1, 15, 0, 0, 0) == 0
    except Exception:
        ok = False
    if not ok:
        os.kill(os.getpid(), 9)
try:
    child = subprocess.Popen(sys.argv[1:], preexec_fn=_pds)
except OSError as e:   # a launch failure is no verdict
    sys.stderr.write("fv ci: cannot start %s: %s\n" % (sys.argv[1], e)); sys.exit(2)
rc = child.wait()
sys.exit(rc if rc >= 0 else 2)   # a child killed by a signal is no verdict (never 128+n / 247)
"""


def _tree_cmd(cmd):
    """the command line that runs CMD, which starts its own process tree (fv-ci.sh), under _GROUP_GUARD (to be
    started with start_new_session=True)"""
    return ["/usr/bin/python3", "-I", "-c", _GROUP_GUARD] + list(cmd)


# ---- a usage error, an infrastructure failure (e.g. no fvserve daemon) or an output
# error is exit 2 with a JSON error object on stdout when --json was given (verify / check / attempt / watch: an API v1 ERROR
# envelope); never Python's default exit 1, which bin/fv reserves for REJECTED (and fv audit for a finding).
# Output-error rule: if a requested output file (--json-out / --sarif / --lsp-out) cannot be written, the whole
# command is an ERROR (exit 2): stdout (--json) carries the ERROR envelope, and every requested output file that CAN be
# written is rewritten with that same ERROR envelope, so no file keeps a verdict the exit status does not report.
_CLI_ENVELOPE_MODE = {"verify": "project", "watch": "project", "check": "export_in", "attempt": "attempt"}
_CLI_ARGS = []
_CLI_STATE = {"outputs_written": False, "stdout_failed": False}
_CLI_OUT_OPTS = (("json_out", "--json-out"), ("sarif", "--sarif"), ("lsp_out", "--lsp-out"))


class CliOutputError(Exception):
    """a requested output file (--json-out / --sarif / --lsp-out) could not be written"""


def _silence_fd(fd):
    """after a failed write: later writes (incl. Python's final flush) go to /dev/null, so the process
    exit status stays bin/fv's own (never Python's 120)"""
    try:
        nul = os.open(os.devnull, os.O_WRONLY)
        os.dup2(nul, fd)
        os.close(nul)
    except OSError:
        pass


class _GuardedStream:
    """stdout / stderr that never raise: a failed write (full device, broken pipe, closed fd)
    is recorded (stdout: the run's output was not delivered -> exit 2) and the fd is pointed at /dev/null"""
    def __init__(self, stream, fd, key):
        self._s, self._fd, self._key = stream, fd, key

    def _failed(self):
        if self._key:
            _CLI_STATE[self._key] = True
        _silence_fd(self._fd)

    def write(self, x):
        if self._key and x:
            _CLI_STATE["stdout_used"] = True
        try:
            if self._s is None:
                raise OSError("closed")
            return self._s.write(x)
        except (OSError, ValueError):
            self._failed()
            return len(x)

    def flush(self):
        try:
            if self._s is not None:
                self._s.flush()
        except (OSError, ValueError):
            self._failed()

    def __getattr__(self, name):
        return getattr(self._s, name)


def _write_optional_outputs_checked(write):
    def wrapped(env, json_out=None, sarif_out=None, lsp_out=None):
        try:
            r = write(env, json_out, sarif_out, lsp_out)
        except Exception as e:  # noqa: BLE001
            raise CliOutputError(f"cannot write a requested output file ({type(e).__name__}: {e}); the run's result "
                                 f"(verdict {env.get('verdict') if isinstance(env, dict) else None}) was not delivered: "
                                 "output error, no verdict") from e
        if json_out or sarif_out or lsp_out:
            _CLI_STATE["outputs_written"] = True
        _CLI_STATE["last_env"] = env
        return r
    wrapped.unchecked = write
    return wrapped


write_optional_outputs = _write_optional_outputs_checked(write_optional_outputs)


_CLI_SUBPARSERS = {}


def _argv_cmd():
    """the subcommand of argv: its first operand (`fv --json check ...` too), None if there is none"""
    for x in sys.argv[1:]:
        if x == "--":
            return None
        if not x.startswith("-"):
            return x
    return None


def _requested_outputs(a):
    """{kw: path} of the requested output files: from the parsed arguments, else (a usage error) from argv, read the way the
    subcommand's parser reads it: long options only, exact or unique-prefix spellings (argparse's
    abbreviations), a value from `--opt=V` or the next token unless that looks like an option, nothing after `--`"""
    if a is not None:
        return {kw: getattr(a, kw) for kw, _ in _CLI_OUT_OPTS if getattr(a, kw, None)}
    cmd = _argv_cmd()
    sp = _CLI_SUBPARSERS.get(cmd)
    if sp is None:
        return {}
    longs = {o: act.dest for o, act in sp._option_string_actions.items() if o.startswith("--")}
    want = {kw for kw, _ in _CLI_OUT_OPTS}
    got, argv = {}, sys.argv[1:]
    i = 0
    while i < len(argv):
        x = argv[i]
        if x == "--":
            break
        if x.startswith("--") and len(x) > 2:
            name, eq, val = x.partition("=")
            cands = [name] if name in longs else [o for o in longs if o.startswith(name)]
            dests = {longs[o] for o in cands}
            if len(dests) == 1:
                dest = dests.pop()
                takes = sp._option_string_actions[cands[0]].nargs != 0
                if takes and not eq:
                    nxt = argv[i + 1] if i + 1 < len(argv) else None
                    if nxt is not None and (not nxt.startswith("-") or nxt == "-" or re.match(r"^-\d+$|^-\d*\.\d+$", nxt)):
                        val, eq = nxt, "="
                        i += 1
                if dest in want and eq and val:
                    got[dest] = val
        i += 1
    return got


def _is_fv_record(path):
    """a file that already holds an fv record: a v1 envelope (also an ERROR record), its LSP form, or its SARIF form"""
    try:
        if not os.path.isfile(path) or os.path.islink(path) or os.path.getsize(path) > (64 << 20):
            return False
        with open(path, encoding="utf-8") as f:
            d = json.load(f)
    except (OSError, ValueError, RecursionError):
        return False
    if isinstance(d, dict) and d.get("api_version") is not None and "verdict" in d:
        return True
    return isinstance(d, dict) and str(d.get("version")) == "2.1.0" and isinstance(d.get("runs"), list)


def _argv_safe_outputs(outs):
    """outputs recovered from the raw argv (a usage error, a signal before parsing):
    an ERROR record goes only where it cannot touch anything else - no symlink; absent, or already an fv record; neither
    equal to nor inside any other path named on the command line (literal and resolved)"""
    toks = sys.argv[2:]
    safe = {}
    for kw, dest in outs.items():
        if os.path.islink(dest) or (os.path.lexists(dest) and not _is_fv_record(dest)):
            continue
        ops = {os.path.abspath(dest), os.path.realpath(dest)}
        others = list(toks)
        for i, t in enumerate(others):   # the output's own value (or --opt=VALUE) once
            if t == dest or (t.startswith("--") and t.partition("=")[2] == dest):
                del others[i]
                break
        hit = False
        for t in others:
            v = t.partition("=")[2] if t.startswith("--") else t
            if not v or v.startswith("-"):
                continue
            for q in {os.path.abspath(v), os.path.realpath(v)}:
                if any(op == q or op.startswith(q.rstrip("/") + "/") for op in ops):
                    hit = True
        if not hit:
            safe[kw] = dest
    return safe


def _write_error_outputs(mode, env, a):
    """best effort, one file at a time (a file written before a failing one is overwritten with the ERROR envelope)"""
    if _CLI_STATE.get("outputs_blocked"):   # an output that collides with an input is never written
        return
    outs = _requested_outputs(a)
    if a is None:   # recovered from argv: only where nothing else can be touched
        outs = _argv_safe_outputs(outs)
    for kw, dest in outs.items():
        try:
            write_optional_outputs.unchecked(env, **{{"sarif": "sarif_out"}.get(kw, kw): dest})
        except Exception:  # noqa: BLE001
            pass
    _CLI_STATE["outputs_written"] = True


def _cli_inputs(a):
    """the input directories / files a verdict command reads (realpaths), for the output-collision check"""
    dirs, files = [], []

    def d_(x):   # both the literal (absolute) and the resolved path
        if x:
            dirs.extend({os.path.abspath(x), os.path.realpath(x)})

    def f_(x):
        if x and x != "-":
            files.extend({os.path.abspath(x), os.path.realpath(x)})
    pins = getattr(a, "pins", None)
    if isinstance(pins, str) and os.sep in pins:   # a pins FILE (the shorthands 436 / 437 / default name no caller file)
        f_(pins)
    if a.cmd == "verify":
        d_(a.project); d_(a.challenge); d_(getattr(a, "packages", None)); d_(getattr(a, "incr_base", None))
        f_(getattr(a, "frontier_base", None))
    elif a.cmd == "check":
        f_(a.export_file); d_(a.challenge); f_(a.challenge_export); f_(a.comparator_json)
        f_(getattr(a, "allowed_frontier", None)); f_(getattr(a, "frontier_axioms", None))
        d_(getattr(a, "frontier_pinned", None)); f_(getattr(a, "frontier_base", None))
    elif a.cmd == "attempt":
        f_(a.file)
    elif a.cmd == "watch":
        (d_ if os.path.isdir(a.path) else f_)(a.path); d_(a.challenge); d_(getattr(a, "packages", None))
    return dirs, files


def _prewrite_error_outputs(a):
    """every requested output file (--json-out / --sarif / --lsp-out) is
    replaced by an ERROR record as soon as its path is known (before any input is read); only this run's completed result
    overwrites it. A refused, failed, interrupted or killed run never leaves an earlier verdict there.
    The replacement is atomic (temp + rename), and an output that cannot be replaced is refused BEFORE anything runs
    (output error, exit 2; the other outputs get the ERROR record)."""
    mode = _cli_mode(a.cmd, a)
    outs = _requested_outputs(a)
    in_dirs, in_files = _cli_inputs(a)
    chk = dict(outs)
    if a.cmd == "verify" and getattr(a, "out", None):   # the --out directory is an output too
        chk["--out"] = a.out
    for kw, dest in chk.items():   # an output never touches an input: refused before ANY write
        ops = {os.path.abspath(dest), os.path.realpath(dest)}
        hit = [d for d in in_dirs for op in ops if op == d or op.startswith(d.rstrip("/") + "/")] + \
              [f for f in in_files if f in ops]
        if hit:
            _CLI_STATE["outputs_blocked"] = True
            raise SystemExit(f"fv {a.cmd}: the requested output {dest} is (inside) the input {hit[0]}: refused before anything "
                             "is written or read (choose an output path outside every input)")
    out_dir = os.path.realpath(a.out) if a.cmd == "verify" and getattr(a, "out", None) else None
    fresh_out = bool(out_dir) and (not os.path.lexists(out_dir) or (os.path.isdir(out_dir) and not os.listdir(out_dir)))
    env = fv_schema.from_error(mode, "no verdict: this run has not completed (replaced by the run's own result when it does)", 0.0)
    if out_dir and not fresh_out and os.path.isdir(out_dir) and os.path.abspath(a.out) == out_dir:
        # never through a link: an --out reached via a symlink is left to the run's own refusal
        # (every output kind) a directory output: the verdict records an earlier run
        # left in --out (bin/fastverify's result.json, an incremental summary.json) are replaced by the ERROR record too
        for n_ in ("result.json", "summary.json"):
            q_ = os.path.join(out_dir, n_)
            if os.path.lexists(q_) and not os.path.isdir(q_):
                outs = dict(outs, **{"_out_" + n_: q_})
    for kw, dest in outs.items():
        if fresh_out and os.path.realpath(dest).startswith(out_dir.rstrip("/") + "/"):
            continue   # inside a fresh --out: no earlier verdict there, and --out must stay empty
        try:
            write_optional_outputs.unchecked(env, **{{"sarif": "sarif_out", "lsp_out": "lsp_out"}.get(kw, "json_out") if kw.startswith("_out_") else {"sarif": "sarif_out"}.get(kw, kw): dest})
        except Exception as e:  # noqa: BLE001
            raise SystemExit(f"fv {a.cmd}: cannot replace the requested output file {dest} ({type(e).__name__}: {e}): refused "
                             "before running (output error, no verdict)")


def _cli_mode(cmd, a):
    mode = _CLI_ENVELOPE_MODE.get(cmd)
    if mode == "export_in" and (getattr(a, "frontier", False) if a is not None else "--frontier" in sys.argv[1:]):
        mode = "frontier"
    return mode


def _cli_error(cmd, a, msg, as_json, outputs=True):
    """print the error (stderr) and, with --json, its JSON object (stdout); exit status 2"""
    print(msg if msg.startswith("fv") else f"fv{' ' + cmd if cmd else ''}: {msg}", file=sys.stderr)
    mode = _cli_mode(cmd, a)
    if mode:
        out = fv_schema.from_error(mode, msg, 0.0)
        if outputs:
            _write_error_outputs(mode, out, a)
    else:
        out = {"ok": False, "error": msg}
    if as_json and not _CLI_STATE.get("stdout_used"):   # never a second JSON object on stdout
        print(json.dumps(out, indent=2), flush=True)
    return 2


class _CliArgumentParser(argparse.ArgumentParser):
    """argparse with the JSON error object for a usage error when --json was given (exit 2 as before); the top-level
    parse result is kept for the error handler of _run_cli"""
    def parse_args(self, args=None, namespace=None):
        ns = super().parse_args(args, namespace)
        _CLI_ARGS[:] = [ns]
        return ns

    def error(self, message):
        _CLI_STATE["finalizing"] = True   # a signal from here on writes ERROR to the requested outputs, exit 2
        cmd = _argv_cmd()   # also `fv --json check ...`
        mode = _cli_mode(cmd, None)
        if mode:   # the requested output files get the ERROR envelope too
            _write_error_outputs(mode, fv_schema.from_error(mode, f"usage: {message}", 0.0), None)
        if "--json" in sys.argv[1:]:   # also `fv --json ...`
            out = fv_schema.from_error(mode, f"usage: {message}", 0.0) if mode else {"ok": False, "error": f"usage: {message}"}
            print(json.dumps(out, indent=2), flush=True)
        super().error(message)


def _direct_children():
    """[(pid, state)] of this process's direct children (/proc; no third-party module)"""
    me, kids = os.getpid(), []
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open(f"/proc/{d}/stat", "rb") as f:
                st = f.read()
            fields = st[st.rindex(b")") + 2:].split()
            if int(fields[1]) == me:
                kids.append((int(d), fields[0]))
        except (OSError, ValueError, IndexError):
            pass
    return kids


def _on_signal(signum, frame):
    """SIGTERM / SIGINT / SIGHUP to bin/fv (an RL harness's subprocess timeout, `kill $pid`): forward it to
    the running child (bin/fastverify, a judge script, incr-reverify.sh, fv-ci.sh - their own handlers stop their stage trees
    and record the interruption), wait for it to stop (grace 60 s, then SIGKILL), and end this run as ERROR (exit 2). A second
    signal kills the children at once."""
    import signal as _sig
    if _CLI_STATE.get("finalizing"):
        # the run is already being reported / delivered (an error envelope, the final stdout flush): no new
        # exception (that gave exit 1 or a death by signal with ACCEPTED left in --json-out). Every requested output file gets
        # the ERROR envelope, and the process ends with 2 at once.
        try:
            a = _CLI_ARGS[0] if _CLI_ARGS else None
            mode = _cli_mode(getattr(a, "cmd", None) if a is not None else _argv_cmd(), a)   # argv before parsing
            if mode:
                _write_error_outputs(mode, fv_schema.from_error(
                    mode, f"interrupted by signal {signum} while the result was being delivered: no verdict", 0.0), a)
        finally:
            os._exit(2)
    again = bool(_CLI_STATE.get("signal"))
    _CLI_STATE["signal"] = signum
    kids = [pid for pid, st in _direct_children() if st != b"Z"]
    for pid in kids:
        try:
            if again and os.getpgid(pid) == pid:   # the ci guard: its whole group
                os.killpg(pid, _sig.SIGKILL)
            else:
                os.kill(pid, _sig.SIGKILL if again else signum)
        except OSError:
            pass
    deadline = time.time() + (0 if again else 60)
    while kids and time.time() < deadline:
        live = {pid for pid, st in _direct_children() if st != b"Z"}
        kids = [k for k in kids if k in live]
        if kids:
            time.sleep(0.1)
    for pid in kids:
        try:   # a child leading its own process group (the `fv ci` guard): the whole group, not only the leader
            if os.getpgid(pid) == pid:
                os.killpg(pid, _sig.SIGKILL)
            else:
                os.kill(pid, _sig.SIGKILL)
        except OSError:
            pass
    if again:   # a second signal while the first one waits: the first handler goes on and raises
        return
    _CLI_STATE["finalizing"] = True   # from here on a further signal can only end the process with 2
    raise SystemExit(f"fv: interrupted by signal {signum}: the run was stopped, no verdict")


def _set_pdeathsig():   # runs in each child between fork and exec: it gets SIGTERM if bin/fv dies (even SIGKILL)
    try:
        ok = _PRCTL(1, 15, 0, 0, 0) == 0   # PR_SET_PDEATHSIG, SIGTERM
    except Exception:  # noqa: BLE001
        ok = False
    if not ok:   # the cancellation guarantee cannot be armed: the child never starts its work
        os.kill(os.getpid(), 9)
    if os.getppid() != _CLI_STATE.get("pid"):   # bin/fv died between fork and prctl: never start the work
        os.kill(os.getpid(), 9)


try:
    import ctypes as _ctypes
    _PRCTL = _ctypes.CDLL(None, use_errno=True).prctl
except Exception:  # noqa: BLE001
    _PRCTL = None


def _install_child_guards():
    import signal as _sig
    _CLI_STATE["pid"] = os.getpid()
    _sig.signal(_sig.SIGCHLD, _sig.SIG_DFL)   # an inherited SIG_IGN never reaches the children
    for s_ in (_sig.SIGTERM, _sig.SIGINT, _sig.SIGHUP):
        _sig.signal(s_, _on_signal)
    if _PRCTL is None:   # the cancellation guarantee cannot be armed: every child stops before its work
        def _no_pdeathsig():
            os.kill(os.getpid(), 9)
        init0 = subprocess.Popen.__init__

        def popen_init0(self, *args, **kw):
            kw.setdefault("preexec_fn", _no_pdeathsig)
            return init0(self, *args, **kw)
        subprocess.Popen.__init__ = popen_init0
    if _PRCTL is not None:
        init = subprocess.Popen.__init__

        def popen_init(self, *args, **kw):
            if kw.get("preexec_fn") is None:
                kw["preexec_fn"] = _set_pdeathsig
            return init(self, *args, **kw)
        subprocess.Popen.__init__ = popen_init


def _run_cli():
    # a closed / full / broken stdout or stderr never changes the exit status into Python's
    # 120 or a traceback exit 1: stderr failures are ignored (diagnostics only); a stdout failure means the run's output was
    # not delivered: output error, exit 2 (and the requested output files carry the ERROR envelope)
    sys.stdout = _GuardedStream(sys.stdout, 1, "stdout_failed")
    sys.stderr = _GuardedStream(sys.stderr, 2, None)
    _install_child_guards()
    a = None
    try:
        rc = main()
        _CLI_STATE["finalizing"] = True   # inside the protected block: a signal here is handled, never exit 1
    except SystemExit as e:
        _CLI_STATE["finalizing"] = True   # reporting: a signal now ends the process with 2 (never 1)
        if not isinstance(e.code, str):   # argparse (2) / an explicit status: unchanged
            rc = e.code if isinstance(e.code, int) else (0 if e.code is None else 2)
        else:
            a = _CLI_ARGS[0] if _CLI_ARGS else None
            msg = e.code[len("fv: "):] if e.code.startswith("fv: ") else e.code
            rc = _cli_error(getattr(a, "cmd", None) if a is not None else _argv_cmd(), a, msg,   # argv before parsing
                            bool(getattr(a, "json", False)) if a is not None else "--json" in sys.argv[1:])
    except Exception as e:  # noqa: BLE001 - an internal / infrastructure / output error is never a verdict
        _CLI_STATE["finalizing"] = True   # reporting: a signal now ends the process with 2 (never 1)
        if not isinstance(e, CliOutputError):
            import traceback
            traceback.print_exc()
        a = _CLI_ARGS[0] if _CLI_ARGS else None
        rc = _cli_error(getattr(a, "cmd", None) if a is not None else _argv_cmd(), a, f"{type(e).__name__}: {e}",
                        bool(getattr(a, "json", False)) if a is not None else "--json" in sys.argv[1:])
    # the handler stays installed through the final delivery (stdout flush, output rewrites): a signal there
    # leaves ERROR in every requested output file and exit 2 (restoring SIG_DFL here would mean death by signal with ACCEPTED left in place)
    _CLI_STATE["finalizing"] = True
    a = _CLI_ARGS[0] if _CLI_ARGS else None
    cmd = getattr(a, "cmd", None)
    sys.stdout.flush()
    if _CLI_STATE["stdout_failed"] and _cli_mode(cmd, a):
        # whatever the run's own exit (a verdict, or already a no-verdict 2): an undelivered stdout is an output
        # error, and every writable output says so (the run's own result is kept as context)
        last = _CLI_STATE.get("last_env") if isinstance(_CLI_STATE.get("last_env"), dict) else {}
        ctx = f"; the run's own result was {last.get('verdict')}: {str(last.get('reason') or last.get('verdict_basis') or '')[:200]}" \
            if last else ""
        print(f"fv {cmd}: stdout could not be written: output error, no verdict (exit 2)", file=sys.stderr)
        _write_error_outputs(_cli_mode(cmd, a), fv_schema.from_error(
            _cli_mode(cmd, a), "stdout could not be written: the run's result was not delivered (output error)" + ctx, 0.0), a)
        rc = 2
    elif _CLI_STATE["stdout_failed"] and rc in (0, 1, 3):
        rc = 2
    if rc not in (0, 1, 3) and _cli_mode(cmd, a) and not _CLI_STATE["outputs_written"] and _requested_outputs(a):
        # no output file was written by this run (e.g. a refused input path): none may keep a
        # verdict of an earlier run
        _write_error_outputs(_cli_mode(cmd, a), fv_schema.from_error(
            _cli_mode(cmd, a), f"no verdict (exit {rc}): the run ended before a result (see stderr)", 0.0), a)
    return rc


# `bin/fv ci` under the same local path policy as every other subcommand: tools/ci-action/fv-ci.sh resolves raw
# arguments with readlink -f / mkdir -p (a symlinked --out-dir / --cache-dir would write outside, --allowed-frontier
# through a link would print outside lines, a symlinked --pins would be followed, --fv-root would replace the package).
# The options are parsed here (exact spelling, fv-ci.sh's own set), and
# fv-ci.sh only ever sees: private no-follow copies of --project / --challenge (lakefile paths confined) and of the
# --allowed-frontier / --frontier-axioms / --frontier-pinned files; --packages / --export-dir checked (no link at any
# component; as fv verify, the challenge's own .lake/packages is the default workspace); --pins resolved by
# _resolve_pins_arg (this package's check/sound/pins*.env only); --cache-dir created / opened without following links (owned
# by the caller; the entries fv-ci.sh reads or writes by name may not be symlinks); a PRIVATE --out-dir, whose reports are
# then written into the caller's --out-dir without following links (paths relocated to the caller's); --fv-root refused.
CI_VALUE_OPTS = frozenset({"--project", "--challenge", "--challenge-sha256", "--comparator-sha256", "--packages", "--preset",
                           "--pins", "--build", "--export-dir", "--cache-dir", "--out-dir", "--allowed-frontier",
                           "--frontier-axioms", "--frontier-pinned", "--wall", "--disk", "--mem", "--threads", "--commit"})
CI_FLAG_OPTS = frozenset({"--no-integrity-cache", "--closure-only", "--confirm-reject", "--frontier", "--experimental"})
CI_RELOCATE_SUFFIXES = (".json", ".sarif", ".md", ".log", ".txt")


def _ci_check_cache(cache):
    """the canonical --cache-dir, created / opened without
    following links, owned by the caller, with NO symlink / special file anywhere in it: fv-ci.sh and incr-build.py read,
    copy and write the whole cached tree on the host (checking only named entries is not enough: a directory link at base/work/proj/Sub
    would make incr-build.py create and overwrite files outside; links at planner/planner or fastexact/* would be executed / loaded);
    fv-ci.sh never asks incr-build.py for symlink farms. A permission error is a refusal (exit 2), never a traceback"""
    return cli_scan_no_links(cache, "fv ci --cache-dir", create=True)


def _reloc_bytes(b, pairs, json_mode):
    for priv, disp in pairs:
        if json_mode:
            priv, disp = json.dumps(priv)[1:-1], json.dumps(disp)[1:-1]
        b = b.replace(priv.encode(), disp.encode())
    return b


def _ci_relocate(tree, pairs):
    """private paths in the reports fv-ci.sh wrote -> the caller's paths (JSON-escaped forms in JSON / SARIF files)"""
    for dp, _dns, fns in os.walk(tree):
        for fn in fns:
            fp = os.path.join(dp, fn)
            if not fn.endswith(CI_RELOCATE_SUFFIXES) or os.path.islink(fp) or not os.path.isfile(fp) \
                    or os.path.getsize(fp) > (64 << 20):
                continue
            try:
                b = open(fp, "rb").read()
            except OSError:
                continue
            nb = _reloc_bytes(b, pairs, fn.endswith((".json", ".sarif")))
            if nb != b:
                with open(fp, "wb") as f:
                    f.write(nb)


CI_MANAGED = ("result-v1.json", "results.sarif", "summary.md", "ci-run.log", "run", "guard-noverdict.json",
              "frontier-check.json", "frontier-check.log")


def _ci_publish(priv_out, out_disp, roots, error_msg=None):
    """deliver this run's reports into the caller's --out-dir. PRINCIPLE: --out-dir
    never shows ACCEPTED unless THIS run completed with ACCEPTED and its delivery succeeded.
    1. Neutralise first: every managed report already there (result-v1.json first, then summary.md, results.sarif,
       ci-run.log, run/, guard*.json, frontier-check.*) - whether or not this run produces it - is renamed aside.
    2. With error_msg (a refusal / an inconsistent child result): only an ERROR result-v1.json is written. Otherwise the
       tree is written into a private staging directory inside --out-dir (no link followed), each entry is renamed into
       place, and result-v1.json is renamed LAST: that rename is the COMMIT point.
    3. A failure before the commit removes what this run had placed, writes an ERROR result-v1.json (best effort) and raises
       CliRefused. After the commit, cleanup errors (stage / old entries) are only reported on stderr: the run's outcome stands.
    Returns nothing."""
    tag = "%d.%s" % (os.getpid(), os.urandom(6).hex())
    stage, asides, placed, committed = ".fv-ci-stage." + tag, [], [], False
    try:
        canon = mcp_server.local_path_under(out_disp, roots)
        ofd = mcp_server.open_nofollow_under(canon, roots, want_dir=True, create=True)
    except (mcp_server.ClientPathError, OSError) as e:
        raise CliRefused(f"fv ci --out-dir {out_disp}: {e}")

    def exists(n):
        try:
            os.stat(n, dir_fd=ofd, follow_symlinks=False)
            return True
        except FileNotFoundError:
            return False

    stuck = []

    def aside(n):
        if exists(n):
            a_ = ".fv-ci-old.%s.%s" % (tag, n)
            try:
                os.rename(n, a_, src_dir_fd=ofd, dst_dir_fd=ofd)
                asides.append(a_)
            except OSError:   # cannot be renamed aside: remove it; if even that fails, say so
                try:
                    remove_entry(n)
                except OSError:
                    stuck.append(n)

    def write_error(msg):
        if stuck:
            msg += f" (WARNING: earlier report entries could not be retired: {', '.join(stuck)} - they are NOT results of this run)"
        env = fv_schema.from_error("project", msg, 0.0)
        mcp_server.write_file_at(ofd, "result-v1.json", json.dumps(env, indent=2))

    def remove_entry(n):
        st = os.stat(n, dir_fd=ofd, follow_symlinks=False)
        if stat.S_ISDIR(st.st_mode):
            shutil.rmtree(os.path.join(canon, n), ignore_errors=True)
        else:
            os.unlink(n, dir_fd=ofd)
    try:
        managed = set(CI_MANAGED) | {n for n in os.listdir(ofd) if n.startswith("guard.") and n.endswith(".json")}
        aside("result-v1.json")
        for n in sorted(managed - {"result-v1.json"}):
            aside(n)
        if error_msg is not None:
            write_error(error_msg)
            committed = True
        elif stuck:
            raise OSError(f"earlier report entries could not be retired: {', '.join(stuck)}")
        else:
            names = sorted(os.listdir(priv_out))
            os.mkdir(stage, 0o700, dir_fd=ofd)
            sfd = os.open(stage, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=ofd)
            try:
                mcp_server.export_tree_to(priv_out, sfd)
                for n in [x for x in names if x != "result-v1.json"]:
                    aside(n)
                    os.rename(n, n, src_dir_fd=sfd, dst_dir_fd=ofd)
                    placed.append(n)
                if "result-v1.json" not in names:
                    raise OSError("the CI run produced no result-v1.json")
                os.rename("result-v1.json", "result-v1.json", src_dir_fd=sfd, dst_dir_fd=ofd)   # the COMMIT point
                committed = True
                _CI_STATE["committed"] = True   # from here a signal / error can no longer change the outcome
                _CI_STATE.pop("records", None)
            finally:
                os.close(sfd)
    except BaseException as e:  # noqa: BLE001  (also a signal / any exception during the delivery)
        if not committed:
            for n in placed:
                try:
                    remove_entry(n)
                except OSError:
                    pass
            try:
                write_error(f"fv ci: the reports could not be delivered ({e}); no result of this run is published")
            except (mcp_server.ClientPathError, OSError):
                pass
            for a_ in asides + [stage]:
                try:
                    remove_entry(a_)
                except OSError:
                    pass
            os.close(ofd)
            if isinstance(e, (mcp_server.ClientPathError, OSError)):
                raise CliRefused(f"fv ci --out-dir {out_disp}: the reports could not be delivered ({e}); earlier reports "
                                 "were retired and an ERROR result-v1.json was written")
            raise
        if not isinstance(e, (mcp_server.ClientPathError, OSError)):
            os.close(ofd)
            raise
    # after the commit (or the ERROR record): cleanup only, never a different outcome
    for a_ in asides + [stage]:
        try:
            if exists(a_):
                remove_entry(a_)
        except OSError as e:
            try:
                print(f"[fv ci] warning: cleanup of {a_} in {out_disp} failed ({e})", file=sys.stderr)
            except (OSError, ValueError):
                pass
    os.close(ofd)


def _ci_cache_records(cache):
    """the cache's previous-run records (last-v1.json, last-frontier.json) as
    bytes (None if absent), read without following links; a record that is not valid JSON is moved aside first (it is
    optional: a truncated one made the report renderer fail, exit 1). Returned so that they can be restored when this
    run's delivery fails (fv-ci.sh writes the new records itself before bin/fv delivers the reports)."""
    roots, out = mcp_server.cli_roots(), {}
    try:
        cfd = mcp_server.open_nofollow_under(cache, roots, want_dir=True)
    except (mcp_server.ClientPathError, OSError):
        return out
    try:
        for n in ("last-v1.json", "last-frontier.json"):
            try:
                st_n = os.stat(n, dir_fd=cfd, follow_symlinks=False)
            except FileNotFoundError:
                out[n] = None
                continue
            b = None
            if stat.S_ISREG(st_n.st_mode):
                fd = os.open(n, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=cfd)
                try:
                    b = os.read(fd, 64 << 20)
                finally:
                    os.close(fd)
                try:
                    json.loads(b.decode("utf-8"))
                except (ValueError, UnicodeDecodeError):
                    b = None
            if b is None:   # not a regular file / not JSON: an unusable optional record, set aside
                os.rename(n, "%s.unusable.%d.%s" % (n, int(time.time()), os.urandom(3).hex()), src_dir_fd=cfd, dst_dir_fd=cfd)
            out[n] = b
    finally:
        os.close(cfd)
    return out


def _ci_restore_cache(cache, records):
    """put the previous-run records back (delivery of this run failed: its records must not become the last success)"""
    roots = mcp_server.cli_roots()
    try:
        cfd = mcp_server.open_nofollow_under(cache, roots, want_dir=True)
    except (mcp_server.ClientPathError, OSError):
        return
    try:
        for n, b in records.items():
            try:
                if b is None:
                    os.unlink(n, dir_fd=cfd)
                else:
                    mcp_server.write_file_at(cfd, n, b, mode=0o644)
            except FileNotFoundError:
                pass
            except OSError as e:   # never leave this run's record as the last success: remove it, say so
                try:
                    os.unlink(n, dir_fd=cfd)
                except OSError:
                    pass
                try:
                    print(f"[fv ci] warning: could not restore {cache}/{n} ({e}); it was removed", file=sys.stderr)
                except (OSError, ValueError):
                    pass
    finally:
        os.close(cfd)


def _ci_relocate_cache(cache, pairs):
    """fv-ci.sh copied the report into --cache-dir before the paths were relocated: the cache's
    last-v1.json / last-frontier.json get the caller's paths too (rewritten without following links)"""
    roots = mcp_server.cli_roots()
    try:
        cfd = mcp_server.open_nofollow_under(cache, roots, want_dir=True)
    except (mcp_server.ClientPathError, OSError):
        return
    try:
        for n in ("last-v1.json", "last-frontier.json"):
            try:
                fd = os.open(n, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=cfd)
            except OSError:
                continue
            try:
                st_n = os.fstat(fd)
                if not stat.S_ISREG(st_n.st_mode) or st_n.st_size > (64 << 20):
                    continue
                chunks = []
                while True:
                    c = os.read(fd, 1 << 20)
                    if not c:
                        break
                    chunks.append(c)
            finally:
                os.close(fd)
            b = b"".join(chunks)
            nb = _reloc_bytes(b, pairs, True)
            if nb != b:
                mcp_server.write_file_at(cfd, n, nb, mode=0o644)
    except OSError:
        pass
    finally:
        os.close(cfd)


def _ci_overlap_error_record(out_disp, out_real, hits, roots):
    """after an overlap refusal, when every overlapping input lies strictly INSIDE --out-dir
    (e.g. --packages OUT/run), the stale top-level reports that are not inputs are neutralised - summary.md / results.sarif
    removed, result-v1.json replaced by an ERROR record - so a retry never leaves the earlier ACCEPTED visible; nothing else
    is touched (no directory is retired). If --out-dir is equal to / inside an input, nothing is written at all."""
    def inside(x, y):
        return x.startswith(y.rstrip("/") + "/")
    if not all(inside(d, out_disp) or inside(r, out_real) for _o, d, r in hits):
        return
    try:
        ofd = mcp_server.open_nofollow_under(out_disp, roots, want_dir=True)
    except (mcp_server.ClientPathError, OSError):
        return
    try:
        for n in ("result-v1.json", "summary.md", "results.sarif"):
            targets = (os.path.join(out_disp, n), os.path.join(out_real, n))
            if any(d == t or inside(d, t) or r == t or inside(r, t) for _o, d, r in hits for t in targets):
                continue   # an input: never touched
            try:
                st_n = os.stat(n, dir_fd=ofd, follow_symlinks=False)
            except FileNotFoundError:
                st_n = None
            if st_n is not None and not stat.S_ISREG(st_n.st_mode) and not stat.S_ISLNK(st_n.st_mode):
                continue
            if n == "result-v1.json":
                env = fv_schema.from_error("project", "refused: fv ci --out-dir overlaps an input (" + ", ".join(
                    f"{o} {d}" for o, d, _r in hits) + "); no result of this run", 0.0)
                mcp_server.write_file_at(ofd, n, json.dumps(env, indent=2))
            elif st_n is not None:
                os.unlink(n, dir_fd=ofd)
    except (mcp_server.ClientPathError, OSError):
        pass
    finally:
        os.close(ofd)


class CiInterrupted(Exception):
    """SIGTERM / SIGINT / SIGHUP during fv ci"""


_CI_STATE = {}


def _argv_value(argv, opt):
    v = None
    for k, t in enumerate(argv[:-1]):
        if t == opt:
            v = argv[k + 1]
    return v


def cmd_ci_argv(argv):
    """`bin/fv ci ARGS`: see CI_VALUE_OPTS above; returns fv-ci.sh's exit code (2 for a refusal / no verdict).
    PUBLICATION RULE: --out-dir never shows ACCEPTED unless THIS run completed with
    ACCEPTED and its delivery succeeded. As soon as --out-dir is known (and is not inside / around --project / --challenge),
    the earlier reports are retired and an ERROR ("in progress") result-v1.json is written - BEFORE anything else is
    validated or run. Every later exit path - a refusal, any exception, SIGTERM / SIGINT / SIGHUP (fv-ci.sh's process group
    is killed) - leaves an ERROR record, retires what this run had placed and restores the cache records; exit 2."""
    # fv ci is EXPERIMENTAL in v0.1: refused (exit 2, nothing read or written) unless opted in
    if "--experimental" not in argv and os.environ.get("FV_EXPERIMENTAL_CI") != "1":
        raise CliRefused("fv ci is EXPERIMENTAL in fastverify v0.1 (its report publication is not yet release grade): pass "
                         "--experimental (or set FV_EXPERIMENTAL_CI=1) to run it")
    roots = mcp_server.cli_roots()
    _CI_STATE.clear()
    out_disp = None
    og = _argv_value(argv, "--out-dir")
    if og:
        try:
            out_disp = mcp_server.local_path_under(og, roots)
        except (mcp_server.ClientPathError, OSError):
            out_disp = None
    if out_disp:   # the overlap refusal is the only one that leaves --out-dir's directories untouched (it may be the project)
        # EVERY path-valued input, not only project / challenge: retiring --out-dir's
        # entries must never delete an input (e.g. a --packages workspace at OUT/run).
        # compared lexically AND resolved (realpath of each side; nothing is read): an input reached through a link into
        # --out-dir (--packages LINK -> OUT/run) must not be deleted by the retire step before its link is refused
        def _ov(a_, b_):
            return a_ == b_ or a_.startswith(b_.rstrip("/") + "/") or b_.startswith(a_.rstrip("/") + "/")
        out_real = os.path.realpath(out_disp)
        hits = []
        for opt in ("--project", "--challenge", "--packages", "--cache-dir", "--export-dir", "--allowed-frontier",
                    "--frontier-axioms", "--frontier-pinned"):
            v = _argv_value(argv, opt)
            try:
                d = mcp_server.local_path_under(v, roots) if v else None
            except (mcp_server.ClientPathError, OSError):
                d = None
            if d and (_ov(out_disp, d) or _ov(out_real, os.path.realpath(d))):
                hits.append((opt, d, os.path.realpath(d)))
        if hits:
            _ci_overlap_error_record(out_disp, out_real, hits, roots)
            opt, d, _r = hits[0]
            raise CliRefused(f"fv ci --out-dir {out_disp} must not be inside {opt} {d} (or contain it; links resolved)")
        try:
            _ci_publish(None, out_disp, roots, error_msg="fv ci: run in progress (no result yet)")
        except CliRefused as e:
            raise CliRefused(f"fv ci --out-dir {og}: {e}")
    old = {}

    def on_signal(signum, _frame):
        for sg_ in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):   # no second interruption during the cleanup
            try:
                signal.signal(sg_, signal.SIG_IGN)
            except (OSError, ValueError):
                pass
        raise CiInterrupted(f"interrupted by signal {signum}")
    import signal
    for sg in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        old[sg] = signal.getsignal(sg)
        if sg == signal.SIGTERM or old[sg] is not signal.SIG_IGN:   # keep nohup's / the shell's ignores (as bin/fastverify)
            signal.signal(sg, on_signal)
    try:
        return _cmd_ci_argv(argv, roots, out_disp)
    except BaseException as e:  # noqa: BLE001
        child = _CI_STATE.get("child")
        if child is not None and child.poll() is None:   # fv-ci.sh and everything it started
            try:
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    child.wait(10)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait(10)
            except (OSError, subprocess.TimeoutExpired):
                pass
        if _CI_STATE.get("records") is not None:
            _ci_restore_cache(_CI_STATE["cache"], _CI_STATE["records"])
        if out_disp and not _CI_STATE.get("committed"):
            msg = (f"refused: {e}" if isinstance(e, CliRefused) else f"fv ci: no verdict ({e!r})")[:600]
            try:
                _ci_publish(None, out_disp, roots, error_msg=msg)
            except BaseException:  # noqa: BLE001
                pass
        if isinstance(e, (CliRefused, KeyboardInterrupt, SystemExit)):
            raise
        print(f"[NO-VERDICT] fv ci: {e}"[:600], file=sys.stderr)
        return 2
    finally:
        for sg, h in old.items():
            try:
                signal.signal(sg, h)
            except (OSError, ValueError, TypeError):
                pass


def _cmd_ci_argv(argv, roots, out_disp):
    vals, flags, i = {}, [], 0
    while i < len(argv):
        t = argv[i]
        if t in CI_FLAG_OPTS:
            flags.append(t)
            i += 1
        elif t in CI_VALUE_OPTS:
            if i + 1 >= len(argv):
                raise CliRefused(f"fv ci {t}: a value is required")
            vals[t] = argv[i + 1]
            i += 2
        elif t == "--fv-root":
            raise CliRefused("fv ci --fv-root: refused (bin/fv ci always runs this package; call tools/ci-action/fv-ci.sh "
                             "directly to test another tree)")
        else:
            raise CliRefused(f"fv ci: unknown argument {t!r} (options: {' '.join(sorted(CI_VALUE_OPTS | CI_FLAG_OPTS))})")
    missing = [o for o in ("--project", "--challenge", "--challenge-sha256", "--out-dir") if not vals.get(o)]
    if missing:
        raise CliRefused(f"fv ci: {' '.join(missing)} required (usage: fv ci --project DIR --challenge DIR "
                         "--challenge-sha256 HEX --out-dir DIR [--cache-dir DIR] [--packages WS] [--preset P] ...)")
    if out_disp is None:
        raise CliRefused(f"fv ci --out-dir {vals['--out-dir']}: not a usable local path")
    proj_disp = cli_path(vals["--project"], "fv ci --project", want_dir=True)
    chal_disp = cli_path(vals["--challenge"], "fv ci --challenge", want_dir=True)
    for d, what in ((proj_disp, "--project"), (chal_disp, "--challenge")):   # as fv-ci.sh
        if out_disp == d or out_disp.startswith(d.rstrip("/") + "/") or d.startswith(out_disp.rstrip("/") + "/"):
            raise CliRefused(f"fv ci --out-dir {out_disp} must not be inside {what} {d} (or contain it)")
    return _cmd_ci_run(vals, flags, roots, proj_disp, chal_disp, out_disp)


def _cmd_ci_run(vals, flags, roots, proj_disp, chal_disp, out_disp):
    tmp = tempfile.mkdtemp(prefix="fv-ci-in.")
    try:
        fwd = {"--project": cli_copy_tree(vals["--project"], os.path.join(tmp, "project"), "fv ci --project"),
               "--challenge": cli_copy_tree(vals["--challenge"], os.path.join(tmp, "challenge"), "fv ci --challenge")}
        for what in ("--project", "--challenge"):
            lerr = mcp_server.lake_config_confined(fwd[what])
            if lerr:
                raise CliRefused(f"fv ci {what}: {lerr}")
        pairs = [(fwd["--project"], proj_disp), (fwd["--challenge"], chal_disp)]
        if vals.get("--packages"):   # cli_packages: no symlinked package entry / build tree
            fwd["--packages"] = cli_packages(vals["--packages"], "fv ci --packages")
        elif _ws_has_packages(chal_disp):   # as fv verify (_packages_arg)
            fwd["--packages"] = cli_packages(chal_disp, "fv ci --challenge (its packages directory)")
        ed = vals.get("--export-dir")
        if ed:
            fwd["--export-dir"] = ed if ed == "none" else cli_path(ed, "fv ci --export-dir", want_dir=True)
        if vals.get("--pins"):
            try:
                fwd["--pins"] = _resolve_pins_arg(vals["--pins"], ctx="fv ci")
            except PinsRefused as e:
                raise CliRefused(str(e))
        for o, nm in (("--allowed-frontier", "allowed-frontier.txt"), ("--frontier-axioms", "frontier-axioms.txt")):
            v = vals.get(o)
            if v and not (o == "--allowed-frontier" and v == "auto"):
                fwd[o] = cli_copy_file(v, os.path.join(tmp, nm), f"fv ci {o}")
                pairs.append((fwd[o], cli_path(v, f"fv ci {o}", want_dir=False)))
        if vals.get("--frontier-pinned"):   # a DIRECTORY (challenge.export + frontier.json): a
            v = vals["--frontier-pinned"]   # private no-follow tree copy, as fv check does
            fwd["--frontier-pinned"] = cli_copy_tree(v, os.path.join(tmp, "frontier-pinned"), "fv ci --frontier-pinned")
            pairs.append((fwd["--frontier-pinned"], cli_path(v, "fv ci --frontier-pinned", want_dir=True)))
        if vals.get("--cache-dir"):
            fwd["--cache-dir"] = _ci_check_cache(vals["--cache-dir"])
        priv_out = os.path.join(tmp, "out")
        os.mkdir(priv_out, 0o700)
        fwd["--out-dir"] = priv_out
        pairs.append((priv_out, out_disp))
        cmd = [os.path.join(FV_ROOT, "tools", "ci-action", "fv-ci.sh")]
        for o in sorted(CI_VALUE_OPTS):
            if o in fwd:
                cmd += [o, fwd[o]]
            elif vals.get(o) is not None:
                cmd += [o, vals[o]]   # the non-path options (pins, preset, build, limits, threads, commit)
        cmd += [f_ for f_ in flags if f_ != "--experimental"] + ["--experimental"]   # the wrapper checked the opt-in
        records = _ci_cache_records(fwd["--cache-dir"]) if fwd.get("--cache-dir") else None
        if records is not None:
            _CI_STATE["cache"], _CI_STATE["records"] = fwd["--cache-dir"], records
        # fv-ci.sh's stdout (its result) is held back: printed only after the reports are delivered;
        # in its own process group, so that an interrupted fv ci stops it and everything it started
        # under the group guard (it leads the new session): the signal handler still kills that process group,
        # and when bin/fv itself dies (even SIGKILL) the guard's PR_SET_PDEATHSIG stops the whole tree.
        # fv-ci.sh gets PR_SET_PDEATHSIG too: the guard arms it for its child (a group SIGKILL of the guard stops it)
        child = subprocess.Popen(_tree_cmd(cmd), stdout=subprocess.PIPE, start_new_session=True)
        _CI_STATE["child"] = child
        child_out, _ = child.communicate()
        p = subprocess.CompletedProcess(cmd, child.returncode, child_out, None)
        rc, pairs_sorted = p.returncode, sorted(pairs, key=lambda x: -len(x[0]))
        _ci_relocate(priv_out, pairs_sorted)
        # exit 0 / 1 must be backed by an ACCEPTED / REJECTED record of this run, else no verdict
        try:
            verdict = json.load(open(os.path.join(priv_out, "result-v1.json"), encoding="utf-8")).get("verdict")
        except (OSError, ValueError, AttributeError):
            verdict = None
        bad = (rc == 0 and verdict != "ACCEPTED") or (rc == 1 and verdict != "REJECTED") or rc not in (0, 1, 2, 3) or verdict is None
        try:
            if bad:
                _ci_publish(None, out_disp, roots, error_msg=f"fv ci: the CI run exited {rc} with verdict {verdict!r} (no "
                                                             "consistent result of this run; see the CI log)")
                if records is not None:
                    _ci_restore_cache(fwd["--cache-dir"], records)
                _CI_STATE["committed"] = True   # the ERROR record is this run's outcome
                print(f"[NO-VERDICT] fv ci: the CI run exited {rc} with verdict {verdict!r}: no verdict", file=sys.stderr)
                return 2
            _ci_publish(priv_out, out_disp, roots)
        except CliRefused:
            if records is not None:   # this run's records must not become the last success
                _ci_restore_cache(fwd["--cache-dir"], records)
            _CI_STATE.pop("records", None)
            raise
        _CI_STATE["committed"] = True   # result-v1.json committed: nothing below may change the outcome
        _CI_STATE.pop("records", None)
        if fwd.get("--cache-dir"):
            try:
                _ci_relocate_cache(fwd["--cache-dir"], pairs_sorted)
            except BaseException as e:  # noqa: BLE001
                print(f"[fv ci] warning: the cache records keep private paths ({e!r})", file=sys.stderr)
        out_b = _reloc_bytes(_reloc_bytes(p.stdout or b"", pairs_sorted, True), pairs_sorted, False)
        try:
            sys.stdout.buffer.write(out_b)
            sys.stdout.flush()
        except (BrokenPipeError, OSError, ValueError):
            pass
        return rc
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def cmd_ci(a):
    _ci_preflight(list(a.ci_args))   # the argparse route into `fv ci` gets the same checks
    return cmd_ci_argv(_ci_cold_argv(list(a.ci_args)))


_CI_FLAG_OPTS = {"--no-integrity-cache", "--closure-only", "--confirm-reject", "--frontier", "--experimental"}   # + the experimental opt-in


def _ci_cold_argv(argv):
    """v0.1: nothing incremental may count, and fv-ci.sh's warm cache runs incr-reverify --optimistic:
    --cache-dir is dropped (a cold run), with a note"""
    out, i = [], 0
    while i < len(argv):
        if argv[i] == "--cache-dir" or argv[i].startswith("--cache-dir="):
            print("fv ci: --cache-dir ignored in v0.1 (incremental CI is experimental and never counted): cold run",
                  file=sys.stderr)
            i += 1 if "=" in argv[i] else 2
            continue
        out.append(argv[i])
        i += 1
    return out


def _ci_preflight(argv):
    """`fv ci ARGS`: every value option of fv-ci.sh has its value (else usage error, exit 2 - fv-ci.sh's own
    parser died with exit 1 = REJECTED), and --comparator-sha256 accompanies --challenge-sha256"""
    i = 0
    seen = set()
    while i < len(argv):
        x = argv[i]
        if x.startswith("--") and "=" not in x:
            seen.add(x)
            if x not in _CI_FLAG_OPTS:
                if i + 1 >= len(argv) or argv[i + 1].startswith("--"):
                    raise SystemExit(f"fv ci: {x} needs a value")
                if x in ("--challenge-sha256", "--comparator-sha256") and not re.fullmatch(r"[0-9a-f]{64}", argv[i + 1]):   # fullmatch
                    # an empty / malformed pin is no pin: fv-ci.sh would skip its comparator check
                    raise SystemExit(f"fv ci: {x} must be 64 lowercase hex digits")
                i += 1
        elif x.startswith("--"):
            if x.split("=", 1)[0] in ("--challenge-sha256", "--comparator-sha256", "--experimental"):   # fv-ci.sh does not parse `--opt=V`
                raise SystemExit(f"fv ci: write {x.split('=', 1)[0]} HEX (the `--opt=VALUE` spelling is not accepted)")
            seen.add(x.split("=", 1)[0])
        i += 1
    for j, x in enumerate(argv):   # a report destination that is not a directory is an error, never REJECTED
        if x == "--out-dir" and j + 1 < len(argv) and os.path.lexists(argv[j + 1]) and not os.path.isdir(argv[j + 1]):
            raise SystemExit(f"fv ci: --out-dir {argv[j + 1]} exists and is not a directory")
    if "--challenge-sha256" in seen and "--comparator-sha256" not in seen:
        raise SystemExit("fv ci: --comparator-sha256 HEX is required with --challenge-sha256 (the sha256 of comparator.json)")


def main():
    # `fv ci ...` arguments go to tools/ci-action/fv-ci.sh (so leading `--flags` work without `--`), only
    # after the local path policy (cmd_ci_argv)
    if len(sys.argv) >= 2 and sys.argv[1] == "ci":
        try:
            _ci_preflight(sys.argv[2:])
            return cmd_ci_argv(_ci_cold_argv(sys.argv[2:]))
        except CliRefused as e:
            print(f"[NO-VERDICT] refused: {e}", file=sys.stderr)
            return 2
        except Exception as e:  # noqa: BLE001  no traceback / exit 1: no verdict, exit 2
            print(f"[NO-VERDICT] internal error: {e!r}"[:600], file=sys.stderr)
            return 2

    ap = _CliArgumentParser(
        prog="fv", description="Ergonomic daily production CLI for fastverify",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="exit status: verify / check / attempt / watch: 0 = ACCEPTED (counted trust), "
               "1 = REJECTED, 3 = CONDITIONAL, 2 = everything else: DECLINED / NO-VERDICT / ERROR, a usage or input error, an "
               "unavailable service, an output file that cannot be written (then every writable output carries the ERROR "
               "envelope). audit: 0 = ok, 1 = a finding, 2 = the audit could not run (incl. deep audit ERROR). triage: 0 = "
               "dispatch, 1 = do not dispatch, 2 = error. doctor / init-challenge / mint / diff: 0 = ok, 2 = not ok or error. "
               "With --json every error is a JSON object on stdout (an API v1 ERROR envelope for verify / check / attempt / "
               "watch, {\"ok\": false, \"error\": ...} otherwise). Exit 1 never means an error.")
    sub = ap.add_subparsers(dest="cmd", required=True)
    _add_parser = sub.add_parser

    def _remember(name, **kw):   # the usage-error handler reads argv with the subcommand's own option table
        _CLI_SUBPARSERS[name] = _add_parser(name, **kw)
        return _CLI_SUBPARSERS[name]
    sub.add_parser = _remember

    # verify
    p = sub.add_parser("verify", help="Verify a Lean project against a pinned challenge")
    p.add_argument("project", help="Lean project directory")
    p.add_argument("--challenge", "-c", required=True, help="clean challenge directory")
    p.add_argument("--challenge-sha256", help="64-hex SHA-256 pin of official challenge.export")
    p.add_argument("--comparator-sha256", default=None,
                   help="64-hex SHA-256 pin of comparator.json: required with a pinned challenge")
    p.add_argument("--trust-challenge-sha256-file", action="store_true",
                   help="read challenge.export.sha256 from challenge dir (only when challenge dir is trusted)")
    p.add_argument("--preset", default="sound-auto", help="preset (default: sound-auto; use 'sound' for RH-tuned "
                   "preset; 'notary'; any other preset needs --allow-unsound-presets and never counts as accepted)")
    p.add_argument("--allow-unsound-presets", action="store_true",
                   help="allow a non-sound --preset (e.g. reference, fastest): reported, but accepted=false / reward=0.0 / exit 2 "
                   "for its ACCEPTED")
    p.add_argument("--pins", default=None, help="explicit trusted pins profile for bin/fastverify: 436 (pins.env), 437 (pins-437.env), or path under check/sound/")
    p.add_argument("--no-integrity-cache", action="store_true", help="sound-auto: verify toolchains and pins in full every run")
    p.add_argument("--build", choices=["B0", "B1", "B2", "B3"], default=None)
    p.add_argument("--packages", help="trusted Lake workspace with .lake/packages")
    p.add_argument("--threads", "-j", type=int, default=0)
    p.add_argument("--out", "-o", help="output dir (default: auto temporary directory)")
    p.add_argument("--export-dir", default=None)
    p.add_argument("--build-cache", default=None, metavar="DIR|none",
                   help="bin/fastverify --build-cache: private cache of untrusted build helpers, checked here (no "
                        "symlink at any component); not accepted via --extra-arg")
    p.add_argument("--keep-work", action="store_true")
    p.add_argument("--confirm-reject", action="store_true")
    p.add_argument("--modulo-frontier", nargs="?", const="auto", default=None, metavar="auto|FILE",
                   help="conditional verification modulo an explicit sorry frontier (exit 3 = CONDITIONAL)")
    p.add_argument("--frontier-pin", default=None, metavar="DIR",
                   help="with --modulo-frontier: judge against a pinned frontier challenge dir")
    p.add_argument("--frontier-base", default=None, metavar="RESULT",
                   help="with --modulo-frontier: earlier result.json for ledger base_status (proved/still_open/dropped)")
    p.add_argument("--incr-base", help="previous --keep-work output dir for incremental re-verification")
    p.add_argument("--optimistic", action="store_true", default=True)
    p.add_argument("--no-optimistic", dest="optimistic", action="store_false")
    p.add_argument("--closure-only", action="store_true")
    p.add_argument("--integrity-cache", default=None)
    p.add_argument("--json", action="store_true", help="print API v1 JSON to stdout")
    p.add_argument("--json-out", help="write API v1 JSON to file")
    p.add_argument("--sarif", help="write SARIF 2.1.0 report to file")
    p.add_argument("--lsp-out", help="write LSP 3.17 diagnostics JSON to file")
    p.add_argument("--include-raw", action="store_true")
    p.add_argument("--quiet", "-q", action="store_true")
    p.add_argument("--guard", default=None, help="optional fvguard resource limits (e.g. mem=8G,wall=300,procs=128)")
    p.add_argument("--extra-arg", dest="extra_args", action="append", default=[], help="extra argument passed to bin/fastverify "
                   "(options that replace the deciding check - --preset, --check, --fast-policy, --fast-checks - are refused)")

    # check
    p = sub.add_parser("check", help="Standalone sound (or --frontier conditional) check on an .export file")
    p.add_argument("export_file")
    p.add_argument("--challenge", "-c", default=None, help="challenge dir containing challenge.export + comparator.json")
    p.add_argument("--challenge-export", default=None)
    p.add_argument("--comparator-json", default=None)
    p.add_argument("--challenge-sha256", required=True)
    p.add_argument("--comparator-sha256", required=True,   # the comparator pin is required with the challenge pin
                   help="64-hex SHA-256 pin of comparator.json (required, as --challenge-sha256)")
    p.add_argument("--frontier", action="store_true", help="run check/frontier/check-frontier.sh (exit 3 = CONDITIONAL)")
    p.add_argument("--allowed-frontier", default=None, help="optional allowed frontier lemma list file (--frontier)")
    p.add_argument("--frontier-axioms", default=None, help="pinned file of declared project axioms (passed as --axioms FILE to check-frontier.sh)")
    p.add_argument("--frontier-pinned", default=None, help="optional pinned frontier challenge dir (--pinned DIR)")
    p.add_argument("--frontier-base", default=None, help="earlier frontier result JSON for base_status ledger (--base FILE)")
    p.add_argument("--low-mem", action="store_true", help="run check/lowmem/check-sound-lowmem.sh for tight RAM budgets")
    p.add_argument("--notary", action="store_true", help="run check/notary/check-notary.sh (unmodified 4.36 libs + 3-leg SHA-256 environment digest); "
                   "EXPERIMENTAL in v0.1: needs --experimental")
    p.add_argument("--experimental", action="store_true", help="opt in to the EXPERIMENTAL notary judge (--notary), required in v0.1")
    p.add_argument("--notary-kernels", default=None, help="comma list of extra kernels for --notary (e.g. gruszka,con-ron)")
    p.add_argument("--pins", default=None, help="pins file for check-sound.sh v2.1 (shorthand: '436', '437', or absolute path to pins.env)")
    p.add_argument("--guard", default=None, help="optional fvguard resource limits (e.g. mem=8G,wall=120)")
    p.add_argument("--threads", "-j", type=int, default=0)
    p.add_argument("--timeout", type=int, default=0,
                   help="seconds, passed to the selected judge's own --timeout (0 = none); its scope differs per judge: "
                        "default check-sound.sh and --notary bound each judging step started after the "
                        "judge's setup and self-test (comparison, kernel legs); --low-mem is ONE budget counted from the "
                        "judge's start (setup and self-test included); --frontier gives it to each stage of "
                        "check-frontier.sh and to each inner check-sound.sh run. A timeout is DECLINED (exit 2). For a "
                        "wall-clock limit on the whole command use --guard wall=SECONDS.")
    p.add_argument("--json", action="store_true")
    p.add_argument("--json-out")
    p.add_argument("--sarif")
    p.add_argument("--lsp-out")
    p.add_argument("--include-raw", action="store_true")
    p.add_argument("--quiet", "-q", action="store_true")

    # attempt
    p = sub.add_parser("attempt", help="Verify a single proof attempt via fvserve or fvapi")
    p.add_argument("file", help="Lean source file (or '-' for stdin)")
    p.add_argument("--pset", required=True)
    p.add_argument("--theorem", "-t", required=True)
    p.add_argument("--state", help="fvserve --state dir")
    p.add_argument("--http", help="fvapi base URL (e.g. http://127.0.0.1:8080)")
    p.add_argument("--api-key", default=None)
    p.add_argument("--timeout", type=float, default=300.0)
    p.add_argument("--json", action="store_true")
    p.add_argument("--json-out")
    p.add_argument("--sarif")
    p.add_argument("--lsp-out")
    p.add_argument("--include-raw", action="store_true")
    p.add_argument("--quiet", "-q", action="store_true")

    # triage
    p = sub.add_parser("triage", help="Pre-proving sandboxed triage of a sorry sub-lemma")
    p.add_argument("--experimental", action="store_true", help="required in v0.1: fv triage is EXPERIMENTAL")
    p.add_argument("file", help="Lean file (or '-' for stdin)")
    p.add_argument("--theorem", "-t", default=None)
    p.add_argument("--toolchain", default=None, help="official Lean toolchain dir (auto-detected from --repo lean-toolchain if omitted)")
    p.add_argument("--packages", default=_default_packages(),
                   help="trusted Lake workspace (default: <repository root>/verify/challenge if present)")
    p.add_argument("--snapshot-dir", default=None)
    p.add_argument("--repo", default=None)
    p.add_argument("--static-only", action="store_true")
    p.add_argument("--timeout", type=float, default=20.0)
    p.add_argument("--json", action="store_true")

    # init-challenge
    p = sub.add_parser("init-challenge", help="Officially build and SHA-256-pin a challenge export (B0+E0)")
    p.add_argument("challenge", help="challenge source directory")
    p.add_argument("out", help="destination directory for pinned challenge.export")
    p.add_argument("--packages", default=None)
    p.add_argument("--threads", "-j", type=int, default=8)
    p.add_argument("--timeout", type=float, default=600.0)
    p.add_argument("--json", action="store_true")

    # mint
    p = sub.add_parser("mint", help="Mint SHA-256-pinned sub-challenges from open sorry frontier lemmas")
    p.add_argument("project", help="blueprint Lean project directory")
    p.add_argument("--out", "-o", required=True, help="output directory for minted sub-challenges")
    p.add_argument("--theorem", "-t", action="append", default=[], help="frontier theorem name (repeatable)")
    p.add_argument("--frontier-file", default=None, help="newline-separated frontier theorem names")
    p.add_argument("--module", default=None, help="Lean root module name (auto-detected if omitted)")
    p.add_argument("--permitted-axioms", default="propext,Quot.sound,Classical.choice")
    p.add_argument("--packages", default=None)
    p.add_argument("--for-fvserve", action="store_true", help="set solution_module=Attempt.<T> for fvserve/batchverify")
    p.add_argument("--threads", "-j", type=int, default=8)
    p.add_argument("--timeout", type=float, default=600.0)
    p.add_argument("--json", action="store_true")

    # audit
    p = sub.add_parser("audit", help="Audit a challenge directory or solution export for statement-fidelity hazards")
    p.add_argument("challenge")
    p.add_argument("--challenge-sha256", default=None)
    p.add_argument("--config", default=None, help="optional comparator.json path when auditing a .export file")
    p.add_argument("--probe", action="store_true", help="run kernel-certified vacuity/refutation probes inside bwrap")
    p.add_argument("--packages", default=None, help="optional Lake packages workspace for --probe")
    p.add_argument("--reading-set", default=None, help="write minimal non-Mathlib reading set to OUT.lean")
    p.add_argument("--conjecture-mode", action="store_true", help="enable conjecture-mode checks in tools/audit/audit.py")
    p.add_argument("--solution-mode", action="store_true", help="audit solution export/dir for zero-project-lemma degenerate proofs")
    p.add_argument("--json", action="store_true")

    # doctor
    p = sub.add_parser("doctor", help="Check host readiness and recommend preset/threads")
    p.add_argument("--project", default=None)
    p.add_argument("--json", action="store_true")

    # watch
    p = sub.add_parser("watch", help="Editor/LSP-friendly continuous verification watch loop")
    p.add_argument("--experimental", action="store_true", help="required in v0.1: fv watch is EXPERIMENTAL")
    p.add_argument("path", help="Lean project dir or single attempt .lean file")
    p.add_argument("--challenge", "-c", default=None)
    p.add_argument("--challenge-sha256", default=None)
    p.add_argument("--comparator-sha256", default=None, help="64-hex pin of comparator.json (required with --challenge-sha256)")
    p.add_argument("--trust-challenge-sha256-file", action="store_true")
    p.add_argument("--fvserve-state", default=None)
    p.add_argument("--fvwork-state", default=None, help="(not available in v0.1: refused) persistent fvwork daemon state dir")
    p.add_argument("--no-advance", action="store_true", help="with --fvwork-state: do not advance fvwork base on watch edits")
    p.add_argument("--pset", default=None)
    p.add_argument("--theorem", default=None)
    p.add_argument("--incr-base", default=None)
    p.add_argument("--closure-only", action="store_true")
    p.add_argument("--integrity-cache", default=None)
    p.add_argument("--preset", default="sound-auto")
    p.add_argument("--no-integrity-cache", action="store_true")
    p.add_argument("--build", default=None)
    p.add_argument("--packages", default=None)
    p.add_argument("--export-dir", default=None)
    p.add_argument("--threads", "-j", type=int, default=0)
    p.add_argument("--interval", type=float, default=0.5)
    p.add_argument("--timeout", type=float, default=300.0)
    p.add_argument("--once", action="store_true")
    p.add_argument("--max-runs", type=int, default=0)
    p.add_argument("--json-out", default=None)
    p.add_argument("--sarif", default=None)
    p.add_argument("--lsp-out", default=None)

    # lookup (dupfind)
    p = sub.add_parser("lookup", help="Duplicate-lemma lookup via kernel exphash (tools/dupfind)")
    p.add_argument("file", nargs="?", default=None, help="Optional candidate .lean file to compile/export/hash and query")
    p.add_argument("--index", "-i", action="append", required=True, help="dupfind sqlite index directory (repeatable)")
    p.add_argument("--name", action="append", default=[], help="theorem name to look up")
    p.add_argument("--hash", action="append", default=[], help="type_hk[:lvl_h] hash to look up")
    p.add_argument("--targets", default=None, help="comma-separated target theorem names for file query")
    p.add_argument("--toolchain", default=None, help="official Lean toolchain dir (auto-detected from --repo lean-toolchain if omitted)")
    p.add_argument("--packages", default=_default_packages(),
                   help="trusted Lake workspace (default: <repository root>/verify/challenge if present)")
    p.add_argument("--snapshot", default=None, help="optional header snapshot directory for warm compile")
    p.add_argument("--threads", "-j", type=int, default=4)
    p.add_argument("--json", action="store_true")

    # diff (expdiff)
    p = sub.add_parser("diff", help="Diagnostic kernel-term diff of two .export files (tools/compress/expdiff; never a verdict)")
    p.add_argument("old_export", help="baseline/original .export file")
    p.add_argument("new_export", help="candidate/new .export file")
    p.add_argument("--targets", default=None, help="comma-separated target names or path to targets file")
    p.add_argument("--explain", type=int, default=5, help="max differing declarations per status to explain (default: 5)")
    p.add_argument("--dead-lets", action="store_true", help="classify value changes equal modulo dead lets")
    p.add_argument("--private-modulo", action="store_true", help="ignore module prefix in _private names")
    p.add_argument("--threads", "-j", type=int, default=0)
    p.add_argument("--timeout", type=float, default=300.0)
    p.add_argument("--json", action="store_true")

    # ci
    p = sub.add_parser("ci", help="Run the CI/PR-gate runner")
    p.add_argument("ci_args", nargs=argparse.REMAINDER)

    a = ap.parse_args()
    if _cli_mode(a.cmd, a):   # the very first action after parsing
        _prewrite_error_outputs(a)
    try:
        return _dispatch(a)
    except Exception as e:  # noqa: BLE001  a path refused by the local path policy: no verdict, nothing followed;
        # any other exception is no verdict either: exit 2, never a traceback with exit 1
        msg = f"refused: {e}" if isinstance(e, CliRefused) else f"internal error (no verdict): {e!r}"[:600]
        mode = {"verify": "project", "watch": "project", "check": "export_in", "attempt": "attempt"}.get(a.cmd)
        if mode:
            env = fv_schema.from_error(mode, msg, 0.0)
            print(json.dumps(env, indent=2) if getattr(a, "json", False) else f"[NO-VERDICT] {msg}",
                  file=sys.stdout if getattr(a, "json", False) else sys.stderr)
            return env["exit_code"]
        if getattr(a, "json", False):
            print(json.dumps({"ok": False, "error": msg}, indent=2))
        else:
            print(f"[ERROR] {msg}", file=sys.stderr)
        return 2


def _dispatch(a):
    dispatch = {
        "verify": cmd_verify,
        "check": cmd_check,
        "attempt": cmd_attempt,
        "triage": cmd_triage,
        "init-challenge": cmd_init_challenge,
        "mint": cmd_mint,
        "audit": cmd_audit,
        "doctor": cmd_doctor,
        "watch": cmd_watch,
        "lookup": cmd_lookup,
        "diff": cmd_diff,
        "ci": cmd_ci,
    }
    return dispatch[a.cmd](a)


if __name__ == "__main__":
    sys.exit(_run_cli())
