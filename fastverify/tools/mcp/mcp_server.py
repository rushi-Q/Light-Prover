#!/usr/bin/python3 -I
"""mcp_server.py — Model Context Protocol (MCP) server for fastverify.

Zero external dependencies (Python 3.10+ stdlib only). Speaks standard JSON-RPC 2.0 over stdio
and auto-detects BOTH framing conventions:
  * Newline-delimited JSON-RPC (MCP 2025-11-25, matching Lean 4.36's lean-beam-mcp and common MCP clients)
  * LSP-style Content-Length headers (MCP 2024-11-05 clients)

Zero TCB change: every ACCEPTED verdict comes exclusively from the unchanged trusted check
(bin/fastverify --preset sound, check/sound/check-sound.sh, tools/incr, or tools/fvserve).
Complements interactive tactic/LSP MCP servers like lean-beam-mcp (which provide goal inspection
and speculative tactics, NOT cheat-proof challenge verification).
"""
import argparse
import atexit
import hashlib
import concurrent.futures as cf
import json
import os
import re
import shutil
import signal
import socket
import stat
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
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


def _repo_packages():
    """Trusted Lake workspace used when --packages is not given: <repository root>/verify/challenge if it exists, else
    None (the tool then answers that --packages is needed)."""
    p = os.path.join(os.path.dirname(FV_ROOT), "verify", "challenge")
    return p if os.path.isdir(p) else None
sys.path.insert(0, os.path.join(FV_ROOT, "schemas"))
sys.path.insert(0, os.path.join(FV_ROOT, "tools", "fvserve"))
sys.path.insert(0, os.path.join(FV_ROOT, "tools", "triage"))
import fv_schema  # noqa: E402
import fvserve    # noqa: E402
import triage     # noqa: E402

SERVER_NAME = "fastverify-mcp"
SERVER_VERSION = "1.0.0"
SUPPORTED_PROTOCOLS = ("2025-11-25", "2025-03-26", "2024-11-05")


def run_subprocess_guarded(fv_root, cmd, timeout, grace=5.0):
    """Run cmd with whole-tree timeout enforcement so timed-out verifications leave ZERO orphaned
    descendants. Uses tools/guard/fvguard.py (child subreaper + /proc descendant
    tree kill, which catches bwrap --new-session children too) when installed, with a start_new_session
    + process-group SIGTERM/SIGKILL fallback."""
    tmo = max(0.5, float(timeout))
    gp = os.path.join(fv_root, "tools", "guard", "fvguard.py")
    if os.path.isfile(gp):
        tmp_gj = tempfile.NamedTemporaryFile(prefix="fv-mcp-guard.", suffix=".json", delete=False)
        gj_path = tmp_gj.name
        tmp_gj.close()
        gcmd = [
            "/usr/bin/python3", "-I", gp,
            "--wall", str(tmo), "--grace", str(grace),
            "--json", gj_path, "--",
        ] + list(cmd)
        try:
            p = subprocess.Popen(gcmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
            try:
                out, err = p.communicate(timeout=tmo + grace + 30.0)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except OSError:
                    p.kill()
                p.communicate()
                raise subprocess.TimeoutExpired(cmd, tmo)
            viol = None
            if os.path.isfile(gj_path):
                try:
                    viol = json.load(open(gj_path, encoding="utf-8")).get("violation")
                except Exception:
                    pass
            if viol == "wall" or (p.returncode == 125 and viol):
                raise subprocess.TimeoutExpired(cmd, tmo)
            return subprocess.CompletedProcess(cmd, p.returncode, out, err)
        finally:
            try:
                os.unlink(gj_path)
            except OSError:
                pass
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        out, err = p.communicate(timeout=tmo)
        return subprocess.CompletedProcess(cmd, p.returncode, out, err)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGTERM)
        except OSError:
            pass
        try:
            p.wait(timeout=min(grace, 5.0))
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except OSError:
                p.kill()
        try:
            p.communicate(timeout=2.0)
        except Exception:
            pass
        raise subprocess.TimeoutExpired(cmd, tmo)


def build_tool_specs():
    return [
        {
            "name": "fv_status",
            "description": (
                "Return fastverify-mcp server status, connected verification backends (fvserve, fvapi, "
                "fvwork, fastverify CLI, optional statement auditor and sorry-frontier extensions), "
                "allowed workspace roots, and active problem sets."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {},
                "required": [],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_doctor",
            "description": (
                "Inspect host readiness (bwrap sandbox, vm.max_map_count, CPU/RAM/cgroup limits, /dev/shm, "
                "official Lean toolchains, pinned checker binaries) and recommend an optimal fastverify "
                "preset and thread count for an optional project directory."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "project_dir": {"type": "string", "description": "Optional Lean project directory to inspect."},
                },
                "required": [],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_verify_attempt",
            "description": (
                "Soundly verify a single Lean 4 proof attempt against a pinned official challenge problem set "
                "via the persistent fvserve daemon (0.6-3 s typical latency). Returns verdict (ACCEPTED / "
                "REJECTED / NO-VERDICT), reward (1.0 iff ACCEPTED, else 0.0), structured compiler diagnostics "
                "(file/line/col/message), and stage timings. Blocks sorry, extra axioms, native_decide, "
                "skipKernelTC, and statement weakening."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "pset": {"type": "string", "description": "Problem set name loaded in fvserve (optional if default set)."},
                    "theorem": {"type": "string", "description": "Target theorem name in the problem set."},
                    "source": {"type": "string", "description": "Complete Lean 4 source text of the proof attempt."},
                    "source_file": {"type": "string", "description": "Alternative to inline 'source': path to a .lean file under allowed roots."},
                    "timeout": {"type": "number", "description": "Optional timeout in seconds."},
                },
                "required": ["theorem"],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_verify_batch",
            "description": (
                "Concurrently verify multiple proof attempts or best-of-N candidates via fvserve, returning "
                "per-candidate sound verdicts, reward flags, parsed diagnostics, and the index of the first "
                "ACCEPTED candidate (if any)."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "pset": {"type": "string", "description": "Default problem set name for candidates."},
                    "candidates": {
                        "type": "array",
                        "description": "List of proof attempt candidates to verify concurrently.",
                        "items": {
                            "type": "object",
                            "properties": {
                                "id": {"type": "string"},
                                "pset": {"type": "string"},
                                "theorem": {"type": "string"},
                                "source": {"type": "string"},
                                "source_file": {"type": "string"},
                            },
                            "required": ["theorem"],
                            "additionalProperties": False,
                        },
                    },
                    "timeout": {"type": "number"},
                },
                "required": ["candidates"],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_verify_project",
            "description": (
                "Soundly verify a Lean 4 project directory against a pinned official challenge. Supports cold "
                "verification (bin/fastverify), fast incremental re-verification (tools/incr with incr_base), "
                "persistent repo daemon (tools/fvwork if configured), and optional sorry-frontier verification "
                "when the backend supports it."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "project_dir": {"type": "string", "description": "Absolute path to Lean project directory."},
                    "challenge_id": {"type": "string", "description": "Pinned challenge ID registered by the service owner (configured via --challenge ID=DIR; preferred for untrusted agents, pins both challenge.export and comparator.json)."},
                    "challenge_dir": {"type": "string", "description": "Absolute path to clean challenge directory (when not using challenge_id; requires challenge_sha256 and comparator_sha256)."},
                    "challenge_sha256": {"type": "string", "description": "64-hex SHA-256 pin of official challenge.export (required with challenge_dir in sound mode)."},
                    "comparator_sha256": {"type": "string", "description": "64-hex SHA-256 pin of comparator.json (REQUIRED with challenge_dir, as challenge_sha256; prevents a forged comparator.json)."},
                    "packages_dir": {"type": "string", "description": "Optional trusted Lake workspace with .lake/packages."},
                    "preset": {"type": "string", "enum": ["sound-auto", "sound", "notary"], "description": "Sound verification preset (default: sound-auto with integrity records + auto low-mem + except-translate + auto-437 pins; 'sound' for RH-tuned preset; 'notary' for B0+E0+CN with a 3-leg SHA-256 environment digest)."},
                    "pins": {"type": "string", "enum": ["436", "437"], "description": "Normally omitted: bin/fastverify then takes the challenge release's own trusted check. '436' (check/sound/pins.env) / '437' (Lean 4.37.0-rc1 check/sound/pins-437.env) must name that same judge; bin/fastverify refuses another release's judge. Arbitrary caller paths are rejected (boundary B4)."},
                    "no_integrity_cache": {"type": "boolean", "description": "Disable sound-auto integrity records (re-verify all toolchains and pins in full every run)."},
                    "build_option": {"type": "string", "enum": ["B0", "B1", "B2", "B3"], "description": "Optional explicit build stage override (use B0 for 1-module small projects)."},
                    "incr_base": {"type": "string", "description": "v0.1: incremental mode is experimental and NOT used: a request with incr_base is verified by the full path (a warning says so)."},
                    "optimistic": {"type": "boolean", "description": "Incremental mode only (not used in v0.1, see incr_base)."},
                    "closure_only": {"type": "boolean", "description": "Build only the solution module's import closure."},
                    "confirm_reject": {"type": "boolean", "description": "Re-verify B3 rejects with exact B1 build (useful for @[to_dual] libraries)."},
                    "modulo_frontier": {"type": "string", "description": "Optional Day 1-99 conditional frontier mode ('auto' or path to allowed frontier list file; verdict CONDITIONAL, exit 3, reward=0.0 while the frontier is non-empty; an empty frontier is ACCEPTED, exit 0)."},
                    "frontier_pin": {"type": "string", "description": "Optional pinned frontier challenge directory (requires modulo_frontier)."},
                    "frontier_base": {"type": "string", "description": "Optional earlier result.json for frontier base_status ledger (proved/still_open/dropped)."},
                    "threads": {"type": "integer", "minimum": 1},
                    "timeout": {"type": "number", "description": "Wall-clock timeout in seconds."},
                },
                "required": ["project_dir"],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_check_export",
            "description": (
                "Run the standalone trusted sound check (ccmp + pleanchecker + gruszka) — or conditional "
                "sorry-frontier check (frontier=true, check/frontier/check-frontier.sh: verdict CONDITIONAL, "
                "exit 3, reward 0 while lemmas stay open; an empty frontier = a complete proof is ACCEPTED, "
                "exit 0, reward 1) — on an existing lean4export NDJSON file against a SHA-256-pinned "
                "official challenge export and comparator.json (or a challenge_id registered by the service owner)."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "export_file": {"type": "string"},
                    "challenge_id": {"type": "string", "description": "Pinned challenge ID registered by the service owner (configured via --challenge ID=DIR; preferred for untrusted agents)."},
                    "challenge_export": {"type": "string"},
                    "comparator_json": {"type": "string"},
                    "challenge_sha256": {"type": "string", "description": "Required 64-hex SHA-256 pin of challenge_export (when not using challenge_id)."},
                    "comparator_sha256": {"type": "string", "description": "Required 64-hex SHA-256 pin of comparator.json (when not using challenge_id; prevents a forged comparator.json)."},
                    "frontier": {"type": "boolean", "description": "If true, allow explicit whole-lemma sorry frontier (verdict CONDITIONAL, reward=0.0, while the frontier is non-empty; empty frontier: ACCEPTED, reward=1.0)."},
                    "allowed_frontier_file": {"type": "string", "description": "Optional allowed frontier lemma list file."},
                    "frontier_pinned_dir": {"type": "string", "description": "Optional pinned frontier challenge directory (--pinned DIR)."},
                    "frontier_base": {"type": "string", "description": "Optional earlier frontier result JSON for base_status ledger (--base FILE)."},
                    "low_mem": {"type": "boolean", "description": "If true (and frontier=false, notary=false), run check/lowmem/check-sound-lowmem.sh for tight RAM budgets."},
                    "notary": {"type": "boolean", "description": "If true (and frontier=false), run check/notary/check-notary.sh (unmodified official 4.36 libs + 3-leg SHA-256 environment digest, trust='notary')."},
                    "pins": {"type": "string", "enum": ["436", "437"], "description": "Normally omitted: the default is the challenge release's own trusted check (Lean 4.36: check/sound/pins.env; Lean 4.37.0-rc1: check/sound/pins-437.env). '436' / '437' are accepted only when they name that same judge; another release's judge is refused. Arbitrary caller paths are rejected (boundary B4)."},
                    "threads": {"type": "integer", "minimum": 1},
                    "timeout": {"type": "integer", "minimum": 1},
                },
                "required": ["export_file"],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_audit_challenge",
            "description": (
                "Audit a challenge directory (comparator.json and optional challenge.export) for statement-fidelity "
                "hazards: non-empty definition_names holes, non-standard permitted_axioms, missing challenge pin, "
                "and—when fastverify/tools/audit is installed—minimal non-Mathlib reading set & vacuity/lint checks."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "challenge_dir": {"type": "string"},
                    "challenge_sha256": {"type": "string", "description": "Optional expected SHA-256 of challenge.export."},
                    "probe": {"type": "boolean", "description": "Run kernel-certified vacuity/refutation probes inside bwrap (default: false for fast static AST audit)."},
                    "packages_dir": {"type": "string", "description": "Optional Lake packages workspace for --probe."},
                    "conjecture_mode": {"type": "boolean", "description": "Enable conjecture-mode checks in tools/audit/audit.py."},
                },
                "required": ["challenge_dir"],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_init_challenge",
            "description": (
                "Build and SHA-256-pin an official challenge export from clean challenge sources using the "
                "unmodified official Lean + official lean4export (--preset reference, B0+E0). Never uses "
                "untrusted build transforms."
            ),
            "inputSchema": {
                "type": "object",
                "properties": {
                    "challenge_dir": {"type": "string", "description": "Directory containing Challenge.lean, lakefile, comparator.json."},
                    "out_dir": {"type": "string", "description": "Directory to write challenge.export, challenge.export.sha256, and comparator.json."},
                    "packages_dir": {"type": "string"},
                    "threads": {"type": "integer", "minimum": 1},
                    "timeout": {"type": "number"},
                },
                "required": ["challenge_dir", "out_dir"],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_parse_diagnostics",
            "description": (
                "Parse raw Lean 4 compiler output into structured API v1 diagnostics, LSP 3.17 diagnostics, "
                "and SARIF 2.1.0 entries."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "compiler_output": {"type": "string"},
                    "default_file": {"type": "string"},
                },
                "required": ["compiler_output"],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_triage_sublemma",
            "description": (
                "EXPERIMENTAL in fastverify v0.1 (advisory only, not release grade; never a verdict): refused unless the "
                "server runs with --experimental or FV_EXPERIMENTAL=1. "
                "Fast pre-proving sandboxed triage of a proposed sorry sub-lemma BEFORE dispatching prover "
                "agents: checks strict elaboration (autoImplicit false), bounded counterexample/refutation "
                "probe on ¬statement, vacuity/contradictory-premise probe, partial-operation hazards "
                "(Nat.sub, / 0, Int.toNat, Real.sqrt), unused binders, local duplicate statements, and "
                "hygiene hints. Advisory only (zero TCB change)."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "source": {"type": "string", "description": "Lean 4 snippet containing the sub-lemma."},
                    "source_file": {"type": "string", "description": "Alternative path to a .lean file under allowed roots."},
                    "theorem": {"type": "string", "description": "Optional declaration name (defaults to last theorem/lemma)."},
                    "repo_dir": {"type": "string", "description": "Optional repository root for duplicate-lemma scan."},
                    "static_only": {"type": "boolean", "description": "Skip sandboxed Lean probes (instant static lints only)."},
                    "timeout": {"type": "number", "description": "Probe timeout seconds (default: 20)."},
                },
                "required": [],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_mint_subchallenges",
            "description": (
                "Mint standalone, SHA-256-pinned official sub-challenges (built by official B0+E0) from "
                "open sorry frontier lemmas in a blueprint project so untrusted prover agents can fill them "
                "in parallel without moving the goalposts."
            ),
            "inputSchema": {
                "type": "object",
                "properties": {
                    "project_dir": {"type": "string", "description": "Blueprint Lean project directory."},
                    "out_dir": {"type": "string", "description": "Destination directory for minted sub-challenges."},
                    "theorems": {"type": "array", "items": {"type": "string"}, "description": "List of frontier theorem names (auto-discovers sorry theorems if omitted)."},
                    "module": {"type": "string", "description": "Root Lean module name (auto-detected if omitted)."},
                    "packages_dir": {"type": "string"},
                    "for_fvserve": {"type": "boolean", "description": "Set solution_module=Attempt.<T> for fvserve/batchverify."},
                    "threads": {"type": "integer", "minimum": 1},
                    "timeout": {"type": "number"},
                },
                "required": ["project_dir", "out_dir"],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_verify_patch",
            "description": (
                "Send an in-memory multi-file patch (relative path -> new Lean source, or null to delete) "
                "or working tree directly to a running persistent fvwork repository daemon for "
                "seconds-level delta sound/frontier verification with progress ledger."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "files": {"type": "object", "description": "Map of repo-relative file paths to full file contents (or null to delete)."},
                    "tree_dir": {"type": "string", "description": "Alternative to 'files': full working tree path under allowed roots."},
                    "advance": {"type": "boolean", "description": "Advance fvwork base tree if build succeeds (default: false for speculative agent patches)."},
                    "merge": {"type": "boolean", "description": "Merge-queue semantics: serialized against current base, enters base ONLY if ACCEPTED or CONDITIONAL."},
                    "drift": {"type": "boolean", "description": "Request statement-drift diff vs base export (requires fvwork --expdiff)."},
                    "optimistic_only": {"type": "boolean", "description": "v0.1: experimental and not used (exact full mode is used; a warning says so)."},
                    "mode": {"type": "string", "enum": ["optimistic", "interface", "full"], "description": "v0.1: always run as full (exact); optimistic / interface are experimental, not used (a warning says so)."},
                    "label": {"type": "string"},
                    "timeout": {"type": "number"},
                },
                "required": [],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_lookup_duplicate",
            "description": (
                "Look up alpha-equivalent (binder-name-invariant kernel exphash) duplicate lemmas in Mathlib "
                "or repository sqlite indexes via tools/dupfind. Supports instant name/hash lookup "
                "or live candidate `.lean` source query. Advisory only (zero TCB change)."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "name": {"type": "string", "description": "Existing theorem name to look up in configured indexes."},
                    "type_hk": {"type": "string", "description": "Kernel statement hash (exphash type_hk) to look up."},
                    "source": {"type": "string", "description": "Candidate Lean 4 source snippet (`theorem X : T := by sorry`) to compile, export, hash, and query."},
                    "source_file": {"type": "string", "description": "Alternative path to candidate `.lean` file under allowed roots."},
                    "indexes": {"type": "array", "items": {"type": "string"}, "description": "Optional override list of dupfind sqlite index directories."},
                    "targets": {"type": "string", "description": "Comma-separated target theorem names for source query."},
                    "timeout": {"type": "number"},
                },
                "required": [],
                "additionalProperties": False,
            },
        },
        {
            "name": "fv_diff_exports",
            "description": (
                "Compare two lean4export NDJSON files at the kernel-term level using tools/compress/expdiff: "
                "reports identical, alpha-equal, value-changed (statement equal), STATEMENT-CHANGED, removed, added, "
                "renamed counts, and optional first-difference subterm explanations (--explain). Diagnostic analysis "
                "only (zero TCB, never a verification verdict)."
            ),
            "annotations": {"readOnlyHint": True},
            "inputSchema": {
                "type": "object",
                "properties": {
                    "old_export": {"type": "string", "description": "Path to baseline/original .export file."},
                    "new_export": {"type": "string", "description": "Path to candidate/new .export file."},
                    "targets": {"type": "string", "description": "Optional comma-separated target theorem names to restrict the closure."},
                    "targets_file": {"type": "string", "description": "Optional path to newline/whitespace-separated targets file."},
                    "explain": {"type": "integer", "minimum": 0, "maximum": 50, "description": "Max differing declarations per status to explain with first subterm path (default: 5)."},
                    "dead_lets": {"type": "boolean", "description": "Classify value changes that vanish modulo unused let/have bindings."},
                    "private_modulo": {"type": "boolean", "description": "Ignore module prefix in _private.<Mod>.0.* names (for module merges/splits)."},
                    "threads": {"type": "integer", "minimum": 1},
                    "timeout": {"type": "number"},
                },
                "required": ["old_export", "new_export"],
                "additionalProperties": False,
            },
        },
    ]


S1_PERMITTED_AXIOMS = ("propext", "Quot.sound", "Classical.choice")
SOUND_MCP_PRESETS = ("sound-auto", "sound", "notary")


# --------------------------------------------------------------------------- client paths, never dereferenced
# Every file or directory the server reads or copies ON THE HOST from a client-supplied location is opened by walking from
# the service owner's --allow-root with O_NOFOLLOW at every component (a symlink anywhere, also one swapped in after
# check_path, fails the open); client-supplied directories that are copied (source-only challenge_dir) or read
# (challenge_dir of fv_audit_challenge / fv_init_challenge) may not contain any symlink, special file or (when copied
# without a sha pin) hard-linked file: refused before anything is copied. Never shutil.copytree(symlinks=False).
# ONE policy for every client-supplied path, and every path read from client JSON / config: it is opened from
# the service owner's --allow-root one component at a time with O_NOFOLLOW (no symlink anywhere, also none swapped in later),
# the opened fd is re-checked with fstat (regular file with exactly one link, or directory; never a FIFO / socket /
# device), relative paths taken from client data have no absolute / '..' / empty component (check_relpath), and no tool
# is ever handed the client path itself: it gets a private copy (or a path configured by the service owner). Trusted inputs that a
# client cannot vouch for (a Lake packages workspace, an incremental base) come only from the service owner.
CLIENT_TREE_IGNORE = (".lake", ".git")       # not copied (like shutil.ignore_patterns(".lake", ".git")); such an
                                             # entry must itself be a real directory (a symlink named .lake is refused)
CLIENT_TREE_MAX_ENTRIES = 200000
# the no-follow walkers recurse once per level: a client tree deeper than this is refused
# (ClientPathError) - ~1200 levels would raise RecursionError (traceback, exit 1 = REJECTED on bin/fv)
CLIENT_TREE_MAX_DEPTH = 256
_O_DIR = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
_O_FILE = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | getattr(os, "O_CLOEXEC", 0)


class ClientPathError(Exception):
    pass


def check_relpath(rel, what="path"):
    """a relative path taken from client data: non-empty components, no absolute path, no '.' / '..' / empty
    component, no NUL / backslash / control character; returns the list of components"""
    if not isinstance(rel, str) or not rel or rel.startswith("/") or "\\" in rel or any(ord(c) < 32 for c in rel):
        raise ClientPathError(f"{what} {rel!r}: not a plain relative path")
    parts = rel.split("/")
    if any(p in ("", ".", "..") for p in parts):
        raise ClientPathError(f"{what} {rel!r}: empty, '.' or '..' component")
    return parts


def _map_to_root(path, roots, allow_dotdot=False):
    """the client's path WITHOUT resolving anything on the filesystem: made absolute
    (relative = against the current directory) and normalized lexically, then matched against the roots (each root as
    given and as resolved; the longest match wins) and re-rooted on that root's realpath. Returns (canonical path, root
    realpath). '..' is refused unless allow_dotdot (local CLI): then it is removed lexically, i.e. it never steps back
    through a symlink (no component is resolved; whatever the result names is then walked with O_NOFOLLOW). roots empty
    (--allow-any-root) = '/'."""
    if not isinstance(path, str) or not path or "\x00" in path or len(path) > 4096 or any(ord(c) < 32 or ord(c) == 127 for c in path):
        raise ClientPathError("invalid path")
    if not allow_dotdot and ".." in path.split("/"):
        raise ClientPathError("'..' path component refused (it could step outside allowed workspace roots)")
    ab = os.path.normpath(os.path.join(os.getcwd(), path))
    if ab.startswith("//"):
        ab = "/" + ab.lstrip("/")
    best = None
    for r in (roots or ["/"]):
        rr = os.path.realpath(r)
        for form in (os.path.normpath(os.path.abspath(r)), rr):
            pre = form.rstrip(os.sep) + os.sep
            if ab == form or ab.startswith(pre):
                if best is None or len(form) > len(best[0]):
                    best = (form, rr)
    if best is None:
        raise ClientPathError("path is outside allowed workspace roots")
    rest = os.path.relpath(ab, best[0])
    return (best[1] if rest == "." else os.path.join(best[1], rest)), best[1]


def client_abspath(path, roots, must_exist=True, expect_dir=None, allow_dotdot=False):
    """check a client path WITHOUT resolving it (replaces fv_schema.safe_resolve_under_roots
    = os.path.realpath, which followed every symlink - inside the root, a planted out_dir link, a bounce link probing
    paths outside the root - before anything was checked): _map_to_root, then every existing component is walked from the
    root with O_NOFOLLOW, so a symlink at ANY component is refused without being resolved; must_exist: the whole path must
    exist; expect_dir True / False: the final component is a directory / a regular file (when it exists). Returns the
    canonical path (no symlink at check time; later opens walk it again with open_nofollow_under)."""
    canon, base = _map_to_root(path, roots, allow_dotdot=allow_dotdot)
    rel = os.path.relpath(canon, base)
    parts = [] if rel == "." else rel.split(os.sep)
    fd = os.open(base, os.O_RDONLY | os.O_DIRECTORY | getattr(os, "O_CLOEXEC", 0))   # the root itself
    try:
        for i, part in enumerate(parts):
            last = i == len(parts) - 1
            try:
                st = os.stat(part, dir_fd=fd, follow_symlinks=False)
            except FileNotFoundError:
                if must_exist:
                    raise ClientPathError(f"{'/'.join(parts[:i + 1])!r} does not exist")
                return canon   # the rest is created later, without following links
            except OSError as e:
                raise ClientPathError(f"{'/'.join(parts[:i + 1])!r}: cannot check ({e.strerror})")
            if stat.S_ISLNK(st.st_mode):
                raise ClientPathError(f"{'/'.join(parts[:i + 1])!r} is a symlink (refused, not followed: a link could lead "
                                      "outside allowed workspace roots)")
            if last:
                if expect_dir is True and not stat.S_ISDIR(st.st_mode):
                    raise ClientPathError("expected a directory")
                if expect_dir is False and not stat.S_ISREG(st.st_mode):
                    raise ClientPathError("expected a regular file")
                if expect_dir is None and not (stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode)):
                    raise ClientPathError("special file refused")
                break
            if not stat.S_ISDIR(st.st_mode):
                raise ClientPathError(f"{'/'.join(parts[:i + 1])!r} is not a directory")
            try:
                nfd = os.open(part, _O_DIR, dir_fd=fd)
            except OSError as e:
                raise ClientPathError(f"{'/'.join(parts[:i + 1])!r}: not a directory reachable without following a "
                                      f"symlink ({e.strerror})")
            os.close(fd)
            fd = nfd
        if not parts and expect_dir is False:
            raise ClientPathError("expected a regular file")
        return canon
    finally:
        os.close(fd)


def cli_roots():
    """the anchors of LOCAL use (bin/fv, tools/audit/audit.py): the resolved current directory, the
    directories in FV_CLI_ROOTS (':'-separated absolute paths, resolved: for a workspace the user reaches through a
    symlink of their own) and '/'. A path is walked from the longest anchor containing it, every component below with
    O_NOFOLLOW: a symlink anywhere below the anchor - the path itself, an intermediate directory, an entry of a tree - is
    refused, never resolved (anchoring at the path's own resolved ancestor would follow a symlinked path or parent
    before anything was checked)."""
    roots = [os.path.realpath(os.getcwd())]
    for r in (os.environ.get("FV_CLI_ROOTS") or "").split(":"):
        if r and os.path.isabs(r) and os.path.isdir(r):
            # the anchor AS WRITTEN (normalized, not resolved): _map_to_root matches a path under
            # /that/link lexically and re-roots it on the realpath (resolving it here would make the link spelling never match)
            roots.append(os.path.normpath(r))
    roots.append("/")
    return roots


def open_nofollow_under(path, roots, want_dir, create=False, single_link=False):
    """open `path` (absolute, normally check_path's canonical path) by walking from the allowed root that contains it, one
    component at a time with O_NOFOLLOW: returns an fd of a directory (want_dir) or of a regular file; any symlink, a
    missing component, a non-regular final file or a path outside every root -> ClientPathError. roots empty (--allow-any-
    root) = walk from '/'. create (want_dir only): missing directories are created (mode 0755) on the way. The
    path is mapped onto the root lexically (_map_to_root: nothing resolved; '..' only removed lexically)."""
    if not isinstance(path, str) or not path or "\x00" in path:
        raise ClientPathError("invalid path")
    real, base = _map_to_root(path, roots, allow_dotdot=True)
    rel = os.path.relpath(real, base)
    parts = [] if rel == "." else rel.split(os.sep)
    if any(p in ("", ".", "..") for p in parts):
        raise ClientPathError("path is not normalized")
    if not parts and not want_dir:
        raise ClientPathError("expected a regular file")
    fd = os.open(base, os.O_RDONLY | os.O_DIRECTORY | getattr(os, "O_CLOEXEC", 0))   # the service owner's root itself
    try:
        for i, part in enumerate(parts):
            last = i == len(parts) - 1
            if create and want_dir:
                try:
                    os.mkdir(part, 0o755, dir_fd=fd)
                except FileExistsError:
                    pass
                except OSError as e:
                    raise ClientPathError(f"{'/'.join(parts[:i + 1])!r}: cannot create ({e.strerror})")
            try:
                nfd = os.open(part, _O_FILE if (last and not want_dir) else _O_DIR, dir_fd=fd)
            except OSError as e:
                raise ClientPathError(f"{'/'.join(parts[:i + 1])!r}: not a {'regular file' if last and not want_dir else 'directory'}"
                                      f" reachable without following a symlink ({e.strerror})")
            if last and not want_dir:
                # (hard-link race) a file's link count read on the fd alone is racy: the name can
                # be a hard link to another file at open() time and be unlinked again before fstat (st_nlink back to 1).
                # After the open, the NAME is re-checked against the parent directory fd: same inode as the fd, a regular
                # file, and (single_link) exactly one link on both - while the name still links to another file, that
                # file has >= 2 links; once the name is gone or replaced, the inode differs.
                try:
                    fst = os.fstat(nfd)
                    nst = os.stat(part, dir_fd=fd, follow_symlinks=False)
                except OSError as e:
                    os.close(nfd)
                    raise ClientPathError(f"{'/'.join(parts)!r}: changed during the open ({e.strerror})")
                if (fst.st_dev, fst.st_ino) != (nst.st_dev, nst.st_ino) or not stat.S_ISREG(nst.st_mode):
                    os.close(nfd)
                    raise ClientPathError(f"{'/'.join(parts)!r}: changed during the open (refused)")
                if single_link and (fst.st_nlink != 1 or nst.st_nlink != 1):
                    os.close(nfd)
                    raise ClientPathError(f"{os.path.basename(path)!r}: hard-linked file refused")
            os.close(fd)
            fd = nfd
        st = os.fstat(fd)
        if want_dir and not stat.S_ISDIR(st.st_mode) or not want_dir and not stat.S_ISREG(st.st_mode):
            raise ClientPathError("expected a %s" % ("directory" if want_dir else "regular file"))
        return fd
    except BaseException:
        os.close(fd)
        raise


def _write_all(fd, b):
    mv = memoryview(b)
    while mv:
        n = os.write(fd, mv)
        mv = mv[n:]


def _copy_fd_fd(src_fd, out):
    os.lseek(src_fd, 0, os.SEEK_SET)
    try:   # in-kernel copy (reflink / server-side where the filesystem supports it), else read/write
        while True:
            n = os.copy_file_range(src_fd, out, 1 << 30)
            if n == 0:
                break
    except (OSError, AttributeError):
        os.lseek(src_fd, 0, os.SEEK_SET)
        os.lseek(out, 0, os.SEEK_SET)
        os.ftruncate(out, 0)
        while True:
            b = os.read(src_fd, 1 << 20)
            if not b:
                break
            _write_all(out, b)


def _copy_fd_to(src_fd, dst, mode=0o600):
    out = os.open(dst, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0), mode)
    try:
        _copy_fd_fd(src_fd, out)
    finally:
        os.close(out)


def _safe_name(name):
    if not isinstance(name, str) or not name or "/" in name or "\x00" in name or name in (".", ".."):
        raise ClientPathError(f"bad file name {name!r}")


def write_file_at(dfd, name, data=None, src_fd=None, mode=0o644):
    """create or replace the entry `name` in the directory open at dfd without following anything: a fresh
    O_EXCL|O_NOFOLLOW temp file in that directory, then an atomic rename over `name` (which replaces a symlink planted there
    instead of writing through it)"""
    _safe_name(name)
    tmp = ".fv-tmp.%d.%s" % (os.getpid(), os.urandom(6).hex())
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0), 0o600, dir_fd=dfd)
    try:
        if src_fd is not None:
            _copy_fd_fd(src_fd, fd)
        else:
            _write_all(fd, data if isinstance(data, (bytes, bytearray)) else str(data).encode("utf-8"))
        os.fchmod(fd, mode)
    except BaseException:
        os.close(fd)
        try:
            os.unlink(tmp, dir_fd=dfd)
        except OSError:
            pass
        raise
    os.close(fd)
    os.replace(tmp, name, src_dir_fd=dfd, dst_dir_fd=dfd)


def subdir_at(dfd, name):
    """the sub-directory `name` of the directory open at dfd (created if missing), opened without following a
    symlink; returns its fd"""
    _safe_name(name)
    try:
        os.mkdir(name, 0o755, dir_fd=dfd)
    except FileExistsError:
        pass
    try:
        return os.open(name, _O_DIR, dir_fd=dfd)
    except OSError as e:
        raise ClientPathError(f"{name!r}: not a directory reachable without following a symlink ({e.strerror})")


def _verify_after_read(path, roots, fd, st0):
    """after the data was read / copied: the fd still has one link and an unchanged ctime (no link / unlink
    happened meanwhile: both update ctime), and the NAME still maps to that inode with one link; else ClientPathError"""
    dfd = open_nofollow_under(os.path.dirname(_map_to_root(path, roots, allow_dotdot=True)[0]), roots, want_dir=True)
    try:
        # twice, 2 ms apart: unlink() drops the link count before the name leaves the dentry cache, so ONE lookup can see
        # the other file's inode with one link for a few microseconds; the second lookup, after that window, sees the
        # name gone or the link count back at 2
        for k in (0, 1):
            if k:
                time.sleep(0.002)
            st1 = os.fstat(fd)
            if st1.st_nlink != 1 or (st1.st_ino, st1.st_ctime_ns) != (st0.st_ino, st0.st_ctime_ns):
                raise ClientPathError(f"{os.path.basename(path)!r}: changed while it was read (refused)")
            try:
                nst = os.stat(os.path.basename(path), dir_fd=dfd, follow_symlinks=False)
            except OSError as e:
                raise ClientPathError(f"{os.path.basename(path)!r}: changed while it was read ({e.strerror})")
            if (nst.st_dev, nst.st_ino) != (st1.st_dev, st1.st_ino) or nst.st_nlink != 1:
                raise ClientPathError(f"{os.path.basename(path)!r}: changed while it was read (refused)")
    finally:
        os.close(dfd)


def read_client_file(path, roots, max_bytes=16 << 20, require_single_link=True):
    """the bytes of a client-supplied regular file, read without following any symlink (name re-checked)"""
    fd = open_nofollow_under(path, roots, want_dir=False, single_link=require_single_link)
    try:
        st = os.fstat(fd)
        if require_single_link and st.st_nlink != 1:
            raise ClientPathError(f"{os.path.basename(path)!r}: hard-linked file refused")
        if st.st_size > max_bytes:
            raise ClientPathError(f"{os.path.basename(path)!r}: larger than {max_bytes} bytes")
        chunks, n = [], 0
        while n <= max_bytes:
            b = os.read(fd, 1 << 20)
            if not b:
                break
            chunks.append(b)
            n += len(b)
        if n > max_bytes:
            raise ClientPathError(f"{os.path.basename(path)!r}: larger than {max_bytes} bytes")
        if require_single_link:
            _verify_after_read(path, roots, fd, st)   # the race window is re-checked after the read
        return b"".join(chunks)
    finally:
        os.close(fd)


def local_roots(path=None):
    """roots for LOCAL CLI use (no --allow-root). = cli_roots(), independent of `path`: returning the
    path's own nearest existing ancestor RESOLVED would follow a symlinked path (or a symlinked parent) before any
    check (`fv init-challenge chal sym_out` would write through sym_out)"""
    return cli_roots()


def local_path_under(path, roots):
    """the absolute path, normalized lexically and re-rooted on the root that contains it (nothing resolved)"""
    return _map_to_root(path, roots, allow_dotdot=True)[0]


def _real_dir_at(path, roots, sub):
    """True iff path/sub[0]/sub[1]... is a directory reachable without following any link"""
    try:
        fd = open_nofollow_under(os.path.join(path, *sub), roots, want_dir=True)
    except (ClientPathError, OSError):
        return False
    os.close(fd)
    return True


def lake_config_confined(proj_dir):
    """None if the lakefile.toml of proj_dir (a PRIVATE copy: no symlink anywhere) names
    only plain relative in-tree paths, else the refusal. lib/autotune.py (run on the host by fv_doctor and by bin/fastverify
    --preset sound-auto) walks every srcDir it reads there, and an absolute or '..' srcDir walked host directories outside
    the copy and --allow-root (module names, sizes, markers; a FIFO hung it). Conservative: every line that mentions one of
    Lake's path keys must be exactly `KEY = "relative/path"` (no quoted / dotted / escaped key, inline table, literal or
    multi-line string), and the path must be relative, without '..' or an empty component. lakefile.lean is Lean code that
    autotune does not read for paths (Lake runs it inside the build sandbox)."""
    p = os.path.join(proj_dir, "lakefile.toml")
    try:
        st = os.lstat(p)
    except FileNotFoundError:
        return None
    except OSError as e:
        return f"lakefile.toml: cannot check ({e.strerror})"
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        return "lakefile.toml: not a single-link regular file"
    txt = _read_plain_file(p, 1 << 20)
    if txt is None:
        return "lakefile.toml: unreadable"
    keys = ("srcDir", "buildDir", "packagesDir", "leanLibDir", "nativeLibDir", "binDir", "irDir", "subDir", "path", "dir")
    alt = "|".join(keys)
    for i, ln in enumerate(txt.splitlines(), 1):
        if ln.lstrip().startswith("#") or not re.search(r"\b(%s)\b" % alt, ln) and "\\" not in ln:
            continue   # a full-line comment, or no path key and no escape on this line
        if re.search(r"\\[uU]", ln):
            return f"lakefile.toml line {i}: unicode escapes are refused (a key could spell a path key)"
        m = re.fullmatch(r'\s*(%s)\s*=\s*"([^"\\]*)"\s*(#.*)?' % alt, ln)
        if not m:
            if re.search(r"""\b(%s)["']?\s*=""" % alt, ln):
                return (f"lakefile.toml line {i}: a path key ({', '.join(keys)}) must be written on its own line as "
                        "KEY = \"relative/path\" (no quoted / dotted key, inline table, literal or multi-line string)")
            continue   # the word only occurs inside a value (name = "path", an array element ...)
        v = m.group(2)
        v2 = v[2:] if v.startswith("./") else v
        if v2 in ("", "."):
            continue
        parts = v2.rstrip("/").split("/")
        if v2.startswith("/") or any(c in ("", ".", "..") or not re.fullmatch(r"[A-Za-z0-9_.+-]+", c) for c in parts):
            return (f"lakefile.toml line {i}: {m.group(1)} {v!r} is not a plain relative path inside the project "
                    "(absolute / '..' / empty component refused)")
    return None


def copy_client_file(path, dst, roots, mode=0o444, require_single_link=True):
    """copy a client-supplied regular file to dst without following any symlink (see open_nofollow_under; name
    re-checked after the open)"""
    fd = open_nofollow_under(path, roots, want_dir=False, single_link=require_single_link)
    try:
        st0 = os.fstat(fd)
        if require_single_link and st0.st_nlink != 1:
            raise ClientPathError(f"{os.path.basename(path)!r}: hard-linked file refused")
        _copy_fd_to(fd, dst)
        if require_single_link:
            try:   # the race window is re-checked after the copy; a refused copy is removed
                _verify_after_read(path, roots, fd, st0)
            except ClientPathError:
                os.unlink(dst)
                raise
    finally:
        os.close(fd)
    os.chmod(dst, mode)


def scan_client_tree(dir_fd, ignore=CLIENT_TREE_IGNORE, single_link=False, max_entries=CLIENT_TREE_MAX_ENTRIES):
    """refuse (ClientPathError) any symlink / special file (and with single_link any regular file with more than one hard
    link) under the directory open at dir_fd; entries named in `ignore` (at every level) are skipped, as when copied"""
    count = [0]

    def walk(dfd, rel):
        with os.scandir(dfd) as it:
            names = sorted(e.name for e in it)
        for n in names:
            r = os.path.join(rel, n) if rel else n
            if n in ignore:   # skipped only if it really is a directory
                st_i = os.stat(n, dir_fd=dfd, follow_symlinks=False)
                # a regular-FILE `.git` (git worktree checkout, git submodule: "gitdir: ...") is skipped
                # too: never read, so its gitdir pointer is never followed; a symlink / special file stays refused
                if n == ".git" and stat.S_ISREG(st_i.st_mode):
                    continue
                if not stat.S_ISDIR(st_i.st_mode):
                    raise ClientPathError(f"{r!r} must be a real directory (symlink / file / special refused)")
                continue
            count[0] += 1
            if count[0] > max_entries:
                raise ClientPathError(f"more than {max_entries} entries")
            st = os.stat(n, dir_fd=dfd, follow_symlinks=False)
            if stat.S_ISLNK(st.st_mode):
                raise ClientPathError(f"symlink {r!r} refused (client-supplied directories may not contain symlinks)")
            if stat.S_ISDIR(st.st_mode):
                try:
                    cfd = os.open(n, _O_DIR, dir_fd=dfd)
                except OSError as e:
                    raise ClientPathError(f"{r!r}: cannot open without following links ({e.strerror})")
                try:
                    if r.count("/") >= CLIENT_TREE_MAX_DEPTH:
                        raise ClientPathError(f"directory tree deeper than {CLIENT_TREE_MAX_DEPTH} levels ({r[:120]!r}...)")
                    walk(cfd, r)
                finally:
                    os.close(cfd)
            elif stat.S_ISREG(st.st_mode):
                if single_link and st.st_nlink != 1:
                    raise ClientPathError(f"hard-linked file {r!r} refused")
            else:
                raise ClientPathError(f"special file {r!r} refused")
    try:
        walk(dir_fd, "")
    except RecursionError:   # never a traceback: a refusal (exit 2 on bin/fv)
        raise ClientPathError("directory tree too deep to walk") from None


def export_tree_to(src_dir, out_fd):
    """copy a tree the server produced itself (regular files + dirs) into the client directory open at out_fd,
    every entry created / replaced without following links (write_file_at / subdir_at)"""
    for n in sorted(os.listdir(src_dir)):
        sp = os.path.join(src_dir, n)
        st = os.lstat(sp)
        if stat.S_ISDIR(st.st_mode):
            cfd = subdir_at(out_fd, n)
            try:
                export_tree_to(sp, cfd)
            finally:
                os.close(cfd)
        elif stat.S_ISREG(st.st_mode):
            fd = os.open(sp, _O_FILE)
            try:
                write_file_at(out_fd, n, src_fd=fd, mode=stat.S_IMODE(st.st_mode) & 0o755 | 0o400)
            finally:
                os.close(fd)


def copy_client_tree(dir_fd, dst, ignore=CLIENT_TREE_IGNORE, max_entries=CLIENT_TREE_MAX_ENTRIES, file_filter=None):
    """copy the directory open at dir_fd to the NEW directory dst (created 0700): regular files and directories only,
    nothing followed (every entry opened relative to its parent's fd with O_NOFOLLOW and re-checked with fstat: same inode
    as the scan, regular file, one hard link); a symlink / special file / hard link anywhere -> ClientPathError (dst may
    then hold a partial copy: the caller discards it)"""
    count = [0]
    os.mkdir(dst, 0o700)

    def walk(dfd, dpath, rel):
        with os.scandir(dfd) as it:
            names = sorted(e.name for e in it)
        for n in names:
            r = os.path.join(rel, n) if rel else n
            if n in ignore:   # skipped only if it really is a directory
                st_i = os.stat(n, dir_fd=dfd, follow_symlinks=False)
                # a regular-FILE `.git` (git worktree checkout, git submodule: "gitdir: ...") is skipped
                # too: never read, so its gitdir pointer is never followed; a symlink / special file stays refused
                if n == ".git" and stat.S_ISREG(st_i.st_mode):
                    continue
                if not stat.S_ISDIR(st_i.st_mode):
                    raise ClientPathError(f"{r!r} must be a real directory (symlink / file / special refused)")
                continue
            if file_filter is not None and not file_filter(n):
                st0 = os.stat(n, dir_fd=dfd, follow_symlinks=False)
                if not stat.S_ISDIR(st0.st_mode):
                    if stat.S_ISREG(st0.st_mode):
                        continue   # a regular file the caller does not need: not copied
                    raise ClientPathError(f"{'symlink' if stat.S_ISLNK(st0.st_mode) else 'special file'} {r!r} refused")
            count[0] += 1
            if count[0] > max_entries:
                raise ClientPathError(f"more than {max_entries} entries")
            st = os.stat(n, dir_fd=dfd, follow_symlinks=False)
            if stat.S_ISLNK(st.st_mode):
                raise ClientPathError(f"symlink {r!r} refused (client-supplied directories may not contain symlinks)")
            if stat.S_ISDIR(st.st_mode):
                try:
                    cfd = os.open(n, _O_DIR, dir_fd=dfd)
                except OSError as e:
                    raise ClientPathError(f"{r!r}: cannot open without following links ({e.strerror})")
                try:
                    cst = os.fstat(cfd)
                    if (cst.st_dev, cst.st_ino) != (st.st_dev, st.st_ino):
                        raise ClientPathError(f"{r!r} changed during the copy")
                    os.mkdir(os.path.join(dpath, n), 0o755)
                    if r.count("/") >= CLIENT_TREE_MAX_DEPTH:
                        raise ClientPathError(f"directory tree deeper than {CLIENT_TREE_MAX_DEPTH} levels ({r[:120]!r}...)")
                    walk(cfd, os.path.join(dpath, n), r)
                finally:
                    os.close(cfd)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink != 1:
                    raise ClientPathError(f"hard-linked file {r!r} refused")
                try:
                    ffd = os.open(n, _O_FILE, dir_fd=dfd)
                except OSError as e:
                    raise ClientPathError(f"{r!r}: cannot open without following links ({e.strerror})")
                try:
                    fst = os.fstat(ffd)
                    if not stat.S_ISREG(fst.st_mode) or (fst.st_dev, fst.st_ino) != (st.st_dev, st.st_ino) or fst.st_nlink != 1:
                        raise ClientPathError(f"{r!r} changed during the copy")
                    _copy_fd_to(ffd, os.path.join(dpath, n), 0o755 if fst.st_mode & 0o111 else 0o644)
                finally:
                    os.close(ffd)
            else:
                raise ClientPathError(f"special file {r!r} refused")
    try:
        walk(dir_fd, dst, "")
    except RecursionError:
        raise ClientPathError("directory tree too deep to copy") from None


def run_xversion_gate(fv_root, chx, cfg):
    """Run check/xversion/xvcheck.py before judging with a 4.36 checker.
    Returns (0, None) on OK, (1, reason) on definite REJECTED, or (2, reason) on DECLINED/error."""
    xv = os.path.join(fv_root, "check", "xversion", "xvcheck.py")
    if not os.path.isfile(xv):
        return 2, "cross-version gate check/xversion/xvcheck.py missing"
    fd, jf = tempfile.mkstemp(prefix="fv-xv.", suffix=".json")
    os.close(fd)
    try:
        p = subprocess.run(
            ["/usr/bin/python3", "-I", xv, chx, cfg, "--json", jf],
            capture_output=True, text=True, timeout=300,
            env={"PATH": "/usr/local/bin:/usr/bin:/bin", "HOME": os.environ.get("HOME", "/tmp"), "LANG": "C.UTF-8"},
        )
        rc = p.returncode
        try:
            j = json.load(open(jf, encoding="utf-8"))
        except (OSError, ValueError):
            j = {}
    except subprocess.TimeoutExpired:
        rc, j = 2, {"verdict": "DECLINED", "reason": "cross-version gate timed out"}
    finally:
        try:
            os.unlink(jf)
        except OSError:
            pass
    if rc == 0:
        return 0, None
    reason = str(j.get("reason") or f"cross-version gate exit {rc}")
    if rc == 1 and j.get("verdict") == "REJECTED":
        return 1, reason
    return 2, reason


def module_name_parts(mod):
    """tools/audit/vacuity_probe.py module_rel_parts: a module name from a client is dotted Lean
    identifier components only (else None)"""
    ad = os.path.join(FV_ROOT, "tools", "audit")
    if ad not in sys.path:
        sys.path.insert(0, ad)
    import vacuity_probe
    return vacuity_probe.module_rel_parts(mod)


def release_pins_shorthand(fv_root, chx):
    """'<X>' of the check/sound/pins-<X>.env whose TC_VERSION is the challenge export's Lean release (meta line);
    None = the default judge (pins.env) - the same rule as `fv check` and bin/fastverify's sound-auto"""
    import glob
    try:
        with open(chx, "rb") as f:
            first = f.readline(1 << 20)
        ver = (json.loads(first).get("meta") or {}).get("lean", {}).get("version")
    except (OSError, ValueError, AttributeError):
        return None
    if not isinstance(ver, str) or not ver:
        return None
    for fp in sorted(glob.glob(os.path.join(fv_root, "check", "sound", "pins-*.env"))):
        try:
            tv = [ln.split("=", 1)[1].strip() for ln in open(fp, encoding="utf-8") if ln.startswith("TC_VERSION=")]
        except OSError:
            continue
        if tv and tv[0] == "leanprover/lean4:v" + ver:
            return os.path.basename(fp)[len("pins-"):-len(".env")]
    return None


def validate_s1_comparator_axioms(cfg_path):
    """Enforce the permitted_axioms subset check on comparator.json."""
    try:
        cc = json.load(open(cfg_path, encoding="utf-8"))
    except Exception as e:
        return f"invalid comparator.json: {e}"
    if not isinstance(cc, dict):   # Lake's config decoder needs an object: configuration error, exit 2
        return f"invalid comparator.json: a JSON object is required, not {type(cc).__name__} (configuration error)"
    axs = cc.get("permitted_axioms")
    if not isinstance(axs, list):
        return "comparator.json missing list permitted_axioms"
    # compared as LEAN names (check/xversion/xvcheck.py parse_lean_name = the judges' String.toName
    # mirror): `«propext»` is propext; the set is not widened (`«Quot.sound»` = one component, a non-name: outside)
    try:
        import importlib.util
        spec = importlib.util.spec_from_file_location("mcp_xvcheck", os.path.join(FV_ROOT, "check", "xversion", "xvcheck.py"))
        xv = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(xv)
    except Exception as e:  # noqa: BLE001
        return f"cannot load the Lean name parser (check/xversion/xvcheck.py): {e}"
    s1 = {xv.parse_lean_name(n) for n in S1_PERMITTED_AXIOMS}
    bad = [x for x in axs if not isinstance(x, str) or xv.parse_lean_name(x) not in s1]
    if bad:
        return (f"comparator.json permitted_axioms {bad} outside GOAL S1(3) "
                f"({', '.join(S1_PERMITTED_AXIOMS)})")
    return None


class McpServer:
    def __init__(self, args):
        self.args = args
        # the EXPERIMENTAL tools (fv_triage_sublemma) run only with the service owner's explicit opt-in
        self.experimental = bool(getattr(args, "experimental", False)) or os.environ.get("FV_EXPERIMENTAL") == "1"
        self.fv_root = os.path.realpath(args.fv_root or FV_ROOT)
        if getattr(args, "allow_any_root", False):
            self.allowed_roots = []
        elif args.allow_root:
            self.allowed_roots = [os.path.realpath(r) for r in args.allow_root]
            # the roots as the service owner wrote them too: a client path is matched lexically (never resolved)
            self.allowed_root_forms = [os.path.abspath(r) for r in args.allow_root] + self.allowed_roots
        else:
            self.allowed_roots = [os.path.realpath(os.getcwd())]
        self.fvserve_state = os.path.realpath(args.fvserve_state) if args.fvserve_state else None
        self.fvapi_url = args.fvapi_url.rstrip("/") if args.fvapi_url else None
        self.fvwork_state = os.path.realpath(args.fvwork_state) if args.fvwork_state else None
        self.dupfind_indexes = [os.path.realpath(p) for p in (args.dupfind_index or [])]
        self.dupfind_socket = os.path.realpath(args.dupfind_socket) if args.dupfind_socket else None
        self.dupfind_snapshot = os.path.realpath(args.dupfind_snapshot) if args.dupfind_snapshot else None
        self.default_pset = args.default_pset
        self.default_packages = os.path.realpath(args.packages) if args.packages else None
        self.default_threads = args.threads or min(16, os.cpu_count() or 4)
        self.max_source_bytes = args.max_source_bytes
        self.max_batch = args.max_batch
        self.default_timeout = args.default_timeout
        # the comparator pin is never optional where the challenge pin is required:
        # --allow-unpinned-comparator is accepted for compatibility but no longer relaxes anything
        self.allow_unpinned_comparator = False
        self.allow_caller_challenge = bool(getattr(args, "allow_caller_challenge", False))
        self.allow_unsound_presets = bool(getattr(args, "allow_unsound_presets", False))
        self.allow_custom_axioms = bool(getattr(args, "allow_custom_axioms", False))
        self.challenges = {}
        self._chal_root = None
        if getattr(args, "challenge", None):
            self._chal_root = tempfile.mkdtemp(prefix="fv-mcp-chals.")
            os.chmod(self._chal_root, 0o700)
            atexit.register(lambda d=self._chal_root: shutil.rmtree(d, ignore_errors=True))
            for spec in args.challenge:
                self._register_challenge_spec(spec)
        self.framing = None  # "newline" or "lsp"
        self.initialized = False
        self.protocol_version = SUPPORTED_PROTOCOLS[0]
        self.tools = build_tool_specs()
        self.tool_names = {t["name"] for t in self.tools}
        self.stats = {"calls": 0, "errors": 0, "started": time.time()}

    def _register_challenge_spec(self, spec):
        """Register a service-owner-pinned challenge 'ID=DIR[:CHALLENGE_SHA256[:COMPARATOR_SHA256]]' into private 0400 copies."""
        if "=" not in spec:
            raise SystemExit(f"fastverify-mcp --challenge: expected ID=DIR[:CHAL_SHA[:CFG_SHA]], got {spec!r}")
        cid, rest = spec.split("=", 1)
        cid = cid.strip()
        if not re.fullmatch(r"[A-Za-z0-9._-]{1,80}", cid):
            raise SystemExit(f"fastverify-mcp --challenge: invalid id {cid!r}")
        parts = rest.split(":")
        cdir = os.path.realpath(parts[0])
        exp_csha = parts[1].strip() if len(parts) >= 2 and parts[1].strip() else None
        exp_cfg_sha = parts[2].strip() if len(parts) >= 3 and parts[2].strip() else None
        src_chx = os.path.join(cdir, "challenge.export")
        src_cfg = os.path.join(cdir, "comparator.json")
        if not os.path.isfile(src_chx) or not os.path.isfile(src_cfg):
            raise SystemExit(f"fastverify-mcp --challenge {cid}: missing challenge.export or comparator.json in {cdir}")
        priv_d = os.path.join(self._chal_root, cid)
        os.makedirs(priv_d, mode=0o700, exist_ok=True)
        priv_chx = os.path.join(priv_d, "challenge.export")
        priv_cfg = os.path.join(priv_d, "comparator.json")
        shutil.copyfile(src_chx, priv_chx)
        shutil.copyfile(src_cfg, priv_cfg)
        os.chmod(priv_chx, 0o400)
        os.chmod(priv_cfg, 0o400)
        tc_src = os.path.join(cdir, "lean-toolchain")
        if os.path.isfile(tc_src):
            shutil.copyfile(tc_src, os.path.join(priv_d, "lean-toolchain"))
            os.chmod(os.path.join(priv_d, "lean-toolchain"), 0o400)
        got_csha = fv_schema.sha256_file(priv_chx)
        got_cfg_sha = fv_schema.sha256_file(priv_cfg)
        if exp_csha and got_csha != exp_csha:
            raise SystemExit(f"fastverify-mcp --challenge {cid}: challenge.export sha256 mismatch ({got_csha} != {exp_csha})")
        if exp_cfg_sha and got_cfg_sha != exp_cfg_sha:
            raise SystemExit(f"fastverify-mcp --challenge {cid}: comparator.json sha256 mismatch ({got_cfg_sha} != {exp_cfg_sha})")
        self.challenges[cid] = {
            "dir": priv_d,
            "challenge_export": priv_chx,
            "comparator_json": priv_cfg,
            "challenge_sha256": got_csha,
            "comparator_sha256": got_cfg_sha,
        }

    def _resolve_pinned_challenge(self, params, tmpd, for_export_check=False):
        """Resolve either a challenge_id registered by the service owner or caller paths with mandatory challenge+comparator SHA-256 pinning
        (prevents untrusted MCP agents from forging comparator.json e.g. adding sorryAx to permitted_axioms).
        Always returns private immutable 0444/0400 paths verified AFTER copying (zero TOCTOU)."""
        cid = params.get("challenge_id")
        if cid is not None:
            rec = self.challenges.get(str(cid))
            if not rec:
                return None, f"unknown challenge_id {cid!r} (registered: {sorted(self.challenges)})"
            if fv_schema.sha256_file(rec["challenge_export"]) != rec["challenge_sha256"]:
                return None, f"registered challenge {cid!r} challenge.export integrity failure"
            if fv_schema.sha256_file(rec["comparator_json"]) != rec["comparator_sha256"]:
                return None, f"registered challenge {cid!r} comparator.json integrity failure"
            if not self.allow_custom_axioms:
                ax_err = validate_s1_comparator_axioms(rec["comparator_json"])
                if ax_err:
                    return None, ax_err
            return rec, None

        # If server has exactly one registered challenge and caller omitted both challenge_id and caller paths,
        # resolve to that sole challenge registered by the service owner.
        has_caller_paths = any(params.get(k) for k in ("challenge_export", "comparator_json", "challenge_dir"))
        if self.challenges and not has_caller_paths:
            if len(self.challenges) == 1:
                only_cid = next(iter(self.challenges))
                p2 = dict(params)
                p2["challenge_id"] = only_cid
                return self._resolve_pinned_challenge(p2, tmpd, for_export_check=for_export_check)
            return None, f"challenge_id is required (registered: {sorted(self.challenges)})"

        # Explicit caller paths: require comparator_sha256 by default
        pin = params.get("challenge_sha256")
        cfg_pin = params.get("comparator_sha256")
        if for_export_check:
            chx, err = self.check_path(params.get("challenge_export"), must_exist=True, expect_dir=False)
            if err:
                return None, f"challenge_export: {err}"
            cfg, err = self.check_path(params.get("comparator_json"), must_exist=True, expect_dir=False)
            if err:
                return None, f"comparator_json: {err}"
            if not fv_schema.validate_sha256(pin):
                return None, "challenge_sha256 must be 64 lowercase hex chars"
            if not self.allow_unpinned_comparator and not fv_schema.validate_sha256(cfg_pin):
                return None, (
                    "comparator_sha256 (64 lowercase hex chars) is required next to challenge_sha256 "
                    "(or pass a challenge_id registered by the service owner; prevents forged comparator.json)"
                )
            if cfg_pin is not None and not fv_schema.validate_sha256(cfg_pin):
                return None, "comparator_sha256 must be 64 lowercase hex chars"
            priv_d = os.path.join(tmpd, "priv_chal")
            os.makedirs(priv_d, mode=0o700, exist_ok=True)
            priv_chx = os.path.join(priv_d, "challenge.export")
            priv_cfg = os.path.join(priv_d, "comparator.json")
            try:   # no symlink followed (also none swapped in after check_path); no hard link (sha oracle)
                copy_client_file(chx, priv_chx, self.allowed_roots, require_single_link=True)
                copy_client_file(cfg, priv_cfg, self.allowed_roots, require_single_link=True)
            except (ClientPathError, OSError) as e:
                return None, f"failed to copy challenge_export / comparator_json privately: {e}"
            got_chx = fv_schema.sha256_file(priv_chx)
            if got_chx != pin:
                return None, f"challenge_export sha256 mismatch (got {got_chx}, pinned {pin})"
            got_cfg = fv_schema.sha256_file(priv_cfg)
            if cfg_pin is not None and got_cfg != cfg_pin:
                return None, f"comparator_json sha256 mismatch (got {got_cfg}, pinned {cfg_pin})"
            if self.challenges and not self.allow_caller_challenge:
                if not any(r["challenge_sha256"] == got_chx and r["comparator_sha256"] == got_cfg
                           for r in self.challenges.values()):
                    return None, (
                        "challenge_export/comparator_json sha256 mismatch against the service owner's --challenge registry "
                        f"(pass challenge_id in {sorted(self.challenges)}; B4)"
                    )
            if not self.allow_custom_axioms:
                ax_err = validate_s1_comparator_axioms(priv_cfg)
                if ax_err:
                    return None, ax_err
            return {
                "dir": priv_d, "challenge_export": priv_chx, "comparator_json": priv_cfg,
                "challenge_sha256": got_chx, "comparator_sha256": got_cfg,
            }, None

        # fv_verify_project with explicit challenge_dir
        chal, err = self.check_path(params.get("challenge_dir"), must_exist=True, expect_dir=True)
        if err:
            return None, f"challenge_dir: {err}"
        # the client's directory is opened without following links and may contain no symlink / special file at all
        # (checked before anything is copied; shutil.copytree(symlinks=False) dereferenced links out of --allow-root and
        # into paths bwrap hides)
        try:
            chal_fd = open_nofollow_under(chal, self.allowed_roots, want_dir=True)
        except ClientPathError as e:
            return None, f"challenge_dir: {e}"
        try:
            # a pinned challenge (challenge.export present) is read as exactly three files relative to chal_fd
            # (O_NOFOLLOW, regular, single link); a source-only challenge is copied and built: the whole tree is scanned
            # first (no symlink / special file / hard link anywhere) and copied with the same checks
            try:
                st = os.stat("challenge.export", dir_fd=chal_fd, follow_symlinks=False)
                pinned_layout = stat.S_ISREG(st.st_mode)
            except OSError:
                pinned_layout = False
            if not pinned_layout:
                try:
                    scan_client_tree(chal_fd, single_link=True)
                except (ClientPathError, OSError) as e:
                    return None, f"challenge_dir refused: {e}"
            return self._resolve_challenge_dir(chal, chal_fd, pin, cfg_pin, tmpd)
        finally:
            os.close(chal_fd)

    def _resolve_challenge_dir(self, chal, chal_fd, pin, cfg_pin, tmpd):
        """the challenge_dir branch of _resolve_pinned_challenge; chal_fd = the directory opened without following links and
        already scanned (no symlink / special file); every read below is relative to chal_fd with O_NOFOLLOW"""
        def entry_kind(name):
            try:
                st = os.stat(name, dir_fd=chal_fd, follow_symlinks=False)
            except OSError:
                return None
            return "f" if stat.S_ISREG(st.st_mode) else ("l" if stat.S_ISLNK(st.st_mode) else "o")

        def copy_entry(name, dst, mode=0o444):
            try:
                fd = os.open(name, _O_FILE, dir_fd=chal_fd)
            except OSError as e:
                raise ClientPathError(f"{name}: cannot open without following links ({e.strerror})")
            try:
                fst = os.fstat(fd)
                if not stat.S_ISREG(fst.st_mode):
                    raise ClientPathError(f"{name}: not a regular file")
                if fst.st_nlink != 1:   # a hard link to another file would turn the sha messages into an oracle
                    raise ClientPathError(f"{name}: hard-linked file refused")
                _copy_fd_to(fd, dst)
            finally:
                os.close(fd)
            os.chmod(dst, mode)
        if entry_kind("comparator.json") != "f":
            return None, f"challenge_dir has no comparator.json (regular file): {chal}"
        has_chx = entry_kind("challenge.export") == "f"
        if pin is not None and not fv_schema.validate_sha256(pin):
            return None, "challenge_sha256 must be 64 lowercase hex chars"
        if not self.allow_unpinned_comparator:
            if not fv_schema.validate_sha256(cfg_pin):
                return None, (
                    "comparator_sha256 (64 lowercase hex chars) is required with challenge_dir "
                    "(or pass a challenge_id registered by the service owner; prevents forged comparator.json)"
                )
            if has_chx and not fv_schema.validate_sha256(pin):
                return None, "challenge_sha256 (64 lowercase hex chars) is required when challenge.export is present"
        elif cfg_pin is not None and not fv_schema.validate_sha256(cfg_pin):
            return None, "comparator_sha256 must be 64 lowercase hex chars"
        priv_d = os.path.join(tmpd, "priv_chal")
        os.makedirs(priv_d, mode=0o700, exist_ok=True)
        priv_cfg = os.path.join(priv_d, "comparator.json")
        try:
            copy_entry("comparator.json", priv_cfg)
        except (ClientPathError, OSError) as e:
            return None, f"failed to copy comparator.json privately: {e}"
        got_cfg = fv_schema.sha256_file(priv_cfg)
        if cfg_pin is not None and got_cfg != cfg_pin:
            return None, f"comparator_json sha256 mismatch (got {got_cfg}, pinned {cfg_pin})"
        priv_chx = None
        got_chx = pin
        if has_chx:
            priv_chx = os.path.join(priv_d, "challenge.export")
            try:
                copy_entry("challenge.export", priv_chx)
            except (ClientPathError, OSError) as e:
                return None, f"failed to copy challenge.export privately: {e}"
            got_chx = fv_schema.sha256_file(priv_chx)
            if pin is not None and got_chx != pin:
                return None, f"challenge_export sha256 mismatch (got {got_chx}, pinned {pin})"
            # Copy lean-toolchain if present; bin/fastverify only needs challenge.export + comparator.json when export exists
            if entry_kind("lean-toolchain") == "f":
                try:
                    copy_entry("lean-toolchain", os.path.join(priv_d, "lean-toolchain"))
                except (ClientPathError, OSError) as e:
                    return None, f"failed to copy lean-toolchain privately: {e}"
            use_dir = priv_d
        else:
            # Source-only challenge dir (needs .lean sources to build): copied WITHOUT following anything (no symlink,
            # special file or hard link anywhere, every entry re-checked by fstat), then the comparator.json copy is re-hashed
            shutil.rmtree(priv_d)
            try:
                copy_client_tree(chal_fd, priv_d)
            except (ClientPathError, OSError) as e:
                shutil.rmtree(priv_d, ignore_errors=True)
                return None, f"challenge_dir refused: {e}"
            os.chmod(os.path.join(priv_d, "comparator.json"), 0o444)
            if fv_schema.sha256_file(os.path.join(priv_d, "comparator.json")) != got_cfg:
                return None, "comparator_json changed during copy (TOCTOU)"
            use_dir = priv_d
        if self.challenges and not self.allow_caller_challenge:
            if not has_chx or not any(r["challenge_sha256"] == got_chx and r["comparator_sha256"] == got_cfg
                                      for r in self.challenges.values()):
                return None, (
                    "challenge_dir sha256 mismatch against the service owner's --challenge registry "
                    f"(pass challenge_id in {sorted(self.challenges)}; B4)"
                )
        if not self.allow_custom_axioms:
            ax_err = validate_s1_comparator_axioms(priv_cfg)
            if ax_err:
                return None, ax_err
        return {
            "dir": use_dir, "challenge_export": priv_chx, "comparator_json": priv_cfg,
            "challenge_sha256": got_chx, "comparator_sha256": got_cfg,
        }, None

    # ----------------------------------------------------------------------- path safety
    def check_path(self, path, must_exist=True, expect_dir=None):
        """the client path is NOT resolved (fv_schema.safe_resolve_under_roots called
        os.path.realpath first, so a symlink inside the root - an intermediate directory, the path itself, a planted out_dir
        link - was followed, and a bounce link made the host resolve paths outside --allow-root): client_abspath maps it
        lexically onto an allowed root ('..' refused) and walks every existing component with O_NOFOLLOW. Returns
        (canonical path, None) or (None, error)."""
        roots = getattr(self, "allowed_root_forms", None) or self.allowed_roots
        try:
            return client_abspath(path, roots, must_exist=must_exist, expect_dir=expect_dir), None
        except ClientPathError as e:
            return None, str(e)
        except OSError as e:
            return None, f"cannot check path ({e.strerror})"

    # ----------------------------------------------------------------------- backend calls
    def call_fvserve(self, payload, timeout=None):
        tmo = float(timeout or self.default_timeout)
        if self.fvserve_state:
            return fvserve.request(self.fvserve_state, payload, timeout=tmo)
        if self.fvapi_url:
            if payload.get("op") == "stats":
                req = urllib.request.Request(f"{self.fvapi_url}/health", method="GET")
                with urllib.request.urlopen(req, timeout=min(tmo, 10.0)) as r:
                    return json.loads(r.read().decode("utf-8"))
            data = json.dumps(payload).encode("utf-8")
            req = urllib.request.Request(
                f"{self.fvapi_url}/v1/verify",
                data=data,
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=tmo) as r:
                return json.loads(r.read().decode("utf-8"))
        raise RuntimeError("no fvserve (--fvserve-state) or fvapi (--fvapi-url) configured")

    def tool_fv_status(self, _params):
        t0 = time.time()
        backends = {
            "fastverify_cli": os.path.isfile(os.path.join(self.fv_root, "bin", "fastverify")),
            "check_sound": os.path.isfile(os.path.join(self.fv_root, "check", "sound", "check-sound.sh")),
            "incr": os.path.isfile(os.path.join(self.fv_root, "tools", "incr", "incr-reverify.sh")),
            "audit_tool": os.path.isdir(os.path.join(self.fv_root, "tools", "audit")),
            "fvwork_tool": os.path.isdir(os.path.join(self.fv_root, "tools", "fvwork")),
            "frontier_tool": os.path.isfile(os.path.join(self.fv_root, "check", "frontier", "check-frontier.sh")),
            "dupfind_tool": os.path.isfile(os.path.join(self.fv_root, "tools", "dupfind", "dupfind.py")),
            "guard_tool": os.path.isfile(os.path.join(self.fv_root, "tools", "guard", "fvguard.py")),
            "subcontract_tool": os.path.isdir(os.path.join(self.fv_root, "tools", "subcontract")),
            "dupfind_indexes": self.dupfind_indexes,
            "fvserve": {"configured": bool(self.fvserve_state), "reachable": False, "psets": []},
            "fvapi": {"configured": bool(self.fvapi_url), "url": self.fvapi_url},
            "fvwork": {"configured": bool(self.fvwork_state), "state": self.fvwork_state},
        }
        if self.fvserve_state:
            try:
                st = fvserve.request(self.fvserve_state, {"op": "stats"}, timeout=3.0)
                code = st.get("code")
                stale = st.get("stale")
                backends["fvserve"] = {
                    "configured": True,
                    "reachable": True,
                    "psets": st.get("psets", []),
                    "uptime_s": st.get("uptime_s"),
                    "pending": st.get("pending", 0),
                    "inflight": st.get("inflight", 0),
                    "verdicts": st.get("verdicts", {}),
                    "code": code,
                    "stale": stale,
                    "restart_recommended": (not isinstance(code, dict)) or bool(stale),
                }
            except Exception as e:  # noqa: BLE001
                backends["fvserve"]["error"] = fv_schema.sanitize_single_line(e, 160)
        out = {
            "server": SERVER_NAME,
            "version": SERVER_VERSION,
            "protocol_version": self.protocol_version,
            "api_version": fv_schema.API_VERSION,
            "fv_root": self.fv_root,
            "default_pset": self.default_pset,
            "allowed_roots": self.allowed_roots,
            "registered_challenges": {
                cid: {"challenge_sha256": r["challenge_sha256"], "comparator_sha256": r["comparator_sha256"]}
                for cid, r in self.challenges.items()
            },
            "backends": backends,
            "uptime_s": round(time.time() - self.stats["started"], 2),
            "calls": self.stats["calls"],
            "elapsed_ms": round((time.time() - t0) * 1000.0, 2),
        }
        return out, False

    def tool_fv_doctor(self, params):
        t0 = time.time()
        proj = params.get("project_dir")
        dtmp = None
        if proj:
            proj, err = self.check_path(proj, must_exist=True, expect_dir=True)
            if err:
                return {"error": f"project_dir: {err}"}, True
            # the doctor reads lean-toolchain and samples sources on the host: it gets a private copy
            dtmp = tempfile.mkdtemp(prefix="fv-mcp-doctor.")
            priv, err = self._private_tree(proj, os.path.join(dtmp, "proj"))
            if err:
                shutil.rmtree(dtmp, ignore_errors=True)
                return {"error": f"project_dir: {err}"}, True
        try:
            doctor = run_host_doctor(self.fv_root, os.path.join(dtmp, "proj") if dtmp else None)
        finally:
            if dtmp:
                shutil.rmtree(dtmp, ignore_errors=True)
        if dtmp:
            doctor = json.loads(json.dumps(doctor).replace(json.dumps(os.path.join(dtmp, "proj"))[1:-1], json.dumps(proj)[1:-1]))
        if self.fvserve_state:
            try:
                st = fvserve.request(self.fvserve_state, {"op": "stats"}, timeout=2.0)
                code = st.get("code")
                stale = st.get("stale")
                restart_rec = (not isinstance(code, dict)) or bool(stale)
                doctor["fvserve_backend"] = {
                    "reachable": True,
                    "code": code,
                    "stale": stale,
                    "restart_recommended": restart_rec,
                }
                if restart_rec:
                    msg = (f"fvserve backend has stale code on disk ({stale}) — restart recommended"
                           if isinstance(code, dict)
                           else "fvserve backend predates code/stale reporting (76f19410) — restart recommended")
                    doctor.setdefault("warnings", []).append(msg)
            except Exception as e:  # noqa: BLE001
                doctor["fvserve_backend"] = {"reachable": False, "error": fv_schema.sanitize_single_line(e, 160)}
        doctor["elapsed_ms"] = round((time.time() - t0) * 1000.0, 2)
        return doctor, False

    def _load_attempt_source(self, params):
        src = params.get("source")
        sfile = params.get("source_file")
        if src is not None and sfile is not None:
            return None, None, "provide either 'source' or 'source_file', not both"
        if sfile is not None:
            rp, err = self.check_path(sfile, must_exist=True, expect_dir=False)
            if err:
                return None, None, f"source_file: {err}"
            try:   # read without following any symlink (also none swapped in after check_path); name re-checked
                fd = open_nofollow_under(rp, self.allowed_roots, want_dir=False, single_link=True)
            except ClientPathError as e:
                return None, None, f"source_file: {e}"
            try:
                if os.fstat(fd).st_nlink != 1:   # uniform policy: a single-link regular file
                    return None, None, "source_file: hard-linked file refused"
                if os.fstat(fd).st_size > self.max_source_bytes:
                    return None, None, f"source_file exceeds {self.max_source_bytes} bytes"
                data = b""
                while len(data) <= self.max_source_bytes:
                    b = os.read(fd, 1 << 20)
                    if not b:
                        break
                    data += b
            finally:
                os.close(fd)
            if len(data) > self.max_source_bytes:
                return None, None, f"source_file exceeds {self.max_source_bytes} bytes"
            return data.decode("utf-8", errors="replace"), rp, None
        if not isinstance(src, str) or not src.strip():
            return None, None, "missing non-empty 'source' or 'source_file'"
        if len(src.encode("utf-8", "replace")) > self.max_source_bytes:
            return None, None, f"source exceeds {self.max_source_bytes} bytes"
        return src, None, None

    def tool_fv_verify_attempt(self, params):
        t0 = time.time()
        pset = params.get("pset") or self.default_pset
        thm = params.get("theorem")
        if not pset or not isinstance(pset, str):
            return fv_schema.from_error("attempt", "missing pset (and no --default-pset set)", 0.0), True
        if not fv_schema.validate_theorem_name(thm, allow_dotted=False):
            # an unresolvable / unsupported theorem name was never judged: NO-VERDICT (exit 2), never
            # REJECTED with sound trust
            return fv_schema.make_envelope(
                mode="attempt", verdict="NO-VERDICT", trust="none",
                verdict_basis="no verdict: invalid or unsupported theorem name (the attempt was not judged)", total_s=0.0,
                reason="bad theorem name", target={"pset": pset, "theorem": thm},
                diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", "bad theorem name"),
            ), False
        src, sfile, err = self._load_attempt_source(params)
        if err:
            return fv_schema.from_error("attempt", err, 0.0, target={"pset": pset, "theorem": thm}), True
        tmo = min(float(params.get("timeout") or self.default_timeout), self.default_timeout)
        try:
            raw = self.call_fvserve({"op": "verify", "pset": pset, "theorem": thm, "source": src}, timeout=tmo)
        except Exception as e:  # noqa: BLE001
            return fv_schema.make_envelope(
                mode="attempt", verdict="NO-VERDICT", trust="sound",
                verdict_basis=f"fvserve unavailable or timed out: {fv_schema.sanitize_single_line(e, 200)}",
                total_s=time.time() - t0, reason=fv_schema.sanitize_single_line(e, 200),
                target={"pset": pset, "theorem": thm},
                diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", str(e)),
            ), False
        wall = time.time() - t0
        if not isinstance(raw, dict):   # a list / null reply is no result: an ERROR envelope, never a crash
            return fv_schema.from_error("attempt", f"the verification backend returned no result object ({type(raw).__name__}); "
                                        "no verdict", wall, target={"pset": pset, "theorem": thm}), False
        if isinstance(raw, dict) and raw.get("api_version") == fv_schema.API_VERSION:
            # the backend's envelope is published only if it is one complete, consistent v1
            # SINGLE-attempt envelope (as `fv attempt --http`); anything else is a fresh ERROR for this attempt
            try:
                bad = fv_schema.validate_v1(raw)
            except Exception as e:  # noqa: BLE001
                bad = [f"validator error: {type(e).__name__}: {e}"]
            if not bad and raw.get("mode") != "attempt":
                bad = [f"mode {raw.get('mode')!r} is not a single-attempt result"]
            if bad:
                return fv_schema.from_error("attempt", "the verification backend returned no valid single-attempt result envelope "
                                            f"({'; '.join(str(b) for b in bad[:3])}); no verdict", wall,
                                            target={"pset": pset, "theorem": thm}), False
            raw["timing"]["mcp_wall_s"] = round(wall, 4)
            return raw, False
        overhead_ms = round(max(0.0, (wall - float(raw.get("total_s") or 0.0)) * 1000.0), 3)
        env = fv_schema.from_fvserve_result(raw, pset=pset, theorem=thm, source_file=sfile,
                                            overhead_ms=overhead_ms, include_raw=False)
        env["timing"]["mcp_wall_s"] = round(wall, 4)
        return env, False

    def tool_fv_verify_batch(self, params):
        t0 = time.time()
        cands = params.get("candidates")
        if not isinstance(cands, list) or not cands:
            return {"error": "candidates must be a non-empty array"}, True
        if len(cands) > self.max_batch:
            return {"error": f"candidates length {len(cands)} exceeds max_batch {self.max_batch}"}, True
        top_pset = params.get("pset") or self.default_pset
        tmo = min(float(params.get("timeout") or self.default_timeout), self.default_timeout)

        def run_one(idx, c):
            p = dict(c)
            if not p.get("pset") and top_pset:
                p["pset"] = top_pset
            p["timeout"] = tmo
            res, _is_err = self.tool_fv_verify_attempt(p)
            return {"id": c.get("id", f"cand_{idx}"), "index": idx, "result": res}

        with cf.ThreadPoolExecutor(max_workers=min(len(cands), 32)) as ex:
            futs = [ex.submit(run_one, i, c) for i, c in enumerate(cands)]
            items = [f.result() for f in futs]
        accepted_indices = [it["index"] for it in items if it["result"].get("accepted") is True]
        wall = round(time.time() - t0, 4)
        return {
            "api_version": fv_schema.API_VERSION,
            "mode": "batch_attempt",
            "trust": "sound",
            "count": len(items),
            "accepted_count": len(accepted_indices),
            "best_accepted_index": accepted_indices[0] if accepted_indices else None,
            "wall_s": wall,
            "results": items,
        }, False

    def _resolve_server_pins(self, pins_sel, lowmem=False):
        """Resolve server-pinned trusted pins profile ('436' or '437') under boundary B4 (no caller paths)."""
        if pins_sel is None:
            return None, None
        sub = ("check", "lowmem") if lowmem else ("check", "sound")
        if pins_sel == "436":
            pins_p = os.path.join(self.fv_root, *sub, "pins.env")
        elif pins_sel == "437":
            pins_p = os.path.join(self.fv_root, *sub, "pins-437.env")
        else:
            return None, f"invalid pins profile {pins_sel!r}: only server-pinned '436' or '437' allowed (B4)"
        if not os.path.isfile(pins_p):
            return None, f"pins file not installed: {pins_p}"
        return pins_p, None

    def tool_fv_verify_project(self, params):
        """incremental mode is experimental and not offered here: a request with incr_base
        (optimistic / closure_only belong to it) is verified by the full path, exactly as without it, and says so"""
        if isinstance(params, dict) and params.get("incr_base"):
            env, is_err = self._tool_fv_verify_project({k: v for k, v in params.items()
                                                        if k not in ("incr_base", "optimistic", "closure_only")})
            if isinstance(env, dict) and "verdict" in env:
                note = ("incremental mode (incr_base) is experimental in v0.1 and was not used: the project was verified by "
                        "the full path")
                env["verdict_basis"] = f"{env.get('verdict_basis') or ''} [{note}]".strip()
                if isinstance(env.get("warnings"), list):
                    env["warnings"].append(note)
                else:
                    env["warnings"] = [note]
            return env, is_err
        return self._tool_fv_verify_project(params)

    def _tool_fv_verify_project(self, params):
        t0 = time.time()
        proj, err = self.check_path(params.get("project_dir"), must_exist=True, expect_dir=True)
        if err:
            return fv_schema.from_error("project", f"project_dir: {err}", 0.0), True
        pins_p, perr = self._resolve_server_pins(params.get("pins"))
        if perr:
            return fv_schema.from_error("project", perr, 0.0), True
        pkgs, err = self._operator_packages(params.get("packages_dir"))   # workspace of the service owner only
        if err:
            return fv_schema.from_error("project", err, 0.0), True
        threads = int(params.get("threads") or self.default_threads)
        tmo = min(float(params.get("timeout") or max(self.default_timeout, 600.0)), 3600.0)
        incr_base = params.get("incr_base")
        if incr_base and pins_p:
            return fv_schema.from_error("project_incremental", "pins is not yet supported with incr_base; omit incr_base", 0.0), True
        if incr_base and not getattr(self.args, "allow_incr_base", False):
            # an incremental base is trusted input (an earlier run's work tree, build plan, planner binary and
            # plugin, its result.json naming toolchains): never taken from a client unless the service owner opts in
            return fv_schema.from_error("project_incremental", "incr_base is disabled on this server (trusted input; start "
                                        "fastverify-mcp with --allow-incr-base to accept client incremental bases)", 0.0), True
        out_dir = tempfile.mkdtemp(prefix="fv-mcp-proj.")
        os.chmod(out_dir, 0o700)
        try:
            crec, cerr = self._resolve_pinned_challenge(params, out_dir, for_export_check=False)
            if cerr:
                return fv_schema.from_error("project", cerr, time.time() - t0), True
            chal = crec["dir"]
            pin = crec["challenge_sha256"]
            # the project goes to bin/fastverify / incr-reverify as a private no-follow copy (sources; .lake/.git
            # skipped), never as the client path
            proj_client = proj
            proj, perr2 = self._private_tree(proj_client, os.path.join(out_dir, "project"))
            if perr2:
                return fv_schema.from_error("project", f"project_dir: {perr2}", time.time() - t0), True
            # bin/fastverify runs lib/autotune.py on the host (sound-auto) and Lake reads
            # the lakefile: no lakefile path of the private copies may leave them
            for what, d in (("project_dir", proj), ("challenge_dir", chal)):
                lerr = lake_config_confined(d)
                if lerr:
                    return fv_schema.from_error("project", f"{what} refused: {lerr}", time.time() - t0), True
            if incr_base:
                base, err = self.check_path(incr_base, must_exist=True, expect_dir=True)
                if err:
                    return fv_schema.from_error("project_incremental", f"incr_base: {err}", 0.0), True
                if not pin:
                    return fv_schema.from_error("project_incremental", "challenge_sha256 is required for incremental mode", 0.0), True
                # (scheme 2) incr-reverify gets the CALLER's comparator pin, verified against the
                # private copy, never one computed here; without it the incremental call is refused
                cpin = params.get("comparator_sha256")
                if not fv_schema.validate_sha256(cpin) or cpin != crec.get("comparator_sha256"):
                    return fv_schema.from_error("project_incremental", "comparator_sha256 (the caller's verified 64-hex pin of "
                                                "comparator.json) is required for incremental mode; it is forwarded to "
                                                "incr-reverify, never computed by the server", 0.0), True
                incr_sh = os.path.join(self.fv_root, "tools", "incr", "incr-reverify.sh")
                run_incr = os.path.join(out_dir, "incr")
                cmd = [incr_sh, base, proj, chal, run_incr, "--challenge-sha256", pin, "--comparator-sha256", cpin,
                       "--threads", str(threads)]
                if pkgs:
                    cmd += ["--packages", pkgs]
                if params.get("optimistic", True):
                    cmd.append("--optimistic")
                if params.get("closure_only"):
                    cmd.append("--closure-only")
                try:
                    proc = run_subprocess_guarded(self.fv_root, cmd, timeout=tmo)
                except subprocess.TimeoutExpired:
                    return fv_schema.make_envelope(
                        mode="project_incremental", verdict="NO-VERDICT", trust="sound",
                        verdict_basis=f"incremental verification timed out after {tmo:.1f}s",
                        total_s=time.time() - t0, reason=f"timeout ({tmo:.1f}s)",
                        target={"project": proj_client, "challenge": chal, "challenge_sha256": pin},
                    ), False
                summ_p = os.path.join(run_incr, "summary.json")
                if os.path.isfile(summ_p):
                    try:
                        summ = json.load(open(summ_p, encoding="utf-8"))
                    except (OSError, ValueError) as e:
                        return fv_schema.from_error("project_incremental", f"malformed incr summary.json: {e}", time.time() - t0), False
                    env_i = fv_schema.from_incr_summary(summ, proj_client, chal, pin, total_s=time.time() - t0, include_raw=False)
                    return fv_schema.enforce_process_exit(env_i, proc.returncode, "project_incremental", time.time() - t0), False
                return fv_schema.from_error("project_incremental",
                                            f"incr-reverify exited {proc.returncode}: {(proc.stderr or proc.stdout)[-300:]}",
                                            time.time() - t0), False

            preset = params.get("preset") or "sound-auto"
            if not self.allow_unsound_presets and preset not in SOUND_MCP_PRESETS:
                return fv_schema.from_error(
                    "project",
                    f"unsound preset {preset!r} is disallowed on fastverify-mcp (allowed: {list(SOUND_MCP_PRESETS)}; B4)",
                    time.time() - t0,
                ), True
            fv_bin = os.path.join(self.fv_root, "bin", "fastverify")
            run_out = os.path.join(out_dir, "out")
            cmd = [fv_bin, proj, chal, run_out, "--preset", preset, "--threads", str(threads)]
            if params.get("no_integrity_cache"):
                cmd.append("--no-integrity-cache")
            if pins_p:
                cmd += ["--pins", pins_p]
            if pin:
                cmd += ["--challenge-sha256", pin]
            if crec.get("comparator_sha256"):   # forwarded whenever verified (a source-only challenge too)
                cmd += ["--comparator-sha256", crec["comparator_sha256"]]
            if pkgs:
                cmd += ["--packages", pkgs]
            if params.get("build_option"):
                cmd += ["--build", params["build_option"]]
            if params.get("confirm_reject"):
                cmd.append("--confirm-reject")
            mf = params.get("modulo_frontier")
            if mf:
                if mf != "auto":
                    mf, err = self.check_path(mf, must_exist=True, expect_dir=False)
                    if err:
                        return fv_schema.from_error("frontier", f"modulo_frontier: {err}", 0.0), True
                    mf, err = self._private_file(mf, os.path.join(out_dir, "modulo_frontier.txt"))
                    if err:
                        return fv_schema.from_error("frontier", f"modulo_frontier: {err}", 0.0), True
                cmd += ["--modulo-frontier", mf]
            fp = params.get("frontier_pin")
            if fp:
                fp, err = self.check_path(fp, must_exist=True, expect_dir=True)
                if err:
                    return fv_schema.from_error("frontier", f"frontier_pin: {err}", 0.0), True
                fp, err = self._private_tree(fp, os.path.join(out_dir, "frontier_pin"))
                if err:
                    return fv_schema.from_error("frontier", f"frontier_pin: {err}", 0.0), True
                cmd += ["--frontier-pin", fp]
            fb = params.get("frontier_base")
            if fb:
                fb, err = self.check_path(fb, must_exist=True, expect_dir=False)
                if err:
                    return fv_schema.from_error("frontier", f"frontier_base: {err}", 0.0), True
                fb, err = self._private_file(fb, os.path.join(out_dir, "frontier_base.json"))
                if err:
                    return fv_schema.from_error("frontier", f"frontier_base: {err}", 0.0), True
                cmd += ["--frontier-base", fb]
            try:
                proc = run_subprocess_guarded(self.fv_root, cmd, timeout=tmo)
            except subprocess.TimeoutExpired:
                return fv_schema.make_envelope(
                    mode="project", verdict="NO-VERDICT", trust="sound" if preset.startswith("sound") else "none",
                    verdict_basis=f"fastverify timed out after {tmo:.1f}s",
                    total_s=time.time() - t0, reason=f"timeout ({tmo:.1f}s)",
                    target={"project": proj_client, "challenge": chal, "challenge_sha256": pin},
                ), False
            res_p = os.path.join(run_out, "result.json")
            if os.path.isfile(res_p):
                try:
                    res = json.load(open(res_p, encoding="utf-8"))
                except (OSError, ValueError) as e:
                    return fv_schema.from_error("project", f"malformed result.json: {e}", time.time() - t0), False
                env_p = fv_schema.from_fastverify_result(res, total_s=time.time() - t0, project_dir=proj_client, include_raw=False)
                return fv_schema.enforce_process_exit(env_p, proc.returncode, "project", time.time() - t0), False
            return fv_schema.from_error("project",
                                        f"fastverify exited {proc.returncode}: {(proc.stderr or proc.stdout)[-300:]}",
                                        time.time() - t0), False
        finally:
            shutil.rmtree(out_dir, ignore_errors=True)

    def tool_fv_check_export(self, params):
        t0 = time.time()
        exp, err = self.check_path(params.get("export_file"), must_exist=True, expect_dir=False)
        if err:
            return fv_schema.from_error("export_in", f"export_file: {err}", 0.0), True
        use_frontier = bool(params.get("frontier"))
        if use_frontier and params.get("notary"):   # two different judges: never a silent choice
            return fv_schema.from_error("frontier", "frontier and notary are different judges: request one of them", 0.0), True
        allowed_f = params.get("allowed_frontier_file")
        if allowed_f:
            allowed_f, err = self.check_path(allowed_f, must_exist=True, expect_dir=False)
            if err:
                return fv_schema.from_error("frontier", f"allowed_frontier_file: {err}", 0.0), True
        pinned_f = params.get("frontier_pinned_dir")
        if pinned_f:
            pinned_f, err = self.check_path(pinned_f, must_exist=True, expect_dir=True)
            if err:
                return fv_schema.from_error("frontier", f"frontier_pinned_dir: {err}", 0.0), True
        base_f = params.get("frontier_base")
        if base_f:
            base_f, err = self.check_path(base_f, must_exist=True, expect_dir=False)
            if err:
                return fv_schema.from_error("frontier", f"frontier_base: {err}", 0.0), True
        threads = int(params.get("threads") or self.default_threads)
        tmo = int(params.get("timeout") or min(int(self.default_timeout), 1800))
        tmpd = tempfile.mkdtemp(prefix="fv-mcp-chk.")
        os.chmod(tmpd, 0o700)
        try:
            crec, cerr = self._resolve_pinned_challenge(params, tmpd, for_export_check=True)
            if cerr:
                return fv_schema.from_error("export_in", cerr, time.time() - t0, target={"export_path": exp}), True
            chx = crec["challenge_export"]
            cfg = crec["comparator_json"]
            pin = crec["challenge_sha256"]
            # Always judge a private copy of the export (also for a standalone export > 4 GiB)
            priv_exp = os.path.join(tmpd, "solution.export")
            try:   # no symlink followed (also none swapped in after check_path)
                copy_client_file(exp, priv_exp, self.allowed_roots)
                if allowed_f:
                    copy_client_file(allowed_f, os.path.join(tmpd, "allowed_frontier.txt"), self.allowed_roots)
                    allowed_f = os.path.join(tmpd, "allowed_frontier.txt")
                if base_f:
                    copy_client_file(base_f, os.path.join(tmpd, "frontier_base.json"), self.allowed_roots)
                    base_f = os.path.join(tmpd, "frontier_base.json")
                if pinned_f:
                    pinned_f, perr = self._private_tree(pinned_f, os.path.join(tmpd, "frontier_pinned"))
                    if perr:
                        raise ClientPathError(perr)
            except (ClientPathError, OSError) as e:
                return fv_schema.from_error("export_in", f"failed to copy export / frontier files privately: {e}", time.time() - t0), False
            jsf = os.path.join(tmpd, "check.json")
            logf = os.path.join(tmpd, "check.log")
            use_lm = bool(params.get("low_mem") and not use_frontier and not params.get("notary"))
            sel = params.get("pins")
            rel = release_pins_shorthand(self.fv_root, chx)
            if sel is None and not params.get("notary"):   # the challenge release's own judge, as `fv check`
                sel = rel
            pins_p, perr = self._resolve_server_pins(sel, lowmem=use_lm)
            if perr:
                return fv_schema.from_error("frontier" if use_frontier else "export_in", perr, time.time() - t0), True
            xv_rc, xv_reason = run_xversion_gate(self.fv_root, chx, cfg)
            if xv_rc == 1:
                trust_lbl = "notary" if params.get("notary") else "sound"
                return fv_schema.make_envelope(
                    mode="frontier" if use_frontier else "export_in",
                    verdict="REJECTED",
                    trust=trust_lbl,
                    verdict_basis=f"{trust_lbl.upper()}: rejected by challenge release comparator rule (check/xversion): {xv_reason}",
                    total_s=time.time() - t0,
                    reason=xv_reason,
                    target={"export_path": exp, "challenge_sha256": pin},
                    diagnostics=fv_schema.classify_verdict_diagnostic("REJECTED", xv_reason),
                ), False
            elif xv_rc != 0:
                return fv_schema.from_error("frontier" if use_frontier else "export_in",
                                            f"cross-version gate: {xv_reason}", time.time() - t0,
                                            target={"export_path": exp}), False
            if sel is None and params.get("notary") and not use_frontier and rel is not None:
                # one release rule: after the release check, notary has no judge for this release
                return fv_schema.from_error("export_in", f"notary has no judge for this challenge's release (pins-{rel}.env is "
                                            "its trusted check) in v0.1; check without notary", time.time() - t0), True
            if params.get("notary") and not getattr(self, "experimental", False):
                # the notary judge is EXPERIMENTAL in v0.1: only with the service owner's opt-in
                return fv_schema.from_error("export_in", "notary is EXPERIMENTAL in fastverify v0.1 (not release grade): refused - "
                                            "the service owner starts fastverify-mcp with --experimental (or FV_EXPERIMENTAL=1) to "
                                            "enable it", time.time() - t0), True
            if not params.get("notary") and (None if sel in (None, "436") else sel) != rel:
                # one release rule, as `fv check` / bin/fastverify: an explicit pins
                # profile is used only when it IS the challenge release's own judge
                return fv_schema.from_error("frontier" if use_frontier else "export_in",
                                            f"pins {params.get('pins')!r} is not this challenge release's own trusted check "
                                            f"({'pins-' + rel + '.env' if rel else 'pins.env'}): another release's judge is "
                                            "never used; omit pins", time.time() - t0), True
            if use_frontier:
                chk_sh = os.path.join(self.fv_root, "check", "frontier", "check-frontier.sh")
                cmd = [chk_sh, priv_exp, chx, cfg, "--threads", str(threads), "--timeout", str(tmo),
                       "--json", jsf, "--log", logf]
                if allowed_f:
                    cmd += ["--allowed", allowed_f]
                if pinned_f:
                    cmd += ["--pinned", pinned_f]
                if base_f:
                    cmd += ["--base", base_f]
                if pins_p:
                    cmd += ["--pins", pins_p]
            else:
                if params.get("notary"):
                    if pins_p:
                        return fv_schema.from_error("export_in", "pins cannot be combined with notary", time.time() - t0), True
                    chk_sh = os.path.join(self.fv_root, "check", "notary", "check-notary.sh")
                    if not os.path.isfile(chk_sh):
                        return fv_schema.from_error("export_in", "check/notary/check-notary.sh not installed", time.time() - t0), True
                    cmd = [chk_sh, priv_exp, chx, cfg, "--threads", str(threads), "--timeout", str(tmo),
                           "--json", jsf, "--log", logf]
                elif params.get("low_mem"):
                    chk_sh = os.path.join(self.fv_root, "check", "lowmem", "check-sound-lowmem.sh")
                    if not os.path.isfile(chk_sh):
                        return fv_schema.from_error("export_in", "check/lowmem/check-sound-lowmem.sh not installed", time.time() - t0), True
                    cmd = [chk_sh, priv_exp, chx, cfg, "--threads", str(threads), "--timeout", str(tmo),
                           "--json", jsf, "--log", logf]
                    if pins_p:
                        cmd += ["--pins", pins_p]
                else:
                    chk_sh = os.path.join(self.fv_root, "check", "sound", "check-sound.sh")
                    cmd = [chk_sh, priv_exp, chx, cfg, "--threads", str(threads), "--timeout", str(tmo),
                           "--json", jsf, "--log", logf]
                    if pins_p:
                        cmd += ["--pins", pins_p]
            try:
                if "--challenge-sha256)" in open(chk_sh, encoding="utf-8", errors="replace").read():
                    cfg_sha = crec.get("comparator_sha256") or fv_schema.sha256_file(cfg)
                    cmd += ["--challenge-sha256", pin, "--comparator-sha256", cfg_sha]
            except OSError:
                pass
            proc = run_subprocess_guarded(self.fv_root, cmd, timeout=tmo + 60)
            chk_mode = "frontier" if use_frontier else "export_in"
            if os.path.isfile(jsf):
                try:
                    res = json.load(open(jsf, encoding="utf-8"))
                except (OSError, ValueError) as e:
                    return fv_schema.from_error(chk_mode, f"malformed check.json: {e}", time.time() - t0), False
                if use_frontier:
                    env_c = fv_schema.from_check_frontier_result(res, exp, pin, total_s=time.time() - t0, include_raw=False)
                else:
                    env_c = fv_schema.from_check_sound_result(res, exp, pin, total_s=time.time() - t0, include_raw=False)
                return fv_schema.enforce_process_exit(env_c, proc.returncode, chk_mode, time.time() - t0), False
            return fv_schema.from_error(chk_mode,
                                        f"checker exited {proc.returncode}: {(proc.stderr or proc.stdout)[-300:]}",
                                        time.time() - t0), False
        except subprocess.TimeoutExpired:
            return fv_schema.make_envelope(
                mode="export_in", verdict="NO-VERDICT", trust="sound",
                verdict_basis=f"check-sound timed out after {tmo}s", total_s=time.time() - t0,
                reason=f"timeout ({tmo}s)", target={"export_path": exp, "challenge_sha256": pin},
            ), False
        finally:
            shutil.rmtree(tmpd, ignore_errors=True)

    def _operator_packages(self, given):
        """a Lake packages workspace is a TRUSTED input (lib/manifest.py binds its checkouts into the build
        sandbox): only the service owner's --packages may be used; a client-supplied packages_dir is accepted only if it IS that
        workspace. Returns (path or None, error or None)."""
        if not given:
            return self.default_packages, None
        rp, err = self.check_path(given, must_exist=True, expect_dir=True)
        if err:
            return None, f"packages_dir: {err}"
        if not self.default_packages or os.path.realpath(rp) != os.path.realpath(self.default_packages):
            return None, ("packages_dir: only the workspace configured by the service owner (fastverify-mcp --packages) may be used: a "
                          "packages workspace is trusted input")
        return self.default_packages, None

    def _private_file(self, path, dst):
        """a private copy of a client file (no symlink followed): (dst, None) or (None, error)"""
        try:
            copy_client_file(path, dst, self.allowed_roots)
            return dst, None
        except (ClientPathError, OSError) as e:
            return None, f"refused: {e}"

    def _private_tree(self, path, dst, file_filter=None, max_entries=CLIENT_TREE_MAX_ENTRIES):
        """a private copy of a client directory (no symlink / special file / hard link): (dst, None) or error"""
        try:
            fd = open_nofollow_under(path, self.allowed_roots, want_dir=True)
            try:
                copy_client_tree(fd, dst, file_filter=file_filter, max_entries=max_entries)
            finally:
                os.close(fd)
            return dst, None
        except (ClientPathError, OSError) as e:
            shutil.rmtree(dst, ignore_errors=True)
            return None, f"refused: {e}"

    def _refuse_client_tree(self, path, single_link=True):
        """None if the client directory (opened without following links) contains no symlink / special file (and,
        single_link, no hard-linked file: its content would be copied / read like the server's own), else the refusal
        message"""
        try:
            fd = open_nofollow_under(path, self.allowed_roots, want_dir=True)
        except ClientPathError as e:
            return str(e)
        try:
            scan_client_tree(fd, single_link=single_link)
        except (ClientPathError, OSError) as e:
            return f"refused: {e}"
        finally:
            os.close(fd)
        return None

    def tool_fv_audit_challenge(self, params):
        t0 = time.time()
        chal, err = self.check_path(params.get("challenge_dir"), must_exist=True, expect_dir=True)
        if err:
            return {"error": f"challenge_dir: {err}"}, True
        pin = params.get("challenge_sha256")
        if pin is not None and not fv_schema.validate_sha256(pin):
            return {"error": "challenge_sha256 must be 64 lowercase hex chars"}, True
        pkgs, err = self._operator_packages(params.get("packages_dir"))
        if err:
            return {"error": err}, True
        # the audit reads, copies and probes files named by the challenge's own comparator.json: it runs on a
        # private no-follow copy (no symlink / special file / hard link), never on the client directory
        atmp = tempfile.mkdtemp(prefix="fv-mcp-audit.")
        try:
            priv, err = self._private_tree(chal, os.path.join(atmp, "challenge"))
            if err:
                return {"error": f"challenge_dir: {err}"}, True
            res = audit_challenge_dir(
                self.fv_root, priv, expected_sha256=pin, input_private=True,
                probe=bool(params.get("probe")),
                packages_dir=pkgs,
                conjecture_mode=bool(params.get("conjecture_mode")),
            )
            res = json.loads(json.dumps(res).replace(json.dumps(priv)[1:-1], json.dumps(chal)[1:-1]))
        finally:
            shutil.rmtree(atmp, ignore_errors=True)
        res["elapsed_ms"] = round((time.time() - t0) * 1000.0, 2)
        return res, False

    def tool_fv_init_challenge(self, params):
        t0 = time.time()
        chal, err = self.check_path(params.get("challenge_dir"), must_exist=True, expect_dir=True)
        if err:
            return {"error": f"challenge_dir: {err}"}, True
        err = self._refuse_client_tree(chal)
        if err:
            return {"error": f"challenge_dir: {err}"}, True
        out_dir, err = self.check_path(params.get("out_dir"), must_exist=False)
        if err:
            return {"error": f"out_dir: {err}"}, True
        pkgs, err = self._operator_packages(params.get("packages_dir"))   # workspace of the service owner only
        if err:
            return {"error": err}, True
        threads = int(params.get("threads") or self.default_threads)
        tmo = min(float(params.get("timeout") or 600.0), 3600.0)
        res = init_official_challenge(self.fv_root, chal, out_dir, packages_dir=pkgs, threads=threads, timeout=tmo,
                                      roots=self.allowed_roots)
        res["elapsed_s"] = round(time.time() - t0, 3)
        return res, (not res.get("ok"))

    def tool_fv_parse_diagnostics(self, params):
        text = params.get("compiler_output") or ""
        if not isinstance(text, str) or len(text) > self.max_source_bytes:
            return {"error": "compiler_output must be a string within size limit"}, True
        dfile = params.get("default_file")
        diags = fv_schema.parse_lean_diagnostics(text, default_file=dfile)
        env = fv_schema.make_envelope(
            mode="attempt",
            verdict="REJECTED" if any(d["severity"] == "error" for d in diags) else "PENDING",
            trust="none",
            verdict_basis="parsed compiler diagnostics only (not a sound verdict)",
            total_s=0.0,
            diagnostics=diags,
        )
        return {
            "count": len(diags),
            "diagnostics": diags,
            "lsp": fv_schema.to_lsp_diagnostics(env),
            "sarif": fv_schema.to_sarif_210(env),
        }, False

    def tool_fv_triage_sublemma(self, params):
        if not getattr(self, "experimental", False):   # a label is not enough: MCP clients do not read it
            return {"error": "fv_triage_sublemma is EXPERIMENTAL in fastverify v0.1 (advisory sub-lemma triage, not release "
                             "grade): refused - the service owner starts fastverify-mcp with --experimental (or FV_EXPERIMENTAL=1) "
                             "to enable it", "experimental": True}, True
        src, _sfile, err = self._load_attempt_source(params)
        if err:
            return {"error": err}, True
        repo = params.get("repo_dir")
        rtmp = None
        if repo:
            repo, err = self.check_path(repo, must_exist=True, expect_dir=True)
            if err:
                return {"error": f"repo_dir: {err}"}, True
            # the duplicate scan reads the repo on the host: it gets a private copy of the repo's .lean files
            rtmp = tempfile.mkdtemp(prefix="fv-mcp-triage.")
            priv, err = self._private_tree(repo, os.path.join(rtmp, "repo"), file_filter=lambda n: n.endswith(".lean"))
            if err:
                shutil.rmtree(rtmp, ignore_errors=True)
                return {"error": f"repo_dir: {err}"}, True
            repo = priv
        try:
            return self._triage_with(params, src, repo)
        finally:
            if rtmp:
                shutil.rmtree(rtmp, ignore_errors=True)

    def _triage_with(self, params, src, repo):
        tc = self.args.toolchain
        ws = self.default_packages or _repo_packages()
        if not ws and not params.get("static_only"):   # the Lean probes need the trusted workspace; static checks do not
            return {"error": "no trusted package workspace for the Lean probes: start fastverify-mcp with --packages DIR "
                             "(or pass static_only)"}, True
        snap_dir = (
            (os.path.join(self.fvserve_state, "snap")
             if self.fvserve_state and os.path.isdir(os.path.join(self.fvserve_state, "snap")) else None)
            or self.dupfind_snapshot
        )
        tmo = min(float(params.get("timeout") or 20.0), 120.0)
        res = triage.triage_sublemma(
            src,
            decl_name=params.get("theorem"),
            tc=tc,
            ws=ws,
            snap_dir=snap_dir,
            repo_dir=repo,
            run_lean_probes=(not bool(params.get("static_only"))),
            timeout=tmo,
        )
        return res, False

    def tool_fv_mint_subchallenges(self, params):
        proj, err = self.check_path(params.get("project_dir"), must_exist=True, expect_dir=True)
        if err:
            return {"error": f"project_dir: {err}"}, True
        out_dir, err = self.check_path(params.get("out_dir"), must_exist=False)
        if err:
            return {"error": f"out_dir: {err}"}, True
        pkgs, err = self._operator_packages(params.get("packages_dir"))   # workspace of the service owner only
        if err:
            return {"error": err}, True
        thms = params.get("theorems") or []
        for t in thms:
            if not fv_schema.validate_theorem_name(t, allow_dotted=False):
                return {"error": f"invalid theorem name: {t!r}"}, True
        if params.get("module") is not None and module_name_parts(params.get("module")) is None:
            return {"error": f"invalid module name: {params.get('module')!r} (dotted Lean identifiers only)"}, True
        # bin/fv mint never sees a client path: the project is copied privately without following
        # anything (symlink / special file / hard link: refused), mint writes into a private directory, and its outputs
        # are then created inside the client's out_dir without following links (a planted symlink is replaced)
        err = self._refuse_client_tree(proj)
        if err:
            return {"error": f"project_dir: {err}"}, True
        mint_tmp = tempfile.mkdtemp(prefix="fv-mcp-mint.")
        try:
            return self._mint_private(params, proj, out_dir, pkgs, thms, mint_tmp)
        finally:
            shutil.rmtree(mint_tmp, ignore_errors=True)

    def _mint_private(self, params, proj, out_dir, pkgs, thms, mint_tmp):
        priv_proj, priv_out = os.path.join(mint_tmp, "proj"), os.path.join(mint_tmp, "out")
        try:
            pfd = open_nofollow_under(proj, self.allowed_roots, want_dir=True)
            try:
                copy_client_tree(pfd, priv_proj)
            finally:
                os.close(pfd)
        except (ClientPathError, OSError) as e:
            return {"error": f"project_dir refused: {e}"}, True
        fv_cli = os.path.join(self.fv_root, "bin", "fv")
        cmd = [fv_cli, "mint", priv_proj, "--out", priv_out, "--json",
               "--threads", str(int(params.get("threads") or self.default_threads))]
        for t in thms:
            cmd += ["--theorem", t]
        if params.get("module"):
            cmd += ["--module", str(params["module"])]
        if pkgs:
            cmd += ["--packages", pkgs]
        if params.get("for_fvserve"):
            cmd.append("--for-fvserve")
        tmo = min(float(params.get("timeout") or 600.0), 3600.0)
        try:
            p = run_subprocess_guarded(self.fv_root, cmd, timeout=tmo)
        except subprocess.TimeoutExpired:
            return {"ok": False, "error": f"mint timed out after {tmo}s"}, True
        try:
            data = json.loads(p.stdout)
        except ValueError:
            return {"ok": False, "error": (p.stderr or p.stdout)[-400:]}, True
        if not data.get("ok"):
            return data, True

        def relocate(x):   # private paths in the manifest -> the client's paths
            if isinstance(x, str):
                return x.replace(priv_out, out_dir).replace(priv_proj, proj)
            if isinstance(x, list):
                return [relocate(v) for v in x]
            if isinstance(x, dict):
                return {k: relocate(v) for k, v in x.items()}
            return x
        data = relocate(data)
        try:
            mf = os.path.join(priv_out, "mint-manifest.json")
            if os.path.isfile(mf):
                with open(mf, "w", encoding="utf-8") as f:
                    json.dump(data, f, indent=2)
            ofd = open_nofollow_under(out_dir, self.allowed_roots, want_dir=True, create=True)
            try:
                export_tree_to(priv_out, ofd)
            finally:
                os.close(ofd)
        except (ClientPathError, OSError) as e:
            return {"ok": False, "error": f"out_dir refused: {e}"}, True
        return data, False

    def tool_fv_verify_patch(self, params):
        """optimistic / interface modes are experimental and never counted: an explicit request for one is
        verified in exact (full) mode, and the envelope says so"""
        asked = params.get("mode") if isinstance(params, dict) else None
        if isinstance(params, dict) and "mode" in params and asked not in ("optimistic", "interface", "full"):   # incl. null
            return fv_schema.from_error("project_incremental", f"invalid mode {asked!r} (one of: full, optimistic, interface)",
                                        0.0), True
        if isinstance(params, dict) and (asked in ("optimistic", "interface") or params.get("optimistic_only")):
            env, is_err = self._tool_fv_verify_patch({k: v for k, v in params.items() if k not in ("mode", "optimistic_only")})
            if isinstance(env, dict) and "verdict" in env:
                what = (f"mode {asked}" if asked in ("optimistic", "interface") else "") + \
                    ((" and " if asked in ("optimistic", "interface") else "") + "optimistic_only" if params.get("optimistic_only") else "")
                note = (f"{what} is experimental in v0.1 and was not used: exact (full) mode was requested instead"
                        + ("" if self.fvwork_state else " (no verification ran: no fvwork service is configured)"))
                env["verdict_basis"] = f"{env.get('verdict_basis') or ''} [{note}]".strip()
                if isinstance(env.get("warnings"), list):
                    env["warnings"].append(note)
                else:
                    env["warnings"] = [note]
            return env, is_err
        return self._tool_fv_verify_patch(params)

    def _tool_fv_verify_patch(self, params):
        t0 = time.time()
        if not self.fvwork_state:
            return fv_schema.from_error("project_incremental", "no --fvwork-state configured on fastverify-mcp", 0.0), True
        req = {
            "op": "verify",
            "advance": bool(params.get("advance", False)),
            "stream": False,
            "mode": "full",   # always exact: optimistic / interface are experimental and never counted
        }
        if req["advance"] and not getattr(self.args, "allow_unsafe_advance", False):
            # Never advance fvwork's shared base on a REJECTED patch: merge=True advances iff ACCEPTED/CONDITIONAL.
            req["merge"] = True
        if params.get("merge"):
            req["merge"] = True
            req["advance"] = True
        if params.get("drift"):
            req["drift"] = True
        if params.get("optimistic_only"):
            req["optimistic_only"] = True
        if params.get("label"):
            req["label"] = fv_schema.sanitize_single_line(params["label"], 120)
        if params.get("files") is not None:
            files = params["files"]
            if not isinstance(files, dict) or not files:
                return fv_schema.from_error("project_incremental", "'files' must be a non-empty object", 0.0), True
            total_b = 0
            for k, v in files.items():
                try:
                    check_relpath(k, "file path")   # one rule for every path taken from client data
                except ClientPathError as e:
                    return fv_schema.from_error("project_incremental", f"invalid relative file path: {e}", 0.0), True
                if v is not None:
                    if not isinstance(v, str):
                        return fv_schema.from_error("project_incremental", f"file content for {k!r} must be string or null", 0.0), True
                    total_b += len(v.encode("utf-8", "replace"))
            if total_b > self.max_source_bytes * 4:
                return fv_schema.from_error("project_incremental", "total patch payload too large", 0.0), True
            req["files"] = files
            proj_dir = None
        elif params.get("tree_dir"):
            td, err = self.check_path(params["tree_dir"], must_exist=True, expect_dir=True)
            if err:
                return fv_schema.from_error("project_incremental", f"tree_dir: {err}", 0.0), True
            # fvwork gets a private no-follow copy of the tree, never the client path
            ttmp = tempfile.mkdtemp(prefix="fv-mcp-tree.")
            os.chmod(ttmp, 0o711)
            priv, err = self._private_tree(td, os.path.join(ttmp, "tree"))
            if err:
                shutil.rmtree(ttmp, ignore_errors=True)
                return fv_schema.from_error("project_incremental", f"tree_dir: {err}", 0.0), True
            req["tree"] = priv
            proj_dir = td
        else:
            return fv_schema.from_error("project_incremental", "provide 'files' or 'tree_dir'", 0.0), True
        tmo = min(float(params.get("timeout") or self.default_timeout), 1800.0)
        try:
            try:
                raw = fvserve.request(self.fvwork_state, req, timeout=tmo)
            finally:
                if req.get("tree"):
                    shutil.rmtree(os.path.dirname(req["tree"]), ignore_errors=True)
        except Exception as e:  # noqa: BLE001
            return fv_schema.make_envelope(
                mode="project_incremental", verdict="NO-VERDICT", trust="sound",
                verdict_basis=f"fvwork unavailable or timed out: {fv_schema.sanitize_single_line(e, 200)}",
                total_s=time.time() - t0, reason=fv_schema.sanitize_single_line(e, 200),
            ), False
        return fv_schema.from_fvwork_result(raw, project_dir=proj_dir, total_s=time.time() - t0, include_raw=False), False

    def tool_fv_lookup_duplicate(self, params):
        t0 = time.time()
        df_py = os.path.join(self.fv_root, "tools", "dupfind", "dupfind.py")
        if not os.path.isfile(df_py):
            return {"error": "tools/dupfind/dupfind.py not installed"}, True
        idxs = []
        client_idx = bool(params.get("indexes"))
        raw_idxs = params.get("indexes") or self.dupfind_indexes
        itmp = tempfile.mkdtemp(prefix="fv-mcp-idx.") if client_idx else None
        try:
            for i, ix in enumerate(raw_idxs):
                rp, err = self.check_path(ix, must_exist=True, expect_dir=True)
                if err:
                    return {"error": f"index {ix!r}: {err}"}, True
                if client_idx:   # a client index: a private copy of its index.sqlite (no link, regular, 1 link)
                    d = os.path.join(itmp, "ix%d" % i)
                    os.makedirs(d)
                    try:
                        copy_client_file(os.path.join(rp, "index.sqlite"), os.path.join(d, "index.sqlite"), self.allowed_roots)
                    except (ClientPathError, OSError) as e:
                        return {"error": f"index {ix!r}: refused: {e}"}, True
                    rp = d
                idxs.append(rp)
            return self._lookup_with(params, t0, df_py, idxs)
        finally:
            if itmp:
                shutil.rmtree(itmp, ignore_errors=True)

    def _lookup_with(self, params, t0, df_py, idxs):
        # Fast Unix-socket lookup path if configured and querying by name or type_hk
        if self.dupfind_socket and not params.get("source") and not params.get("source_file") and (params.get("name") or params.get("type_hk")):
            req = {"op": "lookup"}
            if params.get("name"):
                req["name"] = str(params["name"])
            if params.get("type_hk"):
                req["type_hk"] = str(params["type_hk"])
            try:
                s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                s.settimeout(min(float(params.get("timeout") or 10.0), 30.0))
                s.connect(self.dupfind_socket)
                s.sendall((json.dumps(req) + "\n").encode("utf-8"))
                buf = b""
                while not buf.endswith(b"\n"):
                    c = s.recv(65536)
                    if not c:
                        break
                    buf += c
                s.close()
                res = json.loads(buf.decode("utf-8"))
                res["elapsed_ms"] = round((time.time() - t0) * 1000.0, 2)
                return res, False
            except Exception as e:  # noqa: BLE001
                return {"error": f"dupfind socket failed: {fv_schema.sanitize_single_line(e, 200)}"}, True
        if not idxs:
            return {"error": "no dupfind index configured (pass 'indexes' or start fastverify-mcp with --dupfind-index DIR)"}, True
        tmo = min(float(params.get("timeout") or 60.0), 300.0)
        if params.get("name") or params.get("type_hk"):
            cmd = ["/usr/bin/python3", "-I", df_py, "lookup", "--json"]
            for ix in idxs:
                cmd += ["--index", ix]
            if params.get("name"):
                cmd += ["--name", str(params["name"])]
            if params.get("type_hk"):
                cmd += ["--hash", str(params["type_hk"])]
            p = subprocess.run(cmd, capture_output=True, text=True, timeout=tmo)
            if p.returncode != 0:
                return {"error": (p.stderr or p.stdout)[-300:]}, True
            out = json.loads(p.stdout)
            out["elapsed_ms"] = round((time.time() - t0) * 1000.0, 2)
            return out, False
        src, sfile, err = self._load_attempt_source(params)
        if err:
            return {"error": f"provide 'name', 'type_hk', 'source', or 'source_file' ({err})"}, True
        pk = self.default_packages or _repo_packages()
        if not pk:
            return {"error": "no trusted package workspace: start fastverify-mcp with --packages DIR"}, True
        tmpd = tempfile.mkdtemp(prefix="fv-dupq.")
        try:
            # always the private copy of the source read without following links (never the client path)
            qfile = os.path.join(tmpd, os.path.basename(sfile) if sfile and sfile.endswith(".lean") else "Query.lean")
            open(qfile, "w", encoding="utf-8").write(src)
            cmd = [
                "/usr/bin/python3", "-I", df_py, "query", qfile, "--json", "--fast-export",
                "--toolchain", self.args.toolchain,
                "--packages", pk,
                "--fv", self.fv_root, "--threads", str(min(self.default_threads, 8)),
            ]
            for ix in idxs:
                cmd += ["--index", ix]
            if params.get("targets"):
                cmd += ["--targets", str(params["targets"])]
            # Always use a persistent --snapshot dir (cuts Mathlib query latency in half: ~8s -> ~3-4s)
            snap_dir = self.dupfind_snapshot
            if not snap_dir:
                if self.fvserve_state and os.path.isdir(os.path.join(self.fvserve_state, "snap")):
                    snap_dir = os.path.join(self.fvserve_state, "snap")
                else:
                    base_tmp = "/dev/shm" if (os.path.isdir("/dev/shm") and os.access("/dev/shm", os.W_OK)) else tempfile.gettempdir()
                    snap_dir = os.path.join(base_tmp, f"fv-mcp-dupsnap-{os.getuid()}")
            os.makedirs(snap_dir, mode=0o700, exist_ok=True)
            cmd += ["--snapshot", snap_dir]
            p = run_subprocess_guarded(self.fv_root, cmd, timeout=tmo)
            if p.stdout.strip():
                try:
                    out = json.loads(p.stdout.strip().splitlines()[-1])
                    out["elapsed_ms"] = round((time.time() - t0) * 1000.0, 2)
                    return out, (p.returncode != 0)
                except ValueError:
                    pass
            return {"error": (p.stderr or p.stdout)[-400:]}, True
        except subprocess.TimeoutExpired:
            return {"error": f"dupfind query timed out after {tmo}s"}, True
        finally:
            shutil.rmtree(tmpd, ignore_errors=True)

    def tool_fv_diff_exports(self, params):
        old_p, err = self.check_path(params.get("old_export"), must_exist=True, expect_dir=False)
        if err:
            return {"error": f"old_export: {err}"}, True
        new_p, err = self.check_path(params.get("new_export"), must_exist=True, expect_dir=False)
        if err:
            return {"error": f"new_export: {err}"}, True
        targets = params.get("targets")
        tfile = params.get("targets_file")
        if tfile:
            tfile, err = self.check_path(tfile, must_exist=True, expect_dir=False)
            if err:
                return {"error": f"targets_file: {err}"}, True
            targets = tfile
        elif targets is not None:
            if not isinstance(targets, str) or not targets.strip():
                return {"error": "targets must be a non-empty comma-separated string"}, True
            for tok in targets.split(","):
                if not fv_schema.validate_theorem_name(tok.strip(), allow_dotted=True):
                    return {"error": f"invalid target name: {tok!r}"}, True
        explain = int(params.get("explain") if params.get("explain") is not None else 5)
        explain = max(0, min(explain, 50))
        threads = int(params.get("threads") or min(self.default_threads, 16))
        tmo = min(float(params.get("timeout") or 300.0), 1800.0)
        tmpd = tempfile.mkdtemp(prefix="fv-mcp-diff.")   # private copies: no link followed on the host
        try:
            try:
                copy_client_file(old_p, os.path.join(tmpd, "old.export"), self.allowed_roots)
                copy_client_file(new_p, os.path.join(tmpd, "new.export"), self.allowed_roots)
                if tfile:
                    copy_client_file(tfile, os.path.join(tmpd, "targets.txt"), self.allowed_roots)
                    targets = os.path.join(tmpd, "targets.txt")
            except (ClientPathError, OSError) as e:
                return {"error": f"refused: {e}"}, True
            res = run_expdiff_diff(
                self.fv_root, os.path.join(tmpd, "old.export"), os.path.join(tmpd, "new.export"),
                targets=targets, explain=explain,
                dead_lets=bool(params.get("dead_lets")),
                private_modulo=bool(params.get("private_modulo")),
                threads=threads, timeout=tmo,
            )
            return res, (not res.get("ok"))
        finally:
            shutil.rmtree(tmpd, ignore_errors=True)

    # ----------------------------------------------------------------------- JSON-RPC dispatch
    def dispatch(self, req):
        if not isinstance(req, dict) or req.get("jsonrpc") != "2.0":
            return {"jsonrpc": "2.0", "id": None, "error": {"code": -32600, "message": "Invalid Request"}}
        rid = req.get("id")
        method = req.get("method")
        params = req.get("params") or {}
        is_notif = "id" not in req

        if method == "initialize":
            req_ver = params.get("protocolVersion") if isinstance(params, dict) else None
            self.protocol_version = req_ver if req_ver in SUPPORTED_PROTOCOLS else SUPPORTED_PROTOCOLS[0]
            self.initialized = True
            return {
                "jsonrpc": "2.0",
                "id": rid,
                "result": {
                    "protocolVersion": self.protocol_version,
                    "capabilities": {
                        "tools": {"listChanged": False},
                        "resources": {"subscribe": False, "listChanged": False},
                        "prompts": {"listChanged": False},
                    },
                    "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
                    "instructions": (
                        "fastverify-mcp provides cheat-proof, dual-kernel SOUND verification for Lean 4 proofs "
                        "against pinned official challenges. Pair with an interactive tactic/LSP server (such as "
                        "Lean 4.36 lean-beam-mcp) for tactic exploration, and call fv_verify_attempt / "
                        "fv_verify_project to obtain an authoritative sound verdict. Treat NO-VERDICT/ERROR as "
                        "non-accepted (reward=0.0)."
                    ),
                },
            }
        if method in ("notifications/initialized", "notifications/cancelled"):
            return None
        if method == "ping":
            return {"jsonrpc": "2.0", "id": rid, "result": {}}
        if method == "tools/list":
            return {"jsonrpc": "2.0", "id": rid, "result": {"tools": self.tools}}
        if method == "resources/list":
            return {
                "jsonrpc": "2.0",
                "id": rid,
                "result": {
                    "resources": [
                        {
                            "uri": "fastverify://schema/result-v1",
                            "name": "fastverify result-v1 JSON Schema",
                            "mimeType": "application/json",
                            "description": "Draft 2020-12 JSON schema for all fastverify v1 API responses.",
                        },
                        {
                            "uri": "fastverify://status",
                            "name": "fastverify-mcp live status",
                            "mimeType": "application/json",
                            "description": "Current backend availability and loaded problem sets.",
                        },
                    ]
                },
            }
        if method == "resources/read":
            uri = params.get("uri") if isinstance(params, dict) else None
            if uri == "fastverify://schema/result-v1":
                txt = open(os.path.join(self.fv_root, "schemas", "result-v1.schema.json"), encoding="utf-8").read()
                return {"jsonrpc": "2.0", "id": rid, "result": {"contents": [{"uri": uri, "mimeType": "application/json", "text": txt}]}}
            if uri == "fastverify://status":
                st, _ = self.tool_fv_status({})
                return {"jsonrpc": "2.0", "id": rid, "result": {"contents": [{"uri": uri, "mimeType": "application/json", "text": json.dumps(st, indent=2)}]}}
            return {"jsonrpc": "2.0", "id": rid, "error": {"code": -32602, "message": f"unknown resource uri: {uri}"}}
        if method == "prompts/list":
            return {
                "jsonrpc": "2.0",
                "id": rid,
                "result": {
                    "prompts": [{
                        "name": "sound_proof_repair_loop",
                        "description": "Guide an agent through an iterative sound Lean 4 proof repair loop using fastverify-mcp.",
                        "arguments": [
                            {"name": "theorem", "description": "Target theorem name", "required": True},
                            {"name": "pset", "description": "Problem set name", "required": False},
                        ],
                    }]
                },
            }
        if method == "prompts/get":
            pname = params.get("name") if isinstance(params, dict) else None
            pargs = (params.get("arguments") or {}) if isinstance(params, dict) else {}
            if pname == "sound_proof_repair_loop":
                thm = pargs.get("theorem", "<theorem>")
                pset = pargs.get("pset", self.default_pset or "<pset>")
                text = (
                    f"Prove theorem `{thm}` in problem set `{pset}`.\n"
                    "1. Draft a complete Lean 4 proof (no `sorry`, no custom axioms, no `native_decide`, no `debug.skipKernelTC`).\n"
                    "2. Call `fv_verify_attempt` with `pset`, `theorem`, and `source`.\n"
                    "3. If `accepted` is true (`verdict == 'ACCEPTED'`), stop — the proof is soundly verified by the official Lean kernel and required second kernel (gruszka).\n"
                    "4. Otherwise inspect `diagnostics` and `compiler_output`, repair the proof, and retry."
                )
                return {"jsonrpc": "2.0", "id": rid, "result": {"messages": [{"role": "user", "content": {"type": "text", "text": text}}]}}
            return {"jsonrpc": "2.0", "id": rid, "error": {"code": -32602, "message": f"unknown prompt: {pname}"}}
        if method == "tools/call":
            if not isinstance(params, dict):
                return {"jsonrpc": "2.0", "id": rid, "error": {"code": -32602, "message": "params must be an object"}}
            tname = params.get("name")
            targs = params.get("arguments") or {}
            if tname not in self.tool_names:
                return {"jsonrpc": "2.0", "id": rid, "error": {"code": -32602, "message": f"unknown tool: {tname}"}}
            if not isinstance(targs, dict):
                return {"jsonrpc": "2.0", "id": rid, "error": {"code": -32602, "message": "tool arguments must be an object"}}
            self.stats["calls"] += 1
            handler = getattr(self, f"tool_{tname}")
            try:
                data, is_err = handler(targs)
            except Exception as e:  # noqa: BLE001
                self.stats["errors"] += 1
                data, is_err = {"error": f"internal error: {fv_schema.sanitize_single_line(e, 300)}"}, True
            if is_err:
                self.stats["errors"] += 1
            result_obj = {
                "content": [{"type": "text", "text": json.dumps(data, separators=(",", ":"))}],
                "structuredContent": data,
                "isError": bool(is_err),
            }
            return {"jsonrpc": "2.0", "id": rid, "result": result_obj}

        if is_notif:
            return None
        return {"jsonrpc": "2.0", "id": rid, "error": {"code": -32601, "message": f"Method not found: {method}"}}

    # ----------------------------------------------------------------------- stdio framing loop
    def read_message(self, inp):
        while True:
            line = inp.readline()
            if not line:
                return None
            if line in (b"\r\n", b"\n"):
                continue
            low = line.lower()
            if low.startswith(b"content-length:"):
                if self.framing is None:
                    self.framing = "lsp"
                try:
                    n = int(line.split(b":", 1)[1].strip())
                except ValueError:
                    return {"__parse_error__": "invalid Content-Length"}
                if n < 0 or n > self.max_source_bytes * 4 + 65536:
                    return {"__parse_error__": "message too large"}
                while True:
                    hdr = inp.readline()
                    if not hdr or hdr in (b"\r\n", b"\n"):
                        break
                body = inp.read(n)
                if len(body) != n:
                    return None
                try:
                    return json.loads(body.decode("utf-8", errors="strict"))
                except (ValueError, UnicodeDecodeError) as e:
                    return {"__parse_error__": str(e)}
            else:
                if self.framing is None:
                    self.framing = "newline"
                if len(line) > self.max_source_bytes * 4 + 65536:
                    return {"__parse_error__": "message line too large"}
                try:
                    return json.loads(line.decode("utf-8", errors="strict"))
                except (ValueError, UnicodeDecodeError) as e:
                    return {"__parse_error__": str(e)}

    def write_message(self, out, msg):
        raw = json.dumps(msg, separators=(",", ":")).encode("utf-8")
        try:
            if self.framing == "lsp":
                hdr = f"Content-Length: {len(raw)}\r\n\r\n".encode("ascii")
                out.write(hdr + raw)
            else:
                out.write(raw + b"\n")
            out.flush()
            return True
        except BrokenPipeError:
            return False

    def serve_stdio(self):
        inp = sys.stdin.buffer
        out = sys.stdout.buffer
        while True:
            msg = self.read_message(inp)
            if msg is None:
                break
            if isinstance(msg, dict) and "__parse_error__" in msg:
                if not self.write_message(out, {
                    "jsonrpc": "2.0", "id": None,
                    "error": {"code": -32700, "message": f"Parse error: {msg['__parse_error__']}"},
                }):
                    break
                continue
            resp = self.dispatch(msg)
            if resp is not None:
                if not self.write_message(out, resp):
                    break


# --------------------------------------------------------------------------- shared doctor / audit / init helpers
def read_cgroup_limits():
    lim = {"cgroup_v2": False, "memory_max_bytes": None, "cpu_quota_cores": None}
    try:
        if os.path.isfile("/sys/fs/cgroup/memory.max"):
            lim["cgroup_v2"] = True
            v = open("/sys/fs/cgroup/memory.max").read().strip()
            if v.isdigit():
                lim["memory_max_bytes"] = int(v)
        if os.path.isfile("/sys/fs/cgroup/cpu.max"):
            parts = open("/sys/fs/cgroup/cpu.max").read().strip().split()
            if len(parts) == 2 and parts[0].isdigit() and parts[1].isdigit() and int(parts[1]) > 0:
                lim["cpu_quota_cores"] = round(int(parts[0]) / int(parts[1]), 2)
    except OSError:
        pass
    return lim


def _read_plain_file(path, cap):
    """up to cap bytes of a single-link regular file opened O_NOFOLLOW|O_NONBLOCK (str), else None"""
    try:
        fd = os.open(path, _O_FILE)
    except OSError:
        return None
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
            return None
        return os.read(fd, cap).decode("utf-8", errors="replace")
    except OSError:
        return None
    finally:
        os.close(fd)


def run_host_doctor(fv_root, project_dir=None):
    """host readiness report; project_dir (optional) must be a PRIVATE no-follow copy of the client's project (the
    callers make it), never the client's directory"""
    checks = {}
    warnings = []
    # bwrap
    bwrap = shutil.which("bwrap") or ("/usr/bin/bwrap" if os.access("/usr/bin/bwrap", os.X_OK) else None)
    bwrap_ok = False
    if bwrap:
        p = subprocess.run([bwrap, "--ro-bind", "/", "/", "--unshare-all", "--", "/bin/true"],
                           capture_output=True, text=True, timeout=10)
        bwrap_ok = (p.returncode == 0)
    checks["bwrap"] = {"path": bwrap, "ok": bwrap_ok}
    if not bwrap_ok:
        warnings.append("bwrap unprivileged sandbox unavailable; fastverify cannot isolate untrusted builds")

    # vm.max_map_count
    mmc = None
    try:
        mmc = int(open("/proc/sys/vm/max_map_count").read().strip())
    except (OSError, ValueError):
        pass
    checks["vm_max_map_count"] = {"value": mmc, "ok": (mmc is None or mmc >= 65530)}
    if mmc is not None and mmc < 192000:
        warnings.append(f"vm.max_map_count={mmc} (<192000: OK for normal projects, insufficient for RH 175k modules)")

    # CPU & memory
    cpus = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else (os.cpu_count() or 1)
    mem_total_gb = None
    mem_avail_gb = None
    try:
        for ln in open("/proc/meminfo"):
            if ln.startswith("MemTotal:"):
                mem_total_gb = round(int(ln.split()[1]) / (1024 * 1024), 2)
            elif ln.startswith("MemAvailable:"):
                mem_avail_gb = round(int(ln.split()[1]) / (1024 * 1024), 2)
    except OSError:
        pass
    shm_free_gb = None
    try:
        st = os.statvfs("/dev/shm")
        shm_free_gb = round((st.f_bavail * st.f_frsize) / (1024 ** 3), 2)
    except OSError:
        pass
    cg = read_cgroup_limits()
    eff_mem_gb = mem_avail_gb
    if cg["memory_max_bytes"]:
        eff_mem_gb = min(eff_mem_gb or 1e9, round(cg["memory_max_bytes"] / (1024 ** 3), 2))
    checks["resources"] = {
        "affinity_cpus": cpus,
        "mem_total_gb": mem_total_gb,
        "mem_avail_gb": mem_avail_gb,
        "effective_mem_gb": eff_mem_gb,
        "shm_free_gb": shm_free_gb,
        "cgroup": cg,
    }

    # Pinned sound binaries & config
    pins_p = os.path.join(fv_root, "check", "sound", "pins.env")
    pins_ok = {}
    if os.path.isfile(pins_p):
        for ln in open(pins_p):
            parts = ln.strip().split()
            if len(parts) == 4 and parts[0] == "PIN":
                _, name, _sha, path = parts
                pins_ok[name] = os.path.isfile(path)
    # readiness = the pins check-sound.sh REQUIRES (it declines without them: its PIN loop over
    # the required tuple below); the others are optional components (overlap: pleanchecker_incr / snapshot_exporter; opt-in
    # extra kernels con_leche / nanoda + selftest_kbad): missing ones are warnings, not a failed host
    required = ("ccmp", "pleanchecker", "gruszka", "selftest_comparator", "selftest_challenge", "selftest_good",
                "selftest_bad")   # = check-sound.sh `for name in ccmp pleanchecker gruszka selftest_... do ... decline`
    req_missing = sorted(n for n in required if not pins_ok.get(n))
    opt_missing = sorted(n for n, ok in pins_ok.items() if not ok and n not in required)
    checks["sound_pins"] = {"all_present": bool(pins_ok) and all(pins_ok.values()), "files": pins_ok,
                            "required_present": bool(pins_ok) and not req_missing, "required_missing": req_missing,
                            "optional_missing": opt_missing}
    if not checks["sound_pins"]["required_present"]:
        warnings.append("some pinned sound-check binaries are missing on this node (run tools/deploy.sh or check /scratch/fastverify-next)")
    elif opt_missing:
        warnings.append(f"optional pinned component(s) missing: {', '.join(opt_missing)} (the default sound check runs "
                        "without them; overlap / the named opt-in extra kernels are unavailable on this node)")

    pins437_p = os.path.join(fv_root, "check", "sound", "pins-437.env")
    if os.path.isfile(pins437_p):
        p437 = {}
        for ln in open(pins437_p):
            parts = ln.strip().split()
            if len(parts) == 4 and parts[0] == "PIN":
                _, name, _sha, path = parts
                p437[name] = os.path.isfile(path)
        checks["sound_pins_437"] = {"all_present": bool(p437) and all(p437.values()), "files": p437}

    # Components & toolchains
    comp_p = os.path.join(fv_root, "config", "components.json")
    tcs = []
    registered_tcs = {}
    if os.path.isfile(comp_p):
        c = json.load(open(comp_p))
        for k, v in (c.get("lean_toolchains") or {}).items():
            ok_dir = os.path.isdir(v.get("prefix") or "")
            tcs.append({"id": k, "prefix": v.get("prefix"), "exists": ok_dir})
            registered_tcs[k] = ok_dir
        comp_tc = (c.get("comparator") or {}).get("prefix")
        checks["lean_beam_mcp"] = os.path.isfile(os.path.join(comp_tc or "", "bin", "lean-beam-mcp"))
    checks["toolchains"] = tcs
    exp_comp_p = os.path.join(fv_root, "export", "components.json")
    if os.path.isfile(exp_comp_p):
        try:
            ec = json.load(open(exp_comp_p))
            checks["native_exporters"] = [
                {"lean_version": (ec.get("native") or {}).get("lean_version"), "exists": os.path.isfile((ec.get("native") or {}).get("path") or "")}
            ] + [
                {"lean_version": e.get("lean_version"), "exists": os.path.isfile(e.get("path") or "")}
                for e in (ec.get("natives_other") or [])
            ]
        except Exception:
            pass

    # Optional project shape inspection (+ lib/autotune.py when available)
    proj_info = None
    autotune_plan = None
    rec = {"preset": "sound-auto" if os.path.isfile(os.path.join(fv_root, "lib", "autotune.py")) else "sound",
           "threads": min(cpus, 64), "export_dir": "/dev/shm" if (shm_free_gb or 0) >= 256 else "none", "notes": []}
    if eff_mem_gb is not None and eff_mem_gb < 32:
        rec["threads"] = min(cpus, 8)
        rec["notes"].append("low memory (<32 GB): use --export-dir none and <=8 threads; use --low-mem when available")
    if project_dir and os.path.isdir(project_dir):
        at_py = os.path.join(fv_root, "lib", "autotune.py")
        # project_dir is always a PRIVATE no-follow copy (MCP fv_doctor, CLI fv doctor);
        # lib/autotune.py runs on the host and walks the srcDirs of the copy's lakefile.toml: it runs only when every
        # lakefile path stays inside the copy (an absolute / '..' srcDir walked host directories outside it)
        lake_err = lake_config_confined(project_dir)
        if lake_err:
            warnings.append(f"autotune not run: {lake_err}")
            rec["notes"].append(f"autotune not run: {lake_err}")
        if os.path.isfile(at_py) and not lake_err:
            try:
                p = subprocess.run(["/usr/bin/python3", "-I", at_py, project_dir, "--json"],
                                   capture_output=True, text=True, timeout=15)
                if p.returncode == 0 and p.stdout.strip():
                    autotune_plan = json.loads(p.stdout)
                    rec["preset"] = "sound-auto"
                    if autotune_plan.get("threads"):
                        rec["threads"] = autotune_plan["threads"]
                    if autotune_plan.get("build") == "B0":
                        rec["build_override"] = "B0"
                    opts = autotune_plan.get("options") or {}
                    if "export_dir" in opts:
                        rec["export_dir"] = opts["export_dir"]
                    for k, why in list((autotune_plan.get("reasons") or {}).items())[:4]:
                        rec["notes"].append(f"autotune[{k}]: {why}")
            except Exception:
                pass
        lean_files = []
        mathlib_full = 0
        has_to_dual = False
        for r, ds, fs in os.walk(project_dir):
            ds[:] = [d for d in ds if not d.startswith(".") and d != ".lake"]
            for fn in fs:
                if fn.endswith(".lean"):
                    p = os.path.join(r, fn)
                    lean_files.append(p)
                    if len(lean_files) <= 200:
                        try:   # never through a link / FIFO: single-link regular files only, O_NOFOLLOW|O_NONBLOCK
                            txt = _read_plain_file(p, 4096)
                            if txt is None:
                                continue
                            if re.search(r"^\s*import\s+Mathlib\s*$", txt, re.M):
                                mathlib_full += 1
                            if "@[to_dual" in txt or "@[to_additive" in txt:
                                has_to_dual = True
                        except OSError:
                            pass
        tc_file = os.path.join(project_dir, "lean-toolchain")
        proj_tc = _read_plain_file(tc_file, 256)   # capped, no link / FIFO followed
        proj_tc = proj_tc.strip() if proj_tc is not None else None
        proj_info = {
            "path": project_dir,
            "lean_files": len(lean_files),
            "toolchain": proj_tc,
            "sampled_full_mathlib_imports": mathlib_full,
            "has_to_dual_or_additive": has_to_dual,
        }
        if len(lean_files) <= 3:
            rec["build_override"] = "B0"
            rec["notes"].append("tiny project (<=3 files): use --build B0 or fvserve/batchverify to avoid B3 fixed overhead")
        if has_to_dual:
            rec["notes"].append("detected @[to_dual]/@[to_additive]: consider --confirm-reject or --preset sound-auto")
        if proj_tc and proj_tc != "leanprover/lean4:v4.33.1":
            if registered_tcs.get(proj_tc):
                rec["notes"].append(f"toolchain {proj_tc}: registered & ready in config/components.json")
            else:
                rec["notes"].append(f"toolchain {proj_tc}: not yet registered — add via tools/addrelease.py")

    return {
        "ok": bwrap_ok and checks["sound_pins"]["required_present"],
        "checks": checks,
        "project": proj_info,
        "autotune": autotune_plan,
        "recommendation": rec,
        "warnings": warnings,
    }


def ensure_expdiff_bin(fv_root):
    """Locate or lazily build the std-only Rust tools/compress/expdiff binary on /tmp (never NFS)."""
    env_bin = os.environ.get("EXPDIFF_BIN")
    if env_bin and os.path.isfile(env_bin) and os.access(env_bin, os.X_OK):
        return env_bin, None
    ed_dir = os.path.join(fv_root, "tools", "compress", "expdiff")
    src_rs = os.path.join(ed_dir, "src", "main.rs")
    build_sh = os.path.join(ed_dir, "build.sh")
    if not os.path.isfile(build_sh):
        return None, "tools/compress/expdiff is not installed"
    src_mtime = os.path.getmtime(src_rs) if os.path.isfile(src_rs) else 0
    td = os.environ.get("EXPDIFF_TARGET") or f"/tmp/fastverify-expdiff-{os.getuid()}"
    cands = [os.path.join(td, "release", "expdiff")]
    user = os.environ.get("USER") or ""
    if user:
        cands.append(f"/scratch/{user}-expdiff-target/release/expdiff")
    for c in cands:
        if os.path.isfile(c) and os.access(c, os.X_OK):
            try:
                if os.path.getmtime(c) >= src_mtime:
                    return c, None
            except OSError:
                return c, None
    env = dict(os.environ)
    env["EXPDIFF_TARGET"] = td
    cargo_bin = os.path.expanduser("~/.cargo/bin")
    if os.path.isdir(cargo_bin) and cargo_bin not in env.get("PATH", ""):
        env["PATH"] = cargo_bin + ":" + env.get("PATH", "/usr/bin:/bin")
    if not shutil.which("cc", path=env.get("PATH")):
        linker = (
            shutil.which("gcc", path=env.get("PATH"))
            or shutil.which("clang", path=env.get("PATH"))
            or os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/clang")
        )
        if linker and os.path.isfile(linker):
            env.setdefault("CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER", linker)
            env.setdefault("CC", linker)
    p = subprocess.run(["/bin/bash", build_sh], env=env, capture_output=True, text=True, timeout=180)
    if p.returncode != 0:
        return None, f"expdiff build failed (rc={p.returncode}): {(p.stderr or p.stdout)[-300:]}"
    out_lines = [ln.strip() for ln in p.stdout.splitlines() if ln.strip()]
    if out_lines and os.path.isfile(out_lines[-1]) and os.access(out_lines[-1], os.X_OK):
        return out_lines[-1], None
    return None, "expdiff build produced no executable"


def run_expdiff_diff(
    fv_root, old_export, new_export, targets=None, explain=5,
    dead_lets=False, private_modulo=False, threads=8, timeout=300.0,
):
    """Run tools/compress/expdiff diff and parse TSV output into structured JSON.
    Analysis/diagnostic only — never a verification verdict."""
    t0 = time.time()
    bin_p, berr = ensure_expdiff_bin(fv_root)
    if berr:
        return {"ok": False, "analysis_only": True, "error": berr}
    cmd = [bin_p, "diff", "-j", str(max(1, int(threads))), "--explain", str(max(0, int(explain)))]
    if targets:
        cmd += ["--targets", str(targets)]
    if dead_lets:
        cmd.append("--dead-lets")
    if private_modulo:
        cmd.append("--private-modulo")
    cmd += [old_export, new_export]
    try:
        p = run_subprocess_guarded(fv_root, cmd, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"ok": False, "analysis_only": True, "error": f"expdiff timed out after {timeout}s"}
    if p.returncode != 0:
        return {
            "ok": False, "analysis_only": True,
            "error": f"expdiff exited {p.returncode}: {(p.stderr or p.stdout)[-300:]}",
        }
    old_info, new_info = {}, {}
    statuses = {}
    stmt_changed = []
    stmt_changed_count = 0
    explanations = []
    result_line = ""
    for ln in p.stdout.splitlines():
        if not ln or ln.startswith("#"):
            continue
        parts = ln.split("\t")
        tag = parts[0]
        if tag.startswith("old.") and len(parts) >= 2:
            k = tag[4:]
            old_info[k] = int(parts[1]) if parts[1].isdigit() else parts[1]
        elif tag.startswith("new.") and len(parts) >= 2:
            k = tag[4:]
            new_info[k] = int(parts[1]) if parts[1].isdigit() else parts[1]
        elif tag == "status" and len(parts) >= 3:
            statuses[parts[1]] = int(parts[2]) if parts[2].isdigit() else parts[2]
        elif tag == "statement_changed_count" and len(parts) >= 2 and parts[1].isdigit():
            stmt_changed_count = int(parts[1])
        elif tag == "statement_changed" and len(parts) >= 2:
            stmt_changed.append(parts[1])
        elif tag == "explain" and len(parts) >= 4:
            explanations.append({"status": parts[1], "decl": parts[2], "detail": "\t".join(parts[3:])})
        elif tag == "RESULT" and len(parts) >= 2:
            result_line = parts[1]
    return {
        "ok": True,
        "analysis_only": True,
        "verdict": None,
        "note": "diagnostic kernel-term diff only (never a verification verdict; use fv verify/check for sound ACCEPTED)",
        "old": old_info,
        "new": new_info,
        "statuses": statuses,
        "statement_changed_count": stmt_changed_count,
        "statement_changed": stmt_changed,
        "explanations": explanations,
        "result": result_line,
        "wall_s": round(time.time() - t0, 4),
    }


def audit_challenge_dir(
    fv_root, challenge_dir, expected_sha256=None,
    probe=False, packages_dir=None, reading_set_out=None, conjecture_mode=False,
    solution_mode=False, config_path=None, input_private=False, roots=None,
):
    """statement audit of a challenge directory (or a single .export). Nothing of the
    caller's is read, hashed or followed on the host: unless input_private (the MCP server passes its own private copy),
    challenge_dir (a directory: its tree; a file: it and a sibling comparator.json) and --config are first copied
    privately WITHOUT following anything from the roots (default: cli_roots()), and the reading set is written back
    without following links; an audit.py run that fails (refusal, crash, no report) is an error, never ok."""
    if input_private:
        return _audit_challenge_priv(fv_root, challenge_dir, expected_sha256, probe, packages_dir, reading_set_out,
                                     conjecture_mode, solution_mode, config_path)
    roots = roots or cli_roots()
    tmp_in = tempfile.mkdtemp(prefix="fv-audit-in.")
    try:
        try:
            canon = client_abspath(challenge_dir, roots, must_exist=True, allow_dotdot=True)
            if os.path.isdir(canon):
                priv = os.path.join(tmp_in, "challenge")
                cfd = open_nofollow_under(canon, roots, want_dir=True)
                try:
                    copy_client_tree(cfd, priv)
                finally:
                    os.close(cfd)
            else:
                os.mkdir(os.path.join(tmp_in, "c"), 0o700)
                priv = os.path.join(tmp_in, "c", os.path.basename(canon))
                copy_client_file(canon, priv, roots)
                sib = os.path.join(os.path.dirname(canon), "comparator.json")
                try:
                    sst = os.stat(sib, follow_symlinks=False)
                except OSError:
                    sst = None
                if sst is not None and not config_path:
                    copy_client_file(sib, os.path.join(tmp_in, "c", "comparator.json"), roots)
            cfg_priv = None
            if config_path:
                cfg_priv = os.path.join(tmp_in, "config.json")
                copy_client_file(config_path, cfg_priv, roots)
            rs_canon = client_abspath(reading_set_out, roots, must_exist=False, expect_dir=False, allow_dotdot=True) \
                if reading_set_out else None
        except (ClientPathError, OSError) as e:
            return {"ok": False, "error": f"refused: {e}", "findings": [
                {"rule_id": "FV007", "severity": "error", "message": f"input refused (no symlink / special / hard-linked "
                                                                     f"file is followed): {e}"}]}
        rs_priv = os.path.join(tmp_in, "reading_set.lean") if rs_canon else None
        res = _audit_challenge_priv(fv_root, priv, expected_sha256, probe, packages_dir, rs_priv, conjecture_mode,
                                    solution_mode, cfg_priv)
        res = json.loads(json.dumps(res).replace(json.dumps(priv)[1:-1], json.dumps(challenge_dir)[1:-1]))
        if rs_canon and os.path.isfile(rs_priv):
            try:
                dfd = open_nofollow_under(os.path.dirname(rs_canon), roots, want_dir=True, create=True)
                try:
                    with open(rs_priv, "rb") as f:
                        write_file_at(dfd, os.path.basename(rs_canon), f.read())
                finally:
                    os.close(dfd)
            except (ClientPathError, OSError) as e:
                res["ok"] = False
                res.setdefault("findings", []).append({"rule_id": "FV007", "severity": "error",
                                                       "message": f"--reading-set not written (no link followed): {e}"})
        return res
    finally:
        shutil.rmtree(tmp_in, ignore_errors=True)


def _audit_challenge_priv(fv_root, challenge_dir, expected_sha256, probe, packages_dir, reading_set_out,
                          conjecture_mode, solution_mode, config_path):
    """audit_challenge_dir on a PRIVATE copy (made by the caller / by audit_challenge_dir)"""
    findings = []
    is_file = os.path.isfile(challenge_dir)
    cfg_p = config_path if config_path else (
        os.path.join(os.path.dirname(challenge_dir), "comparator.json") if is_file
        else os.path.join(challenge_dir, "comparator.json")
    )
    chx_p = challenge_dir if is_file else os.path.join(challenge_dir, "challenge.export")
    if not os.path.isfile(cfg_p):
        if is_file and solution_mode:
            cfg = {"theorem_names": [], "definition_names": [], "permitted_axioms": list(S1_PERMITTED_AXIOMS)}
        else:
            return {"ok": False, "error": "missing comparator.json", "findings": findings}
    else:
        try:
            cfg = json.load(open(cfg_p, encoding="utf-8"))
        except Exception as e:  # noqa: BLE001
            return {"ok": False, "error": f"malformed comparator.json: {e}", "findings": findings}
        if not isinstance(cfg, dict):   # not a Lake comparator config: the audit cannot run
            return {"ok": False, "error": f"malformed comparator.json: a JSON object is required, not {type(cfg).__name__}",
                    "findings": findings}
    thms = cfg.get("theorem_names") or []
    defs = cfg.get("definition_names") or []
    axioms = cfg.get("permitted_axioms") or []
    std_axioms = {"propext", "Quot.sound", "Classical.choice"}
    extra_ax = [a for a in axioms if a not in std_axioms]
    if extra_ax:
        findings.append({
            "rule_id": "FV007", "severity": "error",
            "message": f"Non-standard permitted_axioms in comparator.json: {extra_ax}",
        })
    if defs:
        findings.append({
            "rule_id": "FV007", "severity": "warning",
            "message": f"Non-empty definition_names ({len(defs)}): solutions may supply arbitrary bodies for {defs[:10]}",
        })
    if not thms and not defs:
        findings.append({"rule_id": "FV007", "severity": "error", "message": "comparator.json lists no theorems or definitions"})
    chx_info = {"present": os.path.isfile(chx_p)}
    if chx_info["present"]:
        actual = fv_schema.sha256_file(chx_p)
        chx_info["sha256"] = actual
        chx_info["size_bytes"] = os.path.getsize(chx_p)
        if expected_sha256:
            chx_info["pin_matches"] = (actual == expected_sha256)
            if not chx_info["pin_matches"]:
                findings.append({
                    "rule_id": "FV007", "severity": "error",
                    "message": f"challenge.export sha256 mismatch: got {actual}, expected {expected_sha256}",
                })
    else:
        findings.append({
            "rule_id": "FV007", "severity": "info",
            "message": "No pre-built challenge.export; run 'fv init-challenge' to build and pin one officially.",
        })
    # Delegate to fastverify/tools/audit/audit.py if installed
    ext_audit = None
    ap = os.path.join(fv_root, "tools", "audit", "audit.py")
    if os.path.isfile(ap):
        tmp_aj = tempfile.mkdtemp(prefix="fv-audit.")
        try:
            out_aj = os.path.join(tmp_aj, "audit.json")
            acmd = ["/usr/bin/python3", "-I", ap, challenge_dir,
                    "--probe" if probe else "--no-probe", "--json", out_aj]
            if os.path.isfile(cfg_p):
                acmd += ["--config", cfg_p]
            if packages_dir:
                acmd += ["--packages", packages_dir]
            if reading_set_out:
                acmd += ["--reading-set", reading_set_out]
            if conjecture_mode:
                acmd.append("--conjecture-mode")
            if solution_mode:
                acmd.append("--solution-mode")
            p = run_subprocess_guarded(fv_root, acmd, timeout=180 if probe else 60)
            if p.returncode not in (0, 1) or not os.path.isfile(out_aj):
                # a refused / crashed audit is an error, never ok=True
                why = fv_schema.sanitize_single_line((p.stderr or p.stdout or "")[-300:], 300)
                ext_audit = {"error": f"audit.py exited {p.returncode} without a report: {why}"}
                findings.append({"rule_id": "FV007", "severity": "error",
                                 "message": f"deep statement audit failed (audit.py exit {p.returncode}): {why}"})
            else:
                ext_audit = json.load(open(out_aj, encoding="utf-8"))
                st = str(ext_audit.get("status") or "").upper()
                if st in ("CRITICAL", "HIGH"):
                    findings.append({
                        "rule_id": "FV007",
                        "severity": "error" if st == "CRITICAL" else "warning",
                        "message": f"deep statement audit flagged status={st} ({len(ext_audit.get('findings') or [])} finding(s))",
                    })
        except Exception as e:  # noqa: BLE001
            ext_audit = {"error": fv_schema.sanitize_single_line(e, 200)}
            findings.append({"rule_id": "FV007", "severity": "error",   # never ok on a failed audit
                             "message": f"deep statement audit failed: {fv_schema.sanitize_single_line(e, 200)}"})
        finally:
            shutil.rmtree(tmp_aj, ignore_errors=True)
    return {
        "ok": not any(f["severity"] == "error" for f in findings),
        "challenge_dir": challenge_dir,
        "theorem_count": len(thms),
        "definition_names_count": len(defs),
        "permitted_axioms": axioms,
        "challenge_export": chx_info,
        "findings": findings,
        "deep_audit": ext_audit,
    }


def init_official_challenge(fv_root, challenge_dir, out_dir, packages_dir=None, threads=8, timeout=600.0, roots=None):
    """Build & pin official challenge.export from challenge sources via bin/fastverify --preset reference (B0+E0).
    The challenge directory is first copied privately WITHOUT following anything (a symlink, special
    file or hard link anywhere: refused) and built from that copy; every output file is created / replaced inside out_dir
    without following links (a symlink planted in out_dir is replaced, never written through). roots = the MCP
    --allow-root list; None (local CLI) = the user's own resolved ancestors of challenge_dir / out_dir."""
    # neither path is resolved: both are mapped lexically onto the roots and walked with
    # O_NOFOLLOW (never realpath on challenge_dir, never an anchor at the resolved path itself)
    croots = roots or cli_roots()
    oroots = roots or cli_roots()
    try:
        chal_p = local_path_under(challenge_dir, croots)
        out_p = local_path_under(out_dir, oroots)
    except ClientPathError as e:
        return {"ok": False, "error": f"refused: {e}"}
    tmp_run = tempfile.mkdtemp(prefix="fv-init-chal.")
    out_fd = None
    try:
        priv = os.path.join(tmp_run, "challenge")
        try:
            cfd = open_nofollow_under(chal_p, croots, want_dir=True)
            try:
                copy_client_tree(cfd, priv)
            finally:
                os.close(cfd)
        except (ClientPathError, OSError) as e:
            return {"ok": False, "error": f"challenge_dir refused: {e}"}
        if not os.path.isfile(os.path.join(priv, "comparator.json")):
            return {"ok": False, "error": "challenge_dir has no comparator.json"}
        lerr = lake_config_confined(priv)   # uniform: no client lakefile path leaves the copy
        if lerr:
            return {"ok": False, "error": f"challenge_dir refused: {lerr}"}
        # no automatic use of the challenge's own .lake/packages: a packages workspace is trusted input and
        # is used only when given explicitly (the service owner's --packages / the CLI user's --packages)
        if not packages_dir and not roots and _real_dir_at(chal_p, croots, (".lake", "packages")):
            return {"ok": False, "error": "the challenge has its own .lake/packages: pass the packages workspace explicitly "
                                          "with --packages DIR (a workspace is trusted input)"}
        run_out = os.path.join(tmp_run, "ref")
        fv_bin = os.path.join(fv_root, "bin", "fastverify")
        # Build the challenge itself as both project and challenge with --preset reference so B0 + E0 exports it officially
        # Note: challenge has sorry proofs, so C0 rejects, while challenge.export is produced officially before C0!
        cmd = [fv_bin, priv, priv, run_out, "--preset", "reference", "--threads", str(threads)]
        if packages_dir:
            cmd += ["--packages", packages_dir]
        p = run_subprocess_guarded(fv_root, cmd, timeout=timeout)
        chx_src = os.path.join(run_out, "challenge.export")
        if not os.path.isfile(chx_src) or os.path.getsize(chx_src) == 0:
            return {"ok": False, "error": f"official challenge export failed (rc={p.returncode}): {(p.stderr or p.stdout)[-400:]}"}
        try:
            out_fd = open_nofollow_under(out_p, oroots, want_dir=True, create=True)
        except (ClientPathError, OSError) as e:
            return {"ok": False, "error": f"out_dir refused: {e}"}
        try:
            sha = fv_schema.sha256_file(chx_src)
            fd = os.open(chx_src, _O_FILE)
            try:
                write_file_at(out_fd, "challenge.export", src_fd=fd, mode=0o444)
            finally:
                os.close(fd)
            write_file_at(out_fd, "challenge.export.sha256", f"{sha}  challenge.export\n")
            cfg_b = open(os.path.join(priv, "comparator.json"), "rb").read()
            cfg_sha = hashlib.sha256(cfg_b).hexdigest()
            write_file_at(out_fd, "comparator.json", cfg_b)
            write_file_at(out_fd, "comparator.json.sha256", f"{cfg_sha}  comparator.json\n")
            if os.path.isfile(os.path.join(priv, "lean-toolchain")):
                write_file_at(out_fd, "lean-toolchain", open(os.path.join(priv, "lean-toolchain"), "rb").read())
        except (ClientPathError, OSError) as e:
            return {"ok": False, "error": f"cannot write into out_dir without following links: {e}"}
        return {
            "ok": True,
            "out_dir": out_p,
            "challenge_export": os.path.join(out_p, "challenge.export"),
            "challenge_sha256": sha,
            "comparator_sha256": cfg_sha,
            "size_bytes": os.path.getsize(chx_src),
            "provenance": "built by official B0 (lake build) + E0 (official lean4export) in bwrap sandbox",
        }
    except subprocess.TimeoutExpired:
        return {"ok": False, "error": f"challenge build timed out after {timeout}s"}
    finally:
        if out_fd is not None:
            os.close(out_fd)
        shutil.rmtree(tmp_run, ignore_errors=True)


def reset_child_signals():
    """a caller that ignores SIGCHLD makes every child's exit status read as 0 (env -i keeps the
    disposition): restore the default and clear the inherited signal mask before anything starts"""
    import signal as _sg
    if hasattr(_sg, "SIGCHLD"):
        _sg.signal(_sg.SIGCHLD, _sg.SIG_DFL)
    try:
        _sg.pthread_sigmask(_sg.SIG_SETMASK, set())
    except (AttributeError, OSError, ValueError):
        pass


def main():
    ap = argparse.ArgumentParser(prog="fastverify-mcp", description="MCP server (JSON-RPC 2.0 stdio) for fastverify")
    ap.add_argument("--version", action="store_true", help="print server version and protocol info")
    ap.add_argument("--fv-root", default=FV_ROOT, help="fastverify package root")
    ap.add_argument("--fvserve-state", default=None, help="fvserve --state dir for fast attempt verification")
    ap.add_argument("--fvapi-url", default=None, help="optional fvapi HTTP URL fallback")
    ap.add_argument("--fvwork-state", default=None, help="optional persistent project daemon state dir")
    ap.add_argument("--dupfind-index", action="append", default=[], help="optional dupfind sqlite index dir (repeatable)")
    ap.add_argument("--dupfind-socket", default=None, help="optional dupfind serve Unix socket path")
    ap.add_argument("--dupfind-snapshot", default=None, help="persistent directory for dupfind --snapshot official header cache")
    ap.add_argument("--default-pset", default=None, help="default problem set name for fv_verify_attempt")
    ap.add_argument("--packages", default=None, help="default trusted Lake packages workspace")
    ap.add_argument("--toolchain", default=_default_toolchain(),
                    help="official Lean toolchain for sandboxed sub-lemma triage probes")
    ap.add_argument("--allow-root", action="append", default=[],
                    help="allowlisted directory root for file paths (repeatable; defaults to current working directory)")
    ap.add_argument("--allow-any-root", action="store_true",
                    help="disable --allow-root containment (trusted local service owners only; default OFF)")
    ap.add_argument("--challenge", action="append", default=[],
                    help="challenge registry entry pinned by the service owner, ID=DIR[:CHALLENGE_SHA256[:COMPARATOR_SHA256]] (repeatable; prevents a forged comparator.json)")
    ap.add_argument("--allow-caller-challenge", action="store_true",
                    help="allow caller-supplied challenge paths even when --challenge registry is non-empty (trusted callers only)")
    ap.add_argument("--allow-unpinned-comparator", action="store_true",
                    help="(no effect: the comparator pin is required wherever the challenge pin is)")
    ap.add_argument("--experimental", action="store_true",
                    help="(v0.1) enable the EXPERIMENTAL tools (fv_triage_sublemma) and the notary judge "
                         "(fv_check_export notary); FV_EXPERIMENTAL=1 does the same")
    ap.add_argument("--allow-incr-base", action="store_true",
                    help="accept a client-supplied incr_base in fv_verify_project (default OFF: an incremental base is "
                    "trusted input - work tree, build plan, planner binary, plugin)")
    ap.add_argument("--allow-unsound-presets", action="store_true",
                    help="allow non-sound presets (e.g. reference) in fv_verify_project (default OFF)")
    ap.add_argument("--allow-custom-axioms", action="store_true",
                    help="allow comparator.json permitted_axioms outside GOAL S1(3) (default OFF)")
    ap.add_argument("--allow-unsafe-advance", action="store_true",
                    help="allow fv_verify_patch(advance=true) without merge=true (default OFF)")
    ap.add_argument("--threads", type=int, default=0, help="default worker threads")
    ap.add_argument("--max-source-bytes", type=int, default=1 << 20)
    ap.add_argument("--max-batch", type=int, default=64)
    ap.add_argument("--default-timeout", type=float, default=300.0)
    args = ap.parse_args()

    if args.version:
        print(json.dumps({
            "name": SERVER_NAME,
            "version": SERVER_VERSION,
            "supported_protocols": list(SUPPORTED_PROTOCOLS),
            "api_version": fv_schema.API_VERSION,
            "fv_root": os.path.realpath(args.fv_root),
        }))
        return 0
    srv = McpServer(args)
    srv.serve_stdio()
    return 0


if __name__ == "__main__":
    reset_child_signals()
    sys.exit(main())
