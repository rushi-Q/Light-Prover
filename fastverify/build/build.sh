#!/bin/bash
# build/build.sh PROJ PACKAGES_WS TOOLCHAIN_PREFIX [--threads N] [--json FILE] [--lean-path-out FILE] [--log DIR]
#                [--timeout SEC] [--plan-only] [--preset B1|B2|B3] [--unsafe LIST] [--require-modules 'MOD...']
#   --preset B1 (default) exact Lake invocations; B2 = B1 + early release (exact; see build/README.md "Menu");
#            B3 = B2 + the UNSAFE opt-ins of --unsafe (required with B3, refused otherwise)
#   --unsafe LIST  opt-in UNSAFE transforms, comma list of skip-kernel-tc (findings 007 017 030 038), linter-off (022),
#                  native-pkg (015 057),
#                  merge[=ARGS] (S02, sound preset only: module merging as a plan rewrite, build/mergeplan.py; a failing
#                  merged group falls back to its members' exact invocations; ARGS = colon-separated mergeplan options;
#                  the token 'late' = planner concurrent with the build, groups swapped in by sched.py --merge-late),
#                  retries (062), toolchain-T1[=NAME] (patched/PGO lean for the modules, tests 004 014 020 031 037 040 046 048
#                  050 052 061): the build is then NOT the official build; the stage JSON carries "unsafe": [...]
#                  premise-off (S07, sound preset only): every eligible module's setup.json imports += the generated
#                  helper FastverifyPremiseOff (exported library-suggestion deny-list entries, no declarations), so no
#                  premise-selection metadata is computed at .olean write (build/premiseoff/premiseoff.py, README);
#                  lean-path-order (S07, sound preset only): LEAN_PATH with the root lib dir first (same entries);
#                  fast-exact (S04, sound preset only): every lean gets --plugin=libLightFastExact.so (build/plugins/
#                  LightFastExact.lean, compiled per run with the toolchain that runs the modules): 'with_unfolding_all
#                  exact (x :)' / 'exact (by with_unfolding_all ..)' close the goal after the KERNEL's isDefEq instead of the
#                  Meta unifier's (falls back to the official tactic otherwise); only sound with a full kernel re-check
# build/build.sh --preflight TOOLCHAIN_PREFIX
#
# The FAST build = the exact `lean` invocations of the official `lake build`, run by a plain DAG scheduler instead of
# Lake's job engine (Lake 4.33.1 spends ~72% of all CPU on its own bookkeeping on a 175k-module project; see README).
#   1. planner (build/planner/Planner.lean, compiled here with the pinned OFFICIAL toolchain against its own libLake.a)
#      loads the workspace with Lake's OWN code (lakefile.toml/.lean, manifest, dependencies), resolves the default
#      targets like `lake build`, discovers modules (Lake's globs/roots/srcDir), parses headers (Lean.parseImports'),
#      resolves imports (Workspace.findModule?) and takes per module Lake's leanArgs/weakLeanArgs/leanOptions/package
#      id/output paths; it writes, per root-package module, the argv of Lake's compileLeanModule and the exact
#      setup.json text (importArts: see README "importArts"). Anything it cannot reproduce exactly -> DECLINE.
#   2. per-run checks that make importArts={} exactly equivalent (no olean name collision between LEAN_PATH roots, no
#      stray .ir.sig next to a non-module dependency olean) -> else DECLINE.
#   3. dependency packages must be up to date by Lake's OWN check: `lake build --no-build +M...` for every dependency
#      module imported by the project (official lake, same sandbox) -> else DECLINE (the official build would rebuild).
#   4. build/sched.py runs the lean invocations (same sandbox, env, cwd, LEAN_PATH, argv, setup files as Lake).
# Sandboxes: the BUILD (untrusted project code) runs in exactly build/official-build.sh's sandbox, no extra bind: the plan is
# passed on stdin, sched.py as `python3 -I -c`, the records come back on stdout. Planner and plancheck (no project code
# runs in them: a root lakefile.lean is declined, the TOML config is data, dependency lakefiles are the trusted pinned
# workspace's) get the same sandbox + a writable bind of the log dir; the dependency check runs without it.
# Never: retries, skipped checks, edited sources, build-time options, reuse of shipped .lake state.
# Exit: 0 = built; 1 = a module failed with lean's error exit (official `lake build` fails the same way: REJECTED);
#       2 = DECLINED / could not run (caller runs build/official-build.sh).
set -u
D=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)
PY=/usr/bin/python3

bindok() { # bindok SRC DST PROJ: a binds.tsv line this script may act on: plain absolute paths (no
  # control character, no empty/'.'/'..' component); DST strictly inside PROJ (dependency packages, lib/manifest.py) or
  # SRC = DST (a self-bind of the run's own helper dirs that this script appends: LOG/native, LOG/merge, the T1 tree, ...)
  local src=$1 dst=$2 proj=$3
  case "$src$dst" in *[[:cntrl:]]*) return 1 ;; esac
  case "$src" in /*) ;; *) return 1 ;; esac
  case "$dst" in /*) ;; *) return 1 ;; esac
  case "$src/" in */../*|*/./*|*//*) return 1 ;; esac
  case "$dst/" in */../*|*/./*|*//*) return 1 ;; esac
  [ "$src" = "$dst" ] && return 0
  [ -n "$proj" ] || return 1
  case "$dst" in "$proj"/?*) return 0 ;; esac
  return 1
}

mkbinds() { # mkbinds BINDFILE PROJ: create the dependency bind destinations ONCE, before any untrusted code runs:
  # never through a symlink (realpath = the path itself, before and after), never outside PROJ (bindok)
  local src dst
  while IFS=$'\t' read -r src dst; do
    [ -n "$src" ] || continue
    bindok "$src" "$dst" "$2" || return 2
    [ "$src" = "$dst" ] && continue
    [ "$(realpath -m -- "$dst")" = "$dst" ] || return 2
    mkdir -p -- "$dst" || return 2
    [ "$(realpath -e -- "$dst")" = "$dst" ] || return 2
  done < "$1"
}

sandbox() { # sandbox PROJ TC BINDFILE LOGDIR CMD...  (= official-build.sh sandbox [+ --bind LOGDIR if LOGDIR != ""])
  local proj=$1 tc=$2 binds=$3 logd=$4; shift 4
  local args=(--ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /tmp --dir /tmp/home
              --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv)
  # every other top-level directory except the system ones is hidden too (/scratch, /data, /mnt, /opt,
  # ...: service state dirs, sockets, FIFOs, other runs' and tenants' files); the run's own dirs are bound back below
  # (read-only after the binds below: only visibility changes, a write there fails with EROFS as before)
  local d ro=()
  for d in /*; do
    [ -d "$d" ] && [ ! -L "$d" ] || continue
    case "${d#/}" in bin|sbin|lib|lib32|lib64|libx32|usr|etc|dev|proc|sys|nix|gnu|home|root|tmp|run|var) ;; *) args+=(--tmpfs "$d"); ro+=(--remount-ro "$d") ;; esac
  done
  args+=(--ro-bind "$tc" "$tc")
  [ -n "$proj" ] && args+=(--bind "$proj" "$proj")
  if [ -n "$binds" ]; then
    while IFS=$'\t' read -r src dst; do
      [ -n "$src" ] || continue
      # no host-side mkdir here (mkbinds made the destinations before any untrusted code ran); a destination that
      # is missing or now reached through a symlink (planted by an earlier untrusted step) -> no sandbox (fail closed)
      bindok "$src" "$dst" "$proj" || return 2
      if [ "$src" = "$dst" ]; then [ -e "$src" ] || return 2
      else [ -d "$dst" ] && [ "$(realpath -e -- "$dst")" = "$dst" ] || return 2; fi
      args+=(--ro-bind "$src" "$dst")
    done < "$binds"
  fi
  [ -n "$logd" ] && args+=(--bind "$logd" "$logd")
  args+=(${ro[@]+"${ro[@]}"})
  args+=(--setenv PATH "$tc/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8
         --unshare-all --die-with-parent --new-session --chdir "${proj:-/}")
  env -i /usr/bin/bwrap "${args[@]}" -- "$@"
}

srcdigest() { "$PY" -I "$LOG/src/srcdigest.py" "$1"; }   # one sha256 over all non-.lake files + symlinks of PROJ

confined_path() { # confined_path PATH PROJ -> prints normpath(PATH) iff it is a plain absolute path strictly inside PROJ:
  # no control character, no '..' component, no symlink component (realpath of the existing prefix = the path)
  "$PY" -I -c '
import os, sys
p, proj = sys.argv[1], sys.argv[2]
if not p or any(ord(c) < 32 or 127 <= ord(c) <= 159 for c in p) or not os.path.isabs(p) or ".." in p.split("/"):
    sys.exit("not a plain absolute path: %r" % p)
n = os.path.normpath(p)
if not n.startswith(proj + os.sep) or os.path.realpath(n) != n:
    sys.exit("not inside %s (or through a symlink): %r" % (proj, p))
print(n)' "$1" "$2"
}

lpconfined() { # lpconfined FILE PROJ TC: every LEAN_PATH entry in FILE (computed from the UNTRUSTED lakefile) is a plain path
  # strictly inside PROJ (root lib dir, dependency packages bound under PROJ) or TC/lib/lean: the export stage acts on these
  # directories on the host (export/export.sh sizes the .olean files)
  "$PY" -I -c '
import os, sys
lp, proj, tc = open(sys.argv[1]).read().strip(), sys.argv[2], sys.argv[3]
for e in lp.split(":"):
    if not e or e == os.path.join(tc, "lib", "lean"):
        continue
    if any(ord(c) < 32 or 127 <= ord(c) <= 159 for c in e) or not os.path.isabs(e) or ".." in e.split("/"):
        sys.exit("LEAN_PATH entry is not a plain absolute path: %r" % e)
    n = os.path.normpath(e)
    if not n.startswith(proj + os.sep) or os.path.realpath(n) != n:
        sys.exit("LEAN_PATH entry outside the project %s (or through a symlink): %r" % (proj, e))' "$1" "$2" "$3"
}

RESOLVED_RE="[A-Za-z_][A-Za-z0-9_']*([.][A-Za-z_][A-Za-z0-9_']*)*"   # no empty component (`Main.`)
copy_out() { # copy_out SRC DST: copy a sandbox's output file to the host side, a regular file only (O_NOFOLLOW)
  "$PY" -I -c '
import os, shutil, stat, sys
fd = os.open(sys.argv[1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
if not stat.S_ISREG(os.fstat(fd).st_mode):
    sys.exit("not a regular file")
with os.fdopen(fd, "rb") as src, open(sys.argv[2], "wb") as dst:
    shutil.copyfileobj(src, dst)' "$1" "$2" 2>> "$LOG/build.log"
}
resolver_output() { # the resolver's answer is "DECLINE: ..." or a non-empty list of module names;
  # anything else (empty: the helper died, or a malformed line) -> DECLINE, never a silent fast path
  case "$1" in
    DECLINE:*) printf '%s\n' "$1" ;;
    *) if [ -n "$1" ] && printf '%s' "$1" | grep -qxE "$RESOLVED_RE( $RESOLVED_RE)*"; then printf '%s\n' "$1"
       else printf '%s\n' "DECLINE: unexpected target resolver output"; fi ;;
  esac
}
lake_target_modules() { # lake_target_modules PROJ "NAME..." BINDS -> the root modules `lake build NAME` builds, or
  # "DECLINE: why". Lake resolves a bare name as a target
  # declaration of ANY kind, then a package, then a module (Lake/CLI/Build.lean resolveTargetInWorkspace). The fast build
  # reproduces only the plain case and hands every other one to the official build (DECLINE):
  #   - NAME is a root [[lean_lib]] with roots (default [NAME]), no globs, no defaultFacets -> its roots;
  #   - NAME is no declaration and not the package name -> the module NAME;
  #   - anything else (a lean_exe / input_file / input_dir / extern_lib / any other table of that name, globs,
  #     defaultFacets, NAME = the package name, a guillemet name) -> DECLINE;
  #   - a lakefile.toml this strict line parser is not SURE about (single-quoted or multi-line strings, escapes, inline
  #     tables on target keys, comments with quotes, unknown line shapes) -> DECLINE.
  # Lake searches the WHOLE workspace (root first, then every dependency: Workspace.findTargetDecl?,
  # findPackageByName?, findTargetModule?), so the module case is taken only when no other workspace package can claim
  # NAME; otherwise DECLINE: any root [[require]] that is not a trusted workspace package (a path / source dependency, a
  # name not bound from the packages workspace, a require table this parser is unsure about); NAME = a root lean_exe root
  # (findTargetModule? tries exe roots first); NAME = any name, string or `name in a dependency's lakefile
  # (package / target / require names, roots, exe roots, globs: over-inclusive), or such a name is a prefix of NAME (a
  # dependency library that makes NAME buildable). BINDS = this run's binds.tsv (manifest.py: trusted SRC dirs).
  # Host-side read of the project's lakefile.toml: only a regular file inside PROJ (O_PATH, checked on the descriptor).
  "$PY" -I -c '
import os, re, stat, sys
proj, names, binds = os.path.realpath(sys.argv[1]), [sys.argv[2]], sys.argv[3]   # ONE name, unsplit
IDENT = r"[A-Za-z_][A-Za-z0-9_\x27]*(?:\.[A-Za-z_][A-Za-z0-9_\x27]*)*"   # plain ASCII components: toName.toString = itself
def bad(why):
    print("DECLINE: " + why); sys.exit(0)
try:
    pfd = os.open(os.path.join(proj, "lakefile.toml"), os.O_PATH | os.O_CLOEXEC)
    if not stat.S_ISREG(os.fstat(pfd).st_mode) or not os.readlink(f"/proc/self/fd/{pfd}").startswith(proj + "/"):
        bad("lakefile.toml is not a regular file inside the project")
    text = open(f"/proc/self/fd/{pfd}", encoding="utf-8", newline="").read()
except (OSError, UnicodeDecodeError) as e:
    bad(f"cannot read lakefile.toml ({e})")
# only LF / CRLF end a TOML line; str.splitlines() also breaks at U+2028 / U+2029 /
# U+0085 / VT / FF / FS-RS, which TOML allows inside comments. Split on LF only, and hand off on any character outside
# printable ASCII + TAB + LF (+ the CR of a CRLF): then this line parser and the TOML parser of Lake see the same lines.
if any(not (" " <= c <= "~" or c in "\t\n\r") for c in text) or "\r" in text.replace("\r\n", ""):
    bad("lakefile.toml has a non-ASCII or control character (Lake\x27s TOML line structure may differ from this parser\x27s)")
lines = text.replace("\r\n", "\n").split("\n")
if "«" in text or "»" in text:              # Lake decodes `«Main»` as Main
    bad("lakefile.toml uses guillemet-escaped names (Lake decodes them; this resolver compares raw spellings)")
STR = r"\"[^\"\\\\]*\""                       # a basic string without escapes
ARR = r"\[\s*(?:" + STR + r"\s*,\s*)*(?:" + STR + r")?\s*,?\s*\]"
HDR = re.compile(r"^(\[\[?)\s*([A-Za-z_][A-Za-z0-9_.]*)\s*(\]\]?)\s*(#[^\"\x27]*)?$")
KEY = re.compile(r"^([A-Za-z0-9_.\-]+)\s*=\s*(.*)$")
tables, cur, top, pend = [], None, {}, None
for raw in lines:
    ln = raw.strip()
    if pend is not None:                      # a multi-line array of basic strings
        pend[1] += " " + ln
        if "]" in ln:
            v = pend[1].split("#", 1)[0].strip() if "#" in pend[1] and "\"" not in pend[1].split("#", 1)[1] else pend[1]
            if not re.fullmatch(ARR, v.strip()):
                bad("unsure about a multi-line array in lakefile.toml")
            pend[0][pend[2]] = [x[1:-1] for x in re.findall(STR, v)]; pend = None
        continue
    if not ln or ln.startswith("#"):
        continue
    if "\x27" in ln or "\"\"\"" in ln or "\\" in ln:   # one backslash in Python: any escape
        bad("lakefile.toml uses literal / multi-line strings or escapes")
    m = HDR.match(ln)
    if m:
        if (m.group(1) == "[[") != (m.group(3) == "]]"):
            bad("unsure about a table header in lakefile.toml")
        cur = {"_t": m.group(2), "_aot": m.group(1) == "[["}
        tables.append(cur); continue
    m = KEY.match(ln)
    if not m:
        bad("unsure about a line of lakefile.toml")
    k, v = m.group(1), m.group(2).strip()
    if "#" in v:                               # a trailing comment (no quote inside it)
        head, tail = v.rsplit("#", 1)
        if "\"" in tail:
            bad("unsure about a comment in lakefile.toml")
        if head.count("\"") % 2 == 0:
            v = head.strip()
    tgt = top if cur is None else cur
    if re.fullmatch(STR, v):
        tgt[k] = v[1:-1]
    elif v.startswith("[") and "]" not in v:
        pend = [tgt, v, k]
    elif re.fullmatch(ARR, v):
        tgt[k] = [x[1:-1] for x in re.findall(STR, v)]
    elif re.fullmatch(r"true|false|[0-9][0-9_]*", v) or (v.startswith("{") and v.endswith("}") and v.count("{") == v.count("}")):
        tgt[k] = ("<opaque>", v)
    else:
        bad("unsure about a value in lakefile.toml")
if pend is not None:
    bad("unterminated array in lakefile.toml")
def claims(mod, skip=None):                   # root libraries that MAY make mod buildable (over-approximation of
    k = 0                                     # LeanLibConfig.isBuildableModule: a root or glob base equal to / prefix of mod)
    for t in tables:
        if t is skip or t["_t"] != "lean_lib":
            continue
        nm = t.get("name")
        roots, globs = t.get("roots", [nm]), t.get("globs", [])
        if not isinstance(nm, str) or not isinstance(roots, list) or not isinstance(globs, list):
            bad("unsure about a lean_lib (name / roots / globs)")
        if not all(isinstance(g, str) and re.fullmatch(IDENT + r"(?:\.[*+])?", g) for g in globs):   # (Sub.** etc.)
            bad(f"lean_lib {nm}: a glob this resolver does not model exactly")
        bases = list(roots) + [g[:-2] if g.endswith((".*", ".+")) else g for g in globs]
        if any(b == mod or mod.startswith(b + ".") for b in bases):
            k += 1
    return k
def exe_root(mod):                            # a root lean_exe whose root (default: its name) is mod, or unsure
    for t in tables:
        if t["_t"] == "lean_exe":
            r = t.get("root", t.get("name"))
            if not isinstance(r, str) or r == mod:
                return True
    return False
def read_binds():
    srcs, trusted = [], set()
    try:
        for ln in open(binds, encoding="utf-8").read().splitlines():
            f = ln.split("\t")
            if len(f) != 2:
                bad("unsure about binds.tsv")
            srcs.append(f[0]); trusted.add(os.path.basename(f[1]))
    except (OSError, UnicodeDecodeError) as e:
        bad(f"cannot read binds.tsv ({e})")
    return srcs, trusted
def require_check():                          # for EVERY shape: a [[require]] that is
    srcs, trusted = read_binds()              # not a trusted workspace package (path / source / unknown name) joins the
    if any(k.split(".")[0] == "require" for k in top):   # workspace with its own config (a lakefile.lean runs code) -> hand off
        bad("unsure about a require key in lakefile.toml")
    for t in tables:
        if t["_t"].split(".")[0] == "require":
            if t["_t"] != "require" or not t["_aot"] or "path" in t or "source" in t:
                bad("the project requires a path / source dependency (its config joins the workspace)")
            if set(t) - {"_t", "_aot", "name", "scope", "version", "rev", "git", "subDir", "options"}:
                bad("unsure about a [[require]] table")
            if not isinstance(t.get("name"), str) or t["name"] not in trusted:
                bad(f"the project requires {t.get(chr(110) + chr(97) + chr(109) + chr(101))!r}, not a trusted workspace package")
def ws_claims(n):                             # see the comment above
    srcs, trusted = read_binds()
    for t in tables:
        if t["_t"] == "lean_exe" and (not isinstance(t.get("root", t.get("name")), str) or t.get("root", t.get("name")) == n):
            bad(f"{n} is (or may be) the root of a lean_exe: the official build resolves the executable root first")
    toks = set(trusted) | {os.path.basename(x) for x in srcs}
    for d in srcs:
        got = False
        for cf in ("lakefile.lean", "lakefile.toml"):
            try:
                txt = open(os.path.join(d, cf), encoding="utf-8").read()
            except FileNotFoundError:
                continue
            except (OSError, UnicodeDecodeError) as e:
                bad(f"cannot read the workspace package config {d}/{cf} ({e})")
            got = True
            toks.update(re.findall(r"\"([^\"\n]*)\"", txt)); toks.update(re.findall(r"\x27([^\x27\n]*)\x27", txt))
            if cf == "lakefile.lean":
                toks.update(re.findall(r"`+(«[^»\n]*»|[^\s,()\[\]{}⟩⟨`]+)", txt))
                toks.update(re.findall(r"(?m)^\s*(?:@\[[^\]\n]*\]\s*)?(?:package|lean_lib|lean_exe|target|input_file|input_dir|"
                                       r"extern_lib|require)\s+(«[^»\n]*»|[^\s:]+)", txt))
        if not got:
            bad(f"no lakefile in the workspace package {d}")
    for tok in toks:
        tf = tok.replace("«", "").replace("»", "").strip()
        if tf and (n == tf or n.startswith(tf + ".")):
            bad(f"{n}: a workspace dependency declares or provides {tok!r} (Lake resolves the bare name across the workspace)")
if "packagesDir" in top:                     # where Lake looks for the bound dependencies
    bad("lakefile.toml sets packagesDir")
require_check()
out = []
for n in names:
    if "«" in n or "»" in n:
        bad(f"{n}: guillemet names are not resolved here")
    # only a name made of plain ASCII identifier components, whose canonical spelling
    # (toName.toString, what the official comparator passes to Lake) is itself: no whitespace, no empty / numeric
    # component (`Main.`, `Main.01`), no guillemets, no Lake target-spec syntax (@ + / :); anything else -> official build
    if not re.fullmatch(IDENT, n):
        bad(f"{n!r}: not a plain identifier name (its canonical spelling may differ, or Lake spec syntax)")
    # Lake/CLI/Build.lean resolveTargetBaseSpec: if PROJ/NAME exists (realPath: symlinks followed)
    # and is not a directory, `lake build NAME` builds the module whose SOURCE is that file (findModuleBySrc?); a
    # directory resolves like the bare name. Anything at PROJ/NAME other than a real directory -> hand off.
    pth = os.path.join(proj, n)
    if os.path.lexists(pth) and (os.path.islink(pth) or not os.path.isdir(pth)):
        bad(f"{n}: the project has a non-directory (or symlink) at ./{n}, which Lake resolves as a path")
    decl = [t for t in tables if t.get("name") == n or t.get("name") == ("<opaque>", n)]
    if decl:
        t = decl[0]
        if len(decl) > 1 or t["_t"] != "lean_lib" or not t["_aot"]:
            bad(f"{n} is declared as [[{t[chr(95) + chr(116)]}]]: the official build resolves that target")
        if "globs" in t or "defaultFacets" in t or "extraDepTargets" in t:
            bad(f"lean_lib {n} has globs / defaultFacets / extraDepTargets")
        roots = t.get("roots", [n])
        if not isinstance(roots, list) or not roots or not all(re.fullmatch(IDENT, x) for x in roots):
            bad(f"lean_lib {n}: unsure about its roots")
        if n not in roots:   # `lake build NAME` must produce the module NAME
            bad(f"lean_lib {n} does not have the module {n} among its roots {roots}: the official build may not produce it")
        for r in roots:
            if claims(r, skip=t) or exe_root(r):
                bad(f"module {r} of lean_lib {n} is also claimed by another root target (another library context)")
        out += roots
    elif top.get("name") == n:
        bad(f"{n} is the package name: the official build builds its default targets")
    else:
        ws_claims(n)
        if claims(n) != 1:   # over-approximated: exactly one root library may make NAME buildable
            bad(f"module {n} is claimed by {claims(n)} root libraries (by roots / globs): unsure which one Lake builds")
        out.append(n)
print(" ".join(dict.fromkeys(out)))' "$@"
}

hostcc_for() { # hostcc_for TC -> prints a host C compiler iff TC's bundled clang cannot run here (D21: the official 4.33.1
  # clang loads lib/libLLVM.so.22.1 = GLIBC_2.29, so leanc fails on RHEL 8 / Ubuntu 18.04 / Debian 10 / CentOS 7); leanc then
  # compiles with LEAN_CC=<it> (it drops its bundled-clang-only flags) and the callers add -L TC/lib (static GMP/libuv/OpenSSL)
  [ -x "$1/bin/clang" ] && env -i PATH=/usr/bin:/bin "$1/bin/clang" --version > /dev/null 2>&1 && return 0
  local c; for c in /usr/bin/cc /usr/bin/gcc /usr/bin/clang; do [ -x "$c" ] && { echo "$c"; return 0; }; done
}

compile_fastexact() { # compile_fastexact MODULE_TC OFFICIAL_TC OUTDIR SRC -> OUTDIR/libLightFastExact.so (B3 item fast-exact,
  # S04). The C code is generated by the lean that runs the modules (MODULE_TC: official or e.g. T1), so it matches that
  # lean's library; it is compiled and linked by the OFFICIAL toolchain's leanc (bundled clang/lld: works on hosts without a
  # system clang, which the T1 trees' leanc needs; T1's lean.h equals the official one), against MODULE_TC's libleanshared
  # (the library the plugin is loaded into). A smoke test then loads it into the module lean and checks that it acts.
  local tc=$1 otc=$2 o=$3 src=$4
  mkdir -p "$o" || return 1
  env -i PATH=/usr/bin:/bin LEAN_PATH="$tc/lib/lean" "$tc/bin/lean" -R "$(dirname "$src")" -c "$o/LightFastExact.c" "$src" \
    > "$o/compile.log" 2>&1 || return 1
  local hcc; hcc=$(hostcc_for "$otc")
  env -i PATH=/usr/bin:/bin ${hcc:+LEAN_CC=$hcc} "$otc/bin/leanc" -c -O3 -DNDEBUG -DLEAN_EXPORTING -I"$tc/include" -o "$o/LightFastExact.o" \
    "$o/LightFastExact.c" >> "$o/compile.log" 2>&1 || return 1
  env -i PATH=/usr/bin:/bin ${hcc:+LEAN_CC=$hcc} "$otc/bin/leanc" -shared -o "$o/libLightFastExact.so" "$o/LightFastExact.o" -L"$tc/lib/lean" \
    -lleanshared ${hcc:+-L"$otc/lib"} >> "$o/compile.log" 2>&1 || return 1
  # smoke test (our own two-line file, not project code): the module lean loads the plugin and both fast paths act
  mkdir -p "$o/smoke" || return 1
  printf 'def fxU (n : Nat) := n + 0\ntheorem fxSmoke (n : Nat) (h : n = 3) : fxU n = 3 := by\n  exact (by with_unfolding_all exact (h :))\n' \
    > "$o/smoke/FxSmoke.lean" || return 1
  (cd "$o/smoke" && env -i PATH=/usr/bin:/bin LIGHT_FASTEXACT_DEBUG=1 "$tc/bin/lean" --plugin="$o/libLightFastExact.so" \
    FxSmoke.lean > smoke.log 2>&1) || return 1
  grep -q '^fx: ok' "$o/smoke/smoke.log" && grep -q '^fx-outer: ok' "$o/smoke/smoke.log" || return 1
}

compile_planner() { # compile_planner TC OUTDIR [SRC] -> OUTDIR/planner (official toolchain only)
  local tc=$1 o=$2 src=${3:-$D/build/planner/Planner.lean} k= c=
  mkdir -p "$o" || return 1
  if [ -n "${BCACHE:-}" ]; then   # (D04) --build-cache: the planner compiled earlier from the same source + toolchain
    k=$("$PY" -I "$D/build/bcache.py" key "@$src" "$tc/bin/lean" "$tc/bin/leanc" "$tc/lib/lean/libLake.a" 2>/dev/null); c=$BCACHE/planner-$k
    if [ -n "$k" ] && [ -f "$c/planner" ] && [ -f "$c/planner.sha256" ] && cp -- "$c/planner" "$o/planner.tmp" 2>/dev/null \
       && [ "$(sha256sum "$o/planner.tmp" | cut -d' ' -f1)" = "$(cat "$c/planner.sha256")" ]; then
      chmod 755 "$o/planner.tmp" && mv -f "$o/planner.tmp" "$o/planner" && echo "planner: from the build cache $c" > "$o/planner.compile.log" && return 0
    fi
    rm -f "$o/planner.tmp"
  fi
  env -i PATH=/usr/bin:/bin LEAN_PATH="$tc/lib/lean" "$tc/bin/lean" -R "$(dirname "$src")" -c "$o/planner.c" "$src" \
    > "$o/planner.compile.log" 2>&1 || return 1
  local hcc; hcc=$(hostcc_for "$tc")
  env -i PATH=/usr/bin:/bin ${hcc:+LEAN_CC=$hcc} "$tc/bin/leanc" -O1 "$o/planner.c" -o "$o/planner" -L"$tc/lib/lean" -lLake -rdynamic \
    ${hcc:+-L"$tc/lib"} >> "$o/planner.compile.log" 2>&1 || return 1
  if [ -n "$k" ]; then   # store: private temp dir in the cache, then rename (concurrent runs: last writer wins, both valid)
    local t; t=$(mktemp -d "$BCACHE/.planner.XXXXXX" 2>/dev/null) && cp -- "$o/planner" "$t/planner" \
      && sha256sum "$o/planner" | cut -d' ' -f1 > "$t/planner.sha256" && { rm -rf "$c"; mv -T "$t" "$c" 2>/dev/null; }
    [ -n "${t:-}" ] && rm -rf "$t"
  fi
  return 0
}

# Lake releases the planner is ported to.  VALIDATED_LAKE: the planner is an exact
# port (B1/B2/B3).  SOUND_LAKE437: Lake 4.37.0-rc1, planned by Planner435.lean (A03: Lake 4.35's fetchTransImportArts
# walk with allVisited/metaVisited, declines for precompileImports / precompiled libraries; Lake 4.36 -> 4.37: the walk, the
# module setup and compileLeanModule's argv are unchanged, only the build store snapshot and cache plumbing changed),
# accepted for the UNTRUSTED sound build only (B3 + sound-fast-path) until its exactness is validated.
VALIDATED_LAKE="819816b2e0a3bf405af45ae5c7af2491d8f5bee6"   # Lean/Lake 4.33.1 release
SOUND_LAKE437="0b77e12952ad39077d80d8bd6b66d601f225c321"    # Lean/Lake 4.37.0-rc1 release (Planner435.lean)
SOUND_LAKE436="611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"    # Lean/Lake 4.36.0 release (Planner435.lean; A03: b1cmp SAME, 49-project sweep 0 DIFFERENT)
planner_src_for() { # TC DIR -> DIR/Planner435.lean for a SOUND_LAKE437 toolchain, else DIR/Planner.lean
  local gh; gh=$(env -i "$1/bin/lean" --githash 2>/dev/null)
  case " $SOUND_LAKE437 $SOUND_LAKE436 " in *" $gh "*) [ -n "$gh" ] && { echo "$2/Planner435.lean"; return 0; } ;; esac
  echo "$2/Planner.lean"
}

# The whole run is one function: bash parses it completely before executing it, so editing this file while a run is in
# progress cannot change the running script (bash otherwise reads scripts incrementally).
main() {
  if [ "${1:-}" = --preflight ]; then
    TC=$(readlink -f "${2:?toolchain prefix}"); BCACHE=
    # (D04) optional --build-cache DIR: a planner compiled earlier from the same source + toolchain proves "it compiles"
    if [ "${3:-}" = --build-cache ] && [ -n "${4:-}" ] && "$PY" -I "$D/build/bcache.py" check-dir "$4"; then BCACHE=$4; fi
    "$D/build/official-build.sh" --preflight "$TC" || exit 1
    t=$(mktemp -d /tmp/fv-planner.XXXXXX) || exit 1
    compile_planner "$TC" "$t" "$(planner_src_for "$TC" "$D/build/planner")" || { echo "build.sh: preflight: planner does not compile" >&2; cat "$t/planner.compile.log" >&2; rm -rf "$t"; exit 1; }
    rm -rf "$t"; exit 0
  fi

  [ $# -ge 3 ] || { sed -n 2,4p "$0" >&2; exit 2; }
  PROJ=$(readlink -f "$1"); WS=$2; TC=$(readlink -f "$3"); shift 3
  REQMODS=; CLOSURE=; BCACHE=; MLATE=0; MLPID=; JSON=; LPOUT=; LOG=; TIMEOUT=0; THREADS=$(nproc); PLANONLY=0; PRESET=B1; UNSAFE=; NATIVE=0; POFF=0; SFP=0; MERGE=0; MERGE_ARGS=; FASTEXACT=0; ZYGOTE=0
  while [ $# -gt 0 ]; do
    case "$1" in
      --threads) THREADS=$2; shift 2 ;;
      --json) JSON=$2; shift 2 ;;
      --lean-path-out) LPOUT=$2; shift 2 ;;
      --log) LOG=$2; shift 2 ;;
      --timeout) TIMEOUT=$2; shift 2 ;;
      --plan-only) PLANONLY=1; shift ;;   # testing: stop after plan + checks + dependency check (exit 0 = would build fast)
      --preset) PRESET=$2; shift 2 ;;
      --unsafe) UNSAFE=$2; shift 2 ;;
      --build-cache) BCACHE=$2; shift 2 ;;   # (D04) opt-in private cache of untrusted helpers (build/bcache.py)
      --require-modules) REQMODS=$2; shift 2 ;;   # the comparator's module(s):
                                                  # not in the plan, or a failure only outside their import closure -> DECLINE
      *) echo "build.sh: unknown argument $1" >&2; exit 2 ;;
    esac
  done
  case "$THREADS" in ''|*[!0-9]*|0) echo "build.sh: bad --threads" >&2; exit 2 ;; esac
  # (D04) memory-limited cgroup (e.g. a CI runner / laptop budget via cgrun): the scheduler's memory floor must see the cgroup's
  # memory.max - memory.current (MemAvailable is the host's); pass every limited cgroup of this process's chain (host paths)
  CGOPTS=(); CGD=$(sed -n 's/^0:://p' /proc/self/cgroup 2>/dev/null | head -1)
  if [ -n "$CGD" ]; then
    CGD=/sys/fs/cgroup${CGD%/}
    while [ -n "$CGD" ] && [ "$CGD" != /sys/fs/cgroup ] && [ "${CGD#/sys/fs/cgroup}" != "$CGD" ]; do
      { [ -r "$CGD/memory.max" ] && [ "$(cat "$CGD/memory.max" 2>/dev/null)" != max ]; } && CGOPTS+=(--cgroup "$CGD")
      CGD=${CGD%/*}
    done
  fi
  if [ -n "${BCACHE:-}" ] && ! "$PY" -I "$D/build/bcache.py" check-dir "$BCACHE"; then
    echo "build.sh: --build-cache $BCACHE is not a private directory of this user: no cache" >&2; BCACHE=
  fi
  SCHED_OPTS=(${CGOPTS[@]+"${CGOPTS[@]}"}); PLANNER_ARGS=()
  # (D22/A03) githash of the project's official toolchain, needed early: an unofficial toolchain (toolchain-T1) is a build of
  # ONE release and can only build projects of that release (its .olean files carry its githash)
  GH=$(env -i "$TC/bin/lean" --githash 2>/dev/null) || GH=
  T1_NA=
  # B3 = B2 + the --unsafe items (the orchestrator passes --preset B3 --unsafe LIST)
  case "$PRESET" in B1) ;; B2|B3) SCHED_OPTS+=(--early-release) ;; *) echo "build.sh: unknown --preset $PRESET" >&2; exit 2 ;; esac
  if [ "$PRESET" = B3 ] && [ -z "$UNSAFE" ]; then echo "build.sh: --preset B3 needs --unsafe LIST" >&2; exit 2; fi
  if [ "$PRESET" != B3 ] && [ -n "$UNSAFE" ]; then echo "build.sh: --unsafe needs --preset B3" >&2; exit 2; fi
  UNSAFE_JSON="[]"
  if [ -n "$UNSAFE" ]; then
    IFS=, read -r -a UL <<< "$UNSAFE"
    for u in "${UL[@]}"; do
      case "$u" in
        skip-kernel-tc|skipkerneltc) SCHED_OPTS+=(--extra-arg -Ddebug.skipKernelTC=true) ;;
        skip-kernel-tc=except-translate)   # (D04) as skip-kernel-tc, but modules whose source mentions to_additive/to_dual keep
          # the build-time kernel check (Mathlib's translation uses kernel errors as control flow: G1-ML-1/2); sched.py decides per module
          SCHED_OPTS+=(--extra-arg -Ddebug.skipKernelTC=true --ktc-exempt-translate) ;;
        linter-off|nolinters) SCHED_OPTS+=(--extra-arg -Dlinter.all=false) ;;
        early-release) ;;   # B2's exact early release is already on in B3 (041-fixed rule)
        native-pkg|native) NATIVE=1 ;;   # (015 057) package C code compiled into one lib, --load-dynlib once ready
        sound-fast-path) SFP=1; SCHED_OPTS+=(--no-src-check) ;;   # (S07) untrusted, sound preset: skip exactness-only guards (plancheck, Lake dependency check, source digests)
        sound-fast-path=importarts-empty) SFP=1; SCHED_OPTS+=(--no-src-check); PLANNER_ARGS=(--import-arts-empty) ;;   # (V07) as sound-fast-path + setup.json importArts={} for module-system importers too: no up-front transitive importArts walk (whole Mathlib: planner 104-135 s -> <1 s, plan 5.4 GB -> MBs); lean resolves imports via LEAN_PATH (untrusted build only)
        check-tail|check-tail=*)   # (S07) untrusted, sound preset: long kernel-check jobs per module (build order for the targeted check)
          CT=${u#check-tail}; CT=${CT#=}; [ -n "$CT" ] || CT=$D/build/hints/rh-check-tail.json.gz
          [ -f "$CT" ] || { echo "build.sh: --unsafe check-tail: no file $CT" >&2; exit 2; }
          CTCOPY=$CT ;;
        cost-hints|cost-hints=*)   # (S07) untrusted, sound preset: per-module costs of an earlier run of the same project (order / j1 slack only)
          CH=${u#cost-hints}; CH=${CH#=}; [ -n "$CH" ] || CH=$D/build/hints/rh-build-costs.json.gz
          [ -f "$CH" ] || { echo "build.sh: --unsafe cost-hints: no file $CH" >&2; exit 2; }
          CHCOPY=$CH ;;
        premise-off) POFF=1 ;;   # (S07) untrusted, sound preset: setup.json imports += FastverifyPremiseOff (no premise-selection metadata at olean write)
        lean-path-order) SCHED_OPTS+=(--lean-path-order project-first) ;;   # (S07) untrusted, sound preset: root lib first in LEAN_PATH (same files, fewer failed probes)
        fast-exact) FASTEXACT=1 ;;   # (S04) untrusted, sound preset only: kernel defeq in with_unfolding_all exact
        deny-line|deny) echo "build.sh: --unsafe $u is not offered by build.sh (it edits sources; legacy pipeline only, see build/README.md Menu)" >&2; exit 2 ;;
        retries) SCHED_OPTS+=(--retry-exact) ;;
        merge|merge=*) MERGE=1; MERGE_ARGS=${u#merge}; MERGE_ARGS=${MERGE_ARGS#=} ;;   # (S02) untrusted: sound preset only
        closure-only=?*) CLOSURE=${u#closure-only=} ;;   # (A05/A03, ported by D22) untrusted, sound preset: plan and build only the import closure of MODULE[+MODULE..] (planner --targets), as the official lake comparator builds only the solution module
        closure-only|closure-only=) echo "build.sh: --unsafe closure-only needs =MODULE (bin/fastverify fills in the solution module)" >&2; exit 2 ;;
        toolchain-T1|toolchain-T1=*)   # opt-in UNSAFE patched/PGO lean for the modules
          T1DIR=/scratch/fastverify-next/tc; T1N=${u#toolchain-T1}; T1N=${T1N#=}; T1=; T1BASE=0
          for n in ${T1N:-lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo}; do
            # (D22/A03) candidates built from another release are skipped (manifest lean_version must name this githash)
            "$PY" -I -c 'import json,sys; sys.exit(0 if sys.argv[2] and ("commit " + sys.argv[2]) in json.load(open(sys.argv[1])).get("lean_version", "") else 1)' \
              "$D/toolchains/unofficial/$n.json" "$GH" 2>/dev/null || continue
            T1BASE=1
            st=
            if [ -n "${BCACHE:-}" ]; then   # (D04) tree fingerprint unchanged since a full verification on this host: no re-hash
              st=$("$PY" -I "$D/build/bcache.py" stamps "$T1DIR/$n" "$D/toolchains/unofficial/$n.json" "$D/lib/toolchain.py" 2>/dev/null)
              if [ -n "$st" ] && [ -f "$BCACHE/t1-$n.stamps" ] && [ "$(cat "$BCACHE/t1-$n.stamps")" = "$st" ]; then T1=$n; break; fi
            fi
            if "$PY" -I "$D/lib/toolchain.py" verify-unofficial "$T1DIR/$n" "$n" > /dev/null 2>&1; then
              T1=$n
              [ -n "$st" ] && printf '%s\n' "$st" > "$BCACHE/t1-$n.stamps.$$" && mv -f "$BCACHE/t1-$n.stamps.$$" "$BCACHE/t1-$n.stamps"
              break
            fi
          done
          if [ -z "$T1" ] && [ "$T1BASE" = 0 ] && [[ ",$UNSAFE," == *",sound-fast-path"* ]]; then
            # (D22/A03, sound build only) no unofficial toolchain exists for this project's release: the item is a speed-up of
            # an untrusted stage, so the official lean builds instead (the zygote items are dropped below: they need T1)
            T1_NA=1; echo "build.sh: toolchain-T1 not applicable: no pinned unofficial toolchain for release $GH (official lean)" >&2; continue
          fi
          [ -n "$T1" ] || { echo "build.sh: --unsafe toolchain-T1: no pinned unofficial toolchain verifies and starts on this host (${T1N:-pgo, nopgo})" >&2; exit 2; }
          SCHED_OPTS+=(--lean "$T1DIR/$T1/bin/lean"); UNSAFE_T1=$T1 ;;
        zygote|zygote=*)   # sound build (build/README.md): one lean that read the immutable package imports once
          # (BASE, default Mathlib), package oleans >= THPKB KB copied into anonymous huge-page windows (0 = file maps),
          # REPL replicas; needs a zygote-capable lean (toolchain-T1=lean4-s01zy-...); otherwise zyc runs plain lean
          ZS=${u#zygote}; ZS=${ZS#=}; IFS=: read -r ZB ZT ZR <<< "${ZS:-Mathlib:1:24}"
          ZYGOTE=1; SCHED_OPTS+=(--zygote "${ZB:-Mathlib}" --zygote-thp "${ZT:-1}" --zygote-replicas "${ZR:-24}") ;;
        zygote-prefix|zygote-prefix=*)   # sound build (S01): the zygote also imports PREFIX (default Mathlib) completely; a
          # child whose import continues it reuses the prefix import state (needs zygote + a toolchain with prefix support;
          # any other import exits 211 -> plain lean)
          ZP=${u#zygote-prefix}; ZP=${ZP#=}; SCHED_OPTS+=(--zygote-prefix "${ZP:-Mathlib}") ;;
        j1-saturated) SCHED_OPTS+=(--j1-when-saturated) ;;   # sound build (S01): -j1 while every slot has a ready module
        *) echo "build.sh: unknown --unsafe item $u (skip-kernel-tc[=except-translate], linter-off, retries, closure-only=MOD[+MOD], toolchain-T1[=NAME], merge[=ARGS], fast-exact, premise-off, lean-path-order, sound-fast-path, cost-hints[=FILE], check-tail[=FILE], zygote[=BASE:THPKB:REPL], zygote-prefix[=MODS], j1-saturated)" >&2; exit 2 ;;
      esac
    done
    # startup probe: the zygote items need a zygote-capable lean (the s01zy trees). If
    # toolchain-T1 resolved to another tree (e.g. lean4-7586a50cec-nopgo on a glibc 2.35 host where the s01zy/pgo trees
    # cannot start) or to none, drop the zygote options instead of starting a zygote that never comes up and wrapping every
    # module in the zygote client (availability/time only; the build stays the untrusted build).
    # (D04, E29) and the zygote materializes the package imports once: Mathlib = 60-75 GB whatever the thread count (D09). Below a
    # 96 GB memory budget (min of MemAvailable and memory.max - memory.current of every limited cgroup in CGOPTS) it is
    # OOM-killed and the run ends without a verdict (laptop / CI runner, D04's budget table) -> drop the zygote items there
    # too (sound-auto's autotune uses the same 96 GB rule); the build stays the untrusted build, only slower than with it
    ZYMEM=$(awk '/^MemAvailable:/ {print int($2 / 1048576)}' /proc/meminfo 2>/dev/null); ZYMEM=${ZYMEM:-0}
    for ((i = 1; i < ${#CGOPTS[@]}; i += 2)); do
      m=$(cat "${CGOPTS[$i]}/memory.max" 2>/dev/null); c=$(cat "${CGOPTS[$i]}/memory.current" 2>/dev/null)
      case "$m$c" in ''|*[!0-9]*) ;; *) m=$(( (m - c) / 1073741824 )); [ "$m" -lt "$ZYMEM" ] && ZYMEM=$m ;; esac
    done
    if [ "$ZYGOTE" = 1 ] && [ "$ZYMEM" -lt 96 ]; then UNSAFE_T1_ZY=nomem; else UNSAFE_T1_ZY=${UNSAFE_T1:-}; fi
    if [ "$ZYGOTE" = 1 ]; then
      case "$UNSAFE_T1_ZY" in
        lean4-s01zy-*) ;;
        *) if [ "$UNSAFE_T1_ZY" = nomem ]; then
             echo "build.sh: zygote items dropped: memory budget ${ZYMEM} GB < 96 GB (the zygote's Mathlib import alone needs 60-75 GB)" >&2
           else
             echo "build.sh: zygote items dropped: the module lean (${UNSAFE_T1:-official}) has no zygote support" >&2
           fi
           ZYGOTE=0; NO=()
           while [ ${#SCHED_OPTS[@]} -gt 0 ]; do
             case "${SCHED_OPTS[0]}" in
               --zygote|--zygote-thp|--zygote-replicas|--zygote-prefix) SCHED_OPTS=("${SCHED_OPTS[@]:2}") ;;
               *) NO+=("${SCHED_OPTS[0]}"); SCHED_OPTS=("${SCHED_OPTS[@]:1}") ;;
             esac
           done
           SCHED_OPTS=("${NO[@]}"); ZYDROP=1 ;;
      esac
    fi
    UNSAFE_JSON=$("$PY" -I -c 'import json,sys; print(json.dumps([(("toolchain-T1:" + sys.argv[2]) if sys.argv[4] != "1" else "toolchain-T1:not-applicable(release)") if x.startswith("toolchain-T1") else x for x in sys.argv[1].split(",") if not (sys.argv[3] == "1" and x.split("=")[0] in ("zygote", "zygote-prefix"))]))' "$UNSAFE" "${UNSAFE_T1:-}" "${ZYDROP:-0}" "${T1_NA:-0}")
  fi
  [ -n "$LOG" ] || LOG=$PROJ/../log-fast
  mkdir -p "$LOG"; LOG=$(readlink -f "$LOG")
  case "$LOG/" in "$PROJ/"*) echo "build.sh: the log dir must be outside the project" >&2; exit 2 ;; esac
  # snapshot of this stage's helper sources for the whole run (the package may be edited while a run is in progress)
  mkdir -p "$LOG/src" && cp "$D/build/planner/Planner.lean" "$D/build/planner/Planner435.lean" "$D/build/plancheck.py" "$D/build/sched.py" "$D/build/srcdigest.py" "$D/build/native.sh" "$D/build/premiseoff/premiseoff.py" "$D/build/mergeplan.py" "$D/build/plugins/LightFastExact.lean" "$D/build/zyc.c" "$LOG/src/" \
    || { echo "build.sh: cannot snapshot helper sources" >&2; exit 2; }
  T0=$(date +%s.%N)
  emit() { # status exit detail
    local sec; sec=$(echo "$(date +%s.%N) - $T0" | bc)
    local line; line=$("$PY" -I -c 'import json,sys; u=json.loads(sys.argv[7]); print(json.dumps({"stage":"build","mode":"fast","tool":"Lake-planned direct scheduler" + (" (official lean)" if not u else " (UNSAFE options)"),"preset":sys.argv[6],"unsafe":u,"exact":not u,"status":sys.argv[1],"exit":int(sys.argv[2]),"detail":sys.argv[3],"seconds":float(sys.argv[4]),"log":sys.argv[5]}))' "$1" "$2" "$3" "$sec" "$LOG" "$PRESET" "$UNSAFE_JSON")
    echo "$line"; [ -n "$JSON" ] && echo "$line" > "$JSON"
  }
  FINAL=
  decline() { FINAL=1; emit DECLINED 2 "$1"; exit 2; }
  # Any exit that does not go through an explicit verdict below (a `set -u` error, an internal failure, a signal) is a
  # DECLINE (exit 2), never a REJECT: only the explicit FAILED path exits 1.
  on_exit() { local rc=$?; if [ -z "$FINAL" ]; then FINAL=1; emit DECLINED 2 "internal error (exit $rc) -> official build" 2>/dev/null; exit 2; fi; }
  trap on_exit EXIT
  trap 'exit 2' INT TERM HUP
  # The planner ports Lake's compileLeanModule argv / mkModuleSetup / fetchTransImportArts of a SPECIFIC Lake version;
  # only toolchains whose Lake sources were checked against it are planned (others: official lake build).
  # (VALIDATED_LAKE / SOUND_LAKE437: see planner_src_for above)
  [ -n "$GH" ] || decline "cannot run $TC/bin/lean"
  PLANNER_SRC=$LOG/src/Planner.lean
  case " $VALIDATED_LAKE " in
    *" $GH "*) ;;
    *) case " $SOUND_LAKE437 $SOUND_LAKE436 " in
         *" $GH "*) [ "$SFP" = 1 ] || decline "toolchain $GH (Lake 4.36/4.37): fast build validated for the sound build only (sound-fast-path)"
                    PLANNER_SRC=$LOG/src/Planner435.lean ;;
         *) decline "toolchain $GH not validated for the fast build (planner = Lake 4.33.1 port)" ;;
       esac ;;
  esac
  [ -d "$PROJ" ] || decline "no project dir $PROJ"
  [ -e "$PROJ/.lake" ] && decline "$PROJ/.lake exists: the project copy must not carry build state (finding 066/067)"
  "$D/build/official-build.sh" --preflight "$TC" 2>> "$LOG/build.log" || decline "toolchain preflight failed"
  "$PY" -I "$D/lib/manifest.py" "$PROJ" "$WS" > "$LOG/binds.tsv" 2>> "$LOG/build.log" || decline "dependencies cannot be resolved offline"
  mkbinds "$LOG/binds.tsv" "$PROJ" || decline "dependency bind destinations are not plain directories inside the project"
  # a root lakefile.lean is project CODE that Lake runs while loading the workspace; it could detect the planner and steer
  # the plan -> only the declarative lakefile.toml is planned (Lake prefers lakefile.lean when both exist).
  [ -e "$PROJ/lakefile.lean" ] || [ -L "$PROJ/lakefile.lean" ] && decline "root config is lakefile.lean (project code at configuration time): official build"
  [ -f "$PROJ/lakefile.toml" ] || decline "no lakefile.toml"
  # a lakefile.lean ANYWHERE in the project tree (a local path dependency's,
  # accepted by lib/manifest.py) is project code that Lake would run while the planner loads the workspace ->
  # official build, before any planning; in-project symlinked directories are followed (a path dependency may be one)
  lfl=$("$PY" -I -c '
import os, sys
proj = os.path.realpath(sys.argv[1])
seen = set()
for dp, dns, fns in os.walk(proj, followlinks=True):
    rp = os.path.realpath(dp)
    if rp in seen or not (rp == proj or rp.startswith(proj + os.sep)):
        dns[:] = []
        continue
    seen.add(rp)
    dns[:] = [d for d in dns if d != ".lake"]
    if "lakefile.lean" in fns or os.path.islink(os.path.join(dp, "lakefile.lean")):
        print(os.path.relpath(os.path.join(dp, "lakefile.lean"), proj)); break' "$PROJ" 2>> "$LOG/build.log") || lfl="(cannot walk the project)"
  [ -z "$lfl" ] || decline "the project contains $lfl (configuration code a path dependency would run): official build"
  # Lake loads a dependency's configuration from its manifest entry's `configFile` (Lake/Load/Materialize.lean
  # relConfigFile; default "lakefile" = lakefile.lean, else lakefile.toml) and picks the language by EXTENSION alone
  # (Lake/Load/Package.lean resolveConfigFile, the same in 4.33.1 / 4.36 / 4.37): a path entry naming e.g. `build.lean`
  # is Lean code under any name. Every untrusted (non-git) entry must name a `.toml` file; the git entries were checked
  # against the trusted packages workspace by lib/manifest.py (configFile included)
  ncf=$("$PY" -I -c '
import json, os, re, stat, sys
proj = os.path.realpath(sys.argv[1])
def rd(p):
    fd = os.open(p, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    if not stat.S_ISREG(os.fstat(fd).st_mode):
        raise OSError("not a regular file")
    return os.fdopen(fd, "rb").read().decode("utf-8")
def tomlname(cf):   # Lean FilePath.extension: none when the last component starts with its only dot (".toml")
    if not isinstance(cf, str):
        return False
    bn = cf.rsplit("/", 1)[-1]
    return bn.endswith(".toml") and len(bn) > len(".toml")
def check(p):
    try:
        m = json.loads(rd(p))
    except (OSError, ValueError, UnicodeDecodeError) as e:
        return f"{os.path.relpath(p, proj)} is unreadable ({e})"
    pk = m.get("packages", []) if isinstance(m, dict) else None
    if not isinstance(pk, list):
        return f"{os.path.relpath(p, proj)}: packages is not a list"
    for e in pk:
        if isinstance(e, dict) and e.get("type") == "git" and p == root:
            continue   # pinned to the trusted packages workspace by lib/manifest.py (configFile included)
        cf = e.get("configFile", "lakefile") if isinstance(e, dict) else None
        if not tomlname(cf):
            return f"{os.path.relpath(p, proj)}: package configuration file {cf!r} is not a .toml file"
    return ""
root = os.path.join(proj, "lake-manifest.json")
if os.path.lexists(root):
    r = check(root)
    if r:
        print(r); sys.exit(0)
else:   # without a root manifest Lake resolves path requires itself and honours THEIR manifests
    try:
        t = rd(os.path.join(proj, "lakefile.toml"))
    except (OSError, UnicodeDecodeError):
        t = "require"
    if re.search(r"(?m)^\s*(\[\[?\s*require\b|require\s*[=.])", t):
        print("no lake-manifest.json but the lakefile requires packages (Lake would resolve them itself)"); sys.exit(0)
seen = set()
for dp, dns, fns in os.walk(proj, followlinks=True):   # every other lake-manifest.json of the tree (nested packages)
    rp = os.path.realpath(dp)
    if rp in seen or not (rp == proj or rp.startswith(proj + os.sep)):
        dns[:] = []
        continue
    seen.add(rp)
    dns[:] = [d for d in dns if d != ".lake"]
    if "lake-manifest.json" in fns and rp != proj:
        r = check(os.path.join(dp, "lake-manifest.json"))
        if r:
            print(r); sys.exit(0)' "$PROJ" 2>> "$LOG/build.log") || ncf="cannot check the lake-manifest.json files"
  [ -z "$ncf" ] || decline "$ncf (Lean configuration code would run): official build"
  if [ -n "$REQMODS" ]; then
    # the configured module's resolution - incl. the [[require]] check of both shapes - BEFORE the planner runs
    PRE=$(lake_target_modules "$PROJ" "$REQMODS" "$LOG/binds.tsv") || PRE="DECLINE: the target resolver failed"
    PRE=$(resolver_output "$PRE")
    case "$PRE" in DECLINE:*) decline "${PRE#DECLINE: }: official build" ;; esac
  fi
  # B3 fast-exact: compile + smoke-test the plugin in the background while the planner is compiled and runs (S07)
  FXPID=
  if [ "$FASTEXACT" = 1 ]; then
    FXTC=$TC; nxt=
    for a in "${SCHED_OPTS[@]}"; do [ "$nxt" = 1 ] && FXTC=$(dirname "$(dirname "$a")"); nxt=; [ "$a" = --lean ] && nxt=1; done
    compile_fastexact "$FXTC" "$TC" "$LOG/fastexact" "$LOG/src/LightFastExact.lean" & FXPID=$!
  fi
  # closure build (B3 only; A05 item closure-only=MOD[+MOD..], A03's planner --targets): the planner plans the import
  # closure of these root-package modules instead of the default targets
  if [ -n "$CLOSURE" ] && [ -n "$REQMODS" ]; then
    # closure-only of the configured module = the root modules of `lake build MOD` (e.g. lean_lib Main
    # with roots [Statements, Main]); globs / a package name -> plan the default targets instead (checked after planning)
    TM=$(lake_target_modules "$PROJ" "$REQMODS" "$LOG/binds.tsv") || TM="DECLINE: the target resolver failed"
    TM=$(resolver_output "$TM")   # empty / malformed output = hand off
    case "$TM" in
      DECLINE:*) decline "${TM#DECLINE: }: official build" ;;
      *) CLOSURE=$(echo "$TM" | tr ' ' '+') ;;
    esac
  fi
  if [ -n "$CLOSURE" ]; then
    [ "$PRESET" = B3 ] || decline "closure-only needs --preset B3 (the exact build builds the default targets)"
    : > "$LOG/targets.txt" || decline "cannot write $LOG/targets.txt"
    printf '%s\n' "$CLOSURE" | tr '+' '\n' >> "$LOG/targets.txt"
    PLANNER_ARGS+=(--targets "$LOG/targets.txt")
  fi
  compile_planner "$TC" "$LOG/planner" "$PLANNER_SRC" || decline "planner does not compile (see $LOG/planner/planner.compile.log)"

  # B3 premise-off (S07): generate the helper's source (namespace roots of the project, read as text) while Lake plans
  POPID=
  if [ "$POFF" = 1 ]; then
    mkdir -p "$LOG/premiseoff/src" || decline "premise-off: cannot create $LOG/premiseoff"
    # generate AND compile while Lake plans (both off the critical path)
    ( "$PY" -I "$LOG/src/premiseoff.py" "$PROJ" "$LOG/premiseoff/src/FastverifyPremiseOff.lean" > "$LOG/premiseoff/gen.log" 2>&1 || exit 3
      env -i PATH=/usr/bin:/bin LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" -R "$LOG/premiseoff/src" "$LOG/premiseoff/src/FastverifyPremiseOff.lean" \
        -o "$LOG/premiseoff/FastverifyPremiseOff.olean" > "$LOG/premiseoff/compile.log" 2>&1 || exit 4 ) & POPID=$!
  fi
  # B3 merge: scan the project's sources for the merge planner while Lake plans (text parsing only, no project code)
  MPS=
  if [ "$MERGE" = 1 ]; then
    MJ=$THREADS; [ "$MJ" -gt 64 ] && MJ=64
    "$PY" -I "$LOG/src/mergeplan.py" --prescan "$PROJ" "$LOG/merge-prescan.pkl" --jobs "$MJ" > "$LOG/merge-prescan.out" 2>&1 & MPS=$!
  fi
  # 1. plan (Lake's own workspace loading and configuration)
  # never bind LOG writable into a sandbox: it holds helper sources ($LOG/src) that
  # run on the host later. The planner sees LOG read-only (its binary, targets.txt) and writes its plan into a fresh
  # private directory; the plan is copied out as a regular file (O_NOFOLLOW) after the sandbox (own pid ns) is gone
  PQ=$LOG/planq; rm -rf "$PQ"; mkdir "$PQ" || decline "cannot create $PQ"
  { cat "$LOG/binds.tsv"; printf '%s\t%s\n' "$LOG" "$LOG"; } > "$LOG/binds-ro.tsv" || decline "cannot write binds-ro.tsv"
  sandbox "$PROJ" "$TC" "$LOG/binds-ro.tsv" "$PQ" "$LOG/planner/planner" "$TC" "$PQ/plan.jsonl" "${PLANNER_ARGS[@]}" > "$LOG/plan.out" 2> "$LOG/plan.err"
  prc=$?
  if [ $prc -eq 0 ]; then
    copy_out "$PQ/plan.jsonl" "$LOG/plan.jsonl" || decline "the planner's plan is not a regular file"
  fi
  if [ $prc -ne 0 ]; then decline "planner exit $prc: $(grep -m3 DECLINE "$LOG/plan.out" | tr '\n' ' ' | cut -c1-400)"; fi
  if [ -n "$REQMODS" ]; then   # the modules `lake build MOD` builds
    RT=$(lake_target_modules "$PROJ" "$REQMODS" "$LOG/binds.tsv") || RT="DECLINE: the target resolver failed"
    RT=$(resolver_output "$RT")
    case "$RT" in DECLINE:*) decline "${RT#DECLINE: }: official build of the configured module" ;; esac
    REQMODS_RESOLVED=$RT
    miss=$("$PY" -I -c '
import json, sys
names = set()
with open(sys.argv[1]) as f:
    f.readline()
    for ln in f:
        r = json.loads(ln)
        if "name" in r:
            names.add(r["name"])
print(" ".join(m for m in sys.argv[2].split() if m not in names))' "$LOG/plan.jsonl" "$REQMODS_RESOLVED") || decline "cannot read the plan for --require-modules"
    [ -z "$miss" ] || decline "module(s) $miss not built by the planned targets: official build of the configured module"
  fi
  # the sources the plan was computed from must be the sources lean compiles: digest now (after Lake may have written
  # lake-manifest.json; no project code runs in the planner), compare after the build. An honest project never edits its
  # own sources while it is built (Lake also reads every header up front).
  # B3 sound-fast-path (S07, UNTRUSTED, sound preset only): the source digests, plancheck and Lake's dependency check
  # below establish that this build is EXACTLY the official one (sources unchanged, importArts={} equivalent, no olean
  # collisions, dependency oleans current by Lake's trace). Soundness never depends on that (the export is re-checked
  # from scratch against the official challenge; a missing or colliding olean just fails the build -> B1 fallback), so
  # they are skipped: ~7 s before the first lean (plancheck) and ~3-4 s after the last one (175k-file digest).
  if [ "$SFP" = 1 ] && [ "$PLANONLY" = 0 ]; then
    : > "$LOG/extmods.txt"; echo "sound-fast-path: plancheck, dependency check and source digests skipped" > "$LOG/plancheck.out"
  else
  srcdigest "$PROJ" > "$LOG/src.before" & SDPID=$!   # overlapped with the plan check
  # 2. per-run equivalence checks for importArts={} + list of dependency modules to verify
  # (inside the sandbox: the dependency packages are only visible there, bound at their Lake paths)
  PCQ=$LOG/plancheckq; rm -rf "$PCQ"; mkdir "$PCQ" || decline "cannot create $PCQ"   # private output dir, LOG read-only
  sandbox "$PROJ" "$TC" "$LOG/binds-ro.tsv" "$PCQ" /usr/bin/python3 -I "$LOG/src/plancheck.py" "$LOG/plan.jsonl" "$PCQ/extmods.txt" > "$LOG/plancheck.out" 2>&1 \
    || decline "plan check: $(tail -3 "$LOG/plancheck.out" | tr '\n' ' ' | cut -c1-400)"
  copy_out "$PCQ/extmods.txt" "$LOG/extmods.txt" || decline "the plan check's output is not a regular file"
  wait "$SDPID" || decline "cannot digest the project sources"
  fi
  TO=(); [ "$TIMEOUT" != 0 ] && TO=(timeout --signal=KILL "$TIMEOUT")
  # 3. dependency packages up to date by Lake's own check (concurrently with the build)
  DPID=
  if [ -s "$LOG/extmods.txt" ]; then
    mapfile -t EXT < "$LOG/extmods.txt"
    sandbox "$PROJ" "$TC" "$LOG/binds.tsv" "" "$TC/bin/lake" build --no-build "${EXT[@]}" > "$LOG/depcheck.log" 2>&1 &
    DPID=$!
  fi
  if [ $PLANONLY = 1 ]; then
    drc=0; if [ -n "$DPID" ]; then wait "$DPID"; drc=$?; fi
    [ "$drc" = 0 ] || decline "dependency packages not up to date by Lake's own check (exit $drc)"
    FINAL=1; emit PLANNED 0 "plan-only: $(cat "$LOG/plancheck.out" | tail -1)"; exit 0
  fi
  # B3 native-pkg (UNSAFE): compile the trusted packages' C code in the background; leans started after it is ready
  # get --load-dynlib (the lib dir is bound read-only into the build sandbox)
  BUILDBINDS=$LOG/binds.tsv; NPID=
  if [ "$NATIVE" = 1 ]; then
    mkdir -p "$LOG/native"
    bash "$LOG/src/native.sh" "$LOG/binds.tsv" "$LOG/native" "$THREADS" "$TC" > "$LOG/native.log" 2>&1 & NPID=$!
    cp "$LOG/binds.tsv" "$LOG/binds-build.tsv"; printf '%s\t%s\n' "$LOG/native" "$LOG/native" >> "$LOG/binds-build.tsv"
    BUILDBINDS=$LOG/binds-build.tsv; SCHED_OPTS+=(--native-ready "$LOG/native/ready")
  fi
  # B3 merge (UNTRUSTED, sound preset): rewrite the plan so that importer-closed groups of modules with identical lean
  # invocations become one lean process each (merged sources in $LOG/merge/src; the project's sources stay untouched);
  # the members' original plan records are the scheduler's split fallback. A planner failure just builds unmerged.
  PLANF=$LOG/plan.jsonl
  if [ "$MERGE" = 1 ]; then
    IFS=: read -r -a MA <<< "$MERGE_ARGS"
    # measured deny list (S02): groups that failed merged in earlier runs of the same project are not merged
    # (merge=--no-deny disables it; an explicit merge=--deny:FILE replaces it); snapshot in the log dir
    if [ -f "$D/build/hints/merge-deny.txt" ] && ! printf '%s\n' "${MA[@]}" | grep -qx -e '--deny' -e '--no-deny'; then
      cp "$D/build/hints/merge-deny.txt" "$LOG/merge-deny.txt" && MA+=(--deny "$LOG/merge-deny.txt")
    fi
    MA2=(); for x in "${MA[@]}"; do if [ "$x" = late ]; then MLATE=1; else MA2+=("$x"); fi; done; MA=("${MA2[@]}")
    [ -n "$MPS" ] && wait "$MPS"
    if [ "$MLATE" = 1 ]; then
      # merge=late (S02): the build starts at once with Lake's plan; the merge planner runs concurrently and sched.py
      # swaps in every merged group none of whose members has been launched when LOG/merge/READY appears
      mkdir -p "$LOG/merge"; rm -f "$LOG/merge/READY" "$LOG/merge/FAILED"
      [ "$BUILDBINDS" = "$LOG/binds-build.tsv" ] || { cp "$LOG/binds.tsv" "$LOG/binds-build.tsv"; BUILDBINDS=$LOG/binds-build.tsv; }
      printf '%s\t%s\n' "$LOG/merge" "$LOG/merge" >> "$BUILDBINDS"
      SCHED_OPTS+=(--merge-late "$LOG/merge")
      ( if "$PY" -I "$LOG/src/mergeplan.py" "$LOG/plan.jsonl" "$LOG/merge" --jobs "$MJ" --confine "$PROJ" --scan-cache "$LOG/merge-prescan.pkl" "${MA[@]}" > "$LOG/merge.out" 2>&1
        then : > "$LOG/merge/READY"; else : > "$LOG/merge/FAILED"; echo "merge planner failed (building unmerged): $(tail -1 "$LOG/merge.out")" >> "$LOG/build.log"; fi ) & MLPID=$!
    elif "$PY" -I "$LOG/src/mergeplan.py" "$LOG/plan.jsonl" "$LOG/merge" --jobs "$MJ" --confine "$PROJ" --scan-cache "$LOG/merge-prescan.pkl" "${MA[@]}" > "$LOG/merge.out" 2>&1; then
      PLANF=$LOG/merge/plan.jsonl
      [ "$BUILDBINDS" = "$LOG/binds-build.tsv" ] || { cp "$LOG/binds.tsv" "$LOG/binds-build.tsv"; BUILDBINDS=$LOG/binds-build.tsv; }
      printf '%s\t%s\n' "$LOG/merge" "$LOG/merge" >> "$BUILDBINDS"
      SCHED_OPTS+=(--split-fallback "$LOG/merge/fallback.jsonl")
    else
      echo "merge planner failed (building unmerged): $(tail -1 "$LOG/merge.out")" >> "$LOG/build.log"
    fi
  fi
  # B3 fast-exact (S04, UNTRUSTED, sound preset): plugin compiled with the toolchain of the lean that runs the modules
  # (the last --lean given to sched.py, else the official TC), bound read-only into the build sandbox, --plugin on every
  # lean argv (sched.py --extra-arg). A plugin that does not compile or fails its smoke test is NOT used (the build runs
  # without it, slower on with_unfolding_all modules only); LOG/fastexact/STATUS and build.log say which.
  if [ "$FASTEXACT" = 1 ]; then
    if wait "$FXPID"; then   # started in the background before the planner (same function, same arguments)
      echo "active (plugin generated by $FXTC/bin/lean, compiled by $TC/bin/leanc, smoke test ok)" > "$LOG/fastexact/STATUS"
      [ "$BUILDBINDS" = "$LOG/binds-build.tsv" ] || { cp "$LOG/binds.tsv" "$LOG/binds-build.tsv"; BUILDBINDS=$LOG/binds-build.tsv; }
      printf '%s\t%s\n' "$LOG/fastexact" "$LOG/fastexact" >> "$BUILDBINDS"
      SCHED_OPTS+=(--extra-arg "--plugin=$LOG/fastexact/libLightFastExact.so")
    else
      mkdir -p "$LOG/fastexact"; echo "INACTIVE: plugin does not compile or fails its smoke test with $FXTC (see $LOG/fastexact/compile.log, smoke/smoke.log)" > "$LOG/fastexact/STATUS"
    fi
    echo "fast-exact: $(cat "$LOG/fastexact/STATUS")" >> "$LOG/build.log"
  fi
  # B3 premise-off (S07, UNTRUSTED, sound preset): the helper module (no declarations; exported deny-list entries only, see
  # build/premiseoff/premiseoff.py) is compiled with the official toolchain outside the project, placed into the (empty,
  # checked by plancheck) root lib dir = on Lake's LEAN_PATH, so lean and the exporter find it like a project module, and
  # appended by sched.py to every eligible module's setup.json imports
  if [ "$POFF" = 1 ]; then
    wait "$POPID"; porc=$?
    [ $porc = 0 ] || decline "premise-off: helper $([ $porc = 4 ] && echo 'does not compile' || echo "source generation failed ($(tail -1 "$LOG/premiseoff/gen.log"))")"
    # the root lib dir comes from the UNTRUSTED lakefile.toml (buildDir / leanLibDir): it must be a
    # plain directory path strictly inside PROJ (no '..' component, no control character, no symlink component: realpath
    # = the normalized path) before this host-side mkdir/cp acts on it (no untrusted code runs at this point)
    ROOTLIB=$(confined_path "$("$PY" -I -c 'import json,sys; h=json.loads(open(sys.argv[1]).readline()); print([p["leanLibDir"] for p in h["packages"] if p.get("isRoot")][0])' "$LOG/plan.jsonl")" "$PROJ") \
      || decline "premise-off: the root lib dir of the plan is not a plain directory inside the project"
    [ -e "$ROOTLIB/FastverifyPremiseOff.olean" ] && decline "premise-off: $ROOTLIB/FastverifyPremiseOff.olean exists"
    mkdir -p -- "$ROOTLIB" && [ "$(realpath -e -- "$ROOTLIB")" = "$ROOTLIB" ] && cp -- "$LOG/premiseoff/FastverifyPremiseOff.olean" "$ROOTLIB/" \
      || decline "premise-off: cannot place the helper olean"
    SCHED_OPTS+=(--setup-import-append FastverifyPremiseOff)
  fi
  # zygote client (S01): compiled per run (system gcc, else the toolchain's leanc); a 60-line C file, untrusted build helper
  if [ "$ZYGOTE" = 1 ]; then
    mkdir -p "$LOG/zy"
    env -i PATH=/usr/bin:/bin gcc -O2 -o "$LOG/zy/zyc" "$LOG/src/zyc.c" > "$LOG/zyc.compile.log" 2>&1 \
      || env -i PATH=/usr/bin:/bin "$TC/bin/leanc" -O2 -o "$LOG/zy/zyc" "$LOG/src/zyc.c" >> "$LOG/zyc.compile.log" 2>&1 \
      || decline "zyc does not compile"
    [ "$BUILDBINDS" = "$LOG/binds-build.tsv" ] || { cp "$LOG/binds.tsv" "$LOG/binds-build.tsv"; BUILDBINDS=$LOG/binds-build.tsv; }
    printf '%s	%s
' "$LOG/zy" "$LOG/zy" >> "$BUILDBINDS"
    SCHED_OPTS+=(--zyc "$LOG/zy/zyc")
  fi
  # the unofficial module lean (toolchain-T1, a tree under $T1DIR = /scratch, which the S4 masks hide)
  # is bound read-only into the build sandbox at its own path
  if [ -n "${UNSAFE_T1:-}" ]; then
    [ "$BUILDBINDS" = "$LOG/binds-build.tsv" ] || { cp "$LOG/binds.tsv" "$LOG/binds-build.tsv"; BUILDBINDS=$LOG/binds-build.tsv; }
    printf '%s\t%s\n' "$T1DIR/$UNSAFE_T1" "$T1DIR/$UNSAFE_T1" >> "$BUILDBINDS"
  fi
  # B3 cost-hints (S07): the file is snapshotted into the log dir; sched.py reads it inside the sandbox
  if [ -n "${CHCOPY:-}" ]; then
    mkdir -p "$LOG/hints" && cp "$CHCOPY" "$LOG/hints/$(basename "$CHCOPY")" || decline "cost-hints: cannot copy $CHCOPY"
    [ "$BUILDBINDS" = "$LOG/binds-build.tsv" ] || { cp "$LOG/binds.tsv" "$LOG/binds-build.tsv"; BUILDBINDS=$LOG/binds-build.tsv; }
    printf '%s\t%s\n' "$LOG/hints" "$LOG/hints" >> "$BUILDBINDS"
    SCHED_OPTS+=(--cost-hints "$LOG/hints/$(basename "$CHCOPY")")
  fi
  if [ -n "${CTCOPY:-}" ]; then   # B3 check-tail (S07): same handling as cost-hints
    mkdir -p "$LOG/hints" && cp "$CTCOPY" "$LOG/hints/tail-$(basename "$CTCOPY")" || decline "check-tail: cannot copy $CTCOPY"
    if ! grep -q "^$LOG/hints	" "$BUILDBINDS" 2>/dev/null; then
      [ "$BUILDBINDS" = "$LOG/binds-build.tsv" ] || { cp "$LOG/binds.tsv" "$LOG/binds-build.tsv"; BUILDBINDS=$LOG/binds-build.tsv; }
      printf '%s\t%s\n' "$LOG/hints" "$LOG/hints" >> "$BUILDBINDS"
    fi
    SCHED_OPTS+=(--check-tail "$LOG/hints/tail-$(basename "$CTCOPY")")
  fi
  # 4. build
  "${TO[@]}" bash -c "$(declare -f sandbox bindok); sandbox \"\$@\"" _ "$PROJ" "$TC" "$BUILDBINDS" "" \
    /usr/bin/python3 -I -c "$(cat "$LOG/src/sched.py")" "$THREADS" "${SCHED_OPTS[@]}" < "$PLANF" > "$LOG/sched.out" 2>&1
  src=$?
  if [ -n "$MLPID" ]; then pkill -P "$MLPID" 2>/dev/null; kill "$MLPID" 2>/dev/null; wait "$MLPID" 2>/dev/null; fi
  if [ "$MERGE" = 1 ] && [ "$src" = 1 ] && { [ "$PLANF" != "$LOG/plan.jsonl" ] || grep -q '"event": "merge-late", "applied": [1-9]' "$LOG/sched.out"; }; then
    # B3 merge: a module failed although every failing merged group was split -> possibly a silent leak upstream; the
    # merged outputs are not trusted any further: rebuild everything once from Lake's original plan (no merging).
    echo "merge: build failed with the merged plan ($(tail -1 "$LOG/sched.out" | cut -c1-200)) -> rebuilding unmerged" >> "$LOG/build.log"
    mv "$LOG/sched.out" "$LOG/sched.merged.out"
    NOPTS=(); skip=0
    for o in "${SCHED_OPTS[@]}"; do
      if [ "$skip" = 1 ]; then skip=0; continue; fi
      case "$o" in --split-fallback|--merge-late) skip=1; continue ;; esac
      NOPTS+=("$o")
    done
    "${TO[@]}" bash -c "$(declare -f sandbox bindok); sandbox \"\$@\"" _ "$PROJ" "$TC" "$BUILDBINDS" "" \
      /usr/bin/python3 -I -c "$(cat "$LOG/src/sched.py")" "$THREADS" "${NOPTS[@]}" < "$LOG/plan.jsonl" > "$LOG/sched.out" 2>&1
    src=$?
  fi
  if [ -n "$NPID" ]; then kill "$NPID" 2>/dev/null; wait "$NPID" 2>/dev/null; fi
  drc=0; if [ -n "$DPID" ]; then wait "$DPID"; drc=$?; fi
  [ "$drc" = 0 ] || decline "dependency packages not up to date by Lake's own check (lake build --no-build exit $drc, see $LOG/depcheck.log)"
  if [ "$SFP" != 1 ]; then
  srcdigest "$PROJ" > "$LOG/src.after" || decline "cannot digest the project sources after the build"
  cmp -s "$LOG/src.before" "$LOG/src.after" || decline "project sources changed during the build ($LOG/src.before vs src.after)"
  fi
  if [ "$src" = 1 ] && [ -n "$REQMODS" ]; then
    # the official comparator builds only the configured module(s) and their imports
    # (`lake build MOD`); a failure ONLY in modules outside that import closure (e.g. a broken, unimported default target)
    # is not the official result: DECLINE -> the official build of exactly the configured module(s). Only a
    # failure of a module in the closure stays FAILED; an unattributable one declines too (see below).
    outside=$("$PY" -I -c '
import json, sys
plan, sched, req = sys.argv[1], sys.argv[2], sys.argv[3].split()
deps = {}
with open(plan) as f:
    f.readline()
    for ln in f:
        r = json.loads(ln)
        if "name" in r:
            deps[r["name"]] = r.get("deps") or []
clos, todo = set(), [m for m in req if m in deps]
while todo:
    m = todo.pop()
    if m in clos:
        continue
    clos.add(m)
    todo += [d for d in deps.get(m, []) if d in deps]
last = {}   # the FINAL record per module (a retry-exact success replaces its first failure)
with open(sched, errors="replace") as f:
    for ln in f:
        if ln.startswith("{\"event\": \"module\""):
            try:
                r = json.loads(ln)
            except ValueError:
                continue
            last[r.get("module")] = r
failed = {m for m, r in last.items() if r.get("rc") != 0 or r.get("error_msg") or r.get("missing")}   # = sched.py ok
inside = sorted(m for m in failed if m in clos)
print(("INSIDE " + " ".join(inside)) if inside else ("OUTSIDE " + " ".join(sorted(failed))) if failed else "NONE")' \
      "$LOG/plan.jsonl" "$LOG/sched.out" "${REQMODS_RESOLVED:-$REQMODS}" 2>> "$LOG/build.log")
    # FAILED only when a module INSIDE the closure failed; a failure that
    # cannot be attributed there (no module event: a scheduler exception, e.g. on an unrelated target's options; a merged
    # group; only modules outside the closure; the attribution itself failing) is no verdict -> the official build
    case "$outside" in
      INSIDE\ *) ;;
      OUTSIDE\ *) decline "only modules outside the import closure of $REQMODS failed ($(echo "${outside#OUTSIDE }" | cut -c1-200)): official build of the configured module" ;;
      *) decline "the build failed with no module failure inside the import closure of $REQMODS (scheduler: $(tail -1 "$LOG/sched.out" | cut -c1-200)): official build of the configured module" ;;
    esac
  fi
  case $src in
    0) ;;
    1) FINAL=1; emit FAILED 1 "$(tail -1 "$LOG/sched.out" | cut -c1-300)"; exit 1 ;;
    *) decline "scheduler exit $src: $(tail -1 "$LOG/sched.out" | cut -c1-300)" ;;
  esac
  if [ -n "$LPOUT" ] && [ "$SFP" = 1 ]; then   # = what 'lake env printenv LEAN_PATH' prints: ws.leanPath + the toolchain's lib/lean
    "$PY" -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).readline())["leanPath"] + ":" + sys.argv[2])' "$LOG/plan.jsonl" "$TC/lib/lean" > "$LOG/lean_path.txt" \
      || decline "cannot read LEAN_PATH from the plan"
  elif [ -n "$LPOUT" ]; then
    sandbox "$PROJ" "$TC" "$LOG/binds.tsv" "" "$TC/bin/lake" env printenv LEAN_PATH > "$LOG/lean_path.txt" 2>> "$LOG/build.log" \
      || decline "lake env failed after the build"
  fi
  if [ -n "$LPOUT" ]; then
    lpconfined "$LOG/lean_path.txt" "$PROJ" "$TC" 2>> "$LOG/build.log" || decline "LEAN_PATH leaves the project (see $LOG/build.log)"
    tr -d '\n' < "$LOG/lean_path.txt" > "$LPOUT"
  fi
  FINAL=1; emit BUILT 0 "$(tail -1 "$LOG/sched.out" | cut -c1-300)"
  exit 0
}
main "$@"
exit $?
