#!/usr/bin/python3 -I
"""tests/macos-judge/run.py [WORKDIR]: the macOS judge (check/sound/macos) with stand-in programs. No Lean needed,
a few minutes. The files the judge runs are copied to a private tree whose record of programs names shell scripts
that answer in the words of the three programs. The judge scripts, the driver, the sandbox, the resource guard, the
configuration step and the cross-version gate are the real ones. On another system than arm64 macOS the rows that
need no Mac run (sources, crates, config, decision, retry, record, private, earlier): they tell a change of the judge
scripts that the driver would not follow.
  sources    build-judge-macos.sh --sources-only stages the sources with the fingerprints pins.env pins and refuses a
             changed source, a symbolic link and an extra directory; the recipe stops before it compiles with another
             Rust version or another toolchain; pins.env is read strictly and its self-test digests are those of
             check/sound/selftest; both judge scripts hand over right after their clean-environment step, and their
             configuration step is the one the driver knows; their look at enter.py passes for the whole file only,
             and a file cut off below its end handler and started all the same never ends with exit status 0
  crates     the build of the second kernel (cargo_build.py) with archives made here and a stand-in for cargo:
             which packages of a Cargo.lock are taken, that an archive is unpacked only with the checksum of the
             lock and only regular files inside its own folder, a cargo configuration above the build folder, the
             environment and the home that cargo gets, a program that names its build folder
  config     the 90 variants of tests/config-types: a config is refused exactly where the official 4.36 comparator
             stops with a configuration error (data/official-4.36.tsv)
  decision   what the exit status and the output of a leg mean: accepted or rejected only with the status and the
             line of that leg, anything else is no verdict; a comparison that ends with status 1 is read as the two
             judge scripts that run ccmp-lowmem read it, by their own lines
  retry      which first run of the second kernel is repeated with one worker: the wrapper that each judge script
             writes and the driver's condition agree on every row
  record     config/pins-macos.env: duplicate or foreign lines, another file than --pins-sha256 names; the recipe's
             writer run twice
  private    the private copy of an input: the environment of the copy, and a source that changes, a copy of another
             size and a hard link in place of a copy are refused (with a stand-in for /bin/cp)
  earlier    what enter.py takes for the result of an earlier run, which it removes from a --json path: what this
             judge writes, not a file that has some of its keys; the role that the driver gives each word of a
             command line, which words are values of --json and which keep an earlier result there; write_json
             when something fails after the result is in place
  judge      whole runs through both judge scripts: the self-tests, no verdict without --pins-sha256, ACCEPTED,
             REJECTED by each leg, the no-verdict exit of the streaming replay, the one-worker retry, a leg that ends
             with another status, is killed or exceeds the time or memory limit, what a leg may read and write,
             that the programs run from private copies whatever happens at their recorded paths, --pins, programs
             that fail a self-test, the caller's digests, config and gate rules, refused options, output paths, a
             hostile environment; the judge scripts without a hand-over give no verdict
  programs   programs.py of this directory with stand-ins that decide by the name of the export: no FAIL row, and a
             FAIL row when the second kernel accepts an attack that the streaming replay accepts
Prints PASS/FAIL rows and a RESULT line, and SKIP for the sections that need a Mac."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import time

HERE = Path(__file__).resolve().parent
FV = HERE.parents[1]
TESTS = FV / 'tests'
SCRIPT = {'lowmem': 'check/lowmem/check-sound-lowmem.sh', 'ultralowmem': 'check/lowmem/check-sound-ultralowmem.sh'}
CHECKER = {'lowmem': 'checkSoundLowMem', 'ultralowmem': 'checkSoundUltraLowMem'}
ENV = {'PATH': '/usr/bin:/bin'}
# The private tree: what the judge runs, and what build-judge-macos.sh stages.
PINS = 'check/sound/macos/pins.env'
FILES = (*SCRIPT.values(), 'check/sound/check-sound.sh', 'check/sound/macos/judge.py',
         'check/sound/macos/support.py', 'check/sound/macos/enter.py', PINS,
         'check/sound/macos/build-judge-macos.sh', 'check/sound/macos/cargo_build.py', 'check/xversion/xvcheck.py',
         'check/xversion/releases.json',
         'check/sound/hints/default.txt', 'check/checkB/patches/gruszka-combined-v6.diff',
         'lib/macos/sandbox-run.py', 'tools/guard/fvguard.py')
TREES = ('fastverify/check/sound/selftest', 'fastverify/check/sound/src', 'fastverify/check/lowmem/src',
         'fastverify/check/lowmem/src-ultralowmem', 'sources/gruszka')
OFFICIAL_ERROR = ('config refused: official comparator configuration error (the official 4.36 comparator stops with '
                  'exit 2, no verdict): ')
# The look of the two judge scripts at enter.py before they hand over to it, a program for `/usr/bin/python3 -I -c`
# with the path of enter.py, and the reason of their own DECLINED when it fails. It prints COMPLETE, flushed, and
# ends with status 0 only when the run of the file came back and its last statement had run; its end handler gives
# every other way out the status 1. The scripts want that word alone on stdout together with exit status 0, so an
# exception from the file, an exit or an os._exit is a failure.
LOOK = ('import atexit, os, sys; names = {"__name__": "enter", "__file__": sys.argv[1]}; atexit.register(os._exit, 1); '
        'exec(compile(open(sys.argv[1], "rb").read(), sys.argv[1], "exec"), names); '
        'done = names.get("COMPLETE") is True; print("COMPLETE" if done else "INCOMPLETE", flush=True); '
        'os._exit(0 if done else 1)')
NO_ENTRY = ('cannot resolve the path of the judge script, start /usr/bin/python3 or load check/sound/macos/enter.py '
            'to its last statement')
# Stand-ins for the programs of the judge. Each says where it was started from. A line {"marker":"NAME"} in the
# judged export selects another answer. `escaped` tries what the sandbox of a leg must refuse: to read the challenge,
# a folder of the user (as a toolchain is) or the record, and to write next to the private inputs, to the program at
# its recorded path, to the record, to the driver, to the program that runs and to the export. The @NAMES@ are
# filled in by install().
MARKER = r'''mark=$(/usr/bin/sed -n 's/^{"marker":"\(.*\)"}$/\1/p' "$export")
escaped() {
  for file in "${export%/*}/challenge.export" "@TOOLCHAIN@/file" "@RECORD@"; do
    /bin/cat "$file" > /dev/null 2>&1 && return 0
  done
  for file in "${export%/*}/planted" "@SELF@" "@RECORD@" "@DRIVER@"; do
    ( echo planted >> "$file" ) 2> /dev/null && return 0
  done
  for file in "$0" "$export"; do
    ( /bin/chmod u+w "$file" && echo planted >> "$file" ) 2> /dev/null && return 0
  done
  return 1
}
'''
# Every stand-in says how it was started and, in one line, what its environment holds.
SAYS_ENV = 'echo "note: environment $(/usr/bin/env | /usr/bin/sort | /usr/bin/tr \'\\n\' \'|\')" >&2\n'
STAND_INS = {
    'ccmp_lowmem': '''#!/bin/sh
echo "note: started as $0" >&2
''' + SAYS_ENV + '''
if /usr/bin/grep -q fvCheat "$4"; then echo "error: Illegal axiom detected: 'fvCheat'"; exit 1; fi
echo "Comparison and axiom check passed!"
''',
    'pleanchecker': '''#!/bin/sh
echo "[pchk] started as $0" >&2
''' + SAYS_ENV + '''for export; do :; done
case $export in */selftest_kbad)
  echo "Lean default kernel rejects the solution: while replaying declaration 'fvSelfTest':"
  echo "(kernel) declaration type mismatch"; exit 1;;
esac
''' + MARKER + '''case $mark in
  lean-rejects) echo "Lean default kernel rejects the solution: (kernel) declaration type mismatch"; exit 1;;
  lean-parse) echo "uncaught exception: Duplicate declaration: T" >&2; exit 1;;
  lean-stack) echo "Lean default kernel rejects the solution: while replaying declaration 'T':"
    echo '(kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit'; exit 1;;
  lean-undecided) echo "Lean default kernel could not decide (no verdict): closure above the budget"; exit 2;;
  lean-exit-*) echo "Lean default kernel accepts the solution"; exit "${mark#lean-exit-}";;
  lean-killed) kill -KILL $$;;
  lean-silent) exit 1;;
  lean-io) echo "uncaught exception: interrupted system call (error code: 4, interrupted)" >&2
    echo "  file: $export" >&2; exit 1;;
  lean-slow) /bin/sleep 60;;
  lean-waits) /usr/bin/touch ready; while [ ! -e go ]; do /bin/sleep 0.2; done;;
  lean-large) /usr/bin/awk 'BEGIN { while (i++ < 4000000) a[i] = sprintf("%0100d", i); system("/bin/sleep 60") }';;
  lean-peek) if escaped; then echo "Lean default kernel rejects the solution: not confined"; exit 1; fi;;
esac
echo "Lean default kernel accepts the solution"
''',
    'gruszka': '''#!/bin/sh
export=$1
echo "note: $2 workers, started as $0" >&2
''' + SAYS_ENV + '''
case $export in */selftest_kbad) echo "rejected: fvSelfTest: value's type does not match the declared type"; exit 1;;
esac
''' + MARKER + '''case $mark in
  k2-rejects) echo "rejected: Bad.decl: type mismatch"; exit 1;;
  k2-full) echo "declined: Big.decl: a worker table is full"; exit 2;;
  k2-room*) [ "$2" -gt 1 ] && { echo "declined: Big.decl: a worker table is full"; exit 2; };;
  k2-declines) echo "declined: Big.decl: recursion too deep (stack limit)"; exit 2;;
  k2-peek) if escaped; then echo "rejected: not confined"; exit 1; fi;;
esac
[ "$mark" = k2-room-rejects ] && { echo "rejected: Bad.decl: type mismatch"; exit 1; }
echo accepted
''',
}
STAND_INS['pleanchecker_lowmem'] = STAND_INS['pleanchecker']
# Stand-ins for programs.py: each program alone, on exports under their own names. Controls are accepted and attacks
# are rejected, but for the ones on which the real program ends otherwise: the replay aborts on two, the second
# kernel declines ten and three of the forged records. The streaming replay accepts the c1only exports; a file
# gruszka.accept lists exports the second kernel then accepts.
REPLAY_BY_NAME = '''#!/bin/sh
for export; do :; done
name=$(/usr/bin/basename "$export" .export)
case "$name" in
  T-eta-honest-rec) ;;
  L4-ctor-name-mismatch|E17_huge_bvar_2pow20_unsafe_ctor) kill -ABRT $$;;
  *control*|*baseline*|*honest*|C0*|Solution%s) echo "Lean default kernel accepts the solution"; exit 0;;
esac
echo "Lean default kernel rejects the solution: stand-in $name"; exit 1
'''
BY_NAME = {
    'ccmp_lowmem': STAND_INS['ccmp_lowmem'],
    'pleanchecker': REPLAY_BY_NAME % '',
    'pleanchecker_lowmem': REPLAY_BY_NAME % '|c1only_*',
    'gruszka': '''#!/bin/sh
name=$(/usr/bin/basename "$1" .export)
if [ -f "$0.accept" ] && /usr/bin/grep -qx "$name" "$0.accept"; then echo accepted; exit 0; fi
if [ -f "$0.decline" ] && /usr/bin/grep -qx "$name" "$0.decline"; then echo "declined: stand-in $name"; exit 2; fi
case "$name" in
  g1d_dup_rec_thm|g1e_dup_thm_rec|T-isrec-forged|T-numidx-forged|T-eta-forged-isrec|L6-quot-wrong-kind|ind-isrec)
    echo "declined: stand-in $name"; exit 2;;
  ind-nidx|ind-nnested|ind-refl|c2s_isrec_forged|E11_quot_mk_as_unsafe_axiom|E17_huge_bvar_2pow20_unsafe_ctor)
    echo "declined: stand-in $name"; exit 2;;
  T-eta-honest-rec) ;;
  *control*|*baseline*|*honest*|C0*|Solution) echo accepted; exit 0;;
esac
echo "rejected: stand-in $name"; exit 1
''',
}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pin_programs(fv, paths):
    """In pins.env of the private tree `fv`, pin the bytes of `paths` for the programs that pins.env pins."""
    text = (fv / PINS).read_text()
    for name, path in paths.items():
        text = re.sub(f'^PIN {name} [0-9a-f]{{64}}$', f'PIN {name} {digest(path)}', text, flags=re.M)
    (fv / PINS).write_text(text)


def install(fv, where, programs, sources):
    """Write the stand-in programs to `where`, the record that names them and their digests into pins.env of the
    private tree. Returns (record, {name: path})."""
    (where / 'toolchain').mkdir(parents=True)
    (where / 'toolchain/file').write_text('a file of the toolchain\n')
    lines, paths = [], {}
    for name, text in programs.items():
        paths[name] = where / name
        for mark, value in (('@RECORD@', fv / 'config/pins-macos.env'), ('@DRIVER@', fv / 'check/sound/macos/judge.py'),
                            ('@TOOLCHAIN@', where / 'toolchain'), ('@SELF@', paths[name])):
            text = text.replace(mark, str(value))
        paths[name].write_text(text)
        paths[name].chmod(0o755)
        lines += [f'SRC {name} {sources[name]}', f'PIN {name} {digest(paths[name])} {paths[name]}']
    record = fv / 'config/pins-macos.env'
    record.parent.mkdir(exist_ok=True)
    record.write_text('\n'.join(lines) + '\n')
    pin_programs(fv, paths)
    return record, paths


def source_rows(row, judge, support, tree, work, mac):
    def staged(recipe, out):
        done = subprocess.run(['/bin/bash', str(recipe), '--sources-only', str(out)], env=ENV, capture_output=True,
                              text=True)
        found = {name: value for value, name in re.findall(r'^([0-9a-f]{64})  (\w+)$', done.stdout, flags=re.M)}
        return done.returncode, found, done.stderr.strip()[-200:].replace('\n', ' | ')

    pins = support.TreePins()
    rc, found, said = staged(FV / 'check/sound/macos/build-judge-macos.sh', work / 'staged')
    row('sources: the recipe stages the sources that pins.env pins', rc == 0 and found == pins.sources, said)
    recipe = tree / 'fastverify/check/sound/macos/build-judge-macos.sh'
    arena = 'fastverify/check/lowmem/src/lowmem_arena.c'
    # Only regular files are sources: a link is refused, also one that leads to the same bytes.
    for at in ('fastverify/check/sound/src/Extra.lean', arena, 'sources/gruszka/vendor/susz/src/extra.rs',
               'fastverify/check/lowmem/src-ultralowmem/src/pleanchecker-lowmem/PChk/Extra.lean'):
        link, kept = tree / at, work / 'kept-source'
        if link.exists():
            link.rename(kept)
        link.symlink_to(kept if kept.exists() else FV / 'check/sound/src/Main.lean')
        rc, found, said = staged(recipe, work / 'staged-link')
        link.unlink()
        if kept.exists():
            kept.rename(link)
        row(f'sources: a symbolic link at {at} is refused',
            rc == 2 and not found and f'{at}: neither a regular file nor a directory' in said, said)
    # What is left out is named exactly: a directory called target below the top is a source like any other.
    (tree / 'sources/gruszka/src/target').mkdir()
    (tree / 'sources/gruszka/src/target/extra.rs').write_text('// extra\n')
    rc, found, said = staged(recipe, work / 'staged-target')
    shutil.rmtree(tree / 'sources/gruszka/src/target')
    row('sources: a source directory named target is not left out',
        rc == 2 and [name for name in sorted(pins.sources) if found.get(name) != pins.sources[name]] == ['gruszka'],
        said)
    # The patch of the second kernel is taken by its digest: other bytes are refused before patch reads them, also
    # bytes that would give the same sources.
    patch = tree / 'fastverify/check/checkB/patches/gruszka-combined-v6.diff'
    pinned = patch.read_bytes()
    patch.write_bytes(pinned + b'\nA line after the last hunk.\n')
    rc, found, said = staged(recipe, work / 'staged-patch')
    patch.write_bytes(pinned)
    row('sources: a patch of the second kernel with other bytes is refused',
        rc == 2 and not found and 'gruszka-combined-v6.diff: SHA-256 mismatch' in said, said)
    with (tree / arena).open('a') as source:
        source.write('\n')
    rc, found, said = staged(recipe, work / 'staged-changed')
    differ = [name for name in sorted(pins.sources) if found.get(name) != pins.sources[name]]
    row('sources: a changed source file is refused',
        rc == 2 and differ == ['ccmp_lowmem'] and 'not the sources that pins.env pins' in said, said)
    # Before it compiles anything the recipe refuses another Rust version than the Linux recipes use, and a
    # toolchain directory that does not hold the official files.
    release = 'rustc 1.97.1 (8bab26f4f 2026-07-14)'
    for number, (name, line, wanted) in enumerate((
            ('another Rust version', 'rustc 1.100.0 (0000000000 2026-01-01)', 'requires ' + release),
            ('another build of Rust 1.97.1', 'rustc 1.97.1 (0000000000 2026-01-01)', 'requires ' + release),
            ('the Rust release and no Lean toolchain', release, 'not the official Lean 4.36.0 toolchain'))):
        if not mac:
            break
        tools = work / f'rust-{number}'
        tools.mkdir()
        for tool, text in (('rustc', f'echo "{line}"'), ('cargo', 'exit 97')):
            (tools / tool).write_text(f'#!/bin/sh\n{text}\n')
            (tools / tool).chmod(0o755)
        done = subprocess.run(['/bin/bash', str(FV / 'check/sound/macos/build-judge-macos.sh'), str(work / 'unbuilt')],
                              env=dict(ENV, TC36=str(tools), FV_RUST_BIN=str(tools), CARGO_HOME=str(tools)),
                              capture_output=True, text=True)
        row(f'sources: the recipe with {name} stops before it compiles',
            done.returncode == 2 and wanted in done.stderr and not list((work / 'unbuilt').glob('*/bin/*')),
            done.stderr.strip()[-150:])
    # A build folder whose path is written into compiler flags must be plain. The recipe says so before it compiles
    # anything, not when the three Lean programs are built and the second kernel is next.
    for name, folder in (('an equals sign', 'out=dir'), ('a space', 'out dir')):
        if not mac:
            break
        done = subprocess.run(['/bin/bash', str(FV / 'check/sound/macos/build-judge-macos.sh'), str(work / folder)],
                              env=dict(ENV, TC36=str(tools), FV_RUST_BIN=str(tools), CARGO_HOME=str(tools)),
                              capture_output=True, text=True)
        row(f'sources: the recipe refuses a build folder with {name} before it compiles',
            done.returncode == 2 and 'must be a path of letters, digits and . _ + @ -' in done.stderr
            and not list((work / folder).glob('*/bin/*')) and not list((work / folder).glob('*/logs/*.build')),
            done.stderr.strip()[-150:])
    # The Lean programs are built in an environment of the recipe that names the oldest macOS they are for, and the
    # compiler gets another name for the place of the toolchain: neither reaches the bytes that pins.env pins.
    text = (FV / 'check/sound/macos/build-judge-macos.sh').read_text()
    clean = re.search(r'^clean=\((/usr/bin/env -i [^)]*)\)$', text, flags=re.M)
    builds = re.findall(r'^.*"\$tc/bin/(?:lake|leanc)".*$', text, flags=re.M)
    row('sources: the recipe builds the Lean programs in its own environment, for macOS 11.0 and without the place of '
        'the toolchain', clean is not None and 'MACOSX_DEPLOYMENT_TARGET=11.0' in clean.group(1).split()
        and len(builds) == 2 and all('"${clean[@]}" "$tc/bin/' in line for line in builds)
        and text.count('-ffile-prefix-map="$tc"=/lean-tc') == 1, f'{len(builds)} build commands')
    # And the recipe looks: a program that holds a folder of the machine as text is not recorded. The libraries of
    # the release hold paths of the machine that built them, which are nobody's here.
    held = work / 'held-program'
    held.write_bytes(b'\0code\0/Users/somebody/.elan/toolchains/x/include/lean/lean.h\0code\0'
                     b'/Users/runner/work/lean4/lean4/src/runtime/io.cpp\0')
    places = {'the toolchain': Path('/Users/somebody/.elan/toolchains/x'), 'the home folder': '/Users/somebody',
              'the build folder': '/private/tmp/out/build.abcdefgh', 'no folder': '', 'the root': '/'}
    row('sources: a program that holds folders of the machine as text is found, and the recipe asks before it records',
        support.machine_paths(held, places) == ['the toolchain', 'the home folder']
        and support.machine_paths(held, {'the home folder': '/Users/runner'}) == []
        and support.machine_paths(held, {'the home folder': '/Users/runner/work'}) == []
        and 0 < text.find('support.machine_paths(programs[name], places)') < text.rfind('support.TreePins()')
        < text.find('support.write_record(') and ' "$tc" "${HOME:-}" <<' in text)
    # The last step of the recipe, run as the recipe runs it, in the private tree, whose pins.env pins the stand-ins:
    # it records the four pinned programs, and nothing when one of them is another or holds its build folder.
    step = re.search(r"<<'RECORD'\n(.*?\n)RECORD\n", text, flags=re.S).group(1)
    private = tree / 'fastverify'
    built = dict(line.split()[1::2] for line in (private / 'config/pins-macos.env').read_text().splitlines()
                 if line.startswith('PIN '))
    for label, changed, wanted in (
            ('pinned', None, ''),
            ('with a program that is not the pinned one', {'gruszka': '# other bytes\n'},
             'not the programs that pins.env pins; the judge refuses them, and nothing was recorded:\n  gruszka: '),
            ('with a program that holds its build folder', {'pleanchecker': '# built in {run}\n'},
             'a program holds a folder of this machine as text, and nothing was recorded:\n  pleanchecker: the build '
             'folder\n'),
            ('with programs that hold the place of the toolchain and the home folder',
             {'ccmp-lowmem': '# /no/toolchain/include/lean/lean.h\n', 'gruszka': '# /no/home/.cargo\n'},
             'a program holds a folder of this machine as text, and nothing was recorded:\n  ccmp-lowmem: the place '
             'of the Lean toolchain\n  gruszka: the home folder\n')):
        run = work / ('recipe-' + label.replace(' ', '-'))
        (run / 'bin').mkdir(parents=True)
        for name, path in built.items():
            shutil.copy2(path, run / 'bin' / name.replace('_', '-'))
        for name, more in (changed or {}).items():
            with (run / 'bin' / name).open('a') as program:
                program.write(more.format(run=run))
        done = subprocess.run(['/usr/bin/python3', '-I', '-', str(private / 'check/sound/macos'), str(run),
                               str(run / 'record.env'), 'the versions', 'the system', '/no/toolchain', '/no/home'],
                              input=step, env=ENV, capture_output=True, text=True)
        if changed:
            row(f'sources: the recipe {label} records nothing',
                done.returncode == 1 and done.stderr.startswith(wanted) and not (run / 'record.env').exists(),
                done.stderr[:150])
        else:
            lines = (run / 'record.env').read_text().splitlines() if (run / 'record.env').is_file() else []
            row('sources: the recipe records the four programs that pins.env pins and prints the digest of the record',
                done.returncode == 0 and sorted(line.split()[1] for line in lines if line.startswith('PIN '))
                == sorted(support.PROGRAMS) and all(line.split()[3].startswith(f'{run}/bin/') for line in lines
                                                    if line.startswith('PIN '))
                and done.stdout.splitlines()[-1] == f"Recorded in {run / 'record.env'} (SHA-256 "
                f"{digest(run / 'record.env')})", (done.stdout[-120:] + done.stderr[-150:]).replace('\n', ' | '))
    sums = dict(reversed(line.split()) for line in (FV / 'check/sound/selftest/SHA256SUMS').read_text().splitlines())
    row('sources: the five self-test digests of pins.env are those of check/sound/selftest',
        len(sums) == 5 and all(sums.get(pins.files[name][0].name) == pins.files[name][1] == digest(pins.files[name][0])
                               for name in support.SELFTESTS))
    # pins.env is read strictly: every line is a pin of a known kind.
    for name, change, wanted in (('with a line of another kind', lambda text: text + 'TC36=/usr\n', 'not understood'),
                                 ('with a program twice', lambda text: text + 'PIN pleanchecker ' + '0' * 64 + '\n',
                                  'not understood'),
                                 ('with a file outside the tree',
                                  lambda text: text.replace(' check/sound/selftest/good.export', ' ../good.export'),
                                  'not understood'),
                                 ('without a self-test input',
                                  lambda text: re.sub('^PIN selftest_kbad .*\n', '', text, flags=re.M), 'incomplete'),
                                 ('without the digest of a Lean program',
                                  lambda text: re.sub('^PIN pleanchecker_lowmem .*\n', '', text, flags=re.M),
                                  'incomplete'),
                                 ('without the digest of the second kernel',
                                  lambda text: re.sub('^PIN gruszka .*\n', '', text, flags=re.M), 'incomplete')):
        (work / 'pins.env').write_text(change((FV / PINS).read_text()))
        try:
            support.TreePins(work / 'pins.env')
            said = 'read'
        except support.Declined as error:
            said = str(error)
        row(f'sources: pins.env {name} is refused', wanted in said, said[:100])
    marker = 'if [ "${1:-}" = --clean-env-reexec ]; then shift; fi'
    darwin = 'if [ "$(/usr/bin/uname -s 2>/dev/null)" = Darwin ]; then'
    enter = '  exec /usr/bin/python3 -I "${self%/*}/../sound/macos/enter.py" '
    sys.path.insert(0, str(FV / 'check/sound/macos'))
    import enter as supervisor
    row("sources: enter.py and the driver name the judges and the driver's exit statuses alike",
        supervisor.CHECKERS == {mode: spec['checker'] for mode, spec in judge.MODES.items()}
        and {status: verdict for status, (verdict, _code) in supervisor.STATUS.items()}
        == {status: verdict for verdict, status in judge.STATUS.items()}
        and {verdict: code for verdict, code in supervisor.STATUS.values()}
        == {'ACCEPTED': 0, 'PREFLIGHT_OK': 0, 'REJECTED': 1, 'DECLINED': 2})
    for mode, spec in judge.MODES.items():
        script = spec['script']
        lines = script.read_text().split('\n')
        at = lines.index(marker)
        code = [line for line in lines[at + 1:at + 8] if not line.startswith('#')]
        resolve = ('  self=$(/usr/bin/readlink -f "$0") && [ -n "$self" ] && t=$(/usr/bin/python3 -I -c \'' + LOOK
                   + '\' "${self%/*}/../sound/macos/enter.py") && [ "$t" = COMPLETE ] || { printf \'%s\\n\' \'{"checker":"'
                   + spec['checker'] + '","verdict":"DECLINED","exit":2,"reason":"' + NO_ENTRY + '"}\'; exit 2; }')
        row(f'sources: {script.name} hands over right after its clean-environment step, to enter.py',
            lines[0] == '#!/bin/bash -p' and code == [darwin, resolve, enter + mode + ' "$@"', 'fi']
            and lines[at + 8] == 'set -u'
            and [at for at, line in enumerate(lines)
                 if ('enter.py' in line or 'judge.py' in line) and not line.startswith('#')] == [at + 5, at + 6])
        code, arguments = support.config_step(script.read_bytes(), script.name)
        row(f'sources: the configuration step of {script.name} is the one the driver knows',
            arguments == judge.CONFIG_STEP_ARGS and 'kept.txt' in code)
    # That look passes for enter.py and for no file that is enter.py cut off before its last statement: after each
    # of its lines, and at each byte of the last statement and of the comment above it.
    whole = (FV / 'check/sound/macos/enter.py').read_bytes()
    ends = [0]
    for line in whole.splitlines(keepends=True):
        ends.append(ends[-1] + len(line))
    block = whole.rindex(b"if __name__ == '__main__':\n")
    last = whole.index(b'\n#', block) + 1
    registered = whole.index(b'\n', whole.index(b'\n    atexit.register(os._exit, 2)') + 1) + 1

    def started(size, *words):
        cut = work / f'enter-{size}{"-look" if words else ""}.py'
        cut.write_bytes(whole[:size])
        done = subprocess.run(['/usr/bin/python3', '-I', *words, str(cut)], env=ENV, stdin=subprocess.DEVNULL,
                              capture_output=True)
        return size, done.returncode, done.stdout

    with ThreadPoolExecutor(8) as pool:
        looked = list(pool.map(lambda size: started(size, '-c', LOOK), sorted({*ends, *range(last, len(whole) + 1)})))
        direct = list(pool.map(started, [size for size in ends[:-1] if size >= registered]))
    passed = [size for size, status, out in looked if status == 0 and out == b'COMPLETE\n']
    row('sources: the look of the judge scripts at enter.py passes for the file, and not when it is cut off',
        passed == [len(whole) - 1, len(whole)] and whole.endswith(b'\nCOMPLETE = True\n') and len(looked) > 300
        and all(out in (b'', b'COMPLETE\n', b'INCOMPLETE\n') for _size, _status, out in looked),
        f'{len(looked)} files, at {len(ends) - 1} lines and {len(whole) - last} bytes; passes for those of {passed} '
        f'of {len(whole)} bytes')
    # An enter.py that is started without that look, cut off after any line from the one on which it registers how
    # it ends without a verdict: no exit status of ACCEPTED. With status 1, when the rest does not compile, or 2.
    ended = sorted({status for _size, status, _out in direct})
    row('sources: an enter.py that is cut off below its end handler and started all the same never ends with exit '
        'status 0',
        ended == [1, 2] and len(direct) > 250 and block > registered
        and all(status == 2 for size, status, _out in direct if size == block or size == last),
        f'{len(direct)} files, exit statuses {ended}, without a line on stdout: '
        f'{sum(not out for _size, _status, out in direct)}')
    lines = (FV / 'check/sound/check-sound.sh').read_text().split('\n')
    at = lines.index(marker)
    code = [line for line in lines[at + 1:at + 7] if not line.startswith('#')]
    row('sources: check-sound.sh gives no verdict on macOS and names the two judge scripts that do',
        len(code) == 4 and code[0] == darwin and '{"checker":"checkSound","verdict":"DECLINED","exit":2' in code[1]
        and '$' not in code[1]
        and 'check/lowmem/check-sound-lowmem.sh or check/lowmem/check-sound-ultralowmem.sh' in code[1]
        and code[2:] == ['  exit 2', 'fi'] and lines[at + 7] == 'set -u'
        and not any('judge.py' in line for line in lines if not line.startswith('#')))


def crate(name, members):
    """The bytes of a crate archive NAME.crate. A member is (path, text) for a regular file or (path, kind, target)
    for a symbolic link ('sym'), a hard link ('hard') or a directory ('dir')."""
    data = io.BytesIO()
    with tarfile.open(fileobj=data, mode='w:gz') as archive:
        for path, *what in members:
            member = tarfile.TarInfo(path)
            if len(what) == 1:
                body = what[0].encode()
                member.size = len(body)
                archive.addfile(member, io.BytesIO(body))
            else:
                member.type = {'sym': tarfile.SYMTYPE, 'hard': tarfile.LNKTYPE, 'dir': tarfile.DIRTYPE}[what[0]]
                member.linkname = what[1]
                archive.addfile(member)
    return data.getvalue()


def crate_rows(row, support, cargo_build, work):
    registry = 'registry+https://github.com/rust-lang/crates.io-index'
    sha = lambda data: hashlib.sha256(data).hexdigest()

    def package(name, version, source=registry, checksum=None, more=''):
        lines = ['[[package]]', f'name = "{name}"', f'version = "{version}"']
        lines += [f'source = "{source}"'] if source else []
        lines += [f'checksum = "{checksum}"'] if checksum else []
        return '\n'.join(lines) + '\n' + more + '\n'

    def refused(call, *arguments):
        try:
            call(*arguments)
        except support.Declined as error:
            return str(error)
        return 'not refused'

    lock = (FV.parent / 'sources/gruszka/Cargo.lock').read_text()
    crates = cargo_build.locked_crates(lock)
    row('crates: the Cargo.lock of the second kernel names 31 crates of crates.io, each with a checksum',
        len(crates) == 31 and lock.count('[[package]]') == 33 and 'libmimalloc-sys-0.1.49' in crates
        and all(support.SHA256.fullmatch(value) for value in crates.values()), f'{len(crates)} crates')
    head = '# made by a test\nversion = 4\n\n'
    member = package('kernel', '0.1.1', source=None, more='dependencies = [\n "alpha",\n "beta",\n]\n')
    for name, text in (
            ('from a git repository', package('alpha', '1.0.0', source='git+https://example.org/alpha#0123')),
            ('from another registry', package('alpha', '1.0.0', source='registry+https://example.org/index',
                                               checksum='0' * 64)),
            ('of crates.io without a checksum', package('alpha', '1.0.0')),
            ('with a checksum and no source', package('alpha', '1.0.0', source=None, checksum='0' * 64)),
            ('that is there twice', package('alpha', '1.0.0', checksum='0' * 64) * 2),
            ('with two checksums', package('alpha', '1.0.0', checksum='0' * 64,
                                           more='checksum = "' + '1' * 64 + '"\n')),
            ('with a path in its name', package('../alpha', '1.0.0', checksum='0' * 64)),
            ('without a version', '[[package]]\nname = "alpha"\n\n')):
        said = refused(cargo_build.locked_crates, head + member + text)
        row(f'crates: a Cargo.lock with a package {name} is refused', said.startswith('Cargo.lock: '), said[:90])

    alpha = crate('alpha-1.0.0', [('alpha-1.0.0/Cargo.toml', '[package]\nname = "alpha"\n'),
                                  ('alpha-1.0.0/src', 'dir', ''), ('alpha-1.0.0/src/lib.rs', '// alpha\n')])
    beta = crate('beta-0.2.1', [('beta-0.2.1/Cargo.toml', '[package]\nname = "beta"\n'),
                                ('beta-0.2.1/src/lib.rs', '// beta\n')])
    lock = head + member + package('alpha', '1.0.0', checksum=sha(alpha)) + package('beta', '0.2.1', checksum=sha(beta))
    first, second = work / 'crates-first', work / 'crates-second'
    first.mkdir()
    second.mkdir()
    (first / 'alpha-1.0.0.crate').write_bytes(alpha)
    (second / 'beta-0.2.1.crate').write_bytes(beta)
    said = refused(cargo_build.unpack_crates, lock, [first], work / 'unpacked-missing')
    row('crates: an archive that is in no folder is named, and nothing is unpacked',
        said == f'1 of the 2 crate archives of Cargo.lock are not in {first}: beta-0.2.1.crate (`cargo fetch '
                '--locked` in sources/gruszka, with network, downloads all of them)'
        and not (work / 'unpacked-missing').exists(), said[:120])
    names = cargo_build.unpack_crates(lock, [first, second], work / 'unpacked')
    listed = json.loads((work / 'unpacked/alpha-1.0.0/.cargo-checksum.json').read_text())
    row('crates: the archives are unpacked as a directory source of cargo, with the checksums of the lock',
        names == ['alpha-1.0.0', 'beta-0.2.1'] and (work / 'unpacked/beta-0.2.1/src/lib.rs').read_text() == '// beta\n'
        and listed == {'package': sha(alpha), 'files': {'Cargo.toml': sha(b'[package]\nname = "alpha"\n'),
                                                        'src/lib.rs': sha(b'// alpha\n')}})
    # The first folder that has the file counts: other bytes there are refused, whatever a later folder holds.
    (second / 'alpha-1.0.0.crate').write_bytes(alpha + b'\0')
    said = refused(cargo_build.unpack_crates, lock, [second, first], work / 'unpacked-other')
    row('crates: an archive with other bytes than the lock names is refused, and nothing is unpacked',
        said == f"{second / 'alpha-1.0.0.crate'}: SHA-256 {sha(alpha + bytes(1))}, Cargo.lock has {sha(alpha)}"
        and not (work / 'unpacked-other').exists(), said[:120])
    (second / 'alpha-1.0.0.crate').unlink()
    for number, (name, members) in enumerate((
            ('a symbolic link', [('alpha-1.0.0/src/lib.rs', 'sym', '/etc/hosts')]),
            ('a hard link', [('alpha-1.0.0/a', 'x'), ('alpha-1.0.0/b', 'hard', 'alpha-1.0.0/a')]),
            ('a file of another folder', [('beta-0.2.1/src/lib.rs', '// planted\n')]),
            ('a path that leaves its folder', [('alpha-1.0.0/../planted', 'x')]),
            ('an absolute path', [('/alpha-1.0.0/planted', 'x')]),
            ('a file with the name of its folder', [('alpha-1.0.0', 'x')]),
            ('a file twice', [('alpha-1.0.0/a', 'x'), ('alpha-1.0.0/a', 'y')]))):
        odd = crate('alpha-1.0.0', [('alpha-1.0.0/Cargo.toml', '[package]\n'), *members])
        (first / 'alpha-1.0.0.crate').write_bytes(odd)
        dest = work / f'unpacked-odd-{number}'
        said = refused(cargo_build.unpack_crates, lock.replace(sha(alpha), sha(odd)), [first, second], dest)
        row(f'crates: an archive with {name} is refused', said.startswith('alpha-1.0.0.crate')
            and not any(path.name == 'planted' or path.is_symlink() for path in work.rglob('*')), said[:110])
    (first / 'alpha-1.0.0.crate').write_bytes(b'not an archive')
    said = refused(cargo_build.unpack_crates, lock.replace(sha(alpha), sha(b'not an archive')), [first, second],
                   work / 'unpacked-broken')
    row('crates: a file that is no archive is refused', said.startswith('alpha-1.0.0.crate cannot be unpacked'), said)
    (first / 'alpha-1.0.0.crate').write_bytes(alpha)

    # cargo reads .cargo/config.toml and .cargo/config in the build folder and in every folder above it.
    outer = work / 'configured'
    (outer / 'deep/src/gruszka').mkdir(parents=True)
    before = cargo_build.configs_above(outer / 'deep/src/gruszka')
    (outer / '.cargo').mkdir()
    (outer / '.cargo/config.toml').write_text('[build]\nrustflags = ["-Cdebug-assertions"]\n')
    (outer / 'deep/.cargo').mkdir()
    (outer / 'deep/.cargo/config').symlink_to(outer / 'nowhere')
    found = cargo_build.configs_above(outer / 'deep/src/gruszka')
    row('crates: a cargo configuration in a folder above the build is found, also the old name and a link',
        [name for name in found if name not in before] == [str(outer / 'deep/.cargo/config'),
                                                            str(outer / '.cargo/config.toml')], str(found)[:150])

    # The build with a stand-in for cargo, which writes down what it was given and leaves a program.
    tools = work / 'cargo-tools'
    tools.mkdir()
    (tools / 'rustc').write_text('#!/bin/sh\necho "rustc 1.97.1 (stand-in)"\n')
    (tools / 'cargo').write_text(
        '#!/bin/sh\nrun=${CARGO_TARGET_DIR%/target}\n/usr/bin/env > "$run/cargo.env"\n'
        'echo "$PWD" "$@" > "$run/cargo.call"\n/bin/mkdir -p "$CARGO_TARGET_DIR/release"\n'
        'case $(/bin/cat "$run/answer") in\n'
        '  fails) echo "a program" > "$CARGO_TARGET_DIR/release/gruszka"\n'
        '         echo "error: could not compile"; exit 101;;\n'
        '  names-the-folder) echo "built in $PWD" > "$CARGO_TARGET_DIR/release/gruszka";;\n'
        '  *) echo "a program" > "$CARGO_TARGET_DIR/release/gruszka";;\nesac\n')
    for tool in tools.iterdir():
        tool.chmod(0o755)
    # A stand-in for the Lean toolchain, at a place with a space in its name: its clang says how it was started.
    toolchain = work / 'a toolchain'
    (toolchain / 'lib/libc').mkdir(parents=True)
    (toolchain / 'lib/libc/libSystem.tbd').write_text('the stub of the system library\n')
    (toolchain / 'bin').mkdir()
    (toolchain / 'bin/clang').write_text(
        '#!/bin/sh\necho "SDKROOT=${SDKROOT-unset}"\nfor word; do echo "$word"; done\n')
    (toolchain / 'bin/clang').chmod(0o755)

    def build(label, answer, into=work):
        run = into / label
        for folder in ('src/gruszka', 'logs', 'home', 'tmp'):
            (run / folder).mkdir(parents=True)
        (run / 'src/gruszka/Cargo.lock').write_text(lock)
        (run / 'answer').write_text(answer)
        try:
            return run, str(cargo_build.build(run, tools, [first, second], 3, '/the/sdk', toolchain))
        except support.Declined as error:
            return run, 'refused: ' + str(error)

    if cargo_build.configs_above(work):
        print('SKIP macos-judge crates, the build with a stand-in for cargo: a cargo configuration above ' + str(work))
        return
    os.environ.update(RUSTFLAGS='-Cdebug-assertions', CARGO_BUILD_RUSTFLAGS='-Cdebug-assertions', CC='/no/such/cc')
    run, said = build('second-kernel', 'builds')
    for name in ('RUSTFLAGS', 'CARGO_BUILD_RUSTFLAGS', 'CC'):
        del os.environ[name]
    given = dict(line.split('=', 1) for line in (run / 'cargo.env').read_text().splitlines())
    for name in ('PWD', 'OLDPWD', 'SHLVL', '_', 'run'):      # what the shell of the stand-in adds
        given.pop(name, None)
    wanted = {'PATH': f'{tools}:/usr/bin:/bin', 'HOME': f'{run}/home', 'TMPDIR': f'{run}/tmp', 'LC_ALL': 'C',
              'TZ': 'UTC', 'CARGO_HOME': f'{run}/cargo', 'CARGO_TARGET_DIR': f'{run}/target', 'RUSTC': f'{tools}/rustc',
              'RUSTC_WRAPPER': f'{run}/rustc-in-build',
              'RUSTFLAGS': '-Csplit-debuginfo=unpacked -Clink-arg=-Wl,-S -Clink-arg=-Wl,-dead_strip_dylibs',
              'CC': f'{run}/cc-of-the-toolchain', 'AR': f'{toolchain}/bin/llvm-ar', 'SDKROOT': '/the/sdk',
              'MACOSX_DEPLOYMENT_TARGET': '11.0', 'SOURCE_DATE_EPOCH': '1795242059', 'ZERO_AR_DATE': '1'}
    row('crates: cargo gets the environment that cargo_build.py writes and no variable of the caller',
        said == f'{run}/target/release/gruszka' and given == wanted,
        said[:80] + ' ' + str(sorted(set(given.items()) ^ set(wanted.items())))[:200])
    row('crates: cargo builds both packages of the workspace in the staged sources, locked and offline',
        (run / 'cargo.call').read_text() == f'{run}/src/gruszka build --release --locked --offline -j 3 -p gruszka '
                                            '-p susz\n', (run / 'cargo.call').read_text()[:150])
    row("crates: cargo's home is new and replaces crates.io by the unpacked crates",
        (run / 'cargo/config.toml').read_text() == (
            "[source.crates-io]\nreplace-with = 'verified'\n\n"
            f"[source.verified]\ndirectory = '{run}/crates'\n\n[net]\noffline = true\n")
        and sorted(path.name for path in (run / 'cargo').iterdir()) == ['config.toml']
        and sorted(path.name for path in (run / 'crates').iterdir()) == ['alpha-1.0.0', 'beta-0.2.1'])
    wrapped = subprocess.run([str(run / 'rustc-in-build'), '/bin/echo', '--crate-name', 'x'], env=ENV,
                             capture_output=True, text=True).stdout
    row('crates: every rustc is told to write the build folder as /build and to link with the toolchain',
        wrapped == f'--crate-name x --remap-path-prefix={run}=/build -Clinker={run}/link-of-the-toolchain\n',
        wrapped[:150])
    # The C compiler and the linker are the clang of the Lean toolchain, started without SDKROOT, from which clang
    # would take the version of the SDK that the linker writes into the program.
    started = {name: subprocess.run([str(run / name), 'a word', '-o', 'out'], env=dict(ENV, SDKROOT='/the/sdk'),
                                    capture_output=True, text=True).stdout.splitlines()
               for name in ('cc-of-the-toolchain', 'link-of-the-toolchain')}
    row('crates: the C compiler and the linker are the clang of the Lean toolchain, without SDKROOT',
        started['cc-of-the-toolchain'] == [
            'SDKROOT=unset', '--sysroot', str(toolchain), '-nostdinc', '-isystem', f'{toolchain}/include/clang',
            '-isystem', '/the/sdk/usr/include', f'-ffile-prefix-map={run}=/build',
            f'-ffile-prefix-map={toolchain}=/lean-tc', '-ffile-prefix-map=/the/sdk=/sdk', 'a word', '-o', 'out']
        and started['link-of-the-toolchain'] == ['SDKROOT=unset', '--sysroot', str(toolchain), '-fuse-ld=lld', '-L',
                                                 f'{run}/syslib', 'a word', '-o', 'out'], str(started)[:300])
    stubs = {path.name: path.read_text() for path in (run / 'syslib').iterdir()}
    row('crates: the link is given the stub of the system library of the toolchain, and a stub for libiconv',
        stubs == {'libiconv.tbd': cargo_build.ICONV_STUB,
                  **dict.fromkeys(('libSystem.tbd', 'libc.tbd', 'libm.tbd'), 'the stub of the system library\n')}
        and "install-name: '/usr/lib/libiconv.2.dylib'" in cargo_build.ICONV_STUB, str(sorted(stubs)))
    run, said = build('names-its-folder', 'names-the-folder')
    row('crates: a program that names its build folder is refused',
        said == f'refused: {run}/target/release/gruszka names its build folder: another build would give other '
                'bytes', said[:150])
    run, said = build('fails', 'fails')
    row('crates: a build that cargo ends with an error is refused, also when it left a program',
        said == f'refused: cargo build failed (exit status 101): {run}/logs/gruszka.build'
        and 'error: could not compile' in (run / 'logs/gruszka.build').read_text(), said[:150])
    run, said = build('second-kernel', 'builds', into=outer / 'deep')
    row('crates: with a cargo configuration above the build folder cargo is not started',
        said.startswith('refused: cargo would read ') and str(outer / '.cargo/config.toml') in said
        and not (run / 'cargo.call').exists() and not (run / 'crates').exists(), said[:150])
    run, said = build('second kernel', 'builds')
    row('crates: a build folder with a space in its path is refused before anything is unpacked',
        said.startswith(f'refused: the build folder {run} must be a path of letters')
        and not (run / 'crates').exists(), said[:120])


def config_rows(row, judge, support, work):
    data, out = TESTS / 'config-types/data', work / 'variants'
    subprocess.run(['/usr/bin/python3', '-I', str(data / 'mkvariants.py'), str(out)], check=True, env=ENV,
                   stdout=subprocess.DEVNULL)
    table = dict(line.split()[:2] for line in (data / 'official-4.36.tsv').read_text().splitlines()
                 if not line.startswith('#'))
    # The driver's own rule, on every system: the step refuses these only under a Python that limits int().
    own = {'unknown-int-5000-digits': 'config refused: an integer of more than 4300 digits'}
    base = json.loads((data / 'good.json').read_text())
    digits = {}
    for count in (4300, 4301):
        digits[f'{count} digits in a number'] = json.dumps(base)[:-1] + ', "weight": ' + '9' * count + '}'
        digits[f'{count} digits in a name'] = json.dumps(dict(base, definition_names=['Extra.' + '9' * count]))
    # Digits that the step does not convert are text of any length.
    for name, changed in (('between « and » of a name', {'definition_names': ['Extra.«' + '9' * 4301 + '»']}),
                          ('after a dot between « and »', {'definition_names': ['Extra.«a.' + '9' * 4301 + '»']}),
                          ('inside an identifier of a name', {'definition_names': ['Extra.x' + '9' * 4301]}),
                          ('in a text that is no name', {'comment': '9' * 4301})):
        digits['4300 or more: 4301 digits ' + name] = json.dumps(dict(base, **changed))
    digits['4301 digits after a component between « and »'] = json.dumps(
        dict(base, theorem_names=['«a.1».' + '9' * 4301]))
    fields = {'challenge_module', 'solution_module', 'theorem_names', 'definition_names', 'permitted_axioms'}
    for mode, spec in judge.MODES.items():
        script = spec['script']
        step = support.config_step(script.read_bytes(), script.name)

        def guard(source, label, keep=False):
            """What the driver makes of a config: 'passed' with the private config it would hand on, or why not."""
            scratch = out / f'{mode}-{label}'
            scratch.mkdir()
            try:
                private = judge.config_guard(script.name, step, source, scratch, keep, 0)
                return 'passed', json.loads(private.read_text(encoding='utf-8')), scratch
            except judge.Declined as error:
                return str(error), None, scratch

        wrong = []
        for number, (name, text) in enumerate(digits.items()):
            source = out / f'{mode}-digits-{number}.json'
            source.write_text(text)
            said = guard(source, f'digits-{number}')[0]
            if (said == 'passed') != name.startswith('4300') or 'official' in said or 'Traceback' in said:
                wrong.append(f'{name}: {said[:80]}')
        row(f'config {mode}: 4,300 digits in a number or a name component pass, 4,301 are no verdict; digits that '
            'are text pass', not wrong, '; '.join(wrong))
        wrong = []
        for name, status in sorted(table.items()):
            said, private, scratch = guard(out / (name + '.json'), name)
            if name in own:
                right = said == own[name]
            elif status == '2':
                right = said.startswith(OFFICIAL_ERROR)
            else:
                # What the comparison is given is what the step wrote: the fields of the official decoder and,
                # as the only kernel, the script's own wrapper of the second kernel, which --compare-only ignores.
                wrapper = {'gruszka (second kernel)': [str(scratch / 'bin/gruszka-kernel')]}
                right = (said == 'passed' and set(private) - fields == {'external_kernels'}
                         and private['external_kernels'] == wrapper)
            if not right:
                wrong.append(name)
        errors = sum(status == '2' for status in table.values())
        row(f'config {mode}: refused where the official comparator stops, and for a number of 5,000 digits',
            not wrong and (len(table), errors) == (90, 64),
            f'{len(table)} variants, {errors} configuration errors; differs: {", ".join(wrong) or "none"}')
        # --keep-config-kernels: the step lists the kernels it would run, and none can run here.
        kernel = out / f'{mode}-kernel.json'
        kernel.write_text(json.dumps(dict(base, external_kernels={'replay': ['/usr/bin/true']})))
        said = [guard(out / 'good.json', 'keep-none', True)[0], guard(kernel, 'keep-one', True)[0],
                guard(kernel, 'drop-one')[0]]
        row(f'config {mode}: a kernel of the config is no verdict with --keep-config-kernels and dropped without',
            said[0] == said[2] == 'passed' and said[1].startswith("--keep-config-kernels: the config names 'replay'"),
            ' | '.join(item[:60] for item in said))


def decision_rows(row, judge, work):
    compare, lean, no = 'Comparison and axiom check passed!\n', 'Lean default kernel accepts the solution\n', 2
    axiom, rejects = "error: Illegal axiom detected: 'fvCheat'\n", 'Lean default kernel rejects the solution: '
    context, mismatch = "while replaying declaration 'T':\n", '(kernel) declaration type mismatch\n'
    rejected = 'rejected: Bad.decl: type mismatch\n'
    parse = 'uncaught exception: Duplicate declaration: T\n'
    deep = '(kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit\n'
    table = [
        ('compare', 'its line with status 0', 0, compare, 0),
        ('compare', 'an illegal axiom', 1, axiom, 1),
        ('compare', 'a statement that differs', 1,
         "error: Challenge and solution theorem statement do not match: 'T'\n", 1),
        ('compare', 'status 0 without its line', 0, '', no),
        ('compare', 'the line of another leg', 0, 'accepted\n', no),
        ('compare', 'its line with status 1', 1, compare, no),
        ('compare', 'its line and an error', 0, compare + 'error: late failure\n', no),
        ('compare', 'another error line', 1, "error: duplicate declaration 'T'\n", 1),
        ('compare', 'status 1 without an error line', 1, 'note: nothing said\n', no),
        ('compare', 'memory ran out', 1, 'error: out of memory\n', no),
        ('compare', 'a rejection and its line', 1, axiom + compare, no),
        ('compare', 'a rejection after memory ran out', 1, 'out of memory\n' + axiom, no),
        ('compare', 'a rejection with status 2', 2, axiom, no),
        ('compare', 'a hardware fault while reading', 1, 'error: hardware fault (error code: 5)\n', no),
        ('compare', 'an interrupted read', 1,
         'error: interrupted system call (error code: 4, interrupted)\n  file: /w/solution.export\n', no),
        ('compare', 'an end of file that the system reports', 1, 'error: end of file\n', no),
        ('compare', 'a rejection after an error of the system', 1, 'note: resource busy (error code: 16, x)\n' + axiom,
         no),
        ('compare', 'its line with status 0 after a note that names an error of the system', 0,
         'note: interrupted system call (error code: 4, x)\n' + compare, 0),
        ('compare', 'an error line of 3 MiB', 1, 'error: ' + 'x' * (3 << 20) + '\n', 1),
        ('compare', 'an error line of 3 MiB that ends with an error of the system', 1,
         'error: ' + 'x' * (3 << 20) + ' (error code: 5)\n', no),
        ('compare', 'an end of file in a last line without a newline', 1, 'error: end of file', no),
        ('compare', 'a short read of the export, in the words of its reader', 1,
         'error: short pread on export file\n', no),
        ('lean', 'its line with status 0', 0, lean, 0),
        ('lean', 'a rejection', 1, rejects + mismatch, 1),
        ('lean', 'a rejection inside a declaration', 1, rejects + context + mismatch, 1),
        ('lean', 'a rejection by the quotient check', 1,
         lean + 'Quotient post-check rejects the solution: differs\n', 1),
        ('lean', 'status 1 and nothing on stdout: an export that does not parse', 1, ('', parse), 1),
        ('lean', 'status 1 and no output at all', 1, '', no),
        ('lean', 'status 1 and progress lines only', 1, ('', '[pchk] read 5 ms, markPersistent 0 ms\n'), no),
        ('lean', 'status 1 and a line that is no rejection', 1, 'note: nothing judged\n', no),
        ('lean', 'a rejection that is an error of the system', 1,
         rejects + 'resource busy (error code: 16, x)\n', no),
        ('lean', 'a rejection that is an end of file', 1, rejects + 'end of file\n', no),
        ('lean', 'an interrupted read', 1,
         ('', 'uncaught exception: interrupted system call (error code: 4, interrupted)\n  file: x\n'), no),
        ('lean', 'an end of file that the system reports', 1, ('', 'uncaught exception: end of file\n'), no),
        ('lean', 'a rejection of 3 MiB', 1, rejects + 'x' * (3 << 20) + '\n', 1),
        ('lean', 'a rejection of 3 MiB that ends in an end of file', 1, rejects + 'x' * (3 << 20) + ': end of file\n',
         no),
        ('lean', 'a rejection with an error of the system across the 64 KiB of a piece', 1,
         rejects + 'x' * (65536 - len(rejects) - 5) + '(os error 5)\n', no),
        ('lean', 'a rejection of an export whose name says "the end of file"', 1,
         rejects + "unknown constant 'the end of file'\n", 1),
        ('lean', 'a declaration without a cause', 1, rejects + context, 1),
        ('lean', 'a line that is cut', 1, rejects + mismatch[:-1], 1),
        ('lean', 'status 0 without its line', 0, '', no),
        ('lean', 'its line with status 1', 1, lean, no),
        ('lean', 'its line and one more', 0, lean + 'more\n', no),
        ('lean', 'its line on stderr only', 0, ('', lean), no),
        ('lean', 'a rejection with status 0', 0, rejects + mismatch, no),
        ('lean', 'deep recursion', 1, rejects + '(kernel) deep recursion detected\n', no),
        ('lean', 'deep recursion in the words of Lean 4.36', 1, rejects + context + deep, no),
        ('lean', 'memory ran out inside a declaration', 1, rejects + context + 'out of memory\n', no),
        ('lean', 'an internal panic for memory', 1, ('', 'INTERNAL PANIC: out of memory\n'), no),
        ('lean', 'an export that cannot be read', 1,
         ('', 'uncaught exception: permission denied (error code: 13)\n'), no),
        ('lean', 'the no-verdict line with status 1', 1, judge.LEAN_NO_VERDICT + 'closure above the budget\n', no),
        ('k2', 'its line with status 0', 0, 'note: 4 workers\naccepted\n', 0),
        ('k2', 'a rejection', 1, rejected, 1),
        ('k2', 'its line with status 1', 1, 'accepted\n', no),
        ('k2', 'a rejection with status 0', 0, rejected, no),
        ('k2', 'its line and a rejection', 0, 'accepted\n' + rejected, no),
        ('k2', 'its line and an error', 0, 'accepted\nerror: late failure\n', no),
        ('k2', 'a decline with status 1', 1, 'declined: Big.decl: recursion too deep (stack limit)\n', no),
        ('k2', 'a rejection and a decline', 1, rejected + 'declined: Big.decl: recursion too deep\n', no),
        ('k2', 'a rejection that names an error of the system', 1,
         'rejected: T: Input/output error (os error 5)\n', no),
        ('k2', 'its line with status 0 after a note that names an error of the system', 0,
         'note: retry after (os error 4)\naccepted\n', 0),
        ('k2', 'a rejection of 3 MiB', 1, 'rejected: T: ' + 'x' * (3 << 20) + '\n', 1),
        ('k2', 'a rejection of 3 MiB with an error of the system behind the first 64 KiB', 1,
         'rejected: T: ' + 'x' * (3 << 20) + ' (os error 5) and more\n', no),
        ('k2', 'the lines of the other legs', 0, compare + lean, no),
    ]
    log, noise = work / 'leg.log', work / 'leg.stderr'

    def decided(leg, status, output):
        """`output` is what the leg wrote, or (stdout, stderr) for the replay, whose streams are kept apart."""
        stdout, stderr = output if isinstance(output, tuple) else (output, '')
        log.write_text(stdout)
        noise.write_text(stderr)
        try:
            return (judge.decide_replay(status, log, noise) if leg == 'lean' else judge.decide(leg, status, log))[0]
        except judge.Declined:
            return no

    for leg, name, status, output, wanted in table:
        got = decided(leg, status, output)
        row(f'decision {leg}: {name}', got == wanted, ('accepted', 'rejected', 'no verdict')[got])
    # A comparison that ends with exit status 1, by the lines of the two judge scripts that run ccmp-lowmem and by
    # the driver. The driver differs only where it is stricter: an error that names another failure of the machine,
    # and an output that also holds the acceptance line.
    same = ["error: Illegal axiom detected: 'fvCheat'\n", "error: Const not found in solution 'T'\n",
            "error: Challenge and solution theorem statement do not match: 'T'\n", "error: duplicate declaration 'T'\n",
            'error: malformed export: line 12\n', "note: read\nerror: unknown constant 'T'\n",
            'error: out of memory\n', 'error: (kernel) deep recursion detected\n',
            'error: Stack overflow detected. Aborting.\n', 'error: memory allocation of 4096 bytes failed\n', '',
            'note: nothing said\n']
    stricter = ['error: permission denied (error code: 13)\n', 'error: internal error: unreachable\n',
                "error: unknown constant 'T'\nerror: out of memory\n", compare + axiom,
                'error: hardware fault (error code: 5)\n', 'error: end of file\n',
                'error: interrupted system call (error code: 4, interrupted)\n  file: /w/solution.export\n',
                'error: short pread on export file\n']
    home = work / 'comparison'
    home.mkdir()
    for script in (FV / 'check/lowmem/check-sound-lowmem.sh', FV / 'check/lowmem/check-sound-ultralowmem.sh'):
        lines = script.read_text().split('\n')
        start = lines.index('  case "$CRC" in')
        block = 'decline() { echo 2; exit; }\nfinish() { echo "$1"; exit; }\n' + '\n'.join(
            lines[start:lines.index('  esac', start) + 1]) + '\n'
        differ = []
        for output in same + stricter:
            (home / 'ccmp.log').write_text(output)
            theirs = subprocess.run(['/bin/bash', '-c', block], env=dict(ENV, W=str(home), CRC='1'),
                                    capture_output=True, text=True).stdout.strip()
            mine = decided('compare', 1, output)
            if (theirs, mine) != ((str(mine), mine) if output in same else ('1', no)):
                differ.append(f'{output!r}: {script.name} {theirs or "nothing"}, driver {mine}')
        row(f'decision compare: exit status 1 as {script.name} reads it', not differ,
            f'{len(same)} outputs with the same class, {len(stricter)} where the driver gives no verdict and the '
            f'script REJECTED' + ''.join('; ' + item for item in differ))
    # A replay that ends with exit status 1, by the lines of the same two scripts (their stack pattern and their
    # rule) and by the driver. The scripts keep one log for both streams. The driver differs where the scripts'
    # pattern lets a failure of the machine or of the program through as a rejection.
    same = [rejects + mismatch, rejects + context + mismatch, ('', parse), rejects + context,
            lean + 'Quotient post-check rejects the solution: differs\n', '(kernel) deep recursion detected\n',
            ('', 'Stack overflow detected. Aborting.\n')]
    stricter = [rejects + context + deep, ('', 'INTERNAL PANIC: out of memory\n'), lean,
                ('', 'uncaught exception: permission denied (error code: 13)\n'),
                ('', 'uncaught exception: interrupted system call (error code: 4, interrupted)\n  file: x\n'),
                judge.LEAN_NO_VERDICT + 'closure above the budget\n', '', 'note: nothing judged\n',
                ('', '[pchk] read 5 ms, markPersistent 0 ms\n')]
    (home / 'tmp').mkdir()
    for script in (FV / 'check/lowmem/check-sound-lowmem.sh', FV / 'check/lowmem/check-sound-ultralowmem.sh'):
        lines = script.read_text().split('\n')
        pattern = [line for line in lines if line.startswith(("DEEP_RE='", 'lean_deep() {'))]
        start = lines.index('  if [ "$LRC_OUT" = 1 ] && [ "${LRC:-}" = 1 ]; then')
        block = 'decline() { echo 2; exit; }\nfinish() { echo "$1"; exit; }\n' + '\n'.join(
            pattern + lines[start:lines.index('  fi', start) + 1]) + '\n'
        differ = [] if len(pattern) == 2 else ['the stack pattern of the script was not found']
        for output in same + stricter:
            (home / 'tmp/leg-lean.log').write_text(''.join(output))
            theirs = subprocess.run(['/bin/bash', '-c', block], env=dict(ENV, W=str(home), LRC_OUT='1', LRC='1'),
                                    capture_output=True, text=True).stdout.strip()
            mine = decided('lean', 1, output)
            if (theirs, mine) != ((str(mine), mine) if output in same else ('1', no)):
                differ.append(f'{output!r}: {script.name} {theirs or "nothing"}, driver {mine}')
        row(f'decision lean: exit status 1 as {script.name} reads it', not differ,
            f'{len(same)} outputs with the same class, {len(stricter)} where the driver gives no verdict and the '
            f'script REJECTED' + ''.join('; ' + item for item in differ))


def retry_rows(row, judge, work):
    room = b'declined: Big.decl: a worker table is full\n'
    again = [('a note, then the decline', b'note: 16 workers\n' + room), ('the decline alone', room),
             ('an empty name', b'declined: : a worker table is full\n'),
             ('colons in the name', b'declined: A: B: a worker table is full\n'),
             ('a log of 17 MiB', (b'note: ' + b'y' * 1017 + b'\n') * (17 * 1024) + room),
             ('a note of 3 MiB in one line', b'note: ' + b'y' * (3 << 20) + b'\n' + room)]
    never = [('another reason', b'declined: X: recursion too deep (stack limit)\n'),
             ('a reason that only contains the text', b'declined: X: a worker table is full: unknown constant\n'),
             ('no name', b'declined: a worker table is full\n'), ('two declines', room + room),
             ('a rejection next to the decline', b'rejected: Y: bad\n' + room),
             ('a name with a newline', b'declined: X: a worker table is full\nY: recursion too deep\n'),
             ('no final newline', room[:-1]), ('a note after the decline', room + b'note: late\n'),
             ('an empty log', b''), ('a blank last line', room + b'\n'), ('a carriage return', room[:-1] + b'\r\n'),
             ('another line in front', b'warning: x\n' + room)]
    rows = [(*item, 2, True) for item in again] + [(*item, 2, False) for item in never] \
        + [(f'exit status {status}', room, status, False) for status in (0, 1, 3)]
    first, calls, stub = work / 'first.log', work / 'calls', work / 'stub-gruszka'
    # The stub is called with the worker count last: above one worker it repeats the recorded first run.
    stub.write_text(f'#!/bin/sh\nfor a; do w=$a; done; echo "$w" >> "{calls}"\n[ "$w" -gt 1 ] && '
                    f'{{ /bin/cat "{first}"; exit $(/bin/cat "{first}.status"); }}\necho accepted\n')
    stub.chmod(0o755)
    for mode, spec in judge.MODES.items():
        script = spec['script']
        # The wrapper of the second kernel as the judge script writes it, for 16 workers and no time limit.
        lines = script.read_text().split('\n')
        start = lines.index('cat > "$W/bin/gruszka-kernel" <<EOF')
        home = work / ('wrapper-' + mode)
        (home / 'bin').mkdir(parents=True)
        (home / 'tmp').mkdir()
        subprocess.run(['/bin/bash', '-c', '\n'.join(lines[start:lines.index('EOF', start) + 1]) + '\n'], check=True,
                       env=dict(ENV, W=str(home), GRUSZKA=str(stub), T='16', T_EFF='16', GRZ_LM_ARGS='', DL='0'))
        (home / 'bin/gruszka-kernel').chmod(0o755)
        for name, output, status, wanted in rows:
            first.write_bytes(output)
            Path(str(first) + '.status').write_text(str(status))
            calls.write_text('')
            done = subprocess.run([str(home / 'bin/gruszka-kernel'), str(home / 'solution.export')], env=ENV,
                                  capture_output=True)
            used = calls.read_text().split()
            mine = status == 2 and judge.worker_table_decline(first)
            row(f'retry {script.name}: {name}',
                used == (['16', '1'] if wanted else ['16']) and mine == wanted
                and done.returncode == (0 if wanted else status),
                f'the script ran the second kernel with {" then ".join(used)} worker(s); the driver would '
                f'{"" if mine else "not "}run it again')
    # Decided here and left to awk in the scripts, whose implementations differ: a log with a NUL byte is never a
    # reason for a second run. The other bytes are compared as they are.
    for name, output, wanted in (('a NUL byte', b'declined: A\0B: a worker table is full\n', False),
                                 ('a NUL byte in a note', b'note: a\0b\n' + room, False),
                                 ('a byte that is not UTF-8', b'declined: A\xffB: a worker table is full\n', True),
                                 ('a decline of 3 MiB', b'declined: ' + b'y' * (3 << 20) + room[9:], True),
                                 ('a long line that is no note', b'x' * (3 << 20) + b'\n' + room, False)):
        first.write_bytes(output)
        row(f'retry driver: {name}', judge.worker_table_decline(first) == wanted)


def record_rows(row, support, work, text, programs):
    path, zeros = work / 'record.env', '0' * 64
    source = 'SRC gruszka ' + support.TreePins().sources['gruszka'] + '\n'
    pin = f"PIN gruszka {digest(programs['gruszka'])} "
    where = pin + str(programs['gruszka']) + '\n'
    refused = 'not a PIN or SRC line of one program'
    cases = [('complete', text, None), ('with a comment', '# a comment\n' + text, None),
             ('of one program', source + where, None),
             ('with a line of another program', text + f'PIN exporter {zeros} /nonexistent/exporter\n', refused),
             ('with a line for a self-test input', text + f'PIN selftest_good {zeros} /nonexistent\n', refused),
             ('with a toolchain line', text + 'TC36=/usr\n', refused),
             ('with an empty line', text + '\n', refused),
             ('with a PIN line twice', text + where, refused),
             ('with a SRC line twice', text + source, refused),
             ('with a relative path', text.replace(where, pin + 'bin/gruszka\n'), refused),
             ('with a digest that is none', text.replace(where, 'PIN gruszka 0 /nonexistent\n'), refused),
             ('with another tag', text + where.replace('PIN ', 'BIN '), refused)]
    for name, content, wanted in cases:
        path.write_text(content)
        try:
            support.Record(path)
            said = None
        except support.Declined as error:
            said = str(error)
        row(f'record {name}', said is None if wanted is None else wanted in str(said), said or 'read')
    # The recipe's last step, twice, over a file of another form: the reader accepts what is left, the second run.
    written = work / 'written/pins-macos.env'
    written.parent.mkdir()
    written.write_text(f'TC36=/usr\nPIN exporter {zeros} /opt/exporter\n')
    for build in ('first', 'second'):
        files = {}
        for name in support.PROGRAMS:
            files[name] = written.parent / build / name
            files[name].parent.mkdir(exist_ok=True)
            files[name].write_text(f'{name} of the {build} build\n')
        lines, named = support.write_record(written, files, support.TreePins().sources, [f'the {build} build'])
    try:
        record, said = support.Record(written), written.read_text()
        right = (len(said.splitlines()) == 1 + 2 * len(files) and record.sources == support.TreePins().sources and all(
            record.paths[name] == files[name] and record.digests[name] == digest(files[name]) for name in files)
            and lines == said.splitlines() and named == digest(written) == record.sha256)
    except support.Declined as error:
        right, said = False, str(error)
    row('record written twice by the recipe', right, said.splitlines()[-1])
    path.write_text(text)
    for name, expected, wanted in (('that --pins-sha256 names', digest(path), None),
                                   ('that --pins-sha256 does not name', zeros, f'!= --pins-sha256 {zeros}')):
        try:
            support.Record(path, expected_sha256=expected)
            said = None
        except support.Declined as error:
            said = str(error)
        row(f'record {name}', said is None if wanted is None else wanted in str(said), said or 'read')


def copy_rows(row, judge, work):
    source, link, seen, real = work / 'copy-source', work / 'copy-source-link', [], judge.subprocess.run
    link.symlink_to(source)

    def copied(name, change=None, copy=shutil.copyfile, start=source):
        """What judge.private_copy says of a copy that `copy` makes in place of /bin/cp, after which `change` is done
        to the source or to the copy: 'copied', or the reason of the refusal."""
        target = work / f'copy-{name}'

        def stand_in(cmd, **how):
            seen.append((cmd, how))
            copy(cmd[-2], cmd[-1])
            if change is not None:
                change(Path(cmd[-2]), Path(cmd[-1]))
            return subprocess.CompletedProcess(cmd, 0)
        source.write_text('what the caller gave\n')
        judge.subprocess.run = stand_in
        try:
            judge.private_copy(start, target)
            return 'copied' if (target.read_text(), stat.S_IMODE(target.stat().st_mode)) == (
                'what the caller gave\n', 0o400) else 'another copy'
        except judge.Declined as error:
            return str(error)
        finally:
            judge.subprocess.run = real

    def replaced(file, _copy):
        new = file.with_name('copy-replacement')
        new.write_text(file.read_text())
        os.replace(new, file)

    said = copied('plain')
    row('private: a copy is made by /bin/cp -c, in the environment the driver wrote, and is read-only',
        said == 'copied' and seen == [(['/bin/cp', '-c', str(source.resolve()), str(work / 'copy-plain')],
                                       {'check': True, 'env': judge.CLEAN_ENV})], f'{said}; {seen}'[:300])
    row('private: a symbolic link is copied from the file it leads to',
        copied('through-link', start=link) == 'copied' and seen[-1][0][2] == str(source.resolve()))
    for number, (name, how) in enumerate((
            ('a source that grows during the copy', dict(change=lambda file, _copy: file.write_text('more\n' * 9))),
            ('a source that is replaced by a file with the same bytes during the copy', dict(change=replaced)),
            ('a source whose time of change moves during the copy',
             dict(change=lambda file, _copy: os.utime(file, ns=(1, 1)))),
            ('a copy of another size', dict(change=lambda _file, made: os.truncate(made, 3))),
            ('a hard link in place of a copy', dict(copy=os.link)))):
        said = copied(f'refused-{number}', **how)
        row(f'private: {name} is refused', said.startswith('input changed during private copy: '), said[:100])


def result_rows(row, judge, work):
    import enter as supervisor
    written = {'checker': 'checkSoundLowMem', 'verdict': 'ACCEPTED', 'exit': 0, 'wall_s': 12.5, 'reason': 'accepted',
               'wiring': 'macos-sequential', 'threads': 4, 'legs': {'compare': {'rc': 0}}}
    own = {key: written[key] for key in ('checker', 'verdict', 'exit', 'wall_s', 'reason', 'wiring')}
    config = dict(json.loads((FV / 'check/sound/selftest/comparator.json').read_text()), checker='checkSoundLowMem',
                  wiring='configuration metadata', verdict='ACCEPTED', exit=0)
    path, link = work / 'earlier-result.json', work / 'earlier-result-link.json'
    link.symlink_to(path)
    table = [('a result as the driver hands it over', json.dumps(written) + '\n', True),
             ('a DECLINED of enter.py itself', json.dumps(dict(own, verdict='DECLINED', exit=2)) + '\n', True),
             ('a result that was printed again over several lines', json.dumps(written, indent=2), True),
             ('a result without wall_s', json.dumps({k: v for k, v in own.items() if k != 'wall_s'}), False),
             ('a result without reason', json.dumps({k: v for k, v in own.items() if k != 'reason'}), False),
             ('a result without wiring', json.dumps({k: v for k, v in own.items() if k != 'wiring'}), False),
             ('another value of wiring', json.dumps(dict(own, wiring='configuration metadata')), False),
             ('the name of another judge', json.dumps(dict(own, checker='checkSound')), False),
             ('a verdict with the exit status of another', json.dumps(dict(own, exit=1)), False),
             ('an exit status that is no number', json.dumps(dict(own, verdict='REJECTED', exit=True)), False),
             ('a time that is a text', json.dumps(dict(own, wall_s='12.5')), False),
             ('a reason that is no text', json.dumps(dict(own, reason=None)), False),
             ('a comparator configuration with four keys of a result', json.dumps(config), False),
             ('two results', (json.dumps(own) + '\n') * 2, False), ('a list of one result', json.dumps([own]), False),
             ('a result of more than 1 MiB', json.dumps(dict(own, reason='x' * (1 << 20))), False)]
    for verdict, code in supervisor.STATUS.values():
        table.append((f'{verdict} with exit status {code}', json.dumps(dict(own, verdict=verdict, exit=code)), True))
    for name, text, wanted in table:
        path.write_text(text)
        row(f'earlier: {name} is {"" if wanted else "not "}taken for a result',
            supervisor.earlier_result(path) is wanted and supervisor.earlier_result(link) is wanted)
    row('earlier: a folder is not taken for a result', supervisor.earlier_result(work) is False)
    # The role of each word, as the driver reads it, and which words are values of --json. Roles: i an input (a file
    # the driver reads), o an option word, v the value of another option, j of --json, l of --log, ? unknown, from
    # a refused word on. Of unknown words, those after a word --json are taken for values of it, never an input.
    def read(words):
        a = judge.new_arguments()
        try:
            judge.read_arguments('lowmem', words, a)
        except judge.Declined:
            pass
        return a.roles + [None] * (len(words) - len(a.roles))
    letters = {'input': 'i', 'option': 'o', 'value': 'v', 'json': 'j', 'log': 'l', None: '?'}
    inputs = [str(FV / 'check/sound/selftest' / name)
              for name in ('good.export', 'challenge.export', 'comparator.json')]
    for name, words, wanted, roles in (
            ('--json and --log with their values', [*inputs, '--json', 'J', '--log', 'L'], [4], 'iiiojol'),
            ('a --json that a second one replaces', [*inputs, '--json', 'A', '--json', 'B'], [4, 6], 'iiiojoj'),
            ('--json as the last word', [*inputs, '--json'], [], 'iiio'),
            ('--json whose value is the word --log', [*inputs, '--json', '--log', '--threads', '2'], [4], 'iiiojov'),
            ('--json --log X, which is refused', [*inputs, '--json', '--log', 'X'], [4], 'iiioj?'),
            ('--log whose value is the word --json', [*inputs, '--log', '--json', '--threads', '2'], [], 'iiiolov'),
            ('--log --json X, which is refused', [*inputs, '--log', '--json', 'X'], [5], 'iiiol?'),
            ('--hints whose value is the word --json', [*inputs, '--hints', '--json', '--private-inputs'], [],
             'iiioio'),
            ('an input named --json before a refused argument', [inputs[0], '--json', inputs[2], '--bogus'], [],
             'iii?'),
            ('a number that is refused when the words were read',
             [*inputs, '--hints', '--json', '--threads', '0'], [], 'iiioiov'),
            ('two words', ['--json', 'X'], [], '??'),
            ('two inputs and then --json X', [inputs[0], inputs[1], '--json', 'X'], [3], 'iii?'),
            ('--json behind a refused argument', [*inputs, '--bogus', '--json', 'X'], [5], 'iii???'),
            ('--preflight --json J', ['--preflight', '--json', 'J'], [2], 'ooj'),
            ('--json --json', [*inputs, '--json', '--json'], [4], 'iiioj'),
            ('--json --threads --threads 4', [*inputs, '--json', '--threads', '--threads', '4'], [4], 'iiiojov'),
            ('--json --json R', [*inputs, '--json', '--json', 'R'], [4, 5], 'iiioj?'),
            ('--json R R alone, three inputs', ['--json', 'R', 'R'], [], 'iii'),
            ('--bogus R --json R', [*inputs, '--bogus', 'R', '--json', 'R'], [6], 'iii????'),
            ('the options whose value the driver reads, and others',
             [*inputs, '--hints', 'H', '--hide', 'none', '--pins', 'P', '--workdir', 'W', '--log', 'L'], [],
             'iiioiovoiovol'),
            ('--preflight with --hints none', ['--preflight', '--json', 'J', '--hints', 'none'], [2], 'oojov')):
        got = read(words)
        places = supervisor.places(words, got)
        row(f'earlier: {name}: the roles {roles}, the values of --json at {wanted}',
            ''.join(letters[role] for role in got) == roles and places == wanted, f'{got} {places}')
    # Which words keep an earlier result at a --json path, on files: an input or a word of unknown role that names
    # the same file, by its path, a link, a hard link or another spelling; nothing else, and not a word that cannot
    # be resolved or looked up. In a folder of its own, with an earlier result at each name that the row gives.
    folder = work / 'kept'
    folder.mkdir()

    def kept(words, names, setup=None, unread=False):
        for name in [*names, 'LOOP', 'link', 'hard', 'locked']:
            path = folder / name
            if path.is_dir() and not path.is_symlink():
                path.chmod(0o700)
                shutil.rmtree(path)
            elif path.exists() or path.is_symlink():
                path.unlink()
        for name in names:
            (folder / name).write_text(json.dumps(own))
        if setup:
            setup()
        here = os.getcwd()
        os.chdir(folder)
        try:
            supervisor.take_away(words, [None] * len(words) if unread else read(words))
        finally:
            os.chdir(here)
            if (folder / 'locked').is_dir():
                (folder / 'locked').chmod(0o700)
        return [name for name in names if supervisor.earlier_result(folder / name)]

    searched = []                     # whether this user can look up locked/h all the same (root can, on Linux)

    def locked():
        (folder / 'locked').mkdir()
        (folder / 'locked' / 'h').symlink_to(folder / 'OLD')
        (folder / 'locked').chmod(0o600)
        try:
            os.stat(folder / 'locked' / 'h')
            searched.append(True)
        except OSError:
            searched.append(False)
    for name, words, names, setup, wanted in (
            ('--json --json', [*inputs, '--json', '--json'], ['--json'], None, []),
            ('--json --threads --threads 4', [*inputs, '--json', '--threads', '--threads', '4'], ['--threads'], None,
             []),
            ('--json --json R', [*inputs, '--json', '--json', 'R'], ['--json'], None, []),
            ('--json R R alone', ['--json', 'R', 'R'], ['R'], None, ['R']),
            ('--json R R after the inputs', [*inputs, '--json', 'R', 'R'], ['R'], None, ['R']),
            ('--bogus R --json R', [*inputs, '--bogus', 'R', '--json', 'R'], ['R'], None, ['R']),
            ('--pins-sha256 D --bogus --json R --json R, where each R is a value of --json',
             [*inputs, '--pins-sha256', 'D', '--bogus', '--json', 'R', '--json', 'R'], ['R'], None, []),
            ('--bad --json R --json R', [*inputs, '--bad', '--json', 'R', '--json', 'R'], ['R'], None, []),
            ('--json R --bad --json R', [*inputs, '--json', 'R', '--bad', '--json', 'R'], ['R'], None, []),
            ('--hints --json --json ./--json, where the --hints file is ./--json',
             [*inputs, '--hints', '--json', '--json', './--json'], ['--json'], None, ['--json']),
            ('--bogus --json --json, whose first --json may be the value of --bogus',
             [*inputs, '--bogus', '--json', '--json'], ['--json'], None, ['--json']),
            ("--log '' --hints --json --json ./--json, behind a refused value, where the --hints file is ./--json",
             [*inputs, '--pins-sha256', 'D', '--log', '', '--hints', '--json', '--json', './--json'], ['--json'], None,
             ['--json']),
            ('--hints LOOP, a loop of links', [*inputs, '--hints', 'LOOP', '--json', 'OLD'], ['OLD'],
             lambda: (folder / 'LOOP').symlink_to('LOOP'), []),
            ('--hints with a name of 300 letters', [*inputs, '--hints', 'h' * 300, '--json', 'OLD'], ['OLD'], None, []),
            ('--hints in a folder that cannot be searched', [*inputs, '--hints', 'locked/h', '--json', 'OLD'], ['OLD'],
             locked, None),
            ('an input through a link', [inputs[0], inputs[1], 'link', '--json', 'OLD'], ['OLD'],
             lambda: (folder / 'link').symlink_to('OLD'), ['OLD']),
            ('an input by a hard link', [inputs[0], inputs[1], 'hard', '--json', 'OLD'], ['OLD'],
             lambda: os.link(folder / 'OLD', folder / 'hard'), ['OLD']),
            ('an input by another spelling', [inputs[0], inputs[1], 'gone/../OLD', '--json', './OLD'], ['OLD'], None,
             ['OLD']),
            ('a --hints file, behind a refused argument', [*inputs, '--hints', 'OLD', '--bogus', '--json', 'OLD'],
             ['OLD'], None, ['OLD']),
            ('the value of --log', [*inputs, '--log', 'OLD', '--json', 'OLD'], ['OLD'], None, []),
            ('the value of --workdir', [*inputs, '--workdir', 'OLD', '--json', 'OLD'], ['OLD'], None, [])):
        got = kept(words, names, setup)
        if wanted is None:
            # The folder of mode 0600: a user who cannot search it finds no file at locked/h, and the word keeps
            # nothing; one who searches it all the same finds OLD, and then the input keeps it, as every input does.
            wanted = ['OLD'] if searched[-1] else []
            name += (', which this user searches all the same' if searched[-1] else ', which this user cannot search')
        row(f'earlier: {name}: {"stays" if wanted else "is taken away"}', got == wanted, f'still a result: {got}')
    # Without the driver no role is known, and the words are read as they stand (enter.reading): the word after a
    # word --json is a value of it; a word --json is an option word where an option name stands, from the first
    # word after the inputs on, two at a time; neither keeps anything. Every other word may be an input and keeps,
    # also a --json that may be the value of an option that takes a file.
    for name, words, names, wanted in (
            ('--json R --json R', [*inputs, '--json', 'R', '--json', 'R'], ['R'], []),
            ('--json --json', [*inputs, '--json', '--json'], ['--json'], []),
            ('--json R --bad --json R', [*inputs, '--json', 'R', '--bad', '--json', 'R'], ['R'], []),
            ('--json R R', [*inputs, '--json', 'R', 'R'], ['R'], ['R']),
            ('--bogus R --json R', [*inputs, '--bogus', 'R', '--json', 'R'], ['R'], ['R']),
            ('--hints --json --json ./--json, where the --hints file is ./--json',
             [*inputs, '--hints', '--json', '--json', './--json'], ['--json'], ['--json']),
            ('--bogus --json --json', [*inputs, '--bogus', '--json', '--json'], ['--json'], ['--json']),
            ('--json --threads --threads 4, whose second --threads may be a file',
             [*inputs, '--json', '--threads', '--threads', '4'], ['--threads'], ['--threads']),
            ('--threads 4 --json --json, where --threads stands at the start of the chain',
             [*inputs, '--threads', '4', '--json', '--json'], ['--json'], ['--json']),
            ("--log '' --hints --json --json ./--json, where the --hints file is ./--json",
             [*inputs, '--pins-sha256', 'D', '--log', '', '--hints', '--json', '--json', './--json'], ['--json'],
             ['--json']),
            ('--preflight --json R --json R', ['--preflight', '--json', 'R', '--json', 'R'], ['R'], [])):
        got = kept(words, names, unread=True)
        row(f'earlier: {name}, without the driver: {"stays" if wanted else "is taken away"}', got == wanted,
            f'still a result: {got}')
    # A failure after the new result is in place leaves it saying nothing: write_json empties it, through the
    # descriptor it was written with, before it reports the failure. Here the removal of its other name fails.
    placed = work / 'placed'
    placed.mkdir()
    target = placed / 'verdict.json'
    unlink = Path.unlink

    def refused(path, *args, **kwargs):
        if path.parent == placed and path != target:
            raise PermissionError('planted')
        return unlink(path, *args, **kwargs)
    Path.unlink = refused
    try:
        supervisor.write_json(target, json.dumps(own), False)
        failed = False
    except PermissionError:
        failed = True
    finally:
        Path.unlink = unlink
    row('earlier: write_json, when the file is in place and then something fails: emptied before the failure',
        failed and target.read_text() == '' and all(path.read_text() == '' for path in placed.iterdir()),
        f'failed {failed}, the file: {target.read_text()[:40]!r}')


def judge_rows(row, judge, support, fv, work, record, programs):
    st = fv / 'check/sound/selftest'
    good = [st / 'good.export', st / 'challenge.export', st / 'comparator.json']
    physical = int(subprocess.check_output(['/usr/sbin/sysctl', '-n', 'hw.memsize']))
    count = [0]
    printed = {}                      # the lines on stdout of the run in each directory
    destination = {}                  # the JSON destination that each run was given, if it was given one

    def run(mode, *arguments, env=ENV, json_to=None, trusted=True, plain=False, workdir=None, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, prepare=None):
        """Exit status, the result the judge printed, the directory and the mode of one run through a judge
        script. A run that judges names the record it trusts, unless the row is about that; `plain` passes the
        arguments as they are; `prepare` is given the working directory of the run before it starts."""
        count[0] += 1
        case = work / f'run-{count[0]}'
        case.mkdir()
        if prepare is not None:
            prepare(case)
        words = [str(word) for word in arguments]
        if not plain:
            if trusted and not {'--preflight', '--pins-sha256'} & set(words):
                words += ['--pins-sha256', digest(record)]
            if '--log' not in words:
                words += ['--log', str(case / 'judge.log')]
            words += ['--workdir', str(workdir or case), '--json', str(json_to or case / 'verdict.json')]
        given = [at for at in range(len(words) - 1) if words[at] == '--json']
        destination[case] = case / words[given[-1] + 1] if given else None
        done = subprocess.run([str(fv / SCRIPT[mode]), *words], cwd=case, env=env, stdin=subprocess.DEVNULL,
                              stdout=stdout, stderr=stderr, timeout=600)
        printed[case] = (done.stdout or b'').decode('utf-8', errors='replace').splitlines()
        try:
            said = json.loads(printed[case][-1])
        except (ValueError, IndexError):
            said = {}
        return done.returncode, said if isinstance(said, dict) else {}, case, mode

    def result_at(path):
        """What a reader of the path takes for a result, through a link too: a JSON object with a verdict."""
        try:
            held = json.loads(path.read_bytes())
        except (OSError, ValueError):
            return None
        return held if isinstance(held, dict) and 'verdict' in held else None

    def expect(name, outcome, status, verdict, reason='', also=None, file=True):
        """One run: its exit status, the one line it printed, and the JSON destination it was given, which is a
        file of its own with that line. A row of a run that must not write its result there says `file=False`:
        then the destination holds no result at all, neither this one nor an earlier one. `file='earlier'` is
        for the cases the judge names as outside its rule: the destination still reads as an earlier result."""
        got, said, case, mode = outcome
        ok = (got == status and said.get('verdict') == verdict and said.get('exit') == status
              and said.get('checker') == CHECKER[mode] and said.get('wiring') == 'macos-sequential'
              and list(said)[:5] == ['checker', 'verdict', 'exit', 'wall_s', 'reason']
              and reason in str(said.get('reason')) and len(printed[case]) == 1)
        try:
            where = destination.get(case)
            if ok and where is not None:
                own = (where.is_file() and not where.is_symlink()
                       and where.read_bytes() == (printed[case][0] + '\n').encode())
                ok = own if file is True else not own and (result_at(where) is not None) == (file == 'earlier')
            ok = ok and (also is None or bool(also(said)))
        except (KeyError, TypeError, AttributeError, OSError):
            ok = False
        row(f'judge {name}', ok, f'exit {got} {said.get("verdict")}: {str(said.get("reason"))[:110]}')

    def marked(name):
        path = work / (name + '.export')
        path.write_bytes(good[0].read_bytes() + ('{"marker":"%s"}\n' % name).encode())
        return [path, *good[1:]]

    def legs(*names):
        return lambda said: list(said['legs']) == list(names)

    def unstarted(said):
        return 'selftests' not in said and 'legs' not in said

    retry = {'reason': 'a worker table is full', 'first_rc': 2, 'workers': 1}
    lean_rejects, k2_rejects = 'error: Lean default exited with 1', 'error: gruszka (second kernel) exited with 1'
    for mode in SCRIPT:
        program = judge.MODES[mode]['replay']
        expect(f'{mode}: preflight', run(mode, '--preflight'), 0, 'PREFLIGHT_OK', also=lambda said: (
            [leg['rc'] for leg in said['selftests']['good']['legs'].values()] == [0, 0, 0]
            and list(said['selftests']['bad']['legs']) == ['compare']
            and [(name, leg['rc']) for name, leg in said['selftests']['kbad']['legs'].items()] == [('lean', 1),
                                                                                                   ('k2', 1)]
            and 'legs' not in said and said['pins_sha256'] == digest(record)))
        expect(f'{mode}: no verdict without --pins-sha256', run(mode, *good, trusted=False), 2, 'DECLINED',
               '--pins-sha256 is required to judge', lambda said: (
                   unstarted(said) and 'pins_sha256' not in said and digest(record) not in said['reason']))
        outcome = run(mode, *good)
        started = re.findall(r'started as (.*)$', (outcome[2] / 'judge.log').read_text(), flags=re.M)
        row(f'judge {mode}: every program is started from its copy in the private directory of the run',
            len(started) == 9 and all(Path(path).parent.parent == outcome[2] for path in started)
            and not set(started) & {str(path) for path in programs.values()}, f'{len(started)} starts')
        sizes = {'export': {'size': good[0].stat().st_size, 'private': 'copy'},
                 'challenge': {'size': good[1].stat().st_size, 'private': 'copy'}}
        expect(f'{mode}: accepted by the three legs', outcome, 0, 'ACCEPTED', judge.ACCEPTED, lambda said: (
            legs('compare', 'lean', 'k2')(said) and said['mode'] == 'sequential-lowmem'
            and all(leg['rc'] == 0 and type(leg['ms']) is int and leg['message'] for leg in said['legs'].values())
            and sorted(said['binaries_sha256']) == sorted(['ccmp_lowmem', 'gruszka', program, *support.SELFTESTS])
            and said['binaries_sha256'][program] == digest(programs[program])
            and said['wiring_sha256']['pins.env'] == digest(fv / PINS)
            and said['wiring_sha256'][Path(SCRIPT[mode]).name] == digest(fv / SCRIPT[mode])
            and said['version'].startswith('sound-macos-v1 ') and said['toolchain'] == 'leanprover/lean4:v4.36.0'
            and said['inputs'] == sizes and said['private_inputs_asserted'] == 0 and program in said['basis']
            and ('gruszka_lowmem' in said['basis']) == (mode == 'ultralowmem')
            and (said['memory_limit_bytes'], said['memory_limit_source']) == (physical, 'physical memory')
            and said['threads'] == said['effective_threads'] == os.cpu_count()
            and (outcome[2] / 'judge.log').read_text().startswith(
                f'[{CHECKER[mode]}] memory limit of a leg: {physical / 1024**3:.2f} GiB (physical memory)\n')
            and json.loads((outcome[2] / 'verdict.json').read_text()) == said
            and [stat.S_IMODE((outcome[2] / name).stat().st_mode) for name in ('judge.log', 'verdict.json')]
            == [0o600, 0o600]))
        expect(f'{mode}: rejected by the comparison', run(mode, st / 'bad.export', *good[1:]), 1, 'REJECTED',
               "error: Illegal axiom detected: 'fvCheat'", legs('compare'))
        expect(f'{mode}: rejected by the Lean kernel', run(mode, *marked('lean-rejects')), 1, 'REJECTED', lean_rejects,
               lambda said: legs('compare', 'lean')(said) and said['legs']['lean']['message'].startswith(
                   'Lean default kernel rejects the solution: '))
        expect(f'{mode}: rejected by the replay of an export that does not parse', run(mode, *marked('lean-parse')),
               1, 'REJECTED', lean_rejects, lambda said: said['legs']['lean']['message'].startswith('uncaught exc'))
        expect(f'{mode}: no verdict when the replay runs out of stack', run(mode, *marked('lean-stack')), 2,
               'DECLINED', 'the official-kernel leg could not finish ((kernel) deep recursion detected, use',
               legs('compare', 'lean'))
        expect(f'{mode}: rejected by the second kernel', run(mode, *marked('k2-rejects')), 1, 'REJECTED', k2_rejects,
               lambda said: (legs('compare', 'lean', 'k2')(said)
                             and said['legs']['k2']['message'].startswith('rejected: Bad.decl')))
        expect(f'{mode}: no verdict of the replay', run(mode, *marked('lean-undecided')), 2, 'DECLINED',
               judge.LEAN_NO_VERDICT, legs('compare', 'lean'))
        expect(f'{mode}: second kernel again with one worker', run(mode, *marked('k2-room'), '--threads', '4'),
               0, 'ACCEPTED', also=lambda said: said['legs']['k2']['retry'] == retry and said['effective_threads'] > 1)
    expect('retry: a rejection with one worker is kept', run('lowmem', *marked('k2-room-rejects'), '--threads', '4'),
           1, 'REJECTED', k2_rejects, lambda said: said['legs']['k2']['retry'] == retry)
    expect('retry: none after another decline', run('lowmem', *marked('k2-declines'), '--threads', '4'),
           2, 'DECLINED', 'k2.log: abnormal leg exit 2', lambda said: 'retry' not in said['legs']['k2'])
    expect('retry: one second run and no third', run('lowmem', *marked('k2-full'), '--threads', '4'),
           2, 'DECLINED', 'k2-retry.log: abnormal leg exit 2', lambda said: said['legs']['k2']['retry'] == retry)
    expect('retry: none with one worker', run('lowmem', *marked('k2-full'), '--threads', '1'),
           2, 'DECLINED', 'k2.log: abnormal leg exit 2', lambda said: 'retry' not in said['legs']['k2'])
    # No end of a leg but 0 or 1 is a verdict: the statuses of a command that the launcher or the guard could not
    # start (126, 127, 125), a signal, and a leg that the guard stops for time or memory.
    for status in (2, 125, 126, 127):
        expect(f'a leg that prints its acceptance line and ends with status {status}',
               run('lowmem', *marked(f'lean-exit-{status}')), 2, 'DECLINED', f'lean.log: abnormal leg exit {status}',
               legs('compare', 'lean'))
    expect('a leg that is killed', run('lowmem', *marked('lean-killed')), 2, 'DECLINED', 'abnormal leg exit')
    # Exit status 1 is a rejection only when the program has made one.
    expect('a replay that ends with status 1 and no rejection', run('lowmem', *marked('lean-silent')), 2, 'DECLINED',
           'the official-kernel leg ended with exit status 1 without a rejection of its own', legs('compare', 'lean'))
    expect('a replay that reports an error of the operating system', run('ultralowmem', *marked('lean-io')), 2,
           'DECLINED', 'the official-kernel leg could not finish (uncaught exception: interrupted system call (error '
           'code: 4, interrupted)): no verdict', legs('compare', 'lean'))
    # The time limit leaves room for the self-tests on a busy machine; the judged leg sleeps for a minute.
    expect('a leg beyond the time limit', run('lowmem', *marked('lean-slow'), '--timeout', '20'), 2, 'DECLINED',
           'lean.log: wall limit')
    # The limit of a leg is the physical memory of the machine, or less with --mem-budget-mb. A leg that is
    # stopped there is no verdict; the reason names the limit, and the result what the guard measured.
    expect('a leg beyond the memory limit', run('lowmem', *marked('lean-large'), '--mem-budget-mb', '256'),
           2, 'DECLINED', 'lean.log: the leg needs more memory than its limit, --mem-budget-mb 256 (a larger value '
           'raises it): memory ', lambda said: (
               (said['memory_limit_bytes'], said['memory_limit_source']) == (256 * 2**20, '--mem-budget-mb')
               and said['legs']['lean']['rc'] is None and said['legs']['lean']['ms'] > 0
               and said['legs']['lean']['peak_footprint_bytes'] > 200 * 2**20))
    expect('a memory limit above the memory of the machine',
           run('lowmem', *good, '--mem-budget-mb', str(physical // 2**20 + 1)), 2, 'DECLINED',
           f'--mem-budget-mb {physical // 2**20 + 1}: this machine has {physical // 2**20} MiB of memory', unstarted)
    # What the guard is given: a stand-in writes down its options and becomes the guard of the tree.
    guard = fv / 'tools/guard/fvguard.py'
    released = guard.with_name('fvguard-as-released.py')
    shutil.copy2(guard, released)
    guard.write_text('import os, sys\nwith open(%r, "a") as seen:\n'
                     '    seen.write(" ".join(sys.argv[1:sys.argv.index("--")]) + "\\n")\n'
                     'os.execv(sys.executable, [sys.executable, "-I", %r, *sys.argv[1:]])\n'
                     % (str(work / 'guard-calls'), str(released)))
    for words, limit in (([], physical), (['--mem-budget-mb', str(physical // 2**20)], physical),
                         (['--mem-budget-mb', '300'], 300 * 2**20)):
        (work / 'guard-calls').write_text('')
        outcome = run('lowmem', *good, *words)
        calls = [line.split() for line in (work / 'guard-calls').read_text().splitlines()]
        row(f"judge the guard of every leg is given {'--mem-budget-mb ' + words[1] if words else 'the physical memory'}"
            ' as the limit', outcome[0] == 0 and len(calls) == 9
            and all(call[call.index('--mem') + 1] == str(limit) for call in calls),
            f'exit {outcome[0]}, {len(calls)} calls, ' + ' '.join(sorted({call[call.index("--mem") + 1]
                                                                          for call in calls if "--mem" in call})))
    # A guard that says the output of a leg was not passed on completely: no log of that leg is read.
    guard.write_text('import json, subprocess, sys\n'
                     'done = subprocess.run([sys.executable, "-I", %r, *sys.argv[1:]])\n'
                     'report = sys.argv[sys.argv.index("--json") + 1]\n'
                     'if "/judge/lean" in report:\n'
                     '    told = json.load(open(report))\n'
                     '    told.update(violation="guard", detail="the output of the command was not passed on")\n'
                     '    json.dump(told, open(report, "w"))\n'
                     '    sys.exit(125)\n'
                     'sys.exit(done.returncode)\n' % str(released))
    expect('a leg whose output the guard did not pass on completely', run('lowmem', *marked('lean-rejects')), 2,
           'DECLINED', 'lean.log: guard limit or monitor failure: the output of the command was not passed on',
           legs('compare', 'lean'))
    shutil.copy2(released, guard)
    released.unlink()
    # A limit of the run that ends a self-test is said as that limit, not as programs that cannot judge: the time
    # limit between two legs (the guard of the first leg comes back seven seconds late), the time limit inside a
    # leg (a second kernel that sleeps), and wherever one second ends.
    shutil.copy2(guard, released)
    guard.write_text('import subprocess, sys, time\n'
                     'done = subprocess.run([sys.executable, "-I", %r, *sys.argv[1:]])\n'
                     'if "/selftest-good/compare" in sys.argv[sys.argv.index("--json") + 1]:\n'
                     '    time.sleep(7)\n'
                     'sys.exit(done.returncode)\n' % str(released))
    expect('the time limit between two legs of the self-tests', run('lowmem', *good, '--timeout', '6'), 2,
           'DECLINED', 'during the self-tests: time limit of 6 s exceeded',
           lambda said: 'cannot judge' not in said['reason'] and 'legs' not in said)
    shutil.copy2(released, guard)
    released.unlink()
    slow, other = work / 'slow-gruszka', record.with_name('pins-slow.env')
    slow.write_text('#!/bin/sh\n/bin/sleep 60\n')
    slow.chmod(0o755)
    other.write_text(re.sub('^PIN gruszka .*$', f'PIN gruszka {digest(slow)} {slow}', record.read_text(), flags=re.M))
    pin_programs(fv, {'gruszka': slow})
    expect('the time limit inside a leg of the self-tests',
           run('lowmem', *good, '--pins', other, '--pins-sha256', digest(other), '--timeout', '8'), 2, 'DECLINED',
           'during the self-tests: k2.log: wall limit',
           lambda said: 'cannot judge' not in said['reason'] and 'legs' not in said)
    pin_programs(fv, programs)
    expect('a time limit of one second', run('lowmem', *good, '--timeout', '1'), 2, 'DECLINED',
           also=lambda said: (re.search('time limit|wall limit', said['reason'])
                              and 'cannot judge' not in said['reason']))
    for leg in ('lean', 'k2'):
        expect(f'the {leg} leg cannot read the challenge, a folder of the user or the record, or write to an input, '
               'a program, the record or the driver', run('ultralowmem', *marked(leg + '-peek')), 0, 'ACCEPTED')
    # What a leg's program is given: the variables the driver names, with the values of the judge scripts'
    # wrappers, and nothing of the caller, the driver or the guard. The stand-ins are shell scripts, and the
    # shell adds three names of its own.
    hidden = work / 'hide-for-environment.txt'
    hidden.write_text('Hidden.decl\n')
    for mode, options in (('lowmem', ['--hide', hidden]), ('ultralowmem', [])):
        outcome = run(mode, *good, '--threads', '3', *options,
                      env=dict(ENV, LEAN_PATH='/caller', DYLD_LIBRARY_PATH='/caller'))
        log, wrong = (outcome[2] / 'judge.log').read_text().split('\n'), []
        replay = {'PCHK_PRIO_FILE': 'hints', 'PCHK_SLOW_MS': '10000', 'LEAN_STACK_SIZE_KB': '917376',
                  **judge.MODES[mode]['replay_env'], **({'PCHK_HIDE_FILE': 'hide'} if options else {})}
        for leg, extra in (('compare', {}), ('lean', replay), ('k2', {})):
            start = log.index(f'--- judge/{leg}.log (last 64 KiB) ---')
            said = next(line for line in log[start:] if line.startswith('note: environment '))
            given = dict(item.split('=', 1) for item in said[len('note: environment '):].split('|') if item)
            for name in ('PWD', 'OLDPWD', 'SHLVL', '_'):
                given.pop(name, None)
            home = given.get('HOME', '')
            private = home[:-len(f'/judge/{leg}')]
            wanted = {'PATH': '/usr/bin:/bin', 'HOME': home, 'TMPDIR': home, 'LANG': 'C.UTF-8',
                      'LEAN_ABORT_ON_PANIC': '1', 'LEAN_NUM_THREADS': '3'}
            wanted.update({name: f'{private}/{value}' if name.endswith('_FILE') else value
                           for name, value in extra.items()})
            if given != wanted or not home.endswith(f'/judge/{leg}') or Path(private).parent != outcome[2]:
                wrong.append(f'{leg}: {sorted(set(given.items()) ^ set(wanted.items()))}')
        expect(f'{mode}: every leg gets the environment the driver names and nothing else', outcome, 0, 'ACCEPTED',
               also=lambda said: not wrong)
        if wrong:
            print('  ' + '; '.join(wrong)[:600])

    # What happens while a leg runs. The Lean leg waits in its own directory until `change` is done. With
    # `session` the judge script leads a process group of its own, as a job of a terminal does; 'nohup' also
    # makes it ignore a hangup.
    def while_a_leg_runs(label, change, session=None, json_to=None):
        case = work / label
        case.mkdir()
        cmd = [str(fv / SCRIPT['lowmem']), *map(str, marked('lean-waits')), '--pins-sha256', digest(record),
               '--timeout', '120', '--workdir', str(case), '--json', str(json_to or case / 'verdict.json')]
        destination[case] = Path(cmd[-1])
        nohup = (lambda: [signal.signal(number, signal.SIG_IGN) for number in (signal.SIGHUP, signal.SIGINT)]) \
            if session == 'nohup' else None
        with subprocess.Popen(cmd, cwd=case, env=ENV, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL, start_new_session=session is not None,
                              preexec_fn=nohup) as judging:
            waiting = []
            while not waiting and judging.poll() is None:
                time.sleep(0.2)
                waiting = list(case.glob('.check*/judge/lean/ready'))
            for ready in waiting:
                change(ready.parents[2], judging.pid)
                if ready.parent.is_dir():       # a driver that was stopped has removed its directory
                    (ready.parent / 'go').touch()
            printed[case] = judging.communicate()[0].decode('utf-8', errors='replace').splitlines()
        return judging.returncode, json.loads(printed[case][-1]) if printed[case] else {}, case, 'lowmem'

    def change_copy(private, _script):
        (private / 'gruszka').chmod(0o700)
        with (private / 'gruszka').open('a') as copy:
            copy.write('# changed\n')

    def signal_driver(number):
        """Send a signal to the driver that the judge script with process id `script` started: the one process
        below it that runs judge.py."""
        def send(_private, script):
            listed = subprocess.run(['/bin/ps', '-axo', 'pid=,ppid=,command='], capture_output=True, text=True).stdout
            parent = {int(line.split()[0]): int(line.split()[1]) for line in listed.splitlines()}
            drivers = []
            for line in listed.splitlines():
                pid = above = int(line.split()[0])
                while above in parent and above != script:
                    above = parent[above]
                if above == script and re.search(r' -I \S*macos/judge\.py lowmem ', line):
                    drivers.append(pid)
            if len(drivers) == 1:
                os.kill(drivers[0], number)
                time.sleep(3)
        return send

    original = programs['gruszka'].read_bytes()
    expect('a program replaced at its recorded path while a leg runs is not what runs',
           while_a_leg_runs('replaced', lambda private, _script: programs['gruszka'].write_text(
               '#!/bin/sh\necho "rejected: Any.decl: not the recorded program"\nexit 1\n')),
           0, 'ACCEPTED', also=lambda said: said['legs']['k2']['rc'] == 0)
    programs['gruszka'].write_bytes(original)
    expect('a private copy of a program that changes while a leg runs',
           while_a_leg_runs('copy-changed', change_copy), 2, 'DECLINED', 'an input file was modified during the check',
           legs('compare', 'lean'))
    # The files of the judge are watched like the inputs: the run ends at the leg during which one changed.
    gate = fv / 'check/xversion/xvcheck.py'
    unchanged = gate.read_bytes()
    outcome = while_a_leg_runs('judge-changed', lambda _private, _script: gate.write_bytes(unchanged + b'# changed\n'))
    gate.write_bytes(unchanged)
    expect('a file of the judge that changes while a leg runs', outcome, 2, 'DECLINED',
           'judge wiring changed during run', legs('compare', 'lean'))

    def left_running(case):
        """The processes that still name a path of this run a few seconds after it ended."""
        for _attempt in range(40):
            listed = subprocess.run(['/bin/ps', '-axo', 'command='], capture_output=True, text=True).stdout
            found = [text[:80] for text in listed.splitlines() if str(case) in text]
            if not found:
                break
            time.sleep(0.5)
        return found

    # enter.py is the one that publishes. A driver that is interrupted hands over its own DECLINED; for one that
    # is killed enter.py says it.
    outcome = while_a_leg_runs('interrupted', signal_driver(signal.SIGTERM))
    expect('a driver that gets SIGTERM while a leg runs', outcome, 2, 'DECLINED', 'interrupted by signal 15',
           lambda said: not left_running(outcome[2]))
    outcome = while_a_leg_runs('killed', signal_driver(signal.SIGKILL))
    expect('a driver that is killed while a leg runs: enter.py says DECLINED, nothing keeps running', outcome, 2,
           'DECLINED', 'the macOS driver ended without a result (signal 9)',
           lambda said: list(said) == ['checker', 'verdict', 'exit', 'wall_s', 'reason', 'wiring']
           and not left_running(outcome[2]))

    # A stand-in for the driver: judge.py with another end, which hands over what a row gives it and ends with the
    # status the row gives it. What it prints on stdout must reach stderr, never the caller's stdout.
    driver = fv / 'check/sound/macos/judge.py'
    real = driver.read_text()
    ending = "if __name__ == '__main__':\n"

    def stand_in(handed, status, first=''):
        """`handed`: the bytes for descriptor 3. @STDIN@ in it becomes what the caller wrote to stdin, @MASK@ the
        signals that are blocked when the driver starts."""
        driver.write_text(
            real[:real.index(ending)] + ending
            + '    print("a line on the stdout of the driver", flush=True)\n'
            + ''.join(f'    {line}\n' for line in first.splitlines())
            + f'    handed = {handed!r}.replace(b"@STDIN@", sys.stdin.buffer.read())\n'
            + '    blocked = sorted(int(number) for number in signal.pthread_sigmask(signal.SIG_BLOCK, []))\n'
            + '    os.write(3, handed.replace(b"@MASK@", str(blocked).encode()))\n'
            + f'    sys.exit({status})\n')

    def evidence(verdict, change=lambda shown: None):
        """What a positive result must show: the three controls and, for ACCEPTED, the three legs."""
        shown = {'selftests': {'good': {'legs': {name: {'rc': 0} for name in ('compare', 'lean', 'k2')}},
                               'bad': {'legs': {'compare': {'rc': 1}}},
                               'kbad': {'legs': {'lean': {'rc': 1}, 'k2': {'rc': 1}}}}}
        if verdict == 'ACCEPTED':
            shown['legs'] = {name: {'rc': 0, 'ms': 5} for name in ('compare', 'lean', 'k2')}
        change(shown)
        return shown

    def envelope(verdict, code, checker='checkSoundLowMem', reason='a stand-in for the driver', shown=None, **more):
        record = {'checker': checker, 'verdict': verdict, 'exit': code, 'reason': reason, 'more': [1, 2]}
        if shown is None and verdict in ('ACCEPTED', 'PREFLIGHT_OK'):
            shown = evidence(verdict)
        record.update(shown or {})
        return json.dumps(dict({'record': record, 'json_checked': True, 'log_written': False}, **more)).encode()

    def supervised(asked, **how):
        """Run the judge script with the stand-in: (exit status, lines on stdout, the JSON file or None, stderr)."""
        count[0] += 1
        case = work / f'handed-{count[0]}'
        case.mkdir()
        done = subprocess.run([str(fv / SCRIPT['lowmem']), *map(str, asked), '--json', str(case / 'verdict.json')],
                              cwd=case, env=ENV, capture_output=True, timeout=120,
                              **dict({'input': b''}, **how))
        lines = done.stdout.decode().splitlines()
        written = (case / 'verdict.json').read_text() if (case / 'verdict.json').exists() else None
        return done.returncode, lines, written, done.stderr.decode(errors='replace'), case

    own = {'checker': 'checkSoundLowMem', 'verdict': 'DECLINED', 'exit': 2, 'wiring': 'macos-sequential'}

    def own_declined(lines, reason):
        """Whether the one line is a DECLINED that enter.py made itself, with this reason."""
        try:
            said = json.loads(lines[0])
        except (ValueError, IndexError):
            return False
        return len(lines) == 1 and dict(said, wall_s=0) == dict(own, wall_s=0, reason=reason) \
            and type(said['wall_s']) is float

    for name, handed, status, asked, code in (
            ('ACCEPTED with its status', envelope('ACCEPTED', 0), 40, good, 0),
            ('REJECTED with its status', envelope('REJECTED', 1), 41, good, 1),
            ('DECLINED with its status', envelope('DECLINED', 2), 42, good, 2),
            ('PREFLIGHT_OK with its status, asked for', envelope('PREFLIGHT_OK', 0), 43, ['--preflight'], 0)):
        stand_in(handed, status)
        got, lines, written, noise, _case = supervised(asked)
        given = json.loads(handed)['record']
        row(f'judge a driver that hands over {name}: published as it is, exit status {code}',
            got == code and [json.loads(line) for line in lines] == [given] and written == lines[0] + '\n'
            and 'a line on the stdout of the driver\n' in noise
            and noise.endswith(f"[checkSoundLowMem] verdict {given['verdict']} (exit {code}): {given['reason']}\n"),
            f'exit {got}, {len(lines)} line(s): {str(lines[-1:])[:90]}')
    huge = envelope('ACCEPTED', 0)
    # A positive result without what it claims: the legs and the controls, each with its exit status.
    lacking = [(name, envelope(verdict, 0, shown=evidence(verdict, change)), 40 if verdict == 'ACCEPTED' else 43,
                good if verdict == 'ACCEPTED' else ['--preflight']) for name, verdict, change in (
        ('ACCEPTED without legs and controls', 'ACCEPTED', lambda shown: shown.clear()),
        ('ACCEPTED without controls', 'ACCEPTED', lambda shown: shown.pop('selftests')),
        ('ACCEPTED without legs', 'ACCEPTED', lambda shown: shown.pop('legs')),
        ('ACCEPTED without the leg of the second kernel', 'ACCEPTED', lambda shown: shown['legs'].pop('k2')),
        ('ACCEPTED with a leg that ended with status 1', 'ACCEPTED', lambda shown: shown['legs']['lean'].update(rc=1)),
        ('ACCEPTED with a leg whose status is false', 'ACCEPTED', lambda shown: shown['legs']['k2'].update(rc=False)),
        ('ACCEPTED with a fourth leg', 'ACCEPTED', lambda shown: shown['legs'].update(nanoda={'rc': 0})),
        ('ACCEPTED with a second kernel that accepted the kernel-invalid export', 'ACCEPTED',
         lambda shown: shown['selftests']['kbad']['legs']['k2'].update(rc=0)),
        ('ACCEPTED with a custom axiom that the replay rejected and the comparison did not', 'ACCEPTED',
         lambda shown: shown['selftests']['bad'].update(legs={'compare': {'rc': 0}, 'lean': {'rc': 1}})),
        ('PREFLIGHT_OK without controls', 'PREFLIGHT_OK', lambda shown: shown.clear()),
        ('PREFLIGHT_OK with a known-good export that the replay rejected', 'PREFLIGHT_OK',
         lambda shown: shown['selftests']['good']['legs']['lean'].update(rc=1)))]
    for name, handed, status, asked in (
            *lacking,
            ('nothing, with exit status 0', b'', 0, good),
            ('nothing, with the status of ACCEPTED', b'', 40, good),
            ('ACCEPTED with exit status 0', envelope('ACCEPTED', 0), 0, good),
            ('ACCEPTED with exit status 1', envelope('ACCEPTED', 0), 1, good),
            ('ACCEPTED with the status of REJECTED', envelope('ACCEPTED', 0), 41, good),
            ('REJECTED with the status of ACCEPTED', envelope('REJECTED', 1), 40, good),
            ('the ACCEPTED of the other judge script', envelope('ACCEPTED', 0, 'checkSoundUltraLowMem'), 40, good),
            ('PREFLIGHT_OK, not asked for', envelope('PREFLIGHT_OK', 0), 43, good),
            ('PREFLIGHT_OK with the status of ACCEPTED', envelope('PREFLIGHT_OK', 0), 40, good),
            ('ACCEPTED with the status of PREFLIGHT_OK after --preflight', envelope('ACCEPTED', 0), 43,
             ['--preflight']),
            ('ACCEPTED after --preflight', envelope('ACCEPTED', 0), 40, ['--preflight']),
            ('ACCEPTED with exit 1 in the result', envelope('ACCEPTED', 1), 40, good),
            ('ACCEPTED with a reason that is no text', envelope('ACCEPTED', 0, reason=None), 40, good),
            ('half a result', envelope('ACCEPTED', 0)[:40], 40, good),
            ('two results', envelope('ACCEPTED', 0) * 2, 40, good),
            ('a list', b'[]', 40, good),
            ('a result that is no object', b'{"record": "ACCEPTED"}', 40, good),
            ('bytes that are no text', b'\xff\xfe' + envelope('ACCEPTED', 0), 40, good),
            ('more than 1 MiB', huge[:-1] + b' ' * (1 << 20) + b'}', 40, good)):
        stand_in(handed, status)
        got, lines, written, noise, _case = supervised(asked)
        row(f'judge a driver that hands over {name}: DECLINED by enter.py, and nothing else is published',
            got == 2 and own_declined(lines, f'the macOS driver ended without a result (status {status})')
            and written == lines[0] + '\n' and 'ACCEPTED' not in lines[0] + noise.replace('--json', ''),
            f'exit {got}, {len(lines)} line(s): {str(lines[-1:])[:110]}')
    stand_in(envelope('DECLINED', 2, reason='@STDIN@'), 42)
    got, lines, _written, _noise, _case = supervised(good, input=b'what the caller wrote to stdin')
    row('judge the driver reads what the caller writes to stdin',
        got == 2 and len(lines) == 1 and json.loads(lines[0])['reason'] == 'what the caller wrote to stdin')
    # The three signals are blocked when the driver starts, so that one that arrives before its handlers are set
    # waits for them. The real driver unblocks them: the rows with a signal above and below.
    stand_in(envelope('DECLINED', 2, reason='@MASK@'), 42)
    got, lines, _written, _noise, _case = supervised(good)
    row('judge the driver starts with TERM, INT and HUP blocked', got == 2 and len(lines) == 1
        and json.loads(lines[0])['reason'] == str(sorted(map(int, (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)))),
        str(lines)[:120])
    # A signal for the judge script before the result is published is DECLINED, also when the driver is done with
    # ACCEPTED. The stand-in sends it to its parent and hands over half a second later.
    for number in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        stand_in(envelope('ACCEPTED', 0), 40, first=f'os.kill(os.getppid(), {int(number)})\ntime.sleep(0.5)')
        got, lines, written, noise, _case = supervised(good)
        row(f'judge signal {int(number)} for the judge script while the driver finishes with ACCEPTED: DECLINED',
            got == 2 and own_declined(lines, f'interrupted by signal {int(number)}') and written == lines[0] + '\n'
            and 'ACCEPTED' not in noise.replace('--json', ''), f'exit {got}: {str(lines)[:120]}')
    # A signal that the caller ignores does not count.
    stand_in(envelope('ACCEPTED', 0), 40, first=f'os.kill(os.getppid(), {int(signal.SIGHUP)})\ntime.sleep(0.5)')
    got, lines, written, _noise, _case = supervised(
        good, preexec_fn=lambda: signal.signal(signal.SIGHUP, signal.SIG_IGN))
    row('judge a hangup for a judge script that was started to ignore it, while the driver finishes: ACCEPTED',
        got == 0 and len(lines) == 1 and json.loads(lines[0])['verdict'] == 'ACCEPTED' and written == lines[0] + '\n')
    # From the moment the result is being published it stands. The caller's stdout is a pipe that is full, so
    # enter.py has written the JSON file and waits in its write to stdout when the signal arrives.
    stand_in(envelope('ACCEPTED', 0), 40)

    def while_it_publishes(then):
        """The judge script with a full pipe as its stdout. When the JSON file is there, `then(process, directory,
        pipe)` is done and says what arrived on the pipe: (exit status, those lines, the directory, whether the
        script was waiting in its write)."""
        count[0] += 1
        case = work / f'handed-{count[0]}'
        case.mkdir()
        reader, writer = os.pipe()
        os.set_blocking(writer, False)
        filled = 0
        try:
            while True:
                filled += os.write(writer, b'x' * 4096)
        except BlockingIOError:
            pass
        os.set_blocking(writer, True)
        with subprocess.Popen([str(fv / SCRIPT['lowmem']), *map(str, good), '--json', str(case / 'verdict.json')],
                              cwd=case, env=ENV, stdin=subprocess.DEVNULL, stdout=writer,
                              stderr=subprocess.DEVNULL) as publishing:
            os.close(writer)
            for _attempt in range(300):
                if (case / 'verdict.json').exists():
                    break
                time.sleep(0.1)
            time.sleep(0.5)
            waits = publishing.poll() is None
            arrived = then(publishing, case, reader)[filled:].decode().splitlines()
            got = publishing.wait(60)
        return got, arrived, case, waits

    def stopped_then_read(publishing, _case, reader):
        os.kill(publishing.pid, signal.SIGTERM)
        time.sleep(0.5)
        with os.fdopen(reader, 'rb') as caller:
            return caller.read()

    got, arrived, case, waits = while_it_publishes(stopped_then_read)
    row('judge SIGTERM for the judge script while it publishes ACCEPTED: the result stands',
        waits and got == 0 and len(arrived) == 1 and json.loads(arrived[0])['verdict'] == 'ACCEPTED'
        and (case / 'verdict.json').read_text() == arrived[0] + '\n', f'exit {got}, waiting {waits}: {arrived}'[:150])
    # The other end: the line cannot be printed, because nobody reads the pipe any more, and the file, which says
    # ACCEPTED, can be neither rewritten nor removed, because its folder takes no change any more. The file must
    # not go on saying more than the run did: it is emptied.

    def folder_closed_then_reader_gone(_publishing, case, reader):
        case.chmod(0o500)
        os.close(reader)
        return b''

    got, _arrived, case, waits = while_it_publishes(folder_closed_then_reader_gone)
    case.chmod(0o700)
    row('judge an ACCEPTED in the file that cannot be printed, in a folder that takes no change: the file is emptied',
        waits and got == 2 and (case / 'verdict.json').read_text() == '' and len(list(case.iterdir())) == 1,
        f'exit {got}, waiting {waits}, the file: {(case / "verdict.json").read_text()[:60]!r}')
    # And where the file takes no change either: it is emptied through the descriptor it was written with.

    def all_closed_then_reader_gone(_publishing, case, reader):
        (case / 'verdict.json').chmod(0o400)
        case.chmod(0o500)
        os.close(reader)
        return b''

    got, _arrived, case, waits = while_it_publishes(all_closed_then_reader_gone)
    case.chmod(0o700)
    row('judge an ACCEPTED in the file that cannot be printed, where folder and file take no change: emptied',
        waits and got == 2 and (case / 'verdict.json').read_text() == '' and len(list(case.iterdir())) == 1,
        f'exit {got}, waiting {waits}, the file: {(case / "verdict.json").read_text()[:60]!r}')

    # A driver that does not end is killed after a minute: one that has handed over, and one that was sent a
    # signal. The rows shorten the minute.
    supervisor = fv / 'check/sound/macos/enter.py'
    patient = supervisor.read_text()
    supervisor.write_text(patient.replace('GRACE = 60 ', 'GRACE = 2 '))
    stand_in(envelope('ACCEPTED', 0), 40)
    driver.write_text(driver.read_text().replace('    sys.exit(40)\n', '    os.close(3)\n    time.sleep(300)\n'))
    got, lines, written, _noise, _case = supervised(good)
    row('judge a driver that hands over ACCEPTED and does not end: killed, DECLINED',
        patient.count('GRACE = 60 ') == 1 and got == 2
        and own_declined(lines, 'the macOS driver ended without a result (signal 9)') and written == lines[0] + '\n',
        f'exit {got}: {str(lines)[:120]}')
    stand_in(envelope('ACCEPTED', 0), 40, first='time.sleep(300)')
    count[0] += 1
    case = work / f'handed-{count[0]}'
    case.mkdir()
    with subprocess.Popen([str(fv / SCRIPT['lowmem']), *map(str, good), '--json', str(case / 'verdict.json')],
                          cwd=case, env=ENV, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                          stderr=subprocess.DEVNULL) as deaf:
        time.sleep(2)
        os.kill(deaf.pid, signal.SIGTERM)
        began = time.monotonic()
        lines = deaf.communicate(timeout=120)[0].decode().splitlines()
        took = time.monotonic() - began
    row('judge a driver that does not end after the signal that was passed on: killed, DECLINED',
        deaf.returncode == 2 and own_declined(lines, 'interrupted by signal 15') and took < 30
        and (case / 'verdict.json').read_text() == lines[0] + '\n' and not left_running(case),
        f'exit {deaf.returncode} after {took:.1f} s: {str(lines)[:120]}')
    # The time such a driver is given runs from the first signal: more signals, here one a second, do not put
    # its end off.
    count[0] += 1
    case = work / f'handed-{count[0]}'
    case.mkdir()
    with subprocess.Popen([str(fv / SCRIPT['lowmem']), *map(str, good), '--json', str(case / 'verdict.json')],
                          cwd=case, env=ENV, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                          stderr=subprocess.DEVNULL) as deaf:
        time.sleep(2)
        began, sent = time.monotonic(), 0
        while deaf.poll() is None and time.monotonic() - began < 60:
            if sent < 6 and time.monotonic() - began >= sent:
                os.kill(deaf.pid, signal.SIGTERM)
                sent += 1
            time.sleep(0.05)
        took = time.monotonic() - began
        lines = deaf.communicate(timeout=120)[0].decode().splitlines()
    supervisor.write_text(patient)
    row('judge a driver that does not end, and a signal every second: killed two seconds after the first',
        deaf.returncode == 2 and own_declined(lines, 'interrupted by signal 15') and took < 4.5 and sent < 6,
        f'exit {deaf.returncode} after {took:.1f} s and {sent} signals: {str(lines)[:100]}')
    # The JSON destination. An earlier result there does not outlive a run; another file stays unless the driver
    # has compared the destination with every file it protects.
    earlier = json.dumps({'checker': 'checkSoundUltraLowMem', 'verdict': 'ACCEPTED', 'exit': 0, 'wall_s': 1.5,
                          'reason': 'earlier', 'wiring': 'macos-sequential'}) + '\n'
    # `kept` is what the file holds afterwards when it is not the published line: its old text, or None for no file.
    for name, handed, status, before, published, kept in (
            ('an earlier result and a driver that is killed', b'', -9, earlier, 'DECLINED', ''),
            ('an earlier result and a refusal before the driver has compared the destination',
             envelope('DECLINED', 2, json_checked=None), 42, earlier, 'DECLINED', ''),
            ('another file and a destination the driver has not compared',
             envelope('ACCEPTED', 0, json_checked=None), 40, 'not a result\n', 'DECLINED', 'not a result\n'),
            ('another file and a destination the driver has compared', envelope('ACCEPTED', 0), 40,
             'not a result\n', 'ACCEPTED', ''),
            ('no file and a destination the driver has refused', envelope('DECLINED', 2, json_checked=False), 42,
             None, 'DECLINED', None),
            ('an earlier result and a destination the driver has refused',
             envelope('DECLINED', 2, json_checked=False), 42, earlier, 'DECLINED', None)):
        stand_in(handed, 0 if status < 0 else status, first='os.kill(os.getpid(), 9)' if status < 0 else '')
        count[0] += 1
        case = work / f'handed-{count[0]}'
        case.mkdir()
        if before is not None:
            (case / 'verdict.json').write_text(before)
        done = subprocess.run([str(fv / SCRIPT['lowmem']), *map(str, good), '--json', str(case / 'verdict.json')],
                              cwd=case, env=ENV, capture_output=True, timeout=120, stdin=subprocess.DEVNULL)
        lines = done.stdout.decode().splitlines()
        after = (case / 'verdict.json').read_text() if (case / 'verdict.json').exists() else None
        row(f'judge --json with {name}', len(lines) == 1 and json.loads(lines[0])['verdict'] == published
            and after == (lines[0] + '\n' if kept == '' else kept)
            and (not kept or 'not an earlier result' in lines[0]), f'{lines}'[:150])
    driver.write_text('import sys\nsys.exit(40)\n')
    # A line of enter.py or of check-sound.sh holds no word of the caller: a judge script under a name with a
    # double quote, as a copy and as a link, answers with one JSON line that has one verdict.
    def one_verdict(text):
        keys = []
        try:
            lines = [json.loads(line, object_pairs_hook=lambda pairs: keys.extend(k for k, _ in pairs) or dict(pairs))
                     for line in text.splitlines()]
        except ValueError:
            return False
        return len(lines) == 1 and keys.count('verdict') == 1 and lines[0]['verdict'] == 'DECLINED'

    odd = 'x","verdict":"ACCEPTED","y":".sh'
    for script in (SCRIPT['lowmem'], 'check/sound/check-sound.sh'):
        copy, link = (fv / script).with_name(odd), work / odd
        shutil.copy2(fv / script, copy)
        link.symlink_to(fv / script)
        answers = [subprocess.run([str(path), *map(str, good)], cwd=work, env=ENV, capture_output=True, text=True)
                   for path in (copy, link)]
        copy.unlink()
        link.unlink()
        row(f'judge {Path(script).name} under a name with a double quote: one JSON line with one verdict',
            all(done.returncode == 2 and one_verdict(done.stdout) for done in answers),
            ' | '.join(done.stdout.strip()[:90] for done in answers))
    driver.write_text(real)
    for name, words in (('without a mode', []), ('with another mode', ['sound', *map(str, good)])):
        done = subprocess.run(['/usr/bin/python3', '-I', str(fv / 'check/sound/macos/enter.py'), *words], env=ENV,
                              capture_output=True, text=True)
        row(f'judge enter.py {name}: no verdict, no driver', done.returncode == 2 and one_verdict(done.stdout)
            and dict(json.loads(done.stdout), wall_s=0) == dict(
                own, checker='enter.py', wall_s=0, reason='enter.py needs the mode lowmem or ultralowmem'),
            f'exit {done.returncode} {done.stdout[:150]}')

    # TERM to the process the caller started stops the driver, whose DECLINED is published; nothing keeps running.
    outcome = while_a_leg_runs('launcher-stopped', lambda _private, script: (os.kill(script, signal.SIGTERM),
                                                                              time.sleep(3)))
    expect('a judge script that gets SIGTERM while a leg runs: one answer, the driver\'s', outcome, 2, 'DECLINED',
           'interrupted by signal 15', lambda said: 'selftests' in said and not left_running(outcome[2]))
    # KILL of that process: nobody is left to publish. The leg is stopped, without being released by this test,
    # and no result of the run exists anywhere.
    stopped = []

    def kill_script(private, script):
        os.kill(script, signal.SIGKILL)
        for _attempt in range(100):
            if not private.is_dir():
                break
            time.sleep(0.1)
        stopped.append(not private.is_dir())
    got, said, case, _mode = while_a_leg_runs('launcher-killed', kill_script)
    row('judge a judge script that is killed while a leg runs: the leg is stopped, and there is no result',
        got == -signal.SIGKILL and said == {} and printed[case] == [] and stopped == [True]
        and not (case / 'verdict.json').exists() and not left_running(case),
        f'exit {got}, stdout {printed[case]}, stopped {stopped}'[:150])
    # A signal to the whole process group of the judge script, as a terminal sends it: one DECLINED, nothing left.
    for number, name in ((signal.SIGINT, 'an interrupt'), (signal.SIGHUP, 'a hangup')):
        outcome = while_a_leg_runs(f'group-{number}', lambda _private, script: (os.killpg(script, number),
                                                                                time.sleep(3)), session='own')
        # The driver gets the signal itself and once more from enter.py, which passes on what it gets.
        expect(f'{name} for the process group of the judge script while a leg runs', outcome, 2, 'DECLINED',
               f'interrupted by signal {int(number)}',
               lambda said: 'selftests' in said and not left_running(outcome[2]))
        outcome = while_a_leg_runs(f'alone-{number}', lambda _private, script: (os.kill(script, number),
                                                                                time.sleep(3)))
        expect(f'{name} for the judge script alone while a leg runs: passed on as it came', outcome, 2, 'DECLINED',
               f'interrupted by signal {int(number)}',
               lambda said: 'selftests' in said and not left_running(outcome[2]))
    # A caller that ignores hangups and interrupts (nohup, a job in the background) gets its verdict: the run goes
    # on after them.
    outcome = while_a_leg_runs('nohup', lambda _private, script: (
        os.killpg(script, signal.SIGHUP), os.killpg(script, signal.SIGINT), time.sleep(2)), session='nohup')
    expect('a hangup and an interrupt for the process group of a judge script that was started to ignore them',
           outcome, 0, 'ACCEPTED', also=lambda said: not left_running(outcome[2]))
    reader, writer = os.pipe()
    os.close(reader)
    outcome = run('lowmem', *good, stdout=writer)
    os.close(writer)
    lost = json.loads((outcome[2] / 'verdict.json').read_text())
    row('judge a run whose stdout nobody reads: exit status 2, and the JSON file says so',
        outcome[0] == 2 and (lost.get('verdict'), lost.get('exit'), lost.get('reason')) == (
            'DECLINED', 2, 'cannot write the result to stdout'), f'exit {outcome[0]} {lost.get("verdict")}')
    # The destination is tried before the driver starts: no run for a result that could not be written.
    locked = work / 'locked'
    locked.mkdir(mode=0o500)
    expect('--json in a folder that cannot be written: no run', run('lowmem', *good, json_to=locked / 'verdict.json'),
           2, 'DECLINED', 'cannot write JSON: ',
           lambda said: list(said) == ['checker', 'verdict', 'exit', 'wall_s', 'reason', 'wiring'], file=False)
    # A destination that cannot be written any more when the run ends: the ACCEPTED of the driver is not published.
    locked.chmod(0o700)
    outcome = while_a_leg_runs('late-locked', lambda _private, _script: locked.chmod(0o500),
                               json_to=locked / 'verdict.json')
    locked.chmod(0o700)
    expect('--json in a folder that cannot be written when the run ends: the ACCEPTED is not published', outcome, 2,
           'DECLINED', 'cannot write JSON: ', lambda said: legs('compare', 'lean', 'k2')(said)
           and not list(locked.iterdir()), file=False)
    # A failure of enter.py itself is no verdict and has the exit status of none. With six descriptors to open,
    # enter.py cannot start the driver; with more the run declines as usual. With fewer the shell of the judge
    # script fails first, and there is no row: with five, bash 3.2 cannot make the pipe of its first command
    # substitution and then closes two descriptors whose numbers it never set. In most process layouts that frees
    # its input, which leaves room for the hand-over; in others the run ends without a line, with exit status 2 or
    # 127 (seen with more variables in the environment or more arguments), which is no verdict either.
    import resource
    ends, own_failures, other = [], 0, []
    for limit in range(6, 10):
        done = subprocess.run([str(fv / SCRIPT['lowmem']), *map(str, good)], cwd=work, env=ENV, capture_output=True,
                              stdin=subprocess.DEVNULL, text=True,
                              preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_NOFILE, (limit, limit)))
        lines = done.stdout.splitlines()
        try:
            said = json.loads(lines[0]) if len(lines) == 1 else {}
        except ValueError:
            said = {}
        ends.append(done.returncode == 2 and (said.get('verdict'), said.get('exit')) == ('DECLINED', 2))
        own_failures += str(said.get('reason')).startswith('enter.py failed (OSError: ')
        if not ends[-1]:
            other.append(f'with {limit}: exit {done.returncode}, stdout {done.stdout[:100]!r}, stderr '
                         f'{done.stderr[-200:]!r}')
    row('judge with 6 to 9 descriptors to open: one DECLINED line and exit status 2, also when enter.py fails',
        all(ends) and own_failures >= 1, f'{ends}, {own_failures} failure(s) of enter.py itself' + ''.join(
            '; ' + one for one in other))
    # A driver that cannot be read, here for a module it imports: enter.py says so, with the status of no verdict.
    # Its reader of the arguments is the driver's, so nothing is written; but a result of an earlier run after the
    # word --json is taken away all the same.
    module = fv / 'check/sound/macos/support.py'
    module.rename(module.with_name('support-aside.py'))
    outcome = run('lowmem', *good)
    (outcome[2] / 'earlier.json').write_text(earlier)
    unread = run('lowmem', *good, json_to=outcome[2] / 'earlier.json')
    (outcome[2] / 'input.json').write_text(earlier)
    named = run('lowmem', *good[:2], outcome[2] / 'input.json', json_to=outcome[2] / 'input.json')
    (outcome[2] / 'loop').symlink_to('loop')
    (outcome[2] / 'old.json').write_text(earlier)
    looped = run('lowmem', '--preflight', '--json', outcome[2] / 'old.json', '--hints', outcome[2] / 'loop', plain=True)
    # Without the driver the words are read as they stand: a word --json and the word after it keep nothing, every
    # other word may be an input and keeps. After the inputs, with an earlier result at the path each row names.
    without = [(words, at, gone, run('lowmem', *words, plain=True,
                                    prepare=lambda case, at=at: (case / at).write_text(earlier)))
              for words, at, gone in (([*good, '--json', 'R.json', '--json', 'R.json'], 'R.json', True),
                                      ([*good, '--json', '--json'], '--json', True),
                                      ([*good, '--json', 'R.json', '--bad', '--json', 'R.json'], 'R.json', True),
                                      ([*good, '--json', 'R.json', 'R.json'], 'R.json', False),
                                      ([*good, '--bogus', 'R.json', '--json', 'R.json'], 'R.json', False),
                                      ([*good, '--hints', '--json', '--json', './--json'], '--json', False),
                                      ([*good, '--bogus', '--json', '--json'], '--json', False),
                                      ([*good, '--pins-sha256', '0' * 64, '--log', '', '--hints', '--json',
                                        '--json', './--json'], '--json', False),
                                      ([*good, '--threads', '4', '--json', '--json'], '--json', False),
                                      (['--preflight', '--json', 'R.json', '--json', 'R.json'], 'R.json', True))]
    module.with_name('support-aside.py').rename(module)
    for words, at, gone, unread_outcome in without:
        stays = (unread_outcome[2] / at).is_file() and (unread_outcome[2] / at).read_text() == earlier
        shown = (' '.join("''" if word == '' else str(word) for word in words[3:]) + ' after the inputs'
                 if words[:3] == good else ' '.join(words))
        expect(f'a driver that cannot be imported, {shown}, an earlier result at {at}: '
               f'{"it is gone" if gone else "it stays"}', unread_outcome, 2, 'DECLINED',
               'the macOS driver cannot be read (', lambda said: stays != gone, file=False if gone else 'earlier')
    expect('a driver that cannot be imported', outcome, 2, 'DECLINED', 'the macOS driver cannot be read (',
           lambda said: list(said) == ['checker', 'verdict', 'exit', 'wall_s', 'reason', 'wiring'], file=False)
    expect('a driver that cannot be imported, and an earlier result at the destination: the result is gone', unread,
           2, 'DECLINED', 'the macOS driver cannot be read (', lambda said: not (outcome[2] / 'earlier.json').exists(),
           file=False)
    expect('a driver that cannot be imported, and a --json that is also an input: it stays as it was', named,
           2, 'DECLINED', 'the macOS driver cannot be read (',
           lambda said: (outcome[2] / 'input.json').read_text() == earlier, file='earlier')
    expect('a driver that cannot be imported, an earlier result at --json and a loop of links as --hints: it is gone',
           looped, 2, 'DECLINED', 'the macOS driver cannot be read (',
           lambda said: not (outcome[2] / 'old.json').exists(), file=False)

    # An enter.py that cannot be loaded, or not to its last statement: the judge script looks before it hands
    # over, and answers itself. Without that look a file that does not compile ends the interpreter with status 1
    # and no line, and one that is empty, or cut off above the end handler of enter.py, with status 0 and no line:
    # the statuses of a rejection and of an acceptance. An earlier result at --json stays: the script reads no
    # argument.
    entry = fv / 'check/sound/macos/enter.py'
    intact = entry.read_text()
    rows = intact.splitlines(keepends=True)
    block = len(rows) - 1 - rows[::-1].index("if __name__ == '__main__':\n")
    cut = {f'that is cut off after {n} of its {len(rows)} lines{note}': ''.join(rows[:n])
           for n, note in ((1, ''), (len(rows) // 3, ''), (block - 1, ''), (block, ', before its last block'),
                           (block + 2, ', in its last block'), (len(rows) - 3, ', after its last block'),
                           (len(rows) - 1, ', before its last statement'))}
    cut['that lacks its last 2 bytes'] = intact[:-2]
    for name, text in (('that does not compile', intact + 'def (\n'),
                       ('whose first statements fail', 'import no_such_module\n' + intact), ('that is missing', None),
                       ('that is empty', ''), ('whose first statement is an exit with status 0',
                                               'import sys\nsys.exit(0)\n' + intact),
                       ('whose first statement is os._exit(0)', 'import os\nos._exit(0)\n' + intact),
                       ('with os._exit(0) as its statement before COMPLETE',
                        intact.replace('\nCOMPLETE = True\n', '\nos._exit(0)\nCOMPLETE = True\n')), *cut.items()):
        for mode in SCRIPT:
            entry.unlink() if text is None else entry.write_text(text)
            (work / 'stays.json').write_text(earlier)
            done = subprocess.run([str(fv / SCRIPT[mode]), *map(str, good), '--json', str(work / 'stays.json')],
                                  cwd=work, env=ENV, capture_output=True, stdin=subprocess.DEVNULL, text=True)
            entry.write_text(intact)
            lines = done.stdout.splitlines()
            row(f'judge {mode}: an enter.py {name}: the judge script says DECLINED itself, exit status 2',
                done.returncode == 2 and len(lines) == 1 and lines[0] == json.dumps({
                    'checker': CHECKER[mode], 'verdict': 'DECLINED', 'exit': 2, 'reason': NO_ENTRY},
                    separators=(',', ':')) and (work / 'stays.json').read_text() == earlier,
                f'exit {done.returncode}, stdout {done.stdout[:120]!r}')

    # The copy is compared with the pins, not the file at the recorded path with itself. Each of the four programs
    # must have the bytes that pins.env pins, whatever the record says, and the record must name the same bytes.
    other = record.with_name('pins-other.env')
    for name, old, new, reason in (
            ('that the record names with another digest', '^PIN gruszka .*$',
             f"PIN gruszka {'0' * 64} {programs['gruszka']}",
             'the record of the programs names another gruszka than check/sound/macos/pins.env'),
            ('that is missing', '^PIN gruszka .*$',
             f"PIN gruszka {digest(programs['gruszka'])} {work / 'no-such-program'}",
             'pinned file missing or unreadable: gruszka'),
            ('of the Lean toolchain that the record names with another digest', '^PIN pleanchecker .*$',
             f"PIN pleanchecker {'0' * 64} {programs['pleanchecker']}",
             'the record of the programs names another pleanchecker than check/sound/macos/pins.env'),
            ('without lines in the record', '^(PIN|SRC) pleanchecker .*\n', '',
             'the record of the programs has no lines for pleanchecker')):
        other.write_text(re.sub(old, new, record.read_text(), flags=re.M))
        expect(f'a program {name}', run('lowmem', *good, '--pins', other, '--pins-sha256', digest(other)),
               2, 'DECLINED', reason, unstarted)
    other.write_text(re.sub('^(PIN|SRC) pleanchecker_lowmem .*\n', '', record.read_text(), flags=re.M))
    expect('a record without the replay program of the other judge script',
           run('lowmem', *good, '--pins', other, '--pins-sha256', digest(other)), 0, 'ACCEPTED')
    # Programs in a folder whose name has an equals sign: the launcher starts the program, never `env PROGRAM`.
    (work / 'progs=eq').mkdir()
    lines = record.read_text()
    for name, path in programs.items():
        shutil.copy2(path, work / 'progs=eq' / name)
        lines = lines.replace(f' {path}\n', f" {work / 'progs=eq' / name}\n")
    other.write_text(lines)
    expect('programs in a folder named with an equals sign',
           run('lowmem', *good, '--pins', other, '--pins-sha256', digest(other)), 0, 'ACCEPTED')
    # The same programs under the pins of the tree itself: stand-ins are not the pinned programs.
    stand_in_pins = (fv / PINS).read_bytes()
    shutil.copyfile(FV / PINS, fv / PINS)
    expect('programs that are not the ones pins.env pins', run('lowmem', *good), 2, 'DECLINED',
           f"sha256 mismatch for ccmp_lowmem: {digest(programs['ccmp_lowmem'])}, pinned "
           f"{support.TreePins().programs['ccmp_lowmem']} in check/sound/macos/pins.env", unstarted)
    (fv / PINS).write_bytes(stand_in_pins)
    link = record.with_name('pins-link.env')
    shutil.copyfile(record, work / 'pins-elsewhere.env')
    link.symlink_to(work / 'pins-elsewhere.env')
    record.rename(record.with_name('pins-kept.env'))
    record.symlink_to(work / 'pins-elsewhere.env')
    outcome = run('lowmem', *good, '--pins-sha256', digest(link))
    record.unlink()
    record.with_name('pins-kept.env').rename(record)
    expect('a record that is a symbolic link out of config/', outcome, 2, 'DECLINED',
           'the record of the programs must name a pins*.env file in ', lambda said: 'pins_sha256' not in said)

    copy = work / 'pins-macos.env'
    shutil.copyfile(record, copy)
    expect('--pins outside config/, with the right digest',
           run('lowmem', *good, '--pins', copy, '--pins-sha256', digest(copy)), 2, 'DECLINED',
           '--pins must name a pins*.env file in ', lambda said: 'pins_sha256' not in said)
    other_digest = f'record of the programs sha256 {digest(record)} != --pins-sha256 {"0" * 64}'
    expect('--pins-sha256 with another digest', run('lowmem', *good, '--pins-sha256', '0' * 64), 2, 'DECLINED',
           other_digest, unstarted)
    expect('preflight: --pins-sha256 with the digest of the record',
           run('ultralowmem', '--preflight', '--pins-sha256', digest(record)), 0, 'PREFLIGHT_OK')
    expect('preflight: --pins-sha256 with another digest', run('lowmem', '--preflight', '--pins-sha256', '0' * 64),
           2, 'DECLINED', other_digest, unstarted)
    stale = record.with_name('pins-stale.env')
    stale.write_text(record.read_text().replace('SRC gruszka ' + support.TreePins().sources['gruszka'],
                                                'SRC gruszka ' + '0' * 64))
    expect('--pins with a program built from other sources',
           run('lowmem', *good, '--pins', stale, '--pins-sha256', digest(stale)), 2, 'DECLINED',
           'gruszka was not built from the sources of this tree', unstarted)

    # Programs that fail a control before any judgement: a comparison that accepts everything, a kernel that
    # rejects everything, and kernels that do not reject the kernel-invalid export.
    kbad = 'case "$1" in */selftest_kbad) exit 3;; esac\necho accepted'
    for role, text, reason in (
            ('ccmp_lowmem', 'echo "Comparison and axiom check passed!"',
             'self-test failed (bad: the comparison did not reject the export with a custom axiom)'),
            ('gruszka', 'echo "rejected: Any.decl: stand-in"; exit 1', 'self-test failed (good: exit 1, '),
            ('pleanchecker', 'echo "Lean default kernel accepts the solution"',
             'self-test failed (kbad: the lean leg did not reject the kernel-invalid export)'),
            ('gruszka', 'echo accepted',
             'self-test failed (kbad: the k2 leg did not reject the kernel-invalid export)'),
            ('gruszka', kbad, 'self-test failed (k2.log: abnormal leg exit 3')):
        broken, other = work / ('broken-' + role), record.with_name(f'pins-broken-{role}.env')
        broken.write_text('#!/bin/sh\n' + text + '\n')
        broken.chmod(0o755)
        other.write_text(re.sub(f'^PIN {role} .*$', f'PIN {role} {digest(broken)} {broken}', record.read_text(),
                                flags=re.M))
        pin_programs(fv, {role: broken})
        expect(f'no verdict from programs of which {role} fails a control: {reason[18:reason.index(":")]}',
               run('lowmem', *good, '--pins', other, '--pins-sha256', digest(other)), 2, 'DECLINED', reason,
               lambda said: 'legs' not in said)
        pin_programs(fv, programs)
    # The comparison itself must reject the export with a custom axiom: a replay that rejects it does not stand in.
    wrong = {'ccmp_lowmem': 'echo "Comparison and axiom check passed!"',
             'pleanchecker': 'for export; do :; done\ncase $export in */selftest_bad) echo "Lean default kernel '
                             'rejects the solution: stand-in"; exit 1;; esac\n'
                             'echo "Lean default kernel accepts the solution"'}
    lines, other = record.read_text(), record.with_name('pins-wrong-leg.env')
    for role, text in wrong.items():
        broken = work / ('wrong-leg-' + role)
        broken.write_text('#!/bin/sh\n' + text + '\n')
        broken.chmod(0o755)
        lines = re.sub(f'^PIN {role} .*$', f'PIN {role} {digest(broken)} {broken}', lines, flags=re.M)
        pin_programs(fv, {role: broken})
    other.write_text(lines)
    expect('no verdict when the replay rejects the export with a custom axiom and the comparison does not',
           run('lowmem', *good, '--pins', other, '--pins-sha256', digest(other)), 2, 'DECLINED',
           'self-test failed (bad: the comparison did not reject the export with a custom axiom)',
           lambda said: 'legs' not in said and list(said['selftests']['bad']['legs']) == ['compare'])
    pin_programs(fv, programs)
    # A program that cannot be started is no verdict: the launcher says so with its status 126. (/bin/sh ends with
    # exit status 1 when the interpreter of a script is missing, which is why no shell starts a leg.)
    for role, leg in (('ccmp_lowmem', 'compare'), ('pleanchecker', 'lean'), ('gruszka', 'k2')):
        broken, other = work / ('unstartable-' + role), record.with_name(f'pins-unstartable-{role}.env')
        broken.write_text('#!/nonexistent/interpreter\n')
        broken.chmod(0o755)
        other.write_text(re.sub(f'^PIN {role} .*$', f'PIN {role} {digest(broken)} {broken}', record.read_text(),
                                flags=re.M))
        pin_programs(fv, {role: broken})
        expect(f'no verdict from a {role} that cannot be started',
               run('lowmem', *good, '--pins', other, '--pins-sha256', digest(other)), 2, 'DECLINED',
               f'self-test failed ({leg}.log: abnormal leg exit 126 (guard 126))',
               lambda said: 'legs' not in said and list(said['selftests']['good']['legs'])[-1] == leg)
        pin_programs(fv, programs)

    sums = ['--challenge-sha256', digest(good[1]), '--comparator-sha256', digest(good[2])]
    expect("the caller's digests, and --threads 08", run('ultralowmem', *good, *sums, '--threads', '08'), 0,
           'ACCEPTED', also=lambda said: said['threads'] == 8)
    expect('another challenge than --challenge-sha256 names', run('lowmem', *good, '--challenge-sha256', sums[3]),
           2, 'DECLINED', '!= --challenge-sha256', unstarted)
    expect('another config than --comparator-sha256 names', run('ultralowmem', *good, '--comparator-sha256', sums[1]),
           2, 'DECLINED', '!= --comparator-sha256', unstarted)

    # The legs are stand-ins that accept, so a rule of the configuration step that is not applied shows as ACCEPTED.
    base = json.loads(good[2].read_text())

    def config(name, **changes):
        path = work / (name + '.json')
        path.write_text(json.dumps(dict(base, **changes)))
        return path

    four = config('four-axioms', permitted_axioms=[*base['permitted_axioms'], 'sorryAx'])
    for mode in SCRIPT:
        expect(f'{mode}: a fourth permitted axiom', run(mode, *good[:2], four), 2, 'DECLINED', 'config refused: ',
               unstarted)
    twice = work / 'key-twice.json'
    twice.write_text(good[2].read_text().rstrip()[:-1] + ', "permitted_axioms": ["propext", "sorryAx"]}')
    expect('a config with a key twice', run('lowmem', *good[:2], twice), 2, 'DECLINED',
           "duplicate object key 'permitted_axioms'", unstarted)
    expect('a kernel primitive as a definition target',
           run('ultralowmem', *good[:2], config('primitive', definition_names=['Nat.gcd'])), 2, 'DECLINED',
           'config refused: ', unstarted)
    kernel = config('kernel', external_kernels={'replay': ['/usr/bin/true']})
    expect('a kernel of the config is not run', run('lowmem', *good[:2], kernel), 0, 'ACCEPTED')
    expect('a kernel of the config cannot be kept', run('lowmem', *good[:2], kernel, '--keep-config-kernels'),
           2, 'DECLINED', "--keep-config-kernels: the config names 'replay'", unstarted)

    gate = TESTS / 'cross-version-regress/x'
    hole = [gate / 'dupmeta_sol37.export', gate / 'dupmeta_chal37.export', gate / 'dupmeta_cfg.json']
    for mode in SCRIPT:
        expect(f'{mode}: gate, a definition hole that is not sorried', run(mode, *hole), 1, 'REJECTED',
               "xversion: Challenge definition is not sorried: 'secret'", unstarted)
        expect(f'{mode}: gate, a meta line with "lean" twice',
               run(mode, hole[0], gate / 'dupmeta_chal37_dupmeta.export', hole[2]), 2, 'DECLINED',
               'meta line (release identity) refused', unstarted)

    # The arguments are read as the judge script of that name reads them: the inputs in front, every value in
    # the next argument, digits only, and no option that the script does not have (but --pins-sha256).
    number, seconds = '--threads must be a positive number', '--timeout must be a number of seconds (0 = none)'
    refused = [('lowmem', ['--threads=1'], "unknown argument '--threads=1'"),
               ('lowmem', ['--threads', '1_0'], number), ('lowmem', ['--threads', ' 3'], number),
               ('lowmem', ['--threads', '0'], number), ('lowmem', ['--threads', '1234567890'], number),
               ('lowmem', ['--timeout', '1_00'], seconds), ('lowmem', ['--timeout', ''], seconds),
               ('lowmem', ['--mem-budget-mb', '-1'], '--mem-budget-mb must be a non-negative integer'),
               ('lowmem', ['--preflight'], "unknown argument '--preflight'"),
               ('lowmem', ['--no-such-option'], "unknown argument '--no-such-option'"),
               ('lowmem', ['--mode', 'ultralowmem'], "unknown argument '--mode'"),
               ('lowmem', ['--kernel', 'nanoda'], "unknown argument '--kernel'"),
               ('lowmem', ['--skip-kernel', 'nanoda'], "unknown argument '--skip-kernel'"),
               ('lowmem', ['--extra-axioms', four], "unknown argument '--extra-axioms'"),
               ('lowmem', ['--strict'], "unknown argument '--strict'"),
               ('ultralowmem', ['--pins', record], "unknown argument '--pins'"),
               ('ultralowmem', ['--hide', 'none'], "unknown argument '--hide'"),
               ('lowmem', ['--challenge-sha256', ''], '--challenge-sha256 needs a non-empty value'),
               ('lowmem', ['--log', ''], "cannot write log ''"),
               ('lowmem', ['--integrity-cache', four], '--integrity-cache: not a directory owned by this user'),
               ('lowmem', ['--integrity-cache', work / 'none/below'], 'cannot resolve --integrity-cache'),
               ('lowmem', ['--incr-dir', work / 'none/below'], 'cannot resolve --incr-dir'),
               ('lowmem', ['--hints', work / 'none'], "--hints: not a regular file <= 16 MiB: '")]
    # An argument that is refused where it is read ends the reading, as in the scripts: a --json behind it was not
    # read, and no file is written.
    for mode, options, reason in refused:
        shown = ' '.join('PATH' if isinstance(option, Path) else repr(option) if ' ' in option or not option
                         else option for option in options)
        expect(f'{mode}: no verdict with {shown}', run(mode, *good, *options), 2, 'DECLINED', reason, unstarted,
               file=not reason.startswith(('unknown argument ', '--challenge-sha256 needs ', 'cannot write log ')))
    for name, words, reason in (('two inputs', good[:2], 'usage'), ('no argument', [], 'usage'),
                                ('an option in front of the inputs', ['--threads', '1', *good], "unknown argument '"),
                                ('an option without its value', [*good, '--threads'], '--threads needs a value'),
                                ('an empty input', ['', *good[1:]], 'empty input path'),
                                ('an input that is no file', [*good[:2], work / 'none'],
                                 'input is not a regular file: '),
                                ('an input in a folder that is none', [work / 'none/x', *good[1:]], 'cannot resolve ')):
        expect(f'lowmem: no verdict with {name}', run('lowmem', *words, plain=True), 2, 'DECLINED', reason, unstarted)
    expect('the last of a repeated option counts, and an empty --threads is the default',
           run('lowmem', *good, '--threads', '3', '--threads', '2', '--timeout', '1', '--timeout', '0'), 0, 'ACCEPTED',
           also=lambda said: said['threads'] == 2
           and run('ultralowmem', *good, '--threads', '')[1]['threads'] == os.cpu_count())
    expect('an empty --integrity-cache is none, as in the judge scripts',
           run('lowmem', *good, '--integrity-cache', ''), 0, 'ACCEPTED')
    outcome = run('lowmem', *good, '--pins-sha256', digest(record), '--workdir', '', '--log', work / 'no-workdir.log',
                  '--json', work / 'no-workdir.json', plain=True)
    started = re.findall(r'started as (.*)$', (work / 'no-workdir.log').read_text(), flags=re.M)
    expect('an empty --workdir is none, as in the judge scripts: the private directory is made in /tmp', outcome, 0,
           'ACCEPTED', also=lambda said: len(started) == 9 and {Path(path).parent.parent for path in started} == {
               Path('/tmp').resolve()})
    # Options of the judge scripts that have nothing to do here: what runs is at least what Linux runs.
    cache = work / 'cache'
    cache.mkdir(mode=0o700)
    expect('lowmem: --incr-dir, --integrity-cache, --private-inputs, --hide none, --hints none and '
           '--keep-config-kernels without a kernel change nothing',
           run('lowmem', *good[:2], config('no-kernel', external_kernels={}), '--incr-dir', work, '--private-inputs',
               '--integrity-cache', cache, '--hide', 'none', '--hints', 'none', '--keep-config-kernels'),
           0, 'ACCEPTED', also=lambda said: (legs('compare', 'lean', 'k2')(said)
                                             and said['private_inputs_asserted'] == 1
                                             and said['inputs']['export']['private'] == 'copy'))
    hidden = work / 'hide.txt'
    hidden.write_text('Hidden.decl\n')
    expect('lowmem: --hide FILE is copied and named in the result', run('lowmem', *good, '--hide', hidden), 0,
           'ACCEPTED', also=lambda said: said['hide_sha256'] == digest(hidden))

    # As the judge scripts: all processors unless --threads says otherwise, fewer under a small --mem-budget-mb.
    expect('workers: all processors by default, two under --mem-budget-mb 512',
           run('lowmem', *good, '--mem-budget-mb', '512'), 0, 'ACCEPTED',
           also=lambda said: (said['threads'], said['effective_threads']) == (os.cpu_count(), min(os.cpu_count(), 2)))
    (work / 'w$d').mkdir()
    expect('a work directory named with a dollar sign, as in the judge scripts',
           run('lowmem', *good, workdir=work / 'w$d'), 2, 'DECLINED',
           'a path used by the kernel wrappers contains a shell-special character', unstarted)

    aside = work / 'aside'
    aside.write_text('kept\n')
    (work / 'log-link').symlink_to(aside)
    expect('--log that is a symbolic link', run('lowmem', *good, '--log', work / 'log-link'), 2, 'DECLINED',
           'cannot write log', lambda said: aside.read_text() == 'kept\n' and unstarted(said))
    # The log may be the null device, which discards it. Nothing else that is no regular file is an output: not
    # another device, and not a descriptor, which is another file in the driver than in enter.py (the driver's
    # descriptor 1 is the caller's stderr), whatever kind of file it is.
    expect('--log /dev/null', run('lowmem', *good, '--log', '/dev/null'), 0, 'ACCEPTED')
    (work / 'null-link').symlink_to('/dev/null')
    expect('--log that is a symbolic link to /dev/null', run('lowmem', *good, '--log', work / 'null-link'), 2,
           'DECLINED', 'cannot write log', unstarted)
    expect('--log /dev/zero', run('lowmem', *good, '--log', '/dev/zero'), 2, 'DECLINED',
           'output must be a regular file: /dev/zero', unstarted)
    expect('--log /dev/fd/1 when the stderr of the caller is the null device',
           run('lowmem', *good, '--log', '/dev/fd/1', stderr=subprocess.DEVNULL), 2, 'DECLINED',
           'output must be a regular file: /dev/fd/1', unstarted)
    with (work / 'stderr-of-the-caller').open('wb') as errors:
        outcome = run('lowmem', *good, '--log', '/dev/fd/1', stderr=errors)
    expect('--log /dev/fd/1 when the stderr of the caller is a file', outcome, 2, 'DECLINED',
           'output must be a regular file: /dev/fd/1', unstarted)
    (work / 'log-folder').mkdir()
    expect('--log that is a folder', run('lowmem', *good, '--log', work / 'log-folder'), 2, 'DECLINED',
           'output must be a regular file: ', unstarted)
    expect('--json /dev/null', run('lowmem', *good, json_to='/dev/null'), 2, 'DECLINED',
           also=lambda said: unstarted(said) and re.match('cannot write JSON: |output must be a regular file: ',
                                                           said['reason']) and Path('/dev/null').is_char_device(),
           file=False)

    # Whether the JSON destination may be written is decided at the start from the command line: never where
    # another argument points, existing or missing. There is then no run, and nothing is created.
    bare = ['checker', 'verdict', 'exit', 'wall_s', 'reason', 'wiring']
    target = marked('output-target')[0]
    before = target.read_bytes()
    expect('--json that names an input', run('lowmem', target, *good[1:], json_to=target), 2, 'DECLINED',
           'output aliases a protected input', lambda said: target.read_bytes() == before and list(said) == bare,
           file=False)
    (work / 'a-folder').mkdir()
    for name, words, where in (
            ('an export that is missing', [work / 'missing.export', *good[1:]], work / 'missing.export'),
            ('an export that is missing, by another name', [work / 'missing.export', *good[1:]],
             work / 'a-folder/../missing.export'),
            ('a record that is missing', [*good, '--pins', fv / 'config/pins-missing.env', '--pins-sha256', '0' * 64],
             fv / 'config/pins-missing.env'),
            ('the file of the hints, which is missing', [*good, '--hints', work / 'missing-hints'],
             work / 'missing-hints')):
        expect(f'--json where the command line names {name}', run('lowmem', *words, json_to=where), 2, 'DECLINED',
               'output aliases a protected input: ', lambda said: not where.exists() and list(said) == bare,
               file=False)
    (work / 'loop-a').symlink_to(work / 'loop-b')
    (work / 'loop-b').symlink_to(work / 'loop-a')
    expect('--json beside a path that cannot be resolved: said as that',
           run('lowmem', *good, '--hints', work / 'loop-a'), 2, 'DECLINED',
           'cannot resolve a path of the command line (', lambda said: list(said) == bare, file=False)
    expect('--log and --json at one path', run('lowmem', *good, '--log', work / 'one-path', json_to=work / 'one-path'),
           2, 'DECLINED', 'log and JSON must be distinct paths',
           lambda said: not (work / 'one-path').exists() and list(said) == bare, file=False)
    # The driver compares the destination with every file it reads as soon as it has read the record. Where it
    # refuses, nothing is written: here the destination is a program that the record names and that is missing.
    other = record.with_name('pins-absent-program.env')
    other.write_text(re.sub('^PIN gruszka .*$', f"PIN gruszka {'0' * 64} {work / 'absent-program'}",
                            record.read_text(), flags=re.M))
    expect('--json where the record names a program that is missing',
           run('lowmem', *good, '--pins', other, '--pins-sha256', digest(other), json_to=work / 'absent-program'),
           2, 'DECLINED', 'output aliases a protected input: ',
           lambda said: not (work / 'absent-program').exists() and unstarted(said) and 'pins' not in said, file=False)
    # The five self-test inputs are files that every run reads, at the places pins.env names. Neither destination
    # may be one of them: by its path, through a symbolic link, or as a hard link. Nothing is written there and no
    # program starts; a refusal of the log is written to the JSON destination, which has passed. The judged inputs
    # are copies, so that only pins.env leads to the file.
    own = [work / 'own.export', work / 'own-challenge.export', work / 'own-comparator.json']
    for source, copy in zip(good, own):
        shutil.copyfile(source, copy)
    (work / 'names').mkdir()
    pinned = {name: fv / support.TreePins().files[name][0].relative_to(FV) for name in support.SELFTESTS}
    for name, fixture in pinned.items():
        before = fixture.read_bytes()
        for how in ('its path', 'a symbolic link', 'a hard link'):
            for option in ('--log', '--json'):
                where = fixture if how == 'its path' else work / 'names' / f'{name}{option}-{how.split()[1]}'
                if how == 'a symbolic link':
                    where.symlink_to(fixture)
                elif how == 'a hard link':
                    os.link(fixture, where)
                outcome = run('lowmem', *own, *(['--log', where] if option == '--log' else []),
                              json_to=where if option == '--json' else None)
                kept = (fixture.read_bytes() == before and where.is_symlink() == (how == 'a symbolic link')
                        and where.samefile(fixture))
                if fixture.is_symlink() or not fixture.is_file() or fixture.read_bytes() != before:
                    fixture.unlink(missing_ok=True)     # so that a failure here is not one of every later row
                    fixture.write_bytes(before)
                expect(f'{option} that names the self-test input {name[9:]} by {how}', outcome, 2, 'DECLINED',
                       'output aliases a protected input: ', lambda said: kept and unstarted(said),
                       file=option == '--log')
    expect('preflight after the destinations that named the self-test inputs', run('lowmem', '--preflight'), 0,
           'PREFLIGHT_OK')
    # Without a pins.env that can be read and is complete, the places of the self-test inputs are not known, and
    # no destination passes: the log is not written, and the JSON file only as a new file. A destination that is
    # another file of the run is still refused as that, before pins.env is.
    whole, mode, fixture = (fv / PINS).read_bytes(), (fv / PINS).stat().st_mode, pinned['selftest_bad']
    before = fixture.read_bytes()
    for name, reason in (('without the line of a self-test input', 'pins.env is incomplete'),
                         ('that cannot be read', 'Permission denied')):
        if 'line' in name:
            (fv / PINS).write_text(re.sub('^PIN selftest_bad .*\n', '', whole.decode(), flags=re.M))
        else:
            (fv / PINS).chmod(0)
        logged, written = run('lowmem', *own, '--log', fixture), run('lowmem', *own, json_to=fixture)
        aliased = run('lowmem', *own, '--pins', other, '--pins-sha256', digest(other), json_to=work / 'absent-program')
        (fv / PINS).chmod(stat.S_IMODE(mode))
        (fv / PINS).write_bytes(whole)
        kept, absent = fixture.read_bytes() == before, not (work / 'absent-program').exists()
        fixture.write_bytes(before)
        (work / 'absent-program').unlink(missing_ok=True)
        expect(f'a pins.env {name}: a --log that names a self-test input is not written', logged, 2, 'DECLINED',
               reason, lambda said: kept and unstarted(said) and (logged[2] / 'verdict.json').is_file())
        expect(f'a pins.env {name}: a --json that names a self-test input is not written over', written, 2,
               'DECLINED', reason,
               lambda said: kept and unstarted(said) and 'not an earlier result' in said['json_error'], file=False)
        expect(f'a pins.env {name}: a --json where the record names a program is refused as that', aliased, 2,
               'DECLINED', 'output aliases a protected input: ', lambda said: absent and unstarted(said), file=False)
    # One file under two spellings. On a volume that takes names in another letter case or Unicode form for the
    # same name, as the default volume of macOS does, the log and the JSON destination can be one file that does
    # not exist yet, and an output can be an input. Where the volume tells the names apart, they are two files.
    for kind, (one, two) in {'letter case': ('RESULT.txt', 'result.txt'),
                             'Unicode form': ('caf\u00e9.json', 'cafe\u0301.json')}.items():
        folder = work / f'two-{kind.split()[0]}'
        folder.mkdir()
        (folder / one).touch()
        same = (folder / two).exists()
        (folder / one).unlink()
        outcome = run('lowmem', *good, '--log', folder / two, json_to=folder / one)
        if same:
            expect(f'--log and --json at one new file under two spellings ({kind})', outcome, 2, 'DECLINED',
                   'log and JSON must be distinct paths', lambda said: not list(folder.iterdir()) and unstarted(said),
                   file=False)
        else:
            expect(f'--log and --json at two files whose names differ in {kind}', outcome, 0, 'ACCEPTED',
                   also=lambda said: len(list(folder.iterdir())) == 2)
    for option, source in (('--json', own[1]), ('--log', own[0])):
        before, where = source.read_bytes(), source.with_name(source.name.upper())
        outcome = run('lowmem', *own, *(['--log', where] if option == '--log' else []),
                      json_to=where if option == '--json' else None)
        if where.exists() and where.samefile(source):
            expect(f'{option} that names an input in another letter case', outcome, 2, 'DECLINED',
                   'output aliases a protected input: ', lambda said: source.read_bytes() == before and unstarted(said),
                   file=option == '--log')
        else:
            expect(f'{option} at a file whose name differs from an input in letter case', outcome, 0, 'ACCEPTED',
                   also=lambda said: source.read_bytes() == before and where.is_file())
    # An earlier result at the destination does not outlive a run, whatever the run says and however the destination
    # leads to it: the file is removed at the start, before anything is refused, and so is a symbolic link that
    # leads to one. The file behind a link is neither written nor removed. (`earlier` is such a result, above.)
    results = work / 'results'
    results.mkdir()

    def linked(name, link, text=earlier):
        """A destination that leads by `link` (os.symlink or os.link) to a file with `text`: both paths."""
        latest, behind = results / (name + '.json'), results / (name + '-behind.json')
        behind.write_text(text)
        link(behind, latest)
        return latest, behind

    def own_file(latest, behind, outcome, text=earlier):
        """Whether the destination is a file of its own with the line of this run, and the other file as it was."""
        return (not latest.is_symlink() and latest.stat().st_nlink == 1 and behind.read_text() == text
                and latest.read_text() == printed[outcome[2]][0] + '\n')

    for how, link in (('a symbolic link', os.symlink), ('a hard link', os.link)):
        for ends, words, trusted, status, verdict, reason in (
                ('a run without --pins-sha256', [], False, 2, 'DECLINED', '--pins-sha256 is required to judge'),
                ('a run with another --pins-sha256', ['--pins-sha256', '0' * 64], True, 2, 'DECLINED',
                 'record of the programs sha256 '),
                ('a run that judges', [], True, 0, 'ACCEPTED', '')):
            latest, behind = linked(f'{how.split()[1]}-{verdict}-{len(words)}', link)
            outcome = run('lowmem', *good, *words, trusted=trusted, json_to=latest)
            expect(f"--json at {how} to an earlier result, {ends}: the destination holds this run's line", outcome,
                   status, verdict, reason, lambda said: own_file(latest, behind, outcome))
    # Also when the reading of the arguments ends before it comes to --json, and for a --json that a later one
    # replaces: every path that follows a word --json is looked at.
    for name, words, reason in (('an unknown argument', [*good, '--thread', '4'], "unknown argument '--thread'"),
                                ('two inputs', good[:2], "unknown argument '"),
                                ("--log ''", [*good, '--log', ''], "cannot write log ''")):
        behind = results / f'behind-{len(words)}.json'
        behind.write_text(earlier)
        expect(f'an earlier result at a --json behind {name}: the result is gone',
               run('lowmem', *words, '--json', behind, plain=True), 2, 'DECLINED', reason,
               lambda said: not behind.exists(), file=False)
    (results / 'first.json').write_text(earlier)
    expect('an earlier result at a --json that a second --json replaces: the result is gone',
           run('lowmem', *good, '--json', results / 'first.json'), 0, 'ACCEPTED',
           also=lambda said: not (results / 'first.json').exists())
    (results / 'one.json').write_text(earlier)
    expect('--log and --json at one path that holds an earlier result: the result is gone',
           run('lowmem', *good, '--log', results / 'one.json', json_to=results / 'one.json'), 2, 'DECLINED',
           'log and JSON must be distinct paths',
           lambda said: not (results / 'one.json').exists() and list(said) == bare, file=False)
    # A file that another word of the command line names, an input or the value of an option other than --json
    # and --log, is never removed or emptied: if it reads as a result, it stays as it was, and the run is declined
    # for the two names of one file, as for any input. By its path, by a hard link and through a symbolic link;
    # behind an argument that ends the reading; and by its place, as the third word after an input named --json.
    named = results / 'input.json'
    named.write_text(earlier)
    os.link(named, results / 'input-hard.json')
    (results / 'input-link.json').symlink_to(named)
    for name, words, where, reason in (
            ('an input', [*good[:2], named], named, 'output aliases a protected input: '),
            ('an input, by a hard link', [*good[:2], named], results / 'input-hard.json',
             'output aliases a protected input: '),
            ('an input, through a symbolic link', [*good[:2], named], results / 'input-link.json',
             'output aliases a protected input: '),
            ('the value of --hints', [*good, '--hints', named], named, 'output aliases a protected input: '),
            ('an input, behind an argument that is refused', [*good[:2], named, '--thread', '4'], named,
             "unknown argument '--thread'")):
        expect(f'--json at a file that reads as a result and is also {name}: it stays as it was',
               run('lowmem', *words, json_to=where), 2, 'DECLINED', reason,
               lambda said: named.read_text() == earlier and (results / 'input-hard.json').samefile(named)
               and (results / 'input-link.json').is_symlink(), file='earlier')
    expect('the third word after an input named --json is an input: it stays as it was',
           run('lowmem', good[0], '--json', named, plain=True), 2, 'DECLINED', "input is not a regular file: '--json'",
           lambda said: named.read_text() == earlier, file='earlier')
    # A word at which no reader finds a file keeps nothing: here a symbolic link that leads to itself, as the value
    # of --hints. The earlier result is gone where the reading ends before --json, and where the driver cannot be
    # read (above); as the destination the run is then declined, because that word cannot be resolved.
    loop = results / 'loop'
    loop.symlink_to(loop.name)
    for name, words, reason in (
            ("behind --log ''", ['--preflight', '--log', '', '--json', results / 'looped.json', '--hints', loop],
             "cannot write log ''"),
            ('as the destination', ['--preflight', '--json', results / 'looped.json', '--hints', loop],
             'cannot resolve a path of the command line (')):
        (results / 'looped.json').write_text(earlier)
        expect(f'an earlier result at --json {name}, and a loop of links as --hints: the result is gone',
               run('lowmem', *words, plain=True), 2, 'DECLINED', reason,
               lambda said: not (results / 'looped.json').exists(), file=False)
    # An input stays beside such a word: through a symbolic link, by a hard link, and through a folder that does
    # not exist and `..`, at a --json behind an argument that is refused and as the destination.
    for how, word in (('through a symbolic link', results / 'input-link.json'),
                      ('by a hard link', results / 'input-hard.json'),
                      ('through a missing folder and ..', results / 'no-such-folder' / '..' / 'input.json')):
        expect(f'a file that reads as a result and is an input {how}, beside a loop of links, at a --json behind '
               'an argument that is refused: it stays as it was',
               run('lowmem', *good[:2], word, '--hints', loop, '--thread', '4', '--json', named, plain=True), 2,
               'DECLINED', "unknown argument '--thread'", lambda said: named.read_text() == earlier, file='earlier')
        expect(f'a file that reads as a result and is an input {how}, beside a loop of links, as the destination: '
               'it stays as it was', run('lowmem', *good[:2], word, '--hints', loop, json_to=named), 2, 'DECLINED',
               'output aliases a protected input: ', lambda said: named.read_text() == earlier, file='earlier')
    # A word that cannot be looked up names no file and keeps nothing, also an input: here a symbolic link to an
    # earlier result in a folder that this account cannot search, which the driver cannot read either.
    # Where the driver refuses before it has compared the destination, the run's DECLINED is written there as a new
    # file, which is possible only because the earlier result is gone.
    hidden = results / 'hidden'
    hidden.mkdir()
    for n in (1, 2):
        (results / f'behind-hidden-{n}.json').write_text(earlier)
        (hidden / f'link-{n}.json').symlink_to(results / f'behind-hidden-{n}.json')
    hidden.chmod(0o600)
    try:
        refused = run('lowmem', *good[:2], hidden / 'link-1.json', '--thread', '4', '--json',
                      results / 'behind-hidden-1.json', plain=True)
        unresolved = run('lowmem', *good[:2], hidden / 'link-2.json', json_to=results / 'behind-hidden-2.json')
    finally:
        hidden.chmod(0o700)
    expect('an earlier result, and an input that is a link to it in a folder that cannot be searched, at a --json '
           'behind an argument that is refused: the result is gone', refused, 2, 'DECLINED',
           "unknown argument '--thread'", file=False)
    expect('the same as the destination: the earlier result is gone, the run says why it cannot read the input',
           unresolved, 2, 'DECLINED', 'input is not a regular file: ')
    # The same file behind more symbolic links than the system follows in one look: a chain of 40 links to another
    # name of it, a hard link. The system says "too many levels of symbolic links", the driver's resolve reads the
    # file. As an input it stays, and also as the log, which the driver would otherwise open and empty.

    def chain(name, target, links=40):
        for n in range(links):
            (results / f'{name}-{n}').symlink_to(target if n == 0 else f'{name}-{n - 1}')
        return results / f'{name}-{links - 1}'

    far = chain('far', 'input-hard.json')
    expect('a file that reads as a result and is an input through 40 symbolic links, at a --json behind an argument '
           'that is refused: it stays as it was',
           run('lowmem', *good[:2], far, '--thread', '4', '--json', named, plain=True), 2, 'DECLINED',
           "unknown argument '--thread'", lambda said: named.read_text() == earlier, file='earlier')
    expect('a file that reads as a result and is an input through 40 symbolic links, as the destination: it stays',
           run('lowmem', *good[:2], far, json_to=named), 2, 'DECLINED', 'output aliases a protected input: ',
           lambda said: named.read_text() == earlier, file='earlier')
    configuration = results / 'far-configuration.json'
    shutil.copyfile(good[2], configuration)
    os.link(configuration, results / 'far-configuration-hard.json')
    expect('--log at an input reached through 40 symbolic links: refused, and the input keeps its bytes',
           run('lowmem', *good[:2], chain('far-config', 'far-configuration-hard.json'), '--log', configuration), 2,
           'DECLINED', 'output aliases a protected input: ',
           lambda said: configuration.read_bytes() == good[2].read_bytes())
    # The command lines of the review, in the folder of the run, with an earlier result at the path that each
    # names: the role of a word decides. After the three inputs, an option word, the value of another option and a
    # word that cannot be resolved or looked up (a loop of links, a name of 300 letters, a link in a folder that
    # cannot be searched) keep nothing; an input, and after a refused argument a word of unknown role, keep it.
    # Alone, `--json R R` is three inputs, and `--bogus R --json R` has R as its second input.

    def prepared(at):
        def prepare(case):
            (case / at).write_text(earlier)
            (case / 'LOOP').symlink_to('LOOP')
            (case / 'locked').mkdir()
            (case / 'locked' / 'h').symlink_to(case / at)
            (case / 'locked').chmod(0o600)
        return prepare
    # `file` is what the destination then holds: nothing, this run's DECLINED (written as a new file, as above), or
    # the earlier result.
    for words, at, reason, file in (
            ([*good, '--json', '--json'], '--json', 'output aliases a protected input: --json', False),
            ([*good, '--json', '--threads', '--threads', '4'], '--threads',
             'output aliases a protected input: --threads', False),
            ([*good, '--json', '--json', 'R.json'], '--json', 'output aliases a protected input: --json', False),
            ([*good, '--json', 'R.json', 'R.json'], 'R.json', 'output aliases a protected input: R.json', 'earlier'),
            ([*good, '--bogus', 'R.json', '--json', 'R.json'], 'R.json', "unknown argument '--bogus'", 'earlier'),
            ([*good, '--pins-sha256', '0' * 64, '--bogus', '--json', 'R.json', '--json', 'R.json'], 'R.json',
             "unknown argument '--bogus'", False),
            ([*good, '--bad', '--json', 'R.json', '--json', 'R.json'], 'R.json', "unknown argument '--bad'", False),
            ([*good, '--json', 'R.json', '--bad', '--json', 'R.json'], 'R.json', "unknown argument '--bad'", True),
            ([*good, '--hints', '--json', '--json', './--json'], '--json',
             'output aliases a protected input: ./--json', 'earlier'),
            ([*good, '--bogus', '--json', '--json'], '--json', "unknown argument '--bogus'", 'earlier'),
            ([*good, '--pins-sha256', '0' * 64, '--log', '', '--hints', '--json', '--json', './--json'], '--json',
             "cannot write log ''", 'earlier'),
            (['--json', 'R.json', 'R.json'], 'R.json', "input is not a regular file: '--json'", 'earlier'),
            (['--bogus', 'R.json', '--json', 'R.json'], 'R.json', "unknown argument 'R.json'", 'earlier'),
            ([*good, '--hints', 'LOOP', '--json', 'OLD.json'], 'OLD.json',
             'cannot resolve a path of the command line (', False),
            ([*good, '--hints', 'h' * 300, '--json', 'OLD.json'], 'OLD.json', '--pins-sha256 is required', True),
            ([*good, '--hints', 'locked/h', '--json', 'OLD.json'], 'OLD.json', '--pins-sha256 is required', True)):
        outcome = run('lowmem', *words, plain=True, prepare=prepared(at))
        (outcome[2] / 'locked').chmod(0o700)
        stays = (outcome[2] / at).is_file() and (outcome[2] / at).read_text() == earlier
        shown = ' '.join("''" if word == '' else 'NAME' if len(str(word)) == 300
                         else Path(word).name if Path(word).parent == st else str(word) for word in words)
        expect(f'{shown}, an earlier result at {at}: {"it stays" if file == "earlier" else "it is gone"}', outcome, 2,
               'DECLINED', reason, lambda said: stays == (file == 'earlier'), file=file)
    # Another spelling of an input: the letter case, on a volume that takes them for the same.
    if (results / 'INPUT.JSON').exists():
        expect('a file that reads as a result and is an input, at a --json in other letters: it stays as it was',
               run('lowmem', *good[:2], named, json_to=results / 'INPUT.JSON'), 2, 'DECLINED',
               'output aliases a protected input: ', lambda said: named.read_text() == earlier, file='earlier')
    # A --json path with .. after a linked folder is the file that the system puts there: in the folder that ..
    # leads to from the folder the link names. The run writes its result there and leaves no other file behind.
    (results / 'real' / 'sub').mkdir(parents=True)
    (results / 'linked').symlink_to(results / 'real' / 'sub')
    expect('--json with .. after a linked folder: the result is in the real folder, and nothing else is left',
           run('lowmem', *good, json_to=results / 'linked' / '..' / 'dotted.json'), 0, 'ACCEPTED',
           also=lambda said: (results / 'real' / 'dotted.json').is_file()
           and not [*results.glob('tmp*'), *(results / 'real').glob('tmp*')])
    # A result of the Linux scripts has another wiring: it is no earlier result here. A run that is declined
    # before the driver has compared the destination leaves it as it is.
    linux = results / 'linux.json'
    linux.write_text(json.dumps(dict(json.loads(earlier), wiring='check-sound-lowmem-v1.2-D15')))
    expect('--json at a result of a Linux judge script, a run without --pins-sha256: it is no result here, it stays',
           run('lowmem', *good, trusted=False, json_to=linux), 2, 'DECLINED', '--pins-sha256 is required to judge',
           lambda said: 'not an earlier result' in said['json_error'], file='earlier')
    # A comparator configuration that has four keys of a result is a configuration, and the configuration step
    # takes it. It is not what this judge writes: as an input it stays, like every input; as a destination and
    # nothing else it is a file that is no result, which stays until the driver has compared the destination and
    # is then replaced by the result.
    metadata = results / 'configuration.json'
    metadata.write_text(json.dumps(dict(json.loads(good[2].read_text()), checker='checkSoundLowMem',
                                        wiring='configuration metadata', verdict='ACCEPTED', exit=0)))
    before = metadata.read_bytes()
    for mode in SCRIPT:
        expect(f'{mode}: a configuration with four keys of a result is judged as a configuration',
               run(mode, *good[:2], metadata), 0, 'ACCEPTED')
        expect(f'{mode}: --json at that configuration, which is the input: it stays as it was',
               run(mode, *good[:2], metadata, json_to=metadata), 2, 'DECLINED', 'output aliases a protected input: ',
               lambda said: metadata.read_bytes() == before and list(said) == bare, file='earlier')
    # The same for a configuration that has all six fields and so reads as a result. A --json that a later one
    # replaces may name the configuration too, and the configuration may follow a challenge that is a file named
    # --json: neither makes it a destination. The run judges, and the file keeps its bytes.
    both = results / 'configuration-result.json'
    both.write_text(json.dumps(dict(json.loads(good[2].read_text()), **json.loads(earlier))))
    for file, name in ((metadata, 'with four keys of a result'), (both, 'that reads as a result')):
        kept = file.read_bytes()
        expect(f'a configuration {name}, also named by a --json that a later one replaces: judged, it stays',
               run('lowmem', *good[:2], file, '--json', file), 0, 'ACCEPTED',
               also=lambda said: file.read_bytes() == kept)
        expect(f'a configuration {name}, after a challenge that is a file named --json: judged, it stays',
               run('lowmem', good[0], '--json', file, prepare=lambda case: shutil.copyfile(good[1], case / '--json')),
               0, 'ACCEPTED', also=lambda said: file.read_bytes() == kept)
    expect('--json at that configuration and nothing else, a run without --pins-sha256: it stays as it was',
           run('lowmem', *good, trusted=False, json_to=metadata), 2, 'DECLINED', '--pins-sha256 is required to judge',
           lambda said: metadata.read_bytes() == before and 'not an earlier result' in said['json_error'],
           file='earlier')
    expect('--json at that configuration and nothing else, a run that judges: the result takes its place',
           run('lowmem', *good, json_to=metadata), 0, 'ACCEPTED')
    # Which words are destinations. Where the driver read the words to their end, only what it read as the value
    # of a --json: not the word after a --json that is itself the value of another option. Where it refused them,
    # the word after a word --json, and never the word after --log.
    expect('--json as the last word', run('lowmem', *good, '--json', plain=True), 2, 'DECLINED',
           '--json needs a value')
    behind = results / 'after-log.json'
    behind.write_text(earlier)
    expect('--json --log X: the destination is the path --log, and X is left as it was',
           run('lowmem', *good, '--json', '--log', behind, plain=True,
               prepare=lambda case: (case / '--log').write_text(earlier)), 2, 'DECLINED', "unknown argument '",
           lambda said: behind.read_text() == earlier)
    expect('--log --json X, which is refused: an earlier result at X is gone',
           run('lowmem', *good, '--log', '--json', behind, plain=True), 2, 'DECLINED', "unknown argument '",
           lambda said: not behind.exists(), file=False)
    expect('--hints --json --private-inputs, which is read: the word after that --json is no destination',
           run('lowmem', *good, '--pins-sha256', digest(record), '--hints', '--json', '--private-inputs', plain=True,
               prepare=lambda case: (case / '--private-inputs').write_text(earlier)), 2, 'DECLINED',
           "--hints: not a regular file <= 16 MiB: '--json'", file='earlier')
    behind.write_text(earlier)
    expect('one path after two words --json: the result of this run is there',
           run('lowmem', *good, '--json', behind, json_to=behind), 0, 'ACCEPTED')
    # A slash at the end of the word does not make another path of it: the earlier result is taken away from the
    # path that is then written.
    behind.write_text(earlier)
    expect('--json with a slash at its end, at an earlier result: the result of this run is there',
           run('lowmem', *good, json_to=str(behind) + '/'), 0, 'ACCEPTED')
    behind.write_text(earlier)
    expect('--json with a slash at its end, at an earlier result, behind an argument that is refused: it is gone',
           run('lowmem', *good, '--thread', '4', '--json', str(behind) + '/', plain=True), 2, 'DECLINED',
           "unknown argument '--thread'", lambda said: not behind.exists(), file=False)
    # A file that is no result stays where the driver has not compared the destination, also behind a link; where
    # it has, the link is replaced and the file behind it stays.
    latest, behind = linked('no-result', os.symlink, 'not a result\n')
    expect('--json at a symbolic link to a file that is no result, a run without --pins-sha256: both stay',
           run('lowmem', *good, trusted=False, json_to=latest), 2, 'DECLINED', '--pins-sha256 is required to judge',
           lambda said: latest.is_symlink() and behind.read_text() == 'not a result\n'
           and 'not an earlier result' in said['json_error'], file=False)
    outcome = run('lowmem', *good, json_to=latest)
    expect('--json at a symbolic link to a file that is no result, a run that judges: the link is replaced',
           outcome, 0, 'ACCEPTED', also=lambda said: own_file(latest, behind, outcome, 'not a result\n'))
    # An earlier result that cannot be removed is emptied, and there is no run. A result that can be neither
    # removed nor emptied stays. In a folder that cannot be written: one behind a symbolic link, one in a file that
    # cannot be written either, and one in a file with another name, which emptying would reach under that name.
    # In any folder: one in a file with the flag that forbids every change. As the destination: no run. As a --json
    # that a later one replaces, the run judges and says nothing there; behind an argument that is refused, the
    # reason is the argument's.
    kept = work / 'kept-result'
    kept.mkdir()
    (kept / 'verdict.json').write_text(earlier)
    (kept / 'link.json').symlink_to(results / 'one-behind.json')
    (results / 'one-behind.json').write_text(earlier)
    (kept / 'read-only.json').write_text(earlier)
    (kept / 'read-only.json').chmod(0o400)
    (results / 'archive.json').write_text(earlier)
    os.link(results / 'archive.json', kept / 'other-name.json')
    kept.chmod(0o500)
    fixed = results / 'fixed.json'
    fixed.write_text(earlier)
    os.chflags(fixed, stat.UF_IMMUTABLE)
    try:
        outcome = run('lowmem', *good, json_to=kept / 'verdict.json')
        behind = run('lowmem', *good, json_to=kept / 'link.json')
        closed = run('lowmem', *good, json_to=kept / 'read-only.json')
        named = run('lowmem', *good, json_to=kept / 'other-name.json')
        flagged = run('lowmem', *good, json_to=fixed)
        replaced = run('lowmem', *good, '--json', kept / 'link.json', '--json', kept / 'other-name.json',
                       '--json', fixed)
        refused = [run('lowmem', *good, '--thread', '4', '--json', path, plain=True)
                   for path in (kept / 'link.json', kept / 'other-name.json', fixed)]
        stays = ((kept / 'link.json').is_symlink() and (results / 'one-behind.json').read_text() == earlier
                 and (results / 'archive.json').read_text() == earlier and fixed.read_text() == earlier
                 and (kept / 'other-name.json').samefile(results / 'archive.json'))
    finally:
        os.chflags(fixed, 0)
        kept.chmod(0o700)
    expect('--json with an earlier result that cannot be removed: emptied, no run', outcome, 2, 'DECLINED',
           'cannot write JSON: ', lambda said: list(said) == bare and (kept / 'verdict.json').read_text() == '',
           file=False)
    expect('--json at a link, which cannot be removed, to an earlier result: it stays, no run', behind, 2,
           'DECLINED', 'cannot write JSON: ', lambda said: list(said) == bare and stays, file='earlier')
    expect('--json at an earlier result that can be neither removed nor written: it stays, no run', closed, 2,
           'DECLINED', 'cannot write JSON: ',
           lambda said: list(said) == bare and (kept / 'read-only.json').read_text() == earlier, file='earlier')
    expect('--json at an earlier result that cannot be removed and has another name: not emptied, no run', named, 2,
           'DECLINED', 'cannot write JSON: ', lambda said: list(said) == bare and stays, file='earlier')
    expect('--json at an earlier result that may not be changed (uchg): it stays, no run', flagged, 2, 'DECLINED',
           'cannot write JSON: ', lambda said: list(said) == bare and stays, file='earlier')
    expect('three such results at --json words that a later one replaces: the run judges, and they stay', replaced,
           0, 'ACCEPTED', also=lambda said: stays)
    for outcome in refused:
        expect(f'such a result ({destination[outcome[2]].name}) at a --json behind an argument that is refused: '
               'it stays', outcome, 2, 'DECLINED', "unknown argument '--thread'", lambda said: stays, file='earlier')

    # The caller's environment reaches neither the judge script nor the driver.
    trap = work / 'trap'
    (trap / 'bin').mkdir(parents=True)
    for tool in ('uname', 'dirname', 'env', 'python3', 'readlink', 'basename', 'bash'):
        (trap / 'bin' / tool).write_text(f'#!/bin/sh\necho {tool} >> "{trap}/log"\nexit 97\n')
        (trap / 'bin' / tool).chmod(0o755)
    (trap / 'bashenv').write_text(f'echo bash-env >> "{trap}/log"\n')
    (trap / 'sitecustomize.py').write_text(f'open("{trap}/log", "a").write("sitecustomize")\n')
    function = '() { echo function >> %s/log; }' % trap
    hostile = {"the scripts' own marker and a PATH with other tools": {
                   'CHECK_SOUND_CLEAN_ENV': '1', 'CHECK_SOUND_LOWMEM_CLEAN_ENV': '1',
                   'PATH': f'{trap}/bin:/usr/bin:/bin'},
               'BASH_ENV': {'BASH_ENV': str(trap / 'bashenv'), **ENV},
               'exported shell functions': {'BASH_FUNC_readlink%%': function, 'BASH_FUNC_exec%%': function,
                                            'BASH_FUNC_/usr/bin/uname%%': function, **ENV},
               'PYTHONPATH and PYTHONSTARTUP': {'PYTHONPATH': str(trap), 'PYTHONSTARTUP': str(trap / 'bashenv'), **ENV}}
    for name, env in hostile.items():
        for mode in SCRIPT:
            expect(f'{mode}: environment, {name}', run(mode, *good, '--threads', '0', env=env), 2, 'DECLINED',
                   number, lambda said: not (trap / 'log').exists())

    record.unlink()
    expect('no record of programs', run('lowmem', '--preflight'), 2, 'DECLINED',
           'build the programs with check/sound/macos/build-judge-macos.sh', unstarted)
    expect('--json where the record of the programs belongs, which is missing',
           run('lowmem', *good, '--pins-sha256', '0' * 64, json_to=record), 2, 'DECLINED',
           'output aliases a protected input: ', lambda said: not record.exists(), file=False)

    # The other judge scripts: check-sound.sh says which scripts judge on macOS; the rest run their Linux code,
    # which cannot give a verdict there.
    for script, reason in (('check/sound/check-sound.sh', 'not available on macOS: use check/lowmem/'),
                           ('check/sound/check-sound-svc.sh', ''), ('check/notary/check-notary.sh', ''),
                           ('check/frontier/check-frontier.sh', '')):
        case = work / ('linux-' + Path(script).stem)
        case.mkdir()
        done = subprocess.run([str(FV / script), *map(str, good), '--json', str(case / 'verdict.json')], cwd=case,
                              env=dict(ENV, HOME=str(case)), stdin=subprocess.DEVNULL, capture_output=True, text=True,
                              timeout=600)
        try:
            said = json.loads(done.stdout.strip().splitlines()[-1])
        except (ValueError, IndexError):
            said = {}
        row(f'judge {script}: no verdict on macOS',
            done.returncode == 2 and said.get('verdict') == 'DECLINED' and said.get('exit') == 2
            and reason in str(said.get('reason')),
            f'exit {done.returncode} {said.get("verdict")}: {str(said.get("reason"))[:90]}')


def programs_rows(row, support, fv, work):
    _record, programs = install(fv, work / 'by-name', BY_NAME, support.TreePins().sources)

    def run(label):
        (work / label).mkdir()
        done = subprocess.run(['/usr/bin/python3', '-I', '-B', str(HERE / 'programs.py'), '--work', str(work / label),
                               '--fv', str(fv), '--fixtures-fv', str(FV), '--programs-only'], env=ENV,
                              stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=900)
        rows = {name: (status, detail)
                for status, name, detail in re.findall(r'^(PASS|FAIL|INFO) ([^:]+): (.*)$', done.stdout, flags=re.M)}
        result = re.findall(r'^RESULT pass=(\d+) fail=(\d+) info=\d+$', done.stdout, flags=re.M)
        return done.returncode, rows, [int(n) for n in result[0]] if len(result) == 1 else [0, -1]

    stops = 'programs second-kernel stops what the streaming replay accepts'
    rc, rows, (passed, failed) = run('programs')
    totals = rows.get('programs attack totals', ('', ''))[1]
    row('programs: no FAIL row when every program follows the names', rc == 0 and failed == 0 and passed > 250
        and rows.get(stops, ('',))[0] == 'PASS' and totals.startswith('63 attack input(s); ')
        and 'streaming replay: 2 accepted' in totals and '(61 exit 1, 2 other)' in totals
        and '50 rejected, 13 declined' in totals, f'exit {rc}, pass={passed} fail={failed}; {totals[:90]}')
    # A row asks for the class, not for any end but acceptance: a second kernel that declines where it must reject.
    Path(str(programs['gruszka']) + '.decline').write_text('16489_safe_ctor\n')
    rc, rows, (passed, failed) = run('programs-declining')
    Path(str(programs['gruszka']) + '.decline').unlink()
    row('programs: FAIL when the second kernel declines an attack that it must reject',
        rc == 1 and failed == 1 and rows.get('programs second-kernel cves/16489_safe_ctor', ('',))[0] == 'FAIL',
        f'exit {rc}, pass={passed} fail={failed}')
    Path(str(programs['gruszka']) + '.accept').write_text('c1only_unsafe_ctor_loose\n')
    rc, rows, (passed, failed) = run('programs-accepting')
    row('programs: FAIL when the second kernel accepts an attack that the streaming replay accepts',
        rc == 1 and failed == 2 and rows.get(stops, ('',))[0] == 'FAIL'
        and rows.get('programs second-kernel c1only/c1only_unsafe_ctor_loose', ('',))[0] == 'FAIL',
        f'exit {rc}, pass={passed} fail={failed}')


def main():
    mac = sys.platform == 'darwin' and platform.machine() == 'arm64'
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(FV / 'check/sound/macos'))
    import cargo_build
    import judge
    import support
    npass = nfail = 0

    def row(name, ok, detail=''):
        nonlocal npass, nfail
        npass, nfail = npass + bool(ok), nfail + (not ok)
        print(('PASS ' if ok else 'FAIL ') + name + (f': {detail}' if detail else ''), flush=True)

    with tempfile.TemporaryDirectory(prefix='macos-judge-', dir=sys.argv[1] if sys.argv[1:] else None) as tmp:
        work = Path(tmp).resolve()
        tree = work / 'tree'
        fv = tree / 'fastverify'
        for name in FILES:
            (fv / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(FV / name, fv / name)
        for name in TREES:
            shutil.copytree(FV.parent / name, tree / name, ignore=shutil.ignore_patterns('.git', '.lake', 'target'))
        record, programs = install(fv, work / 'stand-ins', STAND_INS, support.TreePins().sources)
        text = record.read_text()
        sections = [(source_rows, (judge, support, tree, work, mac)), (crate_rows, (support, cargo_build, work)),
                    (config_rows, (judge, support, work)),
                    (decision_rows, (judge, work)), (retry_rows, (judge, work)),
                    (record_rows, (support, work, text, programs)), (copy_rows, (judge, work)),
                    (result_rows, (judge, work))]
        if mac:
            sections += [(judge_rows, (judge, support, fv, work, record, programs)),
                         (programs_rows, (support, fv, work))]
        else:
            print('SKIP macos-judge judge, programs: need arm64 macOS')
        for section, arguments in sections:
            try:
                section(row, *arguments)
            except Exception as error:      # a section that cannot finish is a failure with a RESULT line
                row(f'{section.__name__}: ran to its end', False, f'{type(error).__name__}: {error}'[:300])
    print(f'RESULT pass={npass} fail={nfail}')
    return 1 if nfail else 0


if __name__ == '__main__':
    sys.exit(main())
