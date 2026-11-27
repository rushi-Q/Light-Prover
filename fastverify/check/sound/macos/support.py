"""Pins, the sources and the record of the locally built programs and the supervision of a leg, for the macOS
judge. Nothing in this file needs macOS, so the tests of the pins run on Linux too."""
from contextlib import nullcontext
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
GUARD = ROOT / 'tools/guard/fvguard.py'
PINS_FILE = HERE / 'pins.env'
# The four programs. The tree pins the bytes of each; the record of the machine says where they are.
PROGRAMS = ('ccmp_lowmem', 'gruszka', 'pleanchecker', 'pleanchecker_lowmem')
SELFTESTS = ('selftest_comparator', 'selftest_challenge', 'selftest_good', 'selftest_bad', 'selftest_kbad')
SHA256 = re.compile('[0-9a-f]{64}')


class Declined(Exception):
    """The check could not establish a verdict."""


class LegExit(Declined):
    """A leg ended by itself with exit status 2, and no limit was hit: no verdict, like every end other than
    0 or 1. The class exists for the two rules that read this status: the one-worker retry of the second kernel
    and the no-verdict line of the streaming replay (judge.py)."""


class TreePins:
    """pins.env of this directory: everything the tree pins for the macOS judge.

    `PIN <program> <sha256>` is the digest of a program that build-judge-macos.sh builds; the judge refuses
    other bytes. Each of the four programs must have such a line.
    `PIN <name> <sha256> <file>` is a file of this tree, named from fastverify/. `SRC <program> <sha256>` is the
    fingerprint of the sources a program is built from. SOUND_VERSION and TC_VERSION name these pins and the
    Lean release. Any other line is refused."""

    def __init__(self, path=PINS_FILE):
        raw = Path(path).read_bytes()
        self.sha256 = hashlib.sha256(raw).hexdigest()
        self.programs, self.files, self.sources, self.labels = {}, {}, {}, {}
        for line in raw.decode('utf-8').splitlines():
            words = line.split()
            pin = len(words) in (3, 4) and SHA256.fullmatch(words[2]) is not None
            if not words or line.startswith('#'):
                continue
            kind, name = (words[0], words[1]) if pin else (None, None)
            if kind == 'PIN' and len(words) == 3 and name in PROGRAMS and name not in self.programs:
                self.programs[name] = words[2]
            elif (kind == 'PIN' and len(words) == 4 and name not in PROGRAMS and name not in self.files
                  and not Path(words[3]).is_absolute() and '..' not in Path(words[3]).parts):
                self.files[name] = (ROOT / words[3], words[2])
            elif kind == 'SRC' and len(words) == 3 and name in PROGRAMS and name not in self.sources:
                self.sources[name] = words[2]
            elif re.fullmatch('(SOUND_VERSION|TC_VERSION)=.+', line) and line.split('=')[0] not in self.labels:
                self.labels[line.split('=')[0]] = line.split('=', 1)[1]
            else:
                raise Declined('pins.env: a line that is not understood: ' + line[:60])
        if (set(self.sources) != set(PROGRAMS) or set(self.programs) != set(PROGRAMS)
                or set(self.files) != {'gruszka_patch', *SELFTESTS} or len(self.labels) != 2):
            raise Declined('pins.env is incomplete')


# The files each program is built from, as the Linux recipes of this tree take them: tools/reproduce/rebuild-pchk.sh
# and check/lowmem/src-ultralowmem/build-pleanchecker-lowmem.sh (the whole directory), tools/reproduce/
# rebuild-lowmem.sh (these names of two directories) and tools/reproduce/portable-gruszka.sh (four names, without
# two directories of the vendored crate). None is a build directory: .lake at the top of a directory is left out.
SOURCE_SETS = {
    'pleanchecker': (('fastverify/check/sound/src', None),),
    'pleanchecker_lowmem': (('fastverify/check/lowmem/src-ultralowmem/src/pleanchecker-lowmem', None),),
    'ccmp_lowmem': (('fastverify/check/sound/src', ('FastParse.lean', 'ParAxioms.lean', 'CCmp.lean', 'CCmpMain.lean',
                                                     'Main.lean', 'PChk', 'lean-toolchain', 'lake-manifest.json')),
                    ('fastverify/check/lowmem/src', ('lowmem_arena.c', 'LowMemParse.lean', 'CCmpLowMem.lean',
                                                      'CCmpLowMemMain.lean', 'lakefile.toml'))),
    'gruszka': (('sources/gruszka', ('Cargo.toml', 'Cargo.lock', 'src', 'vendor')),),
}
LEFT_OUT = {'gruszka': ('vendor/susz/tests', 'vendor/susz/target')}


def stage_sources(project, dest, patch):
    """Copy the sources of the four programs from the repository `project` to dest/src/<program> and return
    {program: fingerprint}. Nothing in the repository is changed.

    Only regular files and directories are sources: a symbolic link or any other kind of file among them is
    refused. `patch` is (file, SHA-256) of the patch of the second kernel, which must have that digest and apply
    without offset. The fingerprint of a program's sources is the SHA-256 of what
    `find . -type f | LC_ALL=C sort | xargs sha256sum` prints in the staged directory, the number that
    tools/reproduce/portable-gruszka.sh prints as its source tree; the list is kept in
    dest/logs/<program>.sources."""
    src, logs = dest / 'src', dest / 'logs'
    src.mkdir(exist_ok=True)
    logs.mkdir(exist_ok=True)
    for program, parts in SOURCE_SETS.items():
        (src / program).mkdir()
        for folder, names in parts:
            origin = project / folder
            for top in sorted(names or (entry.name for entry in origin.iterdir() if entry.name != '.lake')):
                for path in (origin / top, *sorted((origin / top).rglob('*'))):
                    name = path.relative_to(origin).as_posix()
                    if any(name == out or name.startswith(out + '/') for out in LEFT_OUT.get(program, ())):
                        continue
                    if path.is_symlink() or not (path.is_file() or path.is_dir()):
                        raise Declined(f'{folder}/{name}: neither a regular file nor a directory')
                    if path.is_dir():
                        (src / program / name).mkdir()
                    else:
                        shutil.copyfile(path, src / program / name)
    if hashlib.sha256(patch[0].read_bytes()).hexdigest() != patch[1]:
        raise Declined(patch[0].name + ': SHA-256 mismatch')
    try:
        applied = subprocess.run(['/usr/bin/patch', '--batch', '--verbose', '--fuzz=0', '-p1'],
                                 input=patch[0].read_bytes(), cwd=src / 'gruszka',
                                 env={'PATH': '/usr/bin:/bin', 'LC_ALL': 'C'}, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
    except OSError as error:
        raise Declined(f'cannot run /usr/bin/patch: {error.strerror}') from None
    (logs / 'gruszka.patch').write_bytes(applied.stdout)
    if applied.returncode != 0 or re.search(rb'offset|fuzz|FAILED|reversed|previously applied', applied.stdout,
                                            flags=re.I):
        raise Declined(patch[0].name + ' did not apply exactly: ' + str(logs / 'gruszka.patch'))
    found = {}
    for tree in sorted(src.iterdir()):
        files = sorted('./' + path.relative_to(tree).as_posix() for path in tree.rglob('*') if path.is_file())
        listing = ''.join(f'{hashlib.sha256((tree / name).read_bytes()).hexdigest()}  {name}\n' for name in files)
        (logs / (tree.name + '.sources')).write_text(listing, encoding='utf-8')
        found[tree.name] = hashlib.sha256(listing.encode('utf-8')).hexdigest()
    return found


# Where the machine that built the official Lean libraries kept their sources: every program linked from them holds
# such paths, on every machine alike.
RELEASE_BUILD = b'/Users/runner/work/lean4/'


def machine_paths(program, folders):
    """Which of `folders` ({what: path}) a built program holds as text. A pinned program may hold none: only a
    machine with the same folders could rebuild its bytes, and the name of an account would stand in a file that
    others are asked to reproduce. A folder without a name (empty, or the root) is not looked for."""
    data = Path(program).read_bytes().replace(RELEASE_BUILD, b'')
    return [what for what, folder in folders.items() if len(str(folder)) > 1 and str(folder).encode() in data]


def write_record(record, programs, sources, notes):
    """Write the record of the programs built on this machine: `notes` as comment lines, then one
    `SRC <program> <fingerprint>` and one `PIN <program> <sha256> <absolute path>` line for each program. An
    earlier record is replaced. Returns the lines written and the SHA-256 of the bytes written: the digest a
    caller hands to the judge is that of what this build recorded, not of whatever the path holds later."""
    lines = ['# ' + note for note in notes]
    for name in sorted(programs):
        lines.append(f'SRC {name} {sources[name]}')
        lines.append(f'PIN {name} {hashlib.sha256(Path(programs[name]).read_bytes()).hexdigest()} {programs[name]}')
    data = ('\n'.join(lines) + '\n').encode('utf-8')
    record.parent.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile('wb', dir=record.parent, prefix='.pins-macos.', delete=False) as new:
        new.write(data)
    os.replace(new.name, record)
    return lines, hashlib.sha256(data).hexdigest()


CONFIG_STEP_HEAD = 'CFGMSG=$(/usr/bin/python3 -I - '
CONFIG_STEP_TAIL = " <<'PY' 2>&1"
CONFIG_STEP_END = ') || decline "config refused: $CFGMSG"'


def config_step(script, name):
    """Return (code, arguments) of the configuration step inside a judge script.

    Every judge script keeps its configuration guard (strict JSON, permitted axioms, definition targets, names
    compared as Lean names) as a Python here-document. The macOS judge runs that text unchanged instead of a
    port of it. `script` holds the bytes of the script. The step is located exactly:
    one start line, the first `PY` line after it, where bash ends the here-document, and the line that turns
    a failure of the step into DECLINED."""
    lines = script.decode('utf-8').split('\n')
    starts = [i for i, line in enumerate(lines)
              if line.startswith(CONFIG_STEP_HEAD) and line.endswith(CONFIG_STEP_TAIL)]
    if len(starts) != 1 or 'PY' not in lines[starts[0] + 1:]:
        raise Declined('cannot locate the configuration step of ' + name)
    start = starts[0]
    end = lines.index('PY', start + 1)
    if lines[end + 1:end + 2] != [CONFIG_STEP_END]:
        raise Declined('unexpected end of the configuration step of ' + name)
    arguments = lines[start][len(CONFIG_STEP_HEAD):-len(CONFIG_STEP_TAIL)].split(' ')
    return '\n'.join(lines[start + 1:end]) + '\n', arguments


class Record:
    """The record of the programs built on this machine (fastverify/config/pins-macos.env, not tracked).

    It holds comment lines and, for each program, one `SRC <program> <fingerprint>` and one
    `PIN <program> <sha256> <absolute path>` line; any other line, another program name or a second line for a
    program is refused. `expected_sha256`, when given, is the SHA-256 the caller expects of the record: another
    record is refused before a line of it is read. The driver clones each program it runs from `paths` and
    compares the clone with `digests` and with pins.env (judge.py)."""

    def __init__(self, path, expected_sha256=None):
        self.raw = Path(path).read_bytes()
        self.sha256 = hashlib.sha256(self.raw).hexdigest()
        if expected_sha256 is not None and self.sha256 != expected_sha256:
            raise Declined(f'record of the programs sha256 {self.sha256} != --pins-sha256 {expected_sha256}')
        self.paths, self.digests, self.sources = {}, {}, {}
        try:
            lines = self.raw.decode('utf-8').splitlines()
        except UnicodeDecodeError:
            raise Declined('the record of the programs is not UTF-8 text') from None
        for line in lines:
            words = line.split(maxsplit=3)
            if line.startswith('#'):
                continue
            known = len(words) >= 3 and words[1] in PROGRAMS and SHA256.fullmatch(words[2]) is not None
            if known and words[0] == 'PIN' and len(words) == 4 and words[1] not in self.digests \
                    and Path(words[3]).is_absolute():
                self.digests[words[1]], self.paths[words[1]] = words[2], Path(words[3])
            elif known and words[0] == 'SRC' and len(words) == 3 and words[1] not in self.sources:
                self.sources[words[1]] = words[2]
            else:
                raise Declined('the record of the programs has a line that is not a PIN or SRC line of one program: '
                               'run build-judge-macos.sh')


def tail(path, size=65536):
    """The last `size` bytes of a file. The rest is not read."""
    with open(path, 'rb') as stream:
        stream.seek(0, os.SEEK_END)
        stream.seek(max(0, stream.tell() - size))
        return stream.read(size)


def memory_limit(requested_mib):
    """The memory limit of each leg in bytes and where it comes from: the physical memory of the machine, or
    `--mem-budget-mb` when the caller gives one, which may not be more. The guard stops a leg at the limit, and
    that is no verdict."""
    physical = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
    if not requested_mib:
        return physical, 'physical memory'
    if requested_mib * 1024**2 > physical:
        raise Declined(f'--mem-budget-mb {requested_mib}: this machine has {physical // 1024**2} MiB of memory')
    return requested_mib * 1024**2, '--mem-budget-mb'


def run_leg(cmd, env, cwd, log, limit_s, limit_bytes, stdout_log=None, limit_is='', owner=None):
    """Run one leg under the resource guard. The guard's report and the logs stay outside the directories
    the leg may write. Returns (exit status 0 or 1, peak memory in bytes, seconds). Every other end is raised
    as Declined, with the guard's report in its `report` when there is one; `limit_is` names the memory limit
    for the reason of a leg that was stopped at it. The guard kills the leg when the process
    `owner` ends (this process if none is given) or the guard itself."""
    result = Path(str(log) + '.guard.json')
    if result.exists():
        raise Declined('leg report already exists')
    guard = ['/usr/bin/python3', '-I', str(GUARD), '--owner-pid', str(owner or os.getpid()), '--poll', '1',
             '--grace', '0', '--mem', str(limit_bytes)]
    if limit_s:
        guard += ['--wall', f'{max(limit_s, 0.001):.3f}']
    guard += ['--json', str(result), '--', *cmd]
    with Path(log).open('xb') as output:
        # The replay programs write their decision to stdout and progress to stderr: the two are kept apart.
        with (stdout_log.open('xb') if stdout_log else nullcontext(output)) as stdout:
            proc = subprocess.run(guard, env=env, cwd=cwd, stdin=subprocess.DEVNULL,
                                  stdout=stdout, stderr=output)
    if not result.is_file():
        raise Declined('missing supervision report for ' + Path(log).name)
    report = json.loads(result.read_text())
    rc = report['returncode']
    if report['violation'] == 'mem':
        failed = Declined(f"{Path(log).name}: the leg needs more memory than its limit, {limit_is}: "
                          f"{report['detail']}")
    elif report['violation'] is not None:
        failed = Declined(f"{Path(log).name}: {report['violation']} limit or monitor failure: {report['detail']}")
    elif rc not in (0, 1) or proc.returncode != rc:
        own_exit = type(rc) is int and rc == 2 and proc.returncode == 2
        failed = (LegExit if own_exit else Declined)(
            f'{Path(log).name}: abnormal leg exit {rc} (guard {proc.returncode})')
    else:
        wall, peak = report['wall_s'], report['peak']['mem']
        if not math.isfinite(wall) or wall < 0 or peak < 0:
            raise Declined('invalid supervision metrics')
        return rc, peak, wall
    failed.report = report
    raise failed
