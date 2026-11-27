"""The macOS judge: comparison, official Lean 4.36 kernel replay and second kernel, one after another.

Started by enter.py for check/lowmem/check-sound-lowmem.sh (mode lowmem) and check/lowmem/check-sound-ultralowmem.sh
(mode ultralowmem), each with the legs of that script. It starts programs built from the judge sources of this
tree and applies the rules of the script; no kernel and no comparison is implemented here. It publishes nothing:
its result goes to enter.py on descriptor 3. Arguments and limits: README.md in this directory."""
import argparse
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
# enter.py starts this file with python3 -I: only the sibling module and the standard library are imported. An
# installation that cannot be imported ends this program without a result, which enter.py answers with DECLINED.
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
from support import (GUARD, PINS_FILE, SELFTESTS, Declined, LegExit, Record, TreePins, config_step,  # noqa: E402
                     memory_limit, run_leg, tail)

FV = HERE.parents[2]
RUNNER = FV / 'lib/macos/sandbox-run.py'
# The record of the programs built on this machine lives here: pins-macos.env, or the pins*.env file directly
# in this directory that `--pins` names (own_pins).
PINS_DIR = FV / 'config'
# Shared with the Linux judges, never copied: the cross-version gate with its release table, the default hints.
XVCHECK = FV / 'check/xversion/xvcheck.py'
RELEASES = FV / 'check/xversion/releases.json'
HINTS = FV / 'check/sound/hints/default.txt'
# Each mode is one judge script: the name the script gives itself in a result, the program of its official-kernel
# leg with the arguments and the environment of the script's own wrapper, and the options only that script has.
# The configuration step of the script runs unchanged (support.config_step).
MODES = {
    'lowmem': {'script': FV / 'check/lowmem/check-sound-lowmem.sh', 'checker': 'checkSoundLowMem',
               'replay': 'pleanchecker', 'replay_args': [], 'replay_env': {}, 'options': ('--pins', '--hide'),
               'second': 'gruszka (independent)'},
    'ultralowmem': {'script': FV / 'check/lowmem/check-sound-ultralowmem.sh', 'checker': 'checkSoundUltraLowMem',
                    'replay': 'pleanchecker_lowmem', 'replay_args': ['--low-mem', '--evict=smart'],
                    'replay_env': {'MIMALLOC_PURGE_DELAY': '0', 'MIMALLOC_PURGE_DECOMMITS': '1'}, 'options': (),
                    'second': 'gruszka (independent; the default second kernel, where the Linux script runs '
                              'gruszka_lowmem)'},
}
# The argument list of the configuration step in both scripts. Another list is an interface this driver does not
# know: no verdict.
CONFIG_STEP_ARGS = ['"$W/comparator.orig.json"', '"$W/comparator.json"', '"$W/bin/gruszka-kernel"', '"$KEEPK"', '"$W"']
FLAGS = {'--private-inputs': 'private_inputs', '--keep-config-kernels': 'keep_config_kernels',
         '--require-sorried-holes': 'require_sorried_holes'}
VALUES = {'--threads': 'threads', '--workdir': 'workdir', '--json': 'json', '--timeout': 'timeout',
          '--hints': 'hints', '--incr-dir': 'incr_dir', '--integrity-cache': 'integrity_cache',
          '--mem-budget-mb': 'mem_budget_mb', '--log': 'log', '--challenge-sha256': 'challenge_sha256',
          '--comparator-sha256': 'comparator_sha256', '--pins-sha256': 'pins_sha256', '--pins': 'pins',
          '--hide': 'hide'}
# The options whose value is a file that the driver reads, as it reads the three inputs, and the value that names
# no file. The other values are no file it reads: numbers, digests, folders, and the two outputs.
READ = {'--hints': 'none', '--hide': 'none', '--pins': None}
USAGE = ('usage: {name} EXPORT CHALLENGE_EXPORT COMPARATOR_JSON --pins-sha256 SHA256 [--threads N] [--json FILE] '
         '[--log FILE] [--timeout S] [--workdir DIR] [--keep-config-kernels] [--hints FILE|none] [--incr-dir DIR] '
         '[--private-inputs] [--integrity-cache DIR] [--mem-budget-mb MB]{own} | --preflight')
# What enter.py waits for: the exit status of each verdict and, on descriptor 3, the result with that verdict.
STATUS = {'ACCEPTED': 40, 'REJECTED': 41, 'DECLINED': 42, 'PREFLIGHT_OK': 43}
CLEAN_ENV = {'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8'}
MIB = 1024 * 1024
# The first argument of the comparison program names a Lean installation. With --compare-only it starts nothing
# of it, and no leg may read a toolchain: it is given the system's empty directory.
NO_TOOLCHAIN = '/var/empty'
# The one decline of the second kernel that the judge scripts answer with one more run, with one worker.
K2_ROOM = 'a worker table is full'
# The streaming replay ends with exit status 2 and this line when it cannot decide: resource exhaustion, a
# closure above its budget, an interruption or an internal error.
LEAN_NO_VERDICT = 'Lean default kernel could not decide (no verdict): '
ACCEPT = {
    'compare': 'Comparison and axiom check passed!',
    'lean': 'Lean default kernel accepts the solution',
    'k2': 'accepted',
}
# What the judge scripts say when a kernel rejects, and when all three legs accept.
REJECT = {'lean': 'error: Lean default exited with 1', 'k2': 'error: gruszka (second kernel) exited with 1'}
ACCEPTED = ('statements + axioms match the challenge (official judge code via ccmp-lowmem); the official Lean 4.36 '
            'kernel (parallel replay) and the independent kernel gruszka accept every declaration of the export '
            '(sequential low-memory check)')
# A line that starts like this reports a failure of the machine or of the program itself, never a judgment of
# the export: memory, threads, the stack, a panic, a file that cannot be read or written. The last text is the
# comparison's own, for a read of the export that ends early (lowmem_arena.c).
RESOURCE = re.compile(
    r'^(?:(?:Lean default kernel|Quotient post-check) rejects the solution: |error: |uncaught exception: )?'
    r'(?:memory allocation of [0-9]+ bytes failed|out of memory|std::bad_alloc|failed to create thread|'
    r'resource exhausted|Stack overflow detected|deep recursion was detected at |\(kernel\) deep recursion detected|'
    r'internal error:|internal panic:|worker error:|permission denied|no space left on device|declined:|'
    r'panic(?: at|:)|fatal error:|short pread on export file)', re.I)
# What Lean 4.36 and Rust print for an error of the operating system: every IO.Error but a user error carries
# "(error code: N" and an unexpected end of input is "end of file" (Init/System/IOError.lean, toString); Rust writes
# "(os error N)". A leg that reports one and would otherwise be read as a rejection has not judged the export.
HOST_ERROR = re.compile(rb'\(error code: [0-9]+[,)]|\(os error [0-9]+\)')
END_OF_FILE = b'end of file'
# CPython refuses int() of a text with more than 4300 digits since 3.9.14, 3.10.7 and 3.11; the system Python of
# macOS (3.9.6) does not. The configuration step of the judge scripts converts in two places: an integer literal
# anywhere in the file, and a numeric component of a name in one of these lists.
INT_DIGITS = 4300
NAME_LISTS = ('permitted_axioms', 'definition_names', 'theorem_names')


class Usage(Declined):
    """Fewer than three inputs: the usage line of the judge script, for stderr."""


class TimeLimit(Declined):
    """The caller's --timeout ran out between two steps of the run."""


def new_arguments():
    """The arguments of a run before any is read. enter.py reads them with the same reader. `roles` is what the
    reader took each word for, in order, up to the word it refused: 'option' (an option word), 'input' (one of the
    three inputs, or the value of an option in READ that names a file), 'json' and 'log' (the values of those
    options), 'value' (the value of any other option). enter.py takes from it which words are values of --json and
    which keep an earlier result there."""
    return argparse.Namespace(inputs=[], json=None, log=None, hints=None, hide=None, pins=None, pins_sha256=None,
                              roles=[],
                              preflight=False, threads=None, timeout='0', mem_budget_mb='0', workdir=None,
                              incr_dir=None, integrity_cache=None, challenge_sha256=None, comparator_sha256=None,
                              private_inputs=False, keep_config_kernels=False, require_sorried_holes=False)


def long_number_in_name(name):
    """Whether the configuration step would convert more than INT_DIGITS digits of this name: a component that
    starts with a digit is a number (parse_lean_name of the step), digits between « and » or inside an
    identifier are text. Identifiers are not checked here: the step refuses a name that is no Lean name under
    every Python."""
    i = 0
    while i < len(name):
        if name[i] == '«':
            j = name.find('»', i + 1)
            if j < 0:
                return False
            i = j + 1
        elif '0' <= name[i] <= '9':
            j = i
            while j < len(name) and '0' <= name[j] <= '9':
                j += 1
            if j - i > INT_DIGITS:
                return True
            i = j
        else:
            while i < len(name) and name[i] != '.':
                i += 1
        if i < len(name) and name[i] != '.':
            return False
        i += 1
    return False


def refuse_long_integers(config):
    """No verdict for a configuration that the configuration step refuses only under an interpreter with the
    limit above, so that the answer does not depend on the Python of the machine. A file that is not JSON is
    left to the step, which refuses it in the words of the official comparator."""
    def integer(text):
        if len(text.lstrip('-')) > INT_DIGITS:
            raise Declined(f'config refused: an integer of more than {INT_DIGITS} digits')
        return 0
    try:
        data = json.loads(config.read_bytes().decode('utf-8'), parse_int=integer, parse_float=lambda text: 0.0,
                          parse_constant=lambda text: 0.0)
    except (ValueError, RecursionError):
        return
    for key in NAME_LISTS if isinstance(data, dict) else ():
        names = data[key] if isinstance(data.get(key), list) else []
        if any(isinstance(name, str) and long_number_in_name(name) for name in names):
            raise Declined(f'config refused: a name component of more than {INT_DIGITS} digits in {key}')


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def stamp(path):
    s = path.lstat()
    if not stat.S_ISREG(s.st_mode):
        raise Declined('expected a regular file: ' + str(path))
    return s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns


def private_copy(source, dst, mode=0o400):
    src = Path(source).resolve(strict=True)
    before = stamp(src)
    # On APFS `cp -c` clones the file (a new inode); across file systems cp copies the bytes. A hard link
    # would let the owner of the input change what a leg reads.
    subprocess.run(['/bin/cp', '-c', str(src), str(dst)], check=True, env=CLEAN_ENV)
    if stamp(src) != before or stamp(dst)[2] != before[2] or src.samefile(dst):
        raise Declined('input changed during private copy: ' + str(src))
    dst.chmod(mode)


def read_arguments(mode, words, a):
    """The arguments as the judge script of the mode reads them: `--preflight` only in front, otherwise the three
    inputs in front; then options, the value of an option in the next argument, whatever it is; the last of a
    repeated option counts. `--pins-sha256` is the one option the scripts do not have. The role of each word it
    comes to goes into `a.roles` (new_arguments); the word it refuses, and every word after it, have none."""
    script = MODES[mode]['script'].name
    words = list(words)
    a.preflight = words[:1] == ['--preflight']
    if a.preflight:
        del words[0]
        a.roles.append('option')
    elif len(words) < 3:
        raise Usage(USAGE.format(name=script, own=''.join(f' [{name} FILE]' for name in MODES[mode]['options'])))
    else:
        a.inputs = words[:3]
        del words[:3]
        a.roles += ['input'] * 3
    while words:
        name = words.pop(0)
        if name in FLAGS:
            setattr(a, FLAGS[name], True)
            a.roles.append('option')
        elif name in VALUES and (name not in MODES['lowmem']['options'] or name in MODES[mode]['options']):
            a.roles.append('option')
            if not words:
                raise Declined(name + ' needs a value')
            value = words.pop(0)
            setattr(a, VALUES[name], value)
            a.roles.append({'--json': 'json', '--log': 'log'}.get(
                name, 'input' if name in READ and value != READ[name] else 'value'))
            if name in ('--challenge-sha256', '--comparator-sha256') and not getattr(a, VALUES[name]):
                raise Declined(name + ' needs a non-empty value')
            if name == '--log' and not a.log:
                # The scripts open the log where they read the option, and decline when they cannot.
                raise Declined("cannot write log ''")
        else:
            raise Declined(f"unknown argument '{name}'")

    def number(value, message):
        if not re.fullmatch('[0-9]{1,9}', value):
            raise Declined(message)
        return int(value)
    a.threads = number(a.threads or str(os.cpu_count() or 1), '--threads must be a positive number')
    if a.threads < 1:
        raise Declined('--threads must be a positive number')
    a.timeout = number(a.timeout, '--timeout must be a number of seconds (0 = none)')
    a.mem_budget_mb = number(a.mem_budget_mb, '--mem-budget-mb must be a non-negative integer')
    for name in a.inputs:
        if not name:
            raise Declined('empty input path')
        real = os.path.realpath(name)
        if not os.path.isdir(os.path.dirname(real)):
            raise Declined(f"cannot resolve '{name}'")
        if not os.path.isfile(real):
            raise Declined(f"input is not a regular file: '{name}'")


def own_pins(option):
    """The record of the programs: `--pins` as the judge scripts read it, the judge's own pins files only.

    An absolute path that, after resolving every symbolic link, names a pins*.env file directly in
    fastverify/config. Without the option it is pins-macos.env there, under the same rule: a symbolic link
    that leads elsewhere is refused. Returns the resolved path of the record."""
    if option and not os.path.isabs(option):
        raise Declined('--pins must be an absolute path')
    try:
        manifest = Path(option or PINS_DIR / 'pins-macos.env').resolve()
    except (OSError, RuntimeError):
        raise Declined(f"cannot resolve --pins '{option}'") from None
    if not fnmatch.fnmatchcase(manifest.name, 'pins*.env') or manifest.parent != PINS_DIR:
        raise Declined(('--pins' if option else 'the record of the programs')
                       + f' must name a pins*.env file in {PINS_DIR}')
    if not manifest.is_file():
        raise Declined(f'missing {manifest}: build the programs with check/sound/macos/build-judge-macos.sh')
    return manifest


def options_without_effect(a):
    """Two options of the judge scripts have nothing to do here: every pinned file is hashed at every run, and
    the plain replay always runs. Their values are checked as the scripts check them; an empty value is none."""
    if a.integrity_cache:
        cache = Path(os.path.realpath(a.integrity_cache))
        if not cache.parent.is_dir():
            raise Declined('cannot resolve --integrity-cache')
        if not cache.is_dir() or (cache.stat().st_uid, stat.S_IMODE(cache.stat().st_mode)) != (os.getuid(), 0o700):
            raise Declined(f'--integrity-cache: not a directory owned by this user with mode 700: {cache}')
    if a.incr_dir and not a.preflight and not os.path.isdir(os.path.dirname(os.path.realpath(a.incr_dir))):
        raise Declined('cannot resolve --incr-dir')


def config_guard(script, step, config, scratch, keep, limit):
    """Run the configuration step of the judge script on the private config copy and return the private
    configuration it writes, which the comparison is given.

    The step is the script's own code (support.config_step). It refuses a config that the official comparator
    stops at, that permits an axiom beyond propext, Quot.sound and Classical.choice, or that lists a kernel
    primitive, quotient builtin, theorem target or permitted axiom as a definition target. With
    --keep-config-kernels it also lists the kernels of the config that the script would run; no such kernel
    runs here, so any is no verdict."""
    code, arguments = step
    if arguments != CONFIG_STEP_ARGS:
        raise Declined('unknown interface of the configuration step of ' + script)
    refuse_long_integers(config)
    (scratch / 'bin').mkdir()
    private = scratch / 'comparator.json'
    values = [config, private, scratch / 'bin/gruszka-kernel', '1' if keep else '0', scratch]
    try:
        run = subprocess.run(['/usr/bin/python3', '-I', '-', *map(str, values)], input=code.encode('utf-8'),
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=scratch, env=CLEAN_ENV,
                             timeout=limit or None)
    except subprocess.TimeoutExpired:
        raise Declined('time limit exceeded during the configuration step') from None
    if run.returncode != 0:
        raise Declined('config refused: ' + run.stdout.decode('utf-8', errors='replace').strip()[:1000])
    kept = [line.split('\t', 1)[-1] for line in (scratch / 'kept.txt').read_text(encoding='utf-8').splitlines()]
    if kept:
        raise Declined('--keep-config-kernels: the config names ' + ', '.join(map(repr, kept))
                       + ', and no kernel of a config runs on macOS')
    private.chmod(0o400)
    return private


def check_caller_pins(a, digests):
    """--challenge-sha256 / --comparator-sha256 are verified on this run's private copies."""
    for value in (a.challenge_sha256, a.comparator_sha256):
        if value is not None and not re.fullmatch(r'[0-9a-f]{64}', value):
            raise Declined('--challenge-sha256 / --comparator-sha256 must be 64 lowercase hex digits')
    if a.challenge_sha256 is not None and digests['challenge'] != a.challenge_sha256:
        raise Declined(f"challenge export sha256 {digests['challenge']} (private copy) != "
                       f'--challenge-sha256 {a.challenge_sha256}')
    if a.comparator_sha256 is not None and digests['comparator'] != a.comparator_sha256:
        raise Declined(f"comparator config sha256 {digests['comparator']} (private copy) != "
                       f'--comparator-sha256 {a.comparator_sha256}')


def cross_version_gate(challenge, config, scratch, require_sorried, limit):
    """The cross-version gate (check/xversion/xvcheck.py) on the private copies.

    Same call and same mapping as in the judge scripts: exit 0 with verdict OK lets the legs
    decide (0), exit 1 with verdict REJECTED is REJECTED (1), anything else is no verdict (2).
    Returns that code, the reason and the gate's own report."""
    report = scratch / 'xversion.json'
    cmd = ['/usr/bin/python3', '-I', str(XVCHECK), str(challenge), str(config), '--releases', str(RELEASES)]
    if require_sorried:
        cmd.append('--require-sorried-holes')
    cmd += ['--json', str(report)]
    try:
        with (scratch / 'xversion.out').open('xb') as output:
            rc = subprocess.run(cmd, stdin=subprocess.DEVNULL, stdout=output, stderr=subprocess.STDOUT,
                                cwd=scratch, env=CLEAN_ENV, timeout=limit or None).returncode
    except subprocess.TimeoutExpired:
        raise Declined('time limit exceeded during the cross-version gate') from None
    data, verdict, reason = {}, '', ''
    try:
        loaded = json.loads(report.read_text(encoding='utf-8'))
        if isinstance(loaded, dict):
            data, verdict, reason = loaded, loaded.get('verdict', ''), str(loaded.get('reason', ''))[:300]
    except (OSError, ValueError):
        pass
    if rc == 0 and verdict == 'OK':
        return 0, reason, data
    if rc == 1 and verdict == 'REJECTED':
        return 1, 'xversion: ' + reason, data
    return 2, f'xversion gate failed (rc={rc}): {reason}', data


def output_lines(logfile):
    """The lines of a leg's output, each cut at 64 KiB: the start of a line can identify a message, and a cut
    line is never an exact success line."""
    with logfile.open('rb') as stream:
        while True:
            raw = stream.readline(65536)
            if not raw:
                return
            if not raw.endswith(b'\n') and len(raw) == 65536:
                tail = raw
                while tail and not tail.endswith(b'\n'):
                    tail = stream.readline(65536)
                yield raw.decode('utf-8', errors='replace') + '…'
            else:
                yield raw.rstrip(b'\n').decode('utf-8', errors='replace')


def no_verdict_line(logs):
    """The first line of these outputs that starts as a report of a failure of the machine or of the program
    itself (RESOURCE, LEAN_NO_VERDICT), or None."""
    for log in logs:
        for line in output_lines(log):
            if RESOURCE.match(line) or line.startswith(LEAN_NO_VERDICT):
                return line
    return None


def host_error_line(logfile):
    """The start of the first line of an output that holds an error of the operating system in the words of Lean
    4.36 or of Rust: HOST_ERROR anywhere in the line, or a line that is, or ends in a colon and, `end of file`.
    None without one. Every byte of a line is looked at, piece by piece with an overlap, so a line that
    output_lines cuts cannot hide one."""
    with logfile.open('rb') as stream:
        start, carry, length = None, b'', 0
        while True:
            piece = stream.readline(65536)
            ended = not piece or piece.endswith(b'\n')         # the end of a line, or of the file
            body = carry + (piece[:-1] if piece.endswith(b'\n') else piece)
            start = piece if start is None else start
            length += len(body) - len(carry)
            if HOST_ERROR.search(body) or ended and (
                    body.endswith(b': ' + END_OF_FILE) or body == END_OF_FILE and length == len(END_OF_FILE)):
                return start[:300].decode('utf-8', errors='replace').rstrip('\n')
            if not piece:
                return None
            start, carry, length = (None, b'', 0) if ended else (start, body[-64:], length)


def decide_replay(rc, said, noise):
    """What the end of the official-kernel leg means. `rc` is 0 or 1, the program's own exit status as the guard
    and the launcher both report it; `said` is its stdout, which holds its decision and nothing else, `noise`
    its stderr.

    The judge scripts take exit status 1 as the rejection unless the log shows a stack failure. This driver
    wants the rejection that the program made: its rejection line first on stdout, the rejection of the quotient
    check after its acceptance line, or, with nothing on stdout, the exception that ended it before the replay
    on stderr (an export that does not parse). Exit status 1 without one of these is no verdict, and so is a
    line anywhere that reports a failure of the machine or of the program (RESOURCE, HOST_ERROR). ACCEPTED
    needs exit status 0 and a stdout that is the acceptance line and nothing else, as in the scripts: the
    stderr of a replay that accepts is not searched."""
    lines = output_lines(said)
    first = next(lines, None)
    then = next(lines, None)
    if rc == 0:
        if first != ACCEPT['lean'] or then is not None:
            raise Declined('official-kernel leg rc=0 without its acceptance line alone on stdout')
        return 0, first
    # The quotient check follows an accepted replay and can reject after the acceptance line was printed.
    if first == ACCEPT['lean'] and not (then or '').startswith('Quotient post-check rejects the solution: '):
        raise Declined('inconsistent output of the official-kernel leg: exit status 1 after its acceptance line')
    failure = no_verdict_line((said, noise)) or host_error_line(said) or host_error_line(noise)
    if failure is not None:
        raise Declined(f'the official-kernel leg could not finish ({failure[:300]}): no verdict')
    if first == ACCEPT['lean']:
        rejection = then
    elif first is None:
        rejection = next((line for line in output_lines(noise) if line.startswith('uncaught exception: ')), None)
    else:
        rejection = first if first.startswith('Lean default kernel rejects the solution: ') else None
    if rejection is None:
        raise Declined('the official-kernel leg ended with exit status 1 without a rejection of its own: no verdict')
    return 1, rejection[:400]


def worker_table_decline(logfile):
    """Whether the log of a second-kernel run that ended with exit status 2 is a decline for worker-table
    room and nothing else: the trigger of the one-worker retry of the judge scripts (their gruszka-kernel
    wrapper).

    Such a decline depends on the schedule of the workers, not on the export. The scripts' condition on the
    log, all of it: not empty, ends with a newline, every line is `note: ...` except exactly one `declined: `
    line, which is the last line and ends `: a worker table is full`. It is tested on the bytes of the log,
    read as a stream. One case is decided here and left to awk in the scripts: a log with a NUL byte is never
    such a decline."""
    declines, last, pending = 0, b'', b''
    try:
        with logfile.open('rb') as stream:
            while True:
                block = stream.read(1 << 20)
                if b'\0' in block:
                    return False
                lines = (pending + block).split(b'\n')
                # A line is told by how it starts, the last one also by how it ends: the middle of a long line
                # is not kept.
                pending = lines.pop() if block else b''
                if len(pending) > 256:
                    pending = pending[:16] + pending[-64:]
                if not block and lines.pop() != b'':
                    return False                               # the log does not end with a newline
                for line in lines:
                    if not line.startswith((b'declined: ', b'note: ')):
                        return False
                    declines += line.startswith(b'declined: ')
                    last = line[:16] + line[-64:] if len(line) > 256 else line
                if not block:
                    break
    except OSError:
        return False
    return declines == 1 and last.startswith(b'declined: ') and last[10:].endswith(b': ' + K2_ROOM.encode())


def decide(leg, rc, logfile):
    """What the end of the comparison or of the second kernel means; `rc` is 0 or 1. A rejection is a line the
    program wrote as its judgment, with exit status 1 and without a line that reports a failure of the machine
    or of the program itself. An error of the operating system (host_error_line) counts only there: it does
    not take an acceptance away."""
    rejection = None
    first_error = None
    accepted = False
    for line in output_lines(logfile):
        if line == ACCEPT[leg]:
            accepted = True
        if line.startswith('error:'):
            first_error = first_error or line[:400]
        elif leg == 'k2' and line.startswith('rejected: '):
            rejection = line[:400]
    if leg == 'compare':
        # As the judge scripts: with exit status 1 the first `error:` line of the comparison is its judgment
        # (compareAt, the axiom check, the parse of the export).
        rejection = first_error
    failure = no_verdict_line((logfile,)) or (first_error if leg == 'k2' else None)
    if rc == 0 and accepted and not (failure or rejection or first_error):
        return 0, ACCEPT[leg]
    failure = failure or host_error_line(logfile)
    if rc == 1 and rejection and not (failure or accepted):
        return 1, rejection
    raise Declined('%s could not decide (rc=%s): %s' %
                   ({'compare': 'ccmp-lowmem', 'k2': 'the second kernel'}[leg], rc,
                    (failure or first_error or rejection or 'missing or inconsistent verdict marker')[:400]))


def null_device(path):
    """Whether a resolved path is the null device itself: its name, and a character device with its numbers."""
    try:
        found, null = path.stat(), os.stat(os.devnull)
    except OSError:
        return False
    return str(path) == os.devnull and stat.S_ISCHR(found.st_mode) and found.st_rdev == null.st_rdev


def open_log(path, how):
    """The caller's log for writing. A symbolic link at that path is not followed."""
    return os.fdopen(os.open(path, os.O_WRONLY | os.O_CREAT | os.O_NOFOLLOW | how, 0o600), 'wb')


def execute(mode, a, result):
    spec = MODES[mode]
    script = spec['script']
    if sys.platform != 'darwin':
        raise Declined('this driver requires macOS')
    # The record of the programs is a local file. Which record a verdict may rest on is the caller's word, given
    # before the record or anything it names is read; only --preflight, which judges nothing, runs without it.
    if a.pins_sha256 is None and not a.preflight:
        raise Declined('--pins-sha256 is required to judge: the SHA-256 of the record of the programs you trust, '
                       'which build-judge-macos.sh printed when it built them')
    if a.pins_sha256 is not None and not re.fullmatch(r'[0-9a-f]{64}', a.pins_sha256):
        raise Declined('--pins-sha256 must be 64 lowercase hex digits')
    a.pins = str(own_pins(a.pins))
    record = Record(a.pins, expected_sha256=a.pins_sha256)
    # With the record and pins.env, every file this run reads is known. The caller's files are compared with all of
    # them before anything else is refused, and written only then: the log here, the JSON file by enter.py, which is
    # told whether its destination passed (True), was refused (False) or was not reached (None).
    hints = a.hints
    if not hints and HINTS.is_file():
        hints = str(HINTS)
    shared = (script, XVCHECK, RELEASES)
    wiring = (HERE / 'judge.py', HERE / 'support.py', HERE / 'enter.py', PINS_FILE, RUNNER, GUARD, *shared)
    inputs = [*a.inputs, a.pins, *record.paths.values(), *wiring]
    inputs += [path for path in (a.hide, hints) if path and path != 'none']
    # The self-test inputs are where pins.env says. A pins.env that cannot be read or is incomplete is refused only
    # after the comparison with the files that are known without it; no destination has passed then.
    try:
        tree, unread = TreePins(), None
        inputs += [tree.files[name][0] for name in SELFTESTS]
    except (Declined, OSError, ValueError) as error:
        unread = error
    a.json_checked = False if a.json else None
    outputs = [Path(p).resolve() for p in (a.json, a.log) if p]
    if (len(set(outputs)) != len(outputs) or len(outputs) == 2 and all(p.exists() for p in outputs)
            and outputs[0].samefile(outputs[1])):
        raise Declined('log and JSON must be distinct paths')
    for path in outputs:
        # An output is a regular file or a new one. The log may also be the null device, which discards it. A
        # descriptor (/dev/fd/N) is no output, whatever it is open on: it is another file in the driver than in
        # enter.py, which appends the verdict line to the log by its path.
        null = bool(a.log) and path == outputs[-1] and null_device(path)
        if not null and (path.exists() and not path.is_file() or Path('/dev/fd') in path.parents):
            raise Declined('output must be a regular file: ' + str(path))
        # The same file also behind more symbolic links than the system follows in one look: by the resolved path.
        if any(path == Path(p).resolve()
               or (path.exists() and any(q.exists() and path.samefile(q) for q in (Path(p), Path(p).resolve())))
               for p in inputs):
            raise Declined('output aliases a protected input: ' + str(path))
        if a.json and path == outputs[0]:
            # The JSON destination has passed, and a refusal of the log is written there. Without pins.env it
            # has not passed: it takes a new file only.
            a.json_checked = True if unread is None else None
    if unread is not None:
        raise unread
    if a.log:
        new = not os.path.lexists(a.log)
        try:
            open_log(a.log, os.O_TRUNC).close()
        except OSError as error:
            raise Declined(f'cannot write log {a.log}: {error.strerror}') from None
        # Two paths that did not exist were compared as texts. Now that the log exists, a JSON destination that is
        # the same file shows: one name in two spellings, on a volume that takes them for the same.
        if a.json and Path(a.json).exists() and Path(a.json).samefile(a.log):
            a.json_checked = False
            if new:
                os.unlink(a.log)
            raise Declined('log and JSON must be distinct paths')
        a.log_written = True
    programs = ('ccmp_lowmem', spec['replay'], 'gruszka')
    for name in programs:
        if name not in record.digests or name not in record.sources:
            raise Declined(f'the record of the programs has no lines for {name}: run build-judge-macos.sh')
        if record.sources[name] != tree.sources[name]:
            raise Declined(f'{name} was not built from the sources of this tree: run build-judge-macos.sh')
    # What a run is cloned from: the programs of this mode, where the record says they are, and the self-test
    # inputs of the tree. pins.env has the digest of every one.
    wanted = {name: (record.paths[name], tree.programs[name]) for name in programs}
    wanted.update({name: tree.files[name] for name in SELFTESTS})
    options_without_effect(a)
    for path in shared:
        if not path.is_file():
            raise Declined('rule file missing: ' + '/'.join(path.parts[-3:]))
    wiring_stamps = {p: stamp(p) for p in wiring}
    # The judge script is read once: the bytes that are hashed are the bytes whose step runs.
    entry = script.read_bytes()
    result['wiring_sha256'] = {p.name: hashlib.sha256(entry).hexdigest() if p == script else sha(p) for p in wiring}
    step = config_step(entry, script.name)
    limit, limit_source = memory_limit(a.mem_budget_mb)
    limit_is = (f'--mem-budget-mb {a.mem_budget_mb} (a larger value raises it)' if a.mem_budget_mb else
                f'the physical memory of this machine ({limit // MIB} MiB)')
    # As the judge scripts cap the workers under --mem-budget-mb below 64 GiB: one for each 256 MiB, at most 32.
    threads = a.threads
    if 0 < a.mem_budget_mb < 65536:
        threads = min(threads, max(1, min(32, a.mem_budget_mb // 256)))
    result.update(
        threads=a.threads, effective_threads=threads, mode='sequential-lowmem',
        version=tree.labels['SOUND_VERSION'],
        basis='challenge export as given (sha256 checked by the caller); statements + axioms: official Lean 4.36 '
              'comparator judge code via 2-pass low-memory streaming reader (ccmp-lowmem compareAt + checkAxioms); '
              f"kernel 1: official Lean 4.36 kernel libraries ({spec['replay']} parallel Lean.Replay walk); kernel "
              f"2: {spec['second']}; legs executed one after another in separate sandboxes",
        private_inputs_asserted=int(a.private_inputs), pins=a.pins, pins_sha256=record.sha256,
        toolchain=tree.labels['TC_VERSION'], memory_limit_bytes=limit, memory_limit_source=limit_source)

    def remaining():
        if not a.timeout:
            return 0
        left = a.timeout - (time.monotonic() - a.started)
        if left <= 0:
            raise TimeLimit(f'time limit of {a.timeout} s exceeded')
        return left
    try:
        # As the judge scripts: an empty --workdir is none.
        tmp = tempfile.TemporaryDirectory(prefix=f".{spec['checker']}.", dir=a.workdir or None)
    except OSError:
        # As the judge scripts: a work directory that cannot be used is replaced by the default one.
        tmp = tempfile.TemporaryDirectory(prefix=f".{spec['checker']}.")
    with tmp:
        w = Path(tmp.name).resolve()
        # As the judge scripts, whose wrappers are shell text: no verdict when such a path has one of these.
        named = (w, a.incr_dir or '', *(record.paths[name] for name in programs))
        if re.search(r'["\\$`\n]', ''.join(map(str, named))):
            raise Declined('a path used by the kernel wrappers contains a shell-special character')
        # Every pinned file is cloned into the private directory of this run, and the clone is what is hashed,
        # started and hashed again. A program is started by its path: on Linux a bind mount fixes the file behind
        # that path for the whole run; here the driver fixes the bytes itself, so what the record's path leads to
        # later is of no consequence.
        pinned, cloned = {}, {}
        for name in sorted(wanted):
            source, digest = wanted[name]
            pinned[name] = w / name
            try:
                private_copy(source, pinned[name], mode=0o500 if name in programs else 0o400)
            except (OSError, subprocess.CalledProcessError):
                raise Declined('pinned file missing or unreadable: ' + name) from None
            cloned[name] = sha(pinned[name])
            if cloned[name] != digest:
                raise Declined(f'sha256 mismatch for {name}: {cloned[name]}, pinned {digest} in '
                               'check/sound/macos/pins.env')
            if name in programs and record.digests[name] != digest:
                raise Declined(f'the record of the programs names another {name} than check/sound/macos/pins.env')
        result['binaries_sha256'] = cloned
        hint_file = w / 'hints'
        if hints and hints != 'none':
            if not Path(hints).is_file() or Path(hints).stat().st_size > 16 * MIB:
                raise Declined(f"--hints: not a regular file <= 16 MiB: '{hints}'")
            private_copy(hints, hint_file)
        else:
            hint_file.touch(mode=0o400)
        hide_file = None
        if a.hide and a.hide != 'none':
            if not Path(a.hide).is_file() or Path(a.hide).stat().st_size > 16 * MIB:
                raise Declined(f"--hide: not a regular file <= 16 MiB: '{a.hide}'")
            hide_file = w / 'hide'
            private_copy(a.hide, hide_file)
            result.update(hide=a.hide, hide_sha256=sha(hide_file))
        solution, challenge, config = w / 'solution.export', w / 'challenge.export', w / 'comparator.orig.json'
        if a.preflight:
            config = pinned['selftest_comparator']
        else:
            for source, private in zip(a.inputs, (solution, challenge, config)):
                private_copy(source, private)
            result['inputs'] = {name: {'size': stamp(private)[2], 'private': 'copy'}
                                for name, private in (('export', solution), ('challenge', challenge))}
        protected = {p: stamp(p) for p in w.iterdir()}

        def verify_inputs():
            # The process that the caller started answers for this driver. Without it nobody takes a verdict.
            if os.getppid() != a.launcher or a.launcher == 1:
                raise Declined('the judge script that started this driver is gone')
            if any(stamp(path) != old for path, old in wiring_stamps.items()):
                raise Declined('judge wiring changed during run')
            if any(stamp(p) != old for p, old in protected.items()):
                raise Declined('an input file was modified during the check')

        def note(message):
            line = (message + '\n').encode('utf-8', errors='replace')
            if a.log:
                with open_log(a.log, os.O_APPEND) as out:
                    out.write(line)
            else:
                sys.stderr.buffer.write(line)
                sys.stderr.buffer.flush()
        note(f"[{spec['checker']}] memory limit of a leg: {limit / 1024**3:.2f} GiB ({limit_source})")

        # The steps of the judge scripts between the private copies and the legs, in their order: the
        # configuration step, the caller's pins, the cross-version gate. --preflight judges the self-test config
        # and skips the two steps that need a caller's challenge.
        scratch = w / 'steps'
        scratch.mkdir()
        private_config = config_guard(script.name, step, config, scratch, a.keep_config_kernels, remaining())
        protected[private_config] = stamp(private_config)
        gate = None
        if not a.preflight:
            digests = {'challenge': sha(challenge), 'comparator': sha(config)}
            result.update(challenge_sha256=digests['challenge'], comparator_sha256=digests['comparator'])
            check_caller_pins(a, digests)
            code, reason, report = cross_version_gate(challenge, config, scratch, a.require_sorried_holes,
                                                      remaining())
            result['xversion'] = {key: report.get(key) for key in (
                'verdict', 'reason', 'lean_version', 'lean_githash', 'export_format', 'rules')}
            note(f"[{spec['checker']}] xversion {report.get('verdict')}: {reason}")
            if code == 2:
                raise Declined(reason)
            if code:
                gate = code, reason
        verify_inputs()

        def stage(label, name, role, args, reads, env, count, legs, again=''):
            """One leg in its own directory and sandbox. Returns its exit status, 0 or 1, and its outputs; every
            other end is raised as no verdict. `again` names the directory and the log of a second run."""
            (w / label).mkdir(exist_ok=True)
            cwd = w / label / (name + again)
            cwd.mkdir()
            env = {'PATH': '/usr/bin:/bin', 'HOME': str(cwd), 'TMPDIR': str(cwd), 'LANG': 'C.UTF-8',
                   'LEAN_ABORT_ON_PANIC': '1', 'LEAN_NUM_THREADS': str(count), **env}
            # The launcher starts the program itself, with these variables and no others: no shell stands between,
            # so a program that cannot be started is the launcher's status 126 and never the status of a rejection.
            cmd = ['/usr/bin/python3', '-I', '-B', str(RUNNER)]
            for path in (pinned[role], *reads, cwd):
                cmd.extend(['--read', str(path)])
            cmd += ['--write', str(cwd)]
            for key, value in env.items():
                cmd += ['--setenv', key, value]
            # The second kernel writes its answer and its notes to one stream, in the order written, as
            # `> log 2>&1` in the wrapper of the judge scripts; the replay's decision on stdout is kept apart.
            if name == 'k2':
                cmd.append('--stderr-to-stdout')
            cmd += ['--', str(pinned[role]), *map(str, args)]
            log = w / label / (name + again + '.log')
            said = w / label / 'lean.stdout' if name == 'lean' else None
            note(f"[{spec['checker']}] {label}: leg {name} ({role}) start: threads={count}")
            verify_inputs()
            try:
                # The guard ends the leg when the process that the caller started is gone, or the guard itself.
                rc, peak, seconds = run_leg(cmd, {'PATH': '/usr/bin:/bin', 'LC_ALL': 'C', 'HOME': str(cwd),
                                                  'TMPDIR': str(cwd)}, cwd, log, remaining(), limit, said,
                                            limit_is=limit_is, owner=a.launcher)
                legs[name] = {'rc': rc, 'ms': round(seconds * 1000), 'peak_footprint_bytes': peak}
                verify_inputs()
            except Declined as stopped:
                # What the guard measured of a leg that it stopped tells the caller which limit to set.
                seen = getattr(stopped, 'report', {})
                seconds, peak = seen.get('wall_s'), (seen.get('peak') or {}).get('mem')
                legs[name] = {'rc': None, 'ms': round(seconds * 1000) if type(seconds) in (int, float) else None,
                              'peak_footprint_bytes': peak if type(peak) is int else None, 'message': str(stopped)}
                # A leg that ended because something of the run changed or its caller is gone: that is the reason.
                verify_inputs()
                raise
            finally:
                for path in (log, said):
                    if path is not None and path.is_file():
                        note(f'--- {label}/{path.name} (last 64 KiB) ---')
                        note(tail(path).decode('utf-8', errors='replace').rstrip('\n'))
            return rc, log, said

        def compare(label, cfg, challenge, solution, count, legs):
            rc, log, _said = stage(label, 'compare', 'ccmp_lowmem',
                                   [NO_TOOLCHAIN, cfg, challenge, solution, '--compare-only'],
                                   [cfg, challenge, solution], {}, count, legs)
            code, legs['compare']['message'] = decide('compare', rc, log)
            return code, legs['compare']['message']

        def replay(label, solution, count, legs):
            env = {'PCHK_PRIO_FILE': str(hint_file), 'PCHK_SLOW_MS': '10000', 'LEAN_STACK_SIZE_KB': '917376',
                   **spec['replay_env']}
            reads = [solution, hint_file]
            if hide_file and label == 'judge':
                reads.append(hide_file)
                env['PCHK_HIDE_FILE'] = str(hide_file)
            try:
                rc, log, said = stage(label, 'lean', spec['replay'],
                                      [*spec['replay_args'], f'-j{count}', '-v', '--from-export', solution],
                                      reads, env, count, legs)
            except LegExit:
                # The replay ended by itself with exit status 2: no verdict. If it says why in its own
                # line, that line is the reason.
                with (w / label / 'lean.stdout').open('rb') as stdout:
                    line = stdout.readline(4096).decode('utf-8', errors='replace').rstrip('\n')
                if not line.startswith(LEAN_NO_VERDICT):
                    raise
                legs['lean']['message'] = line[:400]
                raise Declined(line[:400]) from None
            code, legs['lean']['message'] = decide_replay(rc, said, log)
            return code, REJECT['lean']

        def second(label, solution, count, legs):
            # As the wrapper of every judge script (`"$GRUSZKA" EXPORT WORKERS`): gruszka reads the export
            # itself and packs it in its own memory.
            try:
                rc, log, _said = stage(label, 'k2', 'gruszka', [solution, count], [solution], {}, count, legs)
            except LegExit:
                # The retry of the judge scripts: the judged export (never a self-test), more than one
                # worker, exit status exactly 2, and a log that is a decline for worker-table room and
                # nothing else. Then the second kernel runs once more with one worker, inside the time
                # that is left, and that answer is kept. Anything else stays the decline it is.
                if label != 'judge' or count <= 1 or not worker_table_decline(w / label / 'k2.log'):
                    raise
                left = a.timeout - (time.monotonic() - a.started) if a.timeout else None
                if left is not None and left <= 0:
                    note(f'{label}/k2 declined for worker-table room: no time left for a 1-worker retry')
                    raise
                # The time that is left, rounded up: "at most 0 s" would not be true.
                note(f'{label}/k2 declined for worker-table room (first attempt above): again with 1 worker'
                     + (f' (at most {int(-(-left // 1))} s)' if left is not None else ''))
                try:
                    rc, log, _said = stage(label, 'k2', 'gruszka', [solution, 1], [solution], {}, 1, legs, '-retry')
                finally:
                    legs['k2']['retry'] = {'reason': K2_ROOM, 'first_rc': 2, 'workers': 1}
            code, legs['k2']['message'] = decide('k2', rc, log)
            return code, REJECT['k2']

        def judge(label, cfg, challenge, solution, count, legs):
            """The three legs in the order of the judge scripts; the first that does not accept ends the run."""
            for leg in (lambda: compare(label, cfg, challenge, solution, count, legs),
                        lambda: replay(label, solution, count, legs), lambda: second(label, solution, count, legs)):
                code, reason = leg()
                if code:
                    return code, reason
            return 0, ACCEPTED

        legs = None
        if gate is not None:
            # As on Linux, a rejection by the challenge's own release rule ends the run before any program
            # starts. The integrity checks below still apply to it.
            outcome = gate
        else:
            # Before any judgement, with the programs of this run and one worker: all three accept the known-good
            # export, the comparison by itself rejects the one with a custom axiom, and each kernel by itself
            # rejects the kernel-invalid one. The programs are compiled on the machine, so a run does not rest on
            # their digests alone: a rejection by each kernel is part of what must be seen. Any other end of a
            # control is no verdict.
            tests = result['selftests'] = {name: {'legs': {}} for name in ('good', 'bad', 'kbad')}
            try:
                code, reason = judge('selftest-good', pinned['selftest_comparator'], pinned['selftest_challenge'],
                                     pinned['selftest_good'], 1, tests['good']['legs'])
                if code != 0:
                    raise Declined(f'good: exit {code}, {reason}')
                code, reason = compare('selftest-bad', pinned['selftest_comparator'], pinned['selftest_challenge'],
                                       pinned['selftest_bad'], 1, tests['bad']['legs'])
                if code != 1:
                    raise Declined('bad: the comparison did not reject the export with a custom axiom')
                for name, kernel in (('lean', replay), ('k2', second)):
                    code, reason = kernel('selftest-kbad', pinned['selftest_kbad'], 1, tests['kbad']['legs'])
                    if code != 1:
                        raise Declined(f'kbad: the {name} leg did not reject the kernel-invalid export')
            except Declined as failed:
                # A limit of the run is not a program that fails: the caller's time limit, between two legs or
                # inside one, and the memory limit of a leg.
                if isinstance(failed, TimeLimit) or getattr(failed, 'report', {}).get('violation') in ('wall', 'mem'):
                    raise Declined(f'during the self-tests: {failed}') from None
                raise Declined(f'self-test failed ({failed}): the programs of this machine cannot judge') from None
            if a.preflight:
                outcome = 0, 'programs present, sha256 OK, self-test passed'
            else:
                legs = result['legs'] = {}
                outcome = judge('judge', private_config, challenge, solution, threads, legs)
        # The clones are compared once more with what they were when they were hashed, before a result exists.
        for name, copy in pinned.items():
            if sha(copy) != cloned[name]:
                raise Declined(f'pinned {name} changed during the run')
        if any((hashlib.sha256(script.read_bytes()).hexdigest() if p == script else sha(p))
               != result['wiring_sha256'][p.name] for p in wiring):
            raise Declined('judge wiring changed during run')
        verify_inputs()
        remaining()
        return outcome


class JudgeInterrupted(Exception):
    pass


def main(mode, words):
    """Judge and return what enter.py is given: the result, how the JSON destination fared against every file
    this run reads, and whether this driver wrote the caller's log."""
    os.umask(0o077)
    result = {'checker': MODES[mode]['checker'], 'wiring': 'macos-sequential'}
    a = new_arguments()
    a.json_checked, a.log_written = None, False
    a.started, a.launcher = time.monotonic(), os.getppid()
    # A signal that the caller ignores (nohup, a job in the background) stays ignored, by enter.py, by this driver
    # and by the programs it starts. enter.py passes on what it gets, so this driver handles what enter.py handles.
    signals = [sig for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP)
               if signal.getsignal(sig) != signal.SIG_IGN]

    def interrupted(signum, _frame):
        # The first signal ends the run: enter.py passes on what the driver may also get directly.
        for sig in signals:
            signal.signal(sig, signal.SIG_IGN)
        raise JudgeInterrupted('interrupted by signal %d' % signum)

    try:
        for sig in signals:
            signal.signal(sig, interrupted)
        # enter.py starts this driver with the three signals blocked, so that none is lost before this line.
        signal.pthread_sigmask(signal.SIG_UNBLOCK, signals)
        read_arguments(mode, words, a)
        code, reason = execute(mode, a, result)
        # From here the result is handed over whatever arrives.
        for sig in signals:
            signal.signal(sig, signal.SIG_IGN)
    except Exception as error:
        for sig in signals:
            signal.signal(sig, signal.SIG_IGN)
        code, reason = 2, str(error)
        if isinstance(error, Usage):
            print(error, file=sys.stderr)
            reason = 'usage'
    verdict = 'PREFLIGHT_OK' if a.preflight and code == 0 else ('ACCEPTED', 'REJECTED', 'DECLINED')[code]
    record = {'checker': result.pop('checker'), 'verdict': verdict, 'exit': code,
              'wall_s': round(time.monotonic() - a.started, 3), 'reason': reason, **result}
    return {'record': record, 'json_checked': a.json_checked, 'log_written': a.log_written}


if __name__ == '__main__':
    # enter.py gives the mode of the judge script in front of the caller's arguments and takes a verdict only from
    # the exit status together with the result on descriptor 3, which is written last.
    try:
        handed = main(sys.argv[1], sys.argv[2:])
        with os.fdopen(3, 'wb') as channel:
            channel.write(json.dumps(handed).encode())
        status = STATUS[handed['record']['verdict']]
    except BaseException:
        # An unknown mode, an interrupt outside a phase, a result that cannot be handed over: no verdict.
        status = 2
    sys.exit(status)
