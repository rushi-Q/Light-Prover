"""check/sound/macos/enter.py MODE [ARGUMENT...]: what the judge scripts check/lowmem/check-sound-lowmem.sh (MODE
lowmem) and check/lowmem/check-sound-ultralowmem.sh (MODE ultralowmem) become on macOS, right after their
clean-environment step.

This program starts the driver judge.py with the caller's arguments and is the only one that publishes a result.
The driver ends with a status of its own for each verdict and hands its whole result over on descriptor 3. That
result is published only when status and result agree with each other and with what was asked for (the judge of
MODE; a judgement or a preflight), and when a positive result holds what it claims: the three controls with their
outcomes and, for ACCEPTED, the three legs with exit status 0. Then: first the `--json` file, then the line on
stdout, then the exit status 0 (ACCEPTED, PREFLIGHT_OK), 1 (REJECTED) or 2 (DECLINED). For every other end of the
driver, and for its own failures, this program publishes a DECLINED of its own.

The `--json` destination. A result of an earlier run is taken away first, before anything is refused, from
every path that is the value of a --json on the command line: the file is removed, or the symbolic link that
leads to it, and a file that cannot be removed is emptied. Whether the destination may be written is then decided
once, from the command line: not when it is another word of the command line or the record of the programs,
existing or missing; then there is no run. The driver compares the destination with every file it reads; where
it refuses, nothing is written, and before it has compared, only a new file is created. So a path named as
--json does not go on holding a result that says more than this run did. A result here is what earlier_result
takes for one: what this judge writes. Each word has the role that the driver's reader gives it: an option word,
an input (the three inputs, and the values of --hints, --hide and --pins, the files the driver reads), the value
of another option, a value of --json or of --log. From a word it refuses on, and for every word when the driver
cannot be read, the words are read as they stand (reading): the word after a word --json is a value of --json, a
word --json is an option word only where an option name stands, and every other such word has an unknown role. A
path stays as it is if, and only if, another word whose role is an input or unknown names the same file: so an
input is never removed, `--json R R` (three inputs) keeps R, and after a refused argument a word of unknown role
that names the destination keeps it. Option words, the other values and a word that cannot be resolved or looked
up keep nothing. Outside the rule is also a result that can be neither removed nor emptied: in a folder that
cannot be written, one behind a symbolic link, one in a file that cannot be written either and one in a file that
has another name as well, which emptying would reach too; in any folder, one in a file that may not be changed at
all. It stays. At the destination the run is then DECLINED before it starts; at any other --json the run goes on
as it would without that word.

The exit status. The judge scripts hand over only to a file that is whole: they run it under another name first,
and the interpreter prints the word COMPLETE only when that run came back with COMPLETE set, which the last
statement does. Nothing else of this file prints when it runs so. The exit status is that of a verdict at one
place only, in the last block, where main has returned and stdout has taken the line of one result. Every other
end, once the end handler is registered with the signal mask before the definitions, has the status 2: the last
block starts from it, and the handler gives it to every end outside that block, after an exception, at an exit
and at the end of a file that is cut off below it. A signal that comes earlier, while the interpreter starts,
ends this program as it ends any, without a line (README).

Signals. TERM, INT and HUP are passed on to the driver as they come, and the run is DECLINED when one arrives
before the commit point: after the result of the driver was examined, immediately before the first write of a
result. From there the result stands. The three are blocked from the first statement until the handlers are set,
here and in the driver, so that none is lost; one that the caller ignores (nohup) stays ignored by both. A driver
that does not end within GRACE seconds, after a signal or after it handed over, is killed, which is DECLINED.
KILL of this program leaves no verdict: the guard ends the leg that runs, and the driver publishes nothing."""
import atexit
import json
import os
from pathlib import Path
import signal
import stat
import subprocess
import sys
import tempfile
import time

SIGNALS = (signal.SIGTERM, signal.SIGINT, signal.SIGHUP)
if __name__ == '__main__':
    signal.pthread_sigmask(signal.SIG_BLOCK, SIGNALS)
    # From here on an end of the interpreter has the exit status of no verdict, unless the last block ends it: after
    # an exception, at an exit, at the end of a file that is cut off below this line.
    atexit.register(os._exit, 2)
HERE = Path(__file__).resolve().parent
PUBLISHED = []                # the verdict that publish was given to print, once it was
DELIVERED = []                # the verdict whose line stdout has taken, once it has
CHECKERS = {'lowmem': 'checkSoundLowMem', 'ultralowmem': 'checkSoundUltraLowMem'}
# The driver's exit status for each verdict, and the exit status of the judge script for it.
STATUS = {40: ('ACCEPTED', 0), 41: ('REJECTED', 1), 42: ('DECLINED', 2), 43: ('PREFLIGHT_OK', 0)}
EXIT = dict(STATUS.values())      # the exit status of the judge script for each verdict
WIRING = 'macos-sequential'       # what every result of this judge has as `wiring`
LARGEST_RESULT = 1024 * 1024      # bytes: of a result that is handed over, and of an earlier one at the destination
GRACE = 60                        # seconds for the driver to end, after a signal and after it handed over


def earlier_result(path):
    """Whether the path holds a result that this judge published earlier: a small regular file, or a symbolic
    link that leads to one, with one JSON object that has what every result of this judge has. That is six
    fields: `checker`, one of the judge's two names; `verdict` and `exit`, a verdict with its exit status;
    `wall_s`, a number; `reason`, a text; and `wiring` with its one value. A file that has some of these keys,
    a comparator configuration with four of them, is no result. A caller who reads the path would read that
    result, whether the path is the file or a link to it."""
    try:
        before = path.stat()
        if not stat.S_ISREG(before.st_mode) or before.st_size > LARGEST_RESULT:
            return False
        fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK)
        with os.fdopen(fd, 'rb') as stream:
            if not os.path.samestat(before, os.fstat(fd)):
                return False
            data = json.loads(stream.read(LARGEST_RESULT + 1))
    except (OSError, ValueError, RecursionError):
        return False
    return (isinstance(data, dict) and data.get('checker') in CHECKERS.values() and data.get('wiring') == WIRING
            and isinstance(data.get('verdict'), str) and type(data.get('exit')) is int
            and EXIT.get(data['verdict']) == data['exit']
            and type(data.get('wall_s')) in (int, float) and isinstance(data.get('reason'), str))


def retract(path):
    """Take a result away from its path: remove the file, or the symbolic link that leads to it, never the file
    behind a link. Where the folder does not allow that, empty the file in place, which says nothing either; but
    not a file that has another name, a hard link, under which it would be emptied too. OSError for a result that
    can be neither removed nor emptied."""
    try:
        os.unlink(path)
    except OSError:
        fd = os.open(path, os.O_WRONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
        try:
            if os.fstat(fd).st_nlink > 1:
                raise OSError(f'an earlier result that cannot be removed has another name: {path}') from None
            os.ftruncate(fd, 0)
        finally:
            os.close(fd)


def same_path(one, other):
    """Whether two words name one path, existing or missing, or one file: by the paths as given, and by the paths
    with their symbolic links resolved, which also reach a file behind more links than the system follows in one
    look. A word that cannot be resolved raises OSError, RuntimeError or ValueError: about such a path there is
    no answer."""
    one, other = Path(one), Path(other)
    resolved = one.resolve(), other.resolve()
    return resolved[0] == resolved[1] or any(first.exists() and second.exists() and first.samefile(second)
                                             for first, second in ((one, other), resolved))


def reading(words, roles):
    """The role of each word: the driver's reading (its a.roles, then None, an unknown role, for each word from the
    one it refused on; all None when the driver cannot be read), and where it gave none, what the words as they
    stand allow, but never at the place of an input, the first three words of a run that judges, which keep the
    role they have. A word that follows a word --json is a value of --json ('json'): if that --json is the option,
    the word is its value, and if it is the value of the option before it, the word stands where an option name
    stands. A word --json is an option word ('option') only where it can be nothing else: the first word without a
    role stands where an option name stands, and from there each word --json is the option and the word after it
    its value, as long as the words at those places are --json. Every other word without a role stays unknown
    (None), also a --json, which may be the value of an option that takes a file."""
    first = 1 if words[:1] == ['--preflight'] else 3
    place = next((at for at in range(first, len(words)) if roles[at] is None), len(words))
    options = set()
    while place < len(words) and words[place] == '--json':
        options.add(place)
        place += 2
    return [('json' if words[at - 1] == '--json' else 'option' if at in options else None)
            if role is None and at >= first else role for at, role in enumerate(roles)]


def places(words, roles):
    """Which words are values of --json, by `reading`: their positions."""
    return [at for at, role in enumerate(reading(words, roles)) if role == 'json']


def take_away(words, roles):
    """Take a result of an earlier run away from the paths that are values of --json (places): the destination
    of this run, one that a later --json replaces, and one behind an argument that ends the reading. Only what
    earlier_result takes for a result is touched. A path stays as it is if, and only if, another word whose role
    (by `reading`) is an input or unknown names the same file (same_path), for it may be a file that the driver
    reads. Option words, the values of the other options, values of --json and of --log keep nothing, also where
    the role comes from the reading of the words as they stand, nor does a word that cannot be resolved or looked
    up: it names no file. What cannot be taken away stays for the caller of this function to find. The path of a
    word is what pathlib makes of it, here as wherever the destination is written: a slash at its end does not
    count."""
    def names(path, word):
        try:
            return same_path(path, word)
        except (OSError, RuntimeError, ValueError):
            return False

    read = reading(words, roles)
    for at in [at for at, role in enumerate(read) if role == 'json']:
        path = Path(words[at])
        keepers = [word for other, word in enumerate(words) if word and read[other] in ('input', None)]
        try:
            if not any(names(path, word) for word in keepers) and earlier_result(path):
                retract(path)
        except (OSError, RuntimeError, ValueError):
            pass


def shows(result, verdict):
    """Whether a positive result holds what it claims: the three controls with the outcomes the judge requires
    (all three programs accept the known-good export, the comparison rejects the one with a custom axiom, each
    kernel rejects the kernel-invalid one) and, for ACCEPTED, the three legs with exit status 0. The driver
    decides; this is a second look at what it hands over, nothing more."""
    def ends(legs):
        return {name: leg['rc'] if type(leg['rc']) is int else None for name, leg in legs.items()}
    accepted = {'compare': 0, 'lean': 0, 'k2': 0}
    try:
        tests = result['selftests']
        return (ends(tests['good']['legs']) == accepted and ends(tests['bad']['legs']) == {'compare': 1}
                and ends(tests['kbad']['legs']) == {'lean': 1, 'k2': 1}
                and (verdict != 'ACCEPTED' or ends(result['legs']) == accepted))
    except (KeyError, TypeError, AttributeError):
        return False


def write_json(path, line, replace):
    """Write the result as a new file and put it at `path` in one step. Without `replace` a file that is there
    stays: the driver has not compared this destination with the files it reads. Returns a descriptor of the new
    file, through which it can still be emptied when its folder and its mode no longer allow a change; a failure
    after the file is in place empties it so before the failure is reported. The new file is made in the folder of
    `path` after resolving, so that the name tempfile keeps for it is the file it made."""
    path, new, held, placed = Path(path), None, None, False
    try:
        with tempfile.NamedTemporaryFile(dir=os.path.realpath(path.parent), mode='w', encoding='utf-8',
                                         delete=False) as out:
            new = Path(out.name)
            out.write(line + '\n')
            held = os.dup(out.fileno())
        if replace:
            os.replace(new, path)
            new, placed = None, True
        else:
            try:
                os.link(new, path)
            except FileExistsError:
                raise ValueError('the JSON destination holds a file that is not an earlier result') from None
            placed = True
            new.unlink()
            new = None
        return held
    except BaseException:
        if held is not None:
            if placed:
                try:
                    os.ftruncate(held, 0)
                except OSError:
                    pass
            os.close(held)
        if new is not None:
            try:
                new.unlink(missing_ok=True)
            except OSError:
                pass
        raise


def main(mode, words):
    started = time.monotonic()
    checker = CHECKERS.get(mode)

    def declined(reason):
        return {'checker': checker or 'enter.py', 'verdict': 'DECLINED', 'exit': 2,
                'wall_s': round(time.monotonic() - started, 3), 'reason': reason, 'wiring': WIRING}

    def publish(record, json_to=None, replace=False, log=None):
        """The one place a result leaves the judge: to the file, then to stdout, then to the log. What stdout
        has taken is noted in DELIVERED, for the exit status."""
        held = None
        if json_to:
            try:
                held = write_json(json_to, json.dumps(record), replace)
            except (OSError, ValueError) as error:
                if record['verdict'] == 'DECLINED':
                    record = dict(record, json_error=str(error))
                else:
                    record = dict(record, verdict='DECLINED', exit=2, reason='cannot write JSON: ' + str(error))
        PUBLISHED.append(record['verdict'])
        try:
            sys.stdout.write(json.dumps(record) + '\n')
            sys.stdout.flush()
            DELIVERED.append(record['verdict'])
        except (OSError, ValueError, AttributeError):
            # Nobody reads stdout: the verdict was not delivered. The exit status says so, and so does the file:
            # it is written again or, where it cannot be, emptied through the descriptor it was written with,
            # whatever its folder and its mode allow by now. It never says more than the run did.
            if record['verdict'] != 'DECLINED':
                record = dict(record, verdict='DECLINED', exit=2, reason='cannot write the result to stdout')
                if held is not None:
                    try:
                        os.close(write_json(json_to, json.dumps(record), replace=True))
                    except (OSError, ValueError):
                        try:
                            os.ftruncate(held, 0)
                        except OSError:
                            pass
            try:
                os.dup2(os.open(os.devnull, os.O_WRONLY), 1)
            except OSError:
                pass
        line = f"[{record['checker']}] verdict {record['verdict']} (exit {record['exit']}): {record['reason']}\n"
        try:
            # As the judge scripts: the verdict is the last line of the log, or of stderr without --log.
            out = os.open(log, os.O_WRONLY | os.O_APPEND | os.O_NOFOLLOW) if log else 2
            os.write(out, line.encode('utf-8', errors='replace'))
        except (OSError, ValueError):
            pass

    if checker is None:
        return publish(declined('enter.py needs the mode lowmem or ultralowmem'))
    # The arguments are read here only for the two paths this program writes and for what was asked; the reader
    # is the driver's, and what it refuses the driver says.
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(HERE))
    try:
        import judge
        a = judge.new_arguments()
        try:
            judge.read_arguments(mode, words, a)
        except judge.Declined:
            pass
        roles = a.roles + [None] * (len(words) - len(a.roles))
        record = judge.PINS_DIR / 'pins-macos.env'
    except BaseException as error:
        # Without the driver the arguments cannot be read, and nothing is written; no role is known.
        take_away(words, [None] * len(words))
        return publish(declined(f'the macOS driver cannot be read ({type(error).__name__}: {error})'))
    # A result of an earlier run does not outlive this run, whatever becomes of it and wherever the reading of the
    # arguments ended: it is taken away before anything below is refused. A file that the command line also names
    # as an input is not touched.
    take_away(words, roles)
    if a.json:
        # Decided once, for every way a result can leave this run: the destination is not written when it is
        # another word of the command line (an input, the log, a record) or the record of the programs.
        jsons = places(words, roles)
        others = [word for at, word in enumerate(words) if word and at not in jsons]
        try:
            same = any(same_path(a.json, word) for word in (*others, record))
            both = bool(a.log) and same_path(a.json, a.log)
        except (OSError, RuntimeError, ValueError) as error:
            return publish(declined(f'cannot resolve a path of the command line ({error})'))
        if same:
            return publish(declined('log and JSON must be distinct paths' if both
                                    else 'output aliases a protected input: ' + a.json))
        # No other word names the destination. A result of an earlier run that is still there cannot be taken
        # away: no run. And none for a result that could not be written at its end.
        try:
            if earlier_result(Path(a.json)):
                retract(Path(a.json))
            with tempfile.NamedTemporaryFile(dir=os.path.realpath(Path(a.json).parent)):
                pass
        except (OSError, ValueError) as error:
            return publish(declined(f'cannot write JSON: {error}'))

    # The driver: a child with the caller's stdin, whose stdout is stderr, and whose descriptor 3 is a pipe to here.
    reader, writer = os.pipe()
    if writer != 3:
        if reader == 3:
            reader = os.dup(reader)
        os.dup2(writer, 3)
        os.close(writer)
    seen = []
    driver = subprocess.Popen(['/usr/bin/python3', '-I', str(HERE / 'judge.py'), mode, *words], stdout=2,
                              pass_fds=(3,))
    os.close(3)

    def stop(signum, _frame):
        # Passed on as it came: the driver handles what this program handles. A driver that does not end is killed,
        # GRACE seconds after the first signal: later ones do not put that off.
        if not seen:
            signal.alarm(GRACE)
        seen.append(signum)
        driver.send_signal(signum)

    signal.signal(signal.SIGALRM, lambda _signum, _frame: driver.kill())
    for sig in SIGNALS:
        if signal.getsignal(sig) != signal.SIG_IGN:
            signal.signal(sig, stop)
    signal.pthread_sigmask(signal.SIG_UNBLOCK, (*SIGNALS, signal.SIGALRM))
    handed = bytearray()
    with os.fdopen(reader, 'rb') as channel:
        # Read to the end, so that the driver ends by itself; keep no more than a result can be.
        for block in iter(lambda: channel.read(1 << 16), b''):
            if len(handed) <= LARGEST_RESULT:
                handed += block
    try:
        status = driver.wait(GRACE)
    except subprocess.TimeoutExpired:
        # The driver has closed the pipe and does not end: its status will not be that of a verdict.
        driver.kill()
        status = driver.wait()

    # What the driver handed over is examined while a signal still counts.
    said = checked = logged = None
    try:
        envelope = json.loads(bytes(handed).decode('utf-8'))
        verdict, code = STATUS[status]
        result = envelope['record']
        asked = ('PREFLIGHT_OK',) if a.preflight else ('ACCEPTED', 'REJECTED')
        if (type(result) is dict and result.get('checker') == checker and result.get('verdict') == verdict
                and type(result.get('exit')) is int and result['exit'] == code
                and isinstance(result.get('reason'), str) and verdict in (*asked, 'DECLINED')
                and (verdict not in ('ACCEPTED', 'PREFLIGHT_OK') or shows(result, verdict))
                and len(handed) <= LARGEST_RESULT):
            said, checked, logged = result, envelope.get('json_checked'), envelope.get('log_written')
    except (ValueError, KeyError, TypeError, RecursionError):
        pass
    # The commit point: a signal that was seen up to here is DECLINED, one that comes later changes nothing.
    signal.pthread_sigmask(signal.SIG_BLOCK, SIGNALS)
    signal.alarm(0)
    if seen and (said is None or said['verdict'] != 'DECLINED'):
        said = declined(f'interrupted by signal {seen[0]}')
    elif said is None:
        ended = f'signal {-status}' if status < 0 else f'status {status}'
        said = declined(f'the macOS driver ended without a result ({ended})')
    # Where the driver refused the destination, nothing is written; where it has not compared it, only a new file.
    return publish(said, None if checked is False else a.json, replace=checked is True,
                   log=a.log if logged is True else None)


if __name__ == '__main__':
    status = 2
    try:
        main(sys.argv[1] if sys.argv[1:] else '', sys.argv[2:])
        # The one place where the exit status becomes that of a verdict: main has returned, and stdout has taken the
        # line of one result. Its verdict gives the status, 0 for ACCEPTED and PREFLIGHT_OK and for nothing else.
        if len(DELIVERED) == 1:
            status = EXIT[DELIVERED[0]]
    except BaseException as error:
        # A failure of this program is never a verdict, and never the exit status of one.
        try:
            if not PUBLISHED:
                print(json.dumps({'checker': CHECKERS.get(''.join(sys.argv[1:2]), 'enter.py'), 'verdict': 'DECLINED',
                                  'exit': 2, 'reason': f'enter.py failed ({type(error).__name__}: {error})',
                                  'wiring': WIRING}), flush=True)
        except BaseException:
            pass
    finally:
        os._exit(status)
# The last statement of this file. The judge scripts look for it before they hand over: a file that ends anywhere
# before this line does not set it.
COMPLETE = True
