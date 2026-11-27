#!/usr/bin/python3 -I
"""sandbox-run.py [--read PATH]... [--write PATH]... [--setenv NAME VALUE]... [--stderr-to-stdout] -- COMMAND [ARGS...]

The macOS build, export and judge sandbox denies by default. Read and execute grants cover /bin, /usr/bin, /usr/lib,
/System/Library/Frameworks, /System/Volumes/Preboot/Cryptexes/OS/System/Library/dyld (if present), and existing
--read paths. The root directory itself and /dev/{null,random,urandom} are readable. Writes are allowed to /dev/null
and existing --write paths. A directory covers its subtree, a file only itself. Writable grants permit mode and flag
changes for metadata-preserving copies because the stage can clear flags and restore access on its private scratch files.
Metadata may be requested for any path (also the text of a symbolic link). A path with a control character is not
granted. Sysctls are readable except kern.proc* and net.*. Denied: the network, the host's sockets and services, the
host's connections, the list of processes, other processes' arguments and environment. Processes can fork, inspect
themselves and signal others in the same sandbox. Not denied, because the profile language has no rule for it:
creating a System V IPC object (shmget, semget, msgget; attaching to one and removing one are refused, so an object
that a command creates stays until ipcrm or a restart), and asking for the process group, session or priority of any
process id (getpgid, getsid, getpriority). The command inherits the standard streams.
--stderr-to-stdout joins its stderr to its stdout. Its environment contains only the supplied --setenv entries
(the last value of a name wins).
Launcher errors print a sandbox-run diagnostic and return 126 (127 for a command not found on PATH). These are
no-verdict failures. A started command retains its own exit status, including 2, 126 and 127, or 128+signal.
"""
import os
import sys


DYLD_CACHE = '/System/Volumes/Preboot/Cryptexes/OS/System/Library/dyld'
O_EVTONLY = 0x8000  # Darwin fcntl.h; system Python 3.9 omits this os constant


def grant(operation, path):
    import fcntl
    import json
    import stat

    # Darwin O_EVTONLY opens without requiring read access to the file's contents. Use one fd for name and type.
    fd = os.open(path, O_EVTONLY)
    try:
        raw = fcntl.fcntl(fd, fcntl.F_GETPATH, bytes(1024))  # Darwin MAXPATHLEN
        name = os.fsdecode(raw.split(b'\0', 1)[0])
        if not os.path.isabs(name):
            raise ValueError(f'no absolute kernel path for {path!r}')
        # json.dumps writes a control character as \b, \f, \n or \u00XX, which the profile language reads as the
        # letters after the backslash: the grant would be for another path
        if any(ord(char) < 0x20 or ord(char) == 0x7f for char in name):
            raise ValueError(f'control character in the granted path {path!r}')
        kind = 'subpath' if stat.S_ISDIR(os.fstat(fd).st_mode) else 'literal'
        return f'(allow {operation} ({kind} {json.dumps(name, ensure_ascii=False)}))'
    finally:
        os.close(fd)


def profile(reads, writes):
    # process-info and the process/connection sysctls need explicit denies even with deny-default.
    lines = ['(version 1)', '(deny default)', '(allow process-fork)', '(deny process-info*)',
             '(allow process-info* (target self))', '(allow signal (target same-sandbox))',
             '(allow sysctl-read)', '(deny sysctl-read (sysctl-name-prefix "kern.proc") (sysctl-name-prefix "net."))',
             '(allow file-read-metadata)', '(allow file-read-data (literal "/"))',
             '(allow file-write* (literal "/dev/null"))']
    runtime = ['/bin', '/usr/bin', '/usr/lib', '/System/Library/Frameworks']
    if os.path.isdir(DYLD_CACHE):
        runtime.append(DYLD_CACHE)
    lines.extend(grant('file-read* process-exec*', path) for path in runtime + reads)
    lines.extend(grant('file-read*', path) for path in ['/dev/null', '/dev/random', '/dev/urandom'])
    lines.extend(grant('file-write*', path) for path in writes)
    return '\n'.join(lines) + '\n'


def main(args):
    import ctypes
    import errno
    import signal
    import subprocess

    if sys.platform != 'darwin':
        raise ValueError('requires macOS')
    grants = {'--read': [], '--write': []}
    env = {}
    merge_stderr = False
    while args and args[0] != '--':
        if args[0] in grants and len(args) >= 2:
            grants[args[0]].append(args[1])
            args = args[2:]
        elif args[0] == '--setenv' and len(args) >= 3:
            name, value = args[1:3]
            if not name or '=' in name:
                raise ValueError('invalid --setenv name')
            env[name] = value
            args = args[3:]
        elif args[0] == '--stderr-to-stdout':
            merge_stderr = True
            args = args[1:]
        else:
            raise ValueError(__doc__.splitlines()[0])
    if len(args) < 2:
        raise ValueError(__doc__.splitlines()[0])
    command = args[1:]
    policy = profile(grants['--read'], grants['--write']).encode('utf-8')
    # Load the Seatbelt entry point before forking. The child installs the inline profile (flags 0) immediately
    # before Popen's direct exec. Popen's startup pipe distinguishes a failed profile/exec from a command exit.
    init = ctypes.CDLL('/usr/lib/libsandbox.1.dylib').sandbox_init
    init.argtypes = [ctypes.c_char_p, ctypes.c_uint64, ctypes.POINTER(ctypes.c_char_p)]
    init.restype = ctypes.c_int

    def apply_profile():
        if init(policy, 0, None) != 0:
            raise RuntimeError('cannot apply sandbox profile')
        if merge_stderr:
            os.dup2(1, 2)

    # Close inherited descriptors before the child loses access to /dev/fd, including descriptors above 255.
    for entry in os.listdir('/dev/fd'):
        fd = int(entry)
        if fd >= 3:
            try:
                os.close(fd)
            except OSError as exc:
                if exc.errno != errno.EBADF:  # listdir already closed its directory descriptor
                    raise
    child = None
    pending = None

    def forward(signum, _frame):
        nonlocal pending
        if child is None:
            pending = signum
        else:
            child.send_signal(signum)

    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        if signal.getsignal(sig) != signal.SIG_IGN:
            signal.signal(sig, forward)
    try:
        # Inherited fds were closed above. Repeating the close sweep after applying the profile denies /dev/fd
        # enumeration and makes system Python scan the numeric descriptor limit, which can be unlimited.
        child = subprocess.Popen(command, env=env, preexec_fn=apply_profile, close_fds=False)
    except OSError as exc:
        print(f'sandbox-run: could not start command: {exc}', file=sys.stderr, flush=True)
        return 127 if '/' not in command[0] and exc.errno in (errno.ENOENT, errno.ENOTDIR) else 126
    with child:
        if pending is not None:
            child.send_signal(pending)
        status = child.wait()
        return status if status >= 0 else 128 - status


if __name__ == '__main__':
    try:
        status = main(sys.argv[1:])
    except BaseException as exc:  # only a started command may supply a verdict status
        try:
            print(f'sandbox-run: {type(exc).__name__}: {exc}', file=sys.stderr, flush=True)
        except BaseException:
            os.write(2, b'sandbox-run: launcher failed\n')
        finally:
            os._exit(126)
    sys.exit(status)
