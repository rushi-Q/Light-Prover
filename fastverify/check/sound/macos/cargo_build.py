"""The build of the second kernel for the macOS judge: the crates of Cargo.lock, checked and unpacked, and cargo
in an environment that this file writes, with the C compiler and the linker of the Lean toolchain. Used by
build-judge-macos.sh; nothing here needs macOS but the compilers."""
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import shlex
import shutil
import subprocess
import tarfile
import zlib

from support import SHA256, Declined

CRATES_IO = 'registry+https://github.com/rust-lang/crates.io-index'
# What tools/reproduce/portable-gruszka.sh sets, the commit time of gruszka 4ad120b: the C code of libmimalloc-sys
# prints __DATE__ and __TIME__, which the compiler takes from here.
SOURCE_DATE_EPOCH = '1795242059'
# Passed to every rustc. No flag names a folder: cargo forms the names of its outputs from these flags, and the
# name under which the program is linked is part of its code signature. (The linker is named with a folder, so
# rustc gets it from its wrapper, like the path map.)
#   -Csplit-debuginfo, -S    the profile of gruszka asks for line tables (debug = 1). On macOS they stay in the
#                            object files, and the linker would write the paths and the times of those files into
#                            the program; -S leaves that list out. The code is compiled as the profile says.
#   -dead_strip_dylibs       a library that the program names and does not use is not written into it: libiconv,
#                            which the libc crate names for every program on macOS.
RUSTFLAGS = ('-Csplit-debuginfo=unpacked', '-Clink-arg=-Wl,-S', '-Clink-arg=-Wl,-dead_strip_dylibs')
# The Lean toolchain has a stub of the system library and none of libiconv, which the link must find to drop it.
ICONV_STUB = ("--- !tapi-tbd\ntbd-version: 4\ntargets: [ arm64-macos ]\ninstall-name: '/usr/lib/libiconv.2.dylib'\n"
              "current-version: 7\ncompatibility-version: 7\nexports:\n  - targets: [ arm64-macos ]\n"
              "    symbols: [ _iconv, _iconv_close, _iconv_open ]\n...\n")
# A build folder is written into compiler flags that are split at spaces.
PLAIN = re.compile('/[A-Za-z0-9._+@/-]+')


def locked_crates(lock):
    """{'NAME-VERSION': SHA-256 of NAME-VERSION.crate} for every package of Cargo.lock (`lock` is its text) that
    comes from crates.io. A package without a source is a member of the workspace. Any other source, and a
    package of crates.io without a checksum, is refused."""
    crates = {}
    for block in re.split(r'^\[\[package\]\]$', lock, flags=re.M)[1:]:
        found = re.findall(r'^(name|version|source|checksum) = "([^"\\\n]*)"$', re.split(r'^\[', block, flags=re.M)[0],
                           flags=re.M)
        fields = dict(found)
        crate = '{name}-{version}'.format(name=fields.get('name', ''), version=fields.get('version', ''))
        if len(fields) != len(found) or not re.fullmatch(r'[A-Za-z0-9_-]+-[0-9][A-Za-z0-9.+-]*', crate):
            raise Declined('Cargo.lock: a package that is not understood: ' + crate)
        if 'source' not in fields and 'checksum' not in fields:
            continue
        if fields.get('source') != CRATES_IO or not SHA256.fullmatch(fields.get('checksum', '')) or crate in crates:
            raise Declined(f'Cargo.lock: {crate} is not one package of crates.io with its checksum')
        crates[crate] = fields['checksum']
    return crates


def unpack_crates(lock, folders, dest):
    """Unpack NAME-VERSION.crate of every crate of Cargo.lock into dest/NAME-VERSION, as a directory source of
    cargo. An archive is looked for in `folders`, in their order. Only its checksum is trusted: every archive
    must have the SHA-256 that Cargo.lock names before one is unpacked, and Cargo.lock is one of the fingerprinted
    sources. An archive holds regular files and directories inside NAME-VERSION/ and nothing else. Returns the
    names of the crates."""
    crates = locked_crates(lock)
    archives = {crate: next((folder / (crate + '.crate') for folder in folders
                             if (folder / (crate + '.crate')).is_file()), None) for crate in sorted(crates)}
    missing = [crate + '.crate' for crate, archive in archives.items() if archive is None]
    if missing:
        raise Declined(f'{len(missing)} of the {len(crates)} crate archives of Cargo.lock are not in '
                       + (', '.join(map(str, folders)) or 'any folder') + ': ' + ' '.join(missing)
                       + ' (`cargo fetch --locked` in sources/gruszka, with network, downloads all of them)')
    data = {crate: archive.read_bytes() for crate, archive in archives.items()}
    for crate in data:
        found = hashlib.sha256(data[crate]).hexdigest()
        if found != crates[crate]:
            raise Declined(f'{archives[crate]}: SHA-256 {found}, Cargo.lock has {crates[crate]}')
    dest.mkdir()
    for crate in data:
        files = {}
        try:
            with tarfile.open(fileobj=io.BytesIO(data[crate]), mode='r:gz') as archive:
                for member in archive:
                    parts = PurePosixPath(member.name).parts
                    if (not (member.isreg() or member.isdir()) or parts[:1] != (crate,) or '..' in parts
                            or member.isreg() and len(parts) < 2):
                        raise Declined(f'{crate}.crate: {member.name!r} is not a regular file or a directory inside '
                                       f'{crate}/')
                    if member.isdir():
                        dest.joinpath(*parts).mkdir(parents=True, exist_ok=True)
                        continue
                    body = archive.extractfile(member).read()
                    dest.joinpath(*parts).parent.mkdir(parents=True, exist_ok=True)
                    with dest.joinpath(*parts).open('xb') as out:
                        out.write(body)
                    files['/'.join(parts[1:])] = hashlib.sha256(body).hexdigest()
        except (tarfile.TarError, zlib.error, EOFError, OSError) as error:
            raise Declined(f'{crate}.crate cannot be unpacked: {error}') from None
        # What `cargo vendor` writes: cargo compares the files it compiles with this list, and the package with
        # Cargo.lock.
        (dest / crate / '.cargo-checksum.json').write_text(json.dumps({'files': files, 'package': crates[crate]}))
    return sorted(data)


def configs_above(folder):
    """The configuration files that cargo reads for a build in `folder` besides the one of its home:
    .cargo/config.toml and .cargo/config in the folder and in every folder above it."""
    return [str(above / name) for above in (folder, *folder.parents) for name in ('.cargo/config.toml', '.cargo/config')
            if (above / name).exists() or (above / name).is_symlink()]


def build(run, rustbin, folders, jobs, sdk, tc):
    """Build gruszka from the staged sources run/src/gruszka with `rustbin`/cargo and return the program.

    Everything cargo reads is in `run`: the crates (unpack_crates), a new home whose configuration replaces
    crates.io by them, a new target folder. cargo gets no variable of the caller.

    The program must not depend on the machine. Every path under `run` reaches the compilers as /build (rustc
    through a wrapper, so that cargo does not see the folder in its flags), and a program that still names the
    folder is refused. The C code of the allocator is compiled, and the program is linked, by the clang and the
    lld of the Lean toolchain `tc`, as the three Lean programs are: the compiler and the linker of the machine
    would write their own versions and the version of the SDK into the file. Both run without SDKROOT, from
    which clang takes that version. Of the SDK `sdk` only the C headers are used; the link gets the stub of the
    system library that the toolchain carries, under the three names rustc asks for, and ICONV_STUB."""
    source = run / 'src/gruszka'
    if not PLAIN.fullmatch(str(run)):
        raise Declined(f'the build folder {run} must be a path of letters, digits and . _ + @ -: it is written into '
                       'compiler flags')
    above = configs_above(source)
    if above:
        raise Declined('cargo would read ' + ', '.join(above) + ': choose a build folder that is not below it')
    crates = unpack_crates((source / 'Cargo.lock').read_text(encoding='utf-8'), folders, run / 'crates')
    home, wrapper, lib = run / 'cargo', run / 'rustc-in-build', run / 'syslib'
    home.mkdir()
    (home / 'config.toml').write_text(
        "[source.crates-io]\nreplace-with = 'verified'\n\n"
        f"[source.verified]\ndirectory = '{run}/crates'\n\n[net]\noffline = true\n")
    lib.mkdir()
    for name in ('libSystem.tbd', 'libc.tbd', 'libm.tbd'):
        shutil.copyfile(Path(tc) / 'lib/libc/libSystem.tbd', lib / name)
    (lib / 'libiconv.tbd').write_text(ICONV_STUB)
    clang = 'exec /usr/bin/env -u SDKROOT ' + shlex.join([f'{tc}/bin/clang', '--sysroot', str(tc)])
    tools = {
        'cc-of-the-toolchain': clang + ' ' + shlex.join([
            '-nostdinc', '-isystem', f'{tc}/include/clang', '-isystem', f'{sdk}/usr/include',
            f'-ffile-prefix-map={run}=/build', f'-ffile-prefix-map={tc}=/lean-tc', f'-ffile-prefix-map={sdk}=/sdk']),
        'link-of-the-toolchain': clang + ' ' + shlex.join(['-fuse-ld=lld', '-L', str(lib)])}
    for name, command in tools.items():
        (run / name).write_text(f'#!/bin/sh\n{command} "$@"\n')
        (run / name).chmod(0o755)
    wrapper.write_text(f'#!/bin/sh\n# cargo starts every rustc through this file.\n'
                       f'exec "$@" --remap-path-prefix={run}=/build -Clinker={run}/link-of-the-toolchain\n')
    wrapper.chmod(0o755)
    env = {'PATH': f'{rustbin}:/usr/bin:/bin', 'HOME': str(run / 'home'), 'TMPDIR': str(run / 'tmp'), 'LC_ALL': 'C',
           'TZ': 'UTC', 'CARGO_HOME': str(home), 'CARGO_TARGET_DIR': str(run / 'target'),
           'RUSTC': str(rustbin / 'rustc'), 'RUSTC_WRAPPER': str(wrapper), 'RUSTFLAGS': ' '.join(RUSTFLAGS),
           'CC': str(run / 'cc-of-the-toolchain'), 'AR': f'{tc}/bin/llvm-ar', 'SDKROOT': str(sdk),
           'MACOSX_DEPLOYMENT_TARGET': '11.0', 'SOURCE_DATE_EPOCH': SOURCE_DATE_EPOCH, 'ZERO_AR_DATE': '1'}
    # As tools/reproduce/portable-gruszka.sh: both packages of the workspace, so that the features of the crates
    # they share are the ones of the Linux build.
    command = [str(rustbin / 'cargo'), 'build', '--release', '--locked', '--offline', '-j', str(jobs),
               '-p', 'gruszka', '-p', 'susz']
    log = run / 'logs/gruszka.build'
    with log.open('wb') as output:
        output.write(f'{len(crates)} crates of Cargo.lock unpacked; {" ".join(command)}\n'.encode())
        output.flush()
        done = subprocess.run(command, cwd=source, env=env, stdin=subprocess.DEVNULL, stdout=output,
                              stderr=subprocess.STDOUT)
    program = run / 'target/release/gruszka'
    if done.returncode != 0 or not program.is_file():
        raise Declined(f'cargo build failed (exit status {done.returncode}): {log}')
    if str(run).encode() in program.read_bytes():
        raise Declined(f'{program} names its build folder: another build would give other bytes')
    return program
