#!/usr/bin/python3 -I
"""tests/macos-judge/programs.py: the programs of the macOS judge on the repository's attack exports. Kernels run.

Needs the programs that check/sound/macos/build-judge-macos.sh built on this Mac (the record
config/pins-macos.env); without them, or on another system, it prints SKIP. run.py in this directory covers the
driver with stand-in programs; this file covers what only the real programs can show. Every input is a fixture
of this tree or is made here from the judges' self-test by a generator of this tree. The kind of every case
(attack or control) is the one the repository's own tests state; where they state no outcome, the row is INFO
and says so. Where they ask only that an attack is not accepted, a row here asks for the class: a rejection by
the program, or the one other end that is named below for that input.

  programs   Each program alone.
    Inputs in the tree:
      forged-records  tests/forged-inductive-records: inductive records that differ from the kernel's. Two of
                      them (T-isrec-forged, T-numidx-forged) pass the official replay and are rejected only by
                      the export-record check, so they show that the check is compiled into the program.
      kernel-issues   loose bound variables and forged constructor and quotient records
                      (tests/lean-leg-record-checks/corpora/kernel-crafted.tar.xz), two controls.
      forged-ctor     forged constructor, inductive and recursor records (corpora/forged-ctor.tar.xz), one control.
    Inputs made here from check/sound/selftest, by the generators that tests/lean-leg-record-checks/crafted_all.sh,
    leanleg.sh and test_targeted_forged.sh run:
      cves            tests/kernel-cves/craft_cves.py
      issue-analogues, c2s, c1only, implicit
                      mk_kernel_issue_exports.py, mk_c2_stream.py, mk_c1only.py, mk_implicit_closure.py
      recursor-name   recursor_name/craft_g1.py and craft_g1dup.py
      c1c2-edge       build_cases() of test_c1c2_edge_cases.py, with its labels
    Rows:
      generator            A generator that fails, or writes another number of exports than its code does, is a
                           FAIL: its cases would be missing without notice.
      pleanchecker         The replay of mode `lowmem`, parallel and --seq, as leanleg.sh and
                           tests/forged-inductive-records/run.sh run it. Control: accepted. Attack: rejected,
                           exit status 1. Two attacks (PANICS) make the kernel panic, and the program aborts as
                           the judge sets it up (LEAN_ABORT_ON_PANIC=1): for them the abort is required, which
                           under the judge is no verdict of that leg. forged-records: the exit status of its
                           README.
      pleanchecker_lowmem  The streaming replay of mode `ultralowmem`, `--low-mem --evict=smart`. The criteria for that
                           leg (crafted_all.sh, kind lowmem, and test_c1c2_edge_cases.py --modes lowmem;
                           plain_variants.sh): cves, kernel-issues, issue-analogues, c2s, implicit, c1c2-edge and
                           forged-ctor: attack not accepted, control accepted. c1only: accepted, the two attacks
                           included; that leg checks loose bound variables on the blocks it hands to the kernel,
                           and an unsafe block is skipped, as by the official replay (crafted_all.sh leaves these
                           files out for this leg "by design"). forged-records and recursor-name are INFO rows:
                           no test of the repository states an outcome for this leg on them.
      second-kernel        `gruszka EXPORT WORKERS`, the command of the judge's k2 leg. An attack must be
                           rejected (exit 1 and a `rejected: ` line). Ten attacks (SECOND_DECLINES) it does not
                           judge and must decline (exit 2 and a `declined: ` line): a field of a record that
                           Lean 4.36 does not compare, a name of the quotient package declared as something
                           else, an export that its packer finds invalid, a term with too many loose bound
                           variables. The `gruszka` column of the forged-records README is required as it is.
                           A control must be accepted. The controls of c1only, c2s and c1c2-edge are INFO rows:
                           their outcome is stated only for the Lean-leg programs alone, and they are not shaped
                           like genuine exports (an unsafe block, no recursor records, a block before the
                           definition it uses).
      second-kernel stops what the streaming replay accepts
                           No attack input is accepted by both the streaming replay and the second kernel. FAIL
                           names such an input. The inputs in question are the two c1only attacks.
      attack totals        INFO: the counts over all attack inputs.
  judge      The whole judge through its entry scripts, both modes. Every run must print one line, the JSON
             file must hold that line, and every row names what decided: the arguments, the gate, the
             self-tests, the leg that rejected, or all three legs.
      preflight       the self-tests.
      definition-hole tests/definition-hole: the sorried hole is REJECTED, the honest solution is ACCEPTED.
      anonymous-axiom an illegal axiom whose name has index 0, used by the target's proof, made here from the
                      honest solution the way tests/anonymous-axiom makes it: REJECTED.
      gate            rows of tests/cross-version-regress that the cross-version gate decides, with its
                      duplicate-meta rows (a meta line with "lean" twice) in both modes, and a challenge with such
                      a line under a config without definition holes: the gate must not depend on holes.
      caller-pins     --challenge-sha256 / --comparator-sha256, right and wrong.
      extra-kernel    --kernel nanoda is no verdict.
      leg             `binaries_sha256` of an ACCEPTED result names the official-kernel program that ran.
      crafted         Crafted exports through the whole judge, each row with the leg that must end the run (the
                      legs run in the order compare, lean, k2). The honest controls, judging inputs that must be
                      ACCEPTED by all three legs: cves/16489_control_valid and cves/15101_baseline_noquot,
                      kernel-issues/base and kernel-issues/C0-control-unused. Only exports that can stand beside
                      a challenge: the
                      official comparison requires 28 built-in constants and every permitted axiom in a challenge
                      (check/sound/src/CCmp.lean, primitiveTargets), so the small environments of forged-records and
                      forged-ctor, which the release's tests give to a kernel alone, are not judged whole.
                        cves           with the challenge and config of the self-test, as tests/kernel-cves/run.sh
                                       pairs them, and its exit statuses: controls ACCEPTED, attacks REJECTED,
                                       here by the official-kernel leg.
                        kernel-issues  as tests/kernel-issues/test.py judges it: its config, base and C0
                                       ACCEPTED. test.py passes every other export on any verdict but ACCEPTED;
                                       here each must be REJECTED, by the comparison where the export lacks a
                                       constant of the challenge or adds an axiom (COMPARISON_REJECTS), by the
                                       official-kernel leg otherwise. The corpus holds no challenge
                                       export (test.py builds one with the official toolchain), so its honest
                                       so/Solution.export stands in: `main_thm` has the same statement there.
                      `lean leg as the program alone`: the Lean leg of every crafted run decides as the same
                      program did alone in section `programs`. With it the rows show which leg stops what.
                        synthetic controls  The six controls of c1only, c2s and c1c2-edge, with the challenge and
                                       config of the self-test, end to end. INFO rows with verdict and ending leg.

usage: programs.py --work DIR --pins-sha256 HEX [--fv DIR] [--fixtures-fv DIR] [--threads N]
       programs.py --work DIR --programs-only [--pins-sha256 HEX] [--fv DIR] [--fixtures-fv DIR] [--threads N]

  --work DIR        existing directory for the work files (each run gets a new subdirectory)
  --pins-sha256     the SHA-256 of the record, as build-judge-macos.sh printed it. The judge gives no verdict
                    without it, so the `judge` section needs it
  --fv DIR          the fastverify directory whose judge and record are tested (default: the one this file is in)
  --fixtures-fv DIR the fastverify directory whose tests/ holds the fixtures (default: --fv)
  --programs-only   skip the `judge` section

Prints PASS|FAIL|INFO rows and `RESULT pass=N fail=M info=K`. Exit 0: no FAIL, or SKIP. Exit 1: a FAIL row.
Exit 2: could not run (hash mismatch, bad fixture).
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile

FV = Path(__file__).resolve().parents[2]
TESTS = FV / 'tests'                       # main() replaces these two for --fv / --fixtures-fv
ENTRY = {'lowmem': FV / 'check/lowmem/check-sound-lowmem.sh',
         'ultralowmem': FV / 'check/lowmem/check-sound-ultralowmem.sh'}
# tests/forged-inductive-records/README.md, per export: the exit status of the Lean leg (run.sh, with its two
# `either` rows as the README labels them once the export-record check is installed: rejected) and the exit
# status of the second kernel (the column `gruszka`).
FORGED = {'T-honest': (0, 0), 'Tonly-honest': (0, 0), 'T-isrec-forged': (1, 2), 'T-numidx-forged': (1, 2),
          'T-eta-honest-rec': (1, 1), 'T-eta-forged-isrec': (1, 2), 'Tonly-allforged': (1, 1), 'T-allforged': (1, 1),
          'T-ctor-forged': (1, 1)}
RECORD_CHECK_ONLY = ('T-isrec-forged', 'T-numidx-forged')
# The generators of crafted exports: (group, scripts under tests/, arguments, directory of the cases under the
# output directory, number of exports the scripts' code writes). {st} is a directory with the self-test
# (good.export, comparator.json), {out} the output directory. No arguments: the cases come from the script's
# build_cases(), which also labels them.
LEG_CHECKS = 'lean-leg-record-checks/'
GENERATORS = (
    ('cves', ('kernel-cves/craft_cves.py',), ('--selftest-dir', '{st}', '--out', '{out}'), '.', 9),
    ('issue-analogues', (LEG_CHECKS + 'mk_kernel_issue_exports.py',), ('{st}/good.export', '{out}'), '.', 5),
    ('c2s', (LEG_CHECKS + 'mk_c2_stream.py',), ('{st}/good.export', '{out}'), '.', 5),
    ('c1only', (LEG_CHECKS + 'mk_c1only.py',), ('{st}', '{out}'), '.', 3),
    ('implicit', (LEG_CHECKS + 'mk_implicit_closure.py',), ('{st}', '{out}'), 'finals', 2),
    ('recursor-name', (LEG_CHECKS + 'recursor_name/craft_g1.py', LEG_CHECKS + 'recursor_name/craft_g1dup.py'),
     ('{st}', '{out}'), '.', 4),
    ('c1c2-edge', (LEG_CHECKS + 'test_c1c2_edge_cases.py',), None, '.', 18),
)
RUN_BUILD_CASES = '''import json, runpy, sys
from pathlib import Path
script, selftest, out = sys.argv[1:4]
cases = runpy.run_path(script, run_name="generator")["build_cases"](Path(selftest), Path(out))
print(json.dumps([[cid, expect, Path(path).name] for cid, expect, path in cases]))
'''
# Groups whose controls have a stated outcome only for the Lean-leg programs alone, with the script that
# states it. No second-kernel or full-judge outcome is stated for them.
LEAN_ONLY_CONTROLS = {'c1only': 'mk_c1only.py', 'c2s': 'mk_c2_stream.py', 'c1c2-edge': 'test_c1c2_edge_cases.py'}
# Attacks on which the kernel of the replay panics (`INTERNAL PANIC`, or a failed `inductiveVal!`): with
# LEAN_ABORT_ON_PANIC=1 the program aborts. Every other attack is rejected with exit status 1.
PANICS = {('kernel-issues', 'L4-ctor-name-mismatch'), ('c1c2-edge', 'E17_huge_bvar_2pow20_unsafe_ctor')}
ABORT = -signal.SIGABRT
# Attacks that the second kernel declines, by its own `declined: ` line. Every other attack it rejects.
SECOND_DECLINES = {
    ('kernel-issues', 'L6-quot-wrong-kind'), ('forged-ctor', 'ind-isrec'), ('forged-ctor', 'ind-nidx'),
    ('forged-ctor', 'ind-nnested'), ('forged-ctor', 'ind-refl'), ('c2s', 'c2s_isrec_forged'),
    ('recursor-name', 'g1d_dup_rec_thm'), ('recursor-name', 'g1e_dup_thm_rec'),
    ('c1c2-edge', 'E11_quot_mk_as_unsafe_axiom'), ('c1c2-edge', 'E17_huge_bvar_2pow20_unsafe_ctor')}
# Attacks of kernel-issues that the comparison rejects, before a kernel sees them.
COMPARISON_REJECTS = ('L10-unsafe-axiom-as-ctor', 'L4-ctor-name-mismatch')
# CASES of tests/kernel-cves/run.sh: per export the config (the self-test's, or the one craft_cves.py writes
# without Quot.sound) and the exit status of every trusted judge script.
CVE_CASES = {
    '16489_control_valid': ('comparator.json', 0),
    '16489_safe_ctor': ('comparator.json', 1),
    '16489_unsafe_ctor': ('comparator.json', 1),
    '16489_2param_unsafe': ('comparator.json', 1),
    '15100_unsafe_axiom_as_ctor': ('comparator.json', 1),
    '15100_unsafe_ctor_forged_meta': ('comparator.json', 1),
    '15101_baseline_noquot': ('comparator_noquot.json', 0),
    '15101_fake_quot_clean': ('comparator_noquot.json', 1),
    '15101_fake_quot_plus_mk': ('comparator_noquot.json', 1),
}
# CFG of tests/kernel-issues/test.py.
KERNEL_ISSUES_CONFIG = {'challenge_module': 'Challenge', 'solution_module': 'Solution', 'theorem_names': ['main_thm'],
              'definition_names': [], 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
# What is expected of the streaming replay (`pleanchecker_lowmem --low-mem --evict=smart`), by group. As the
# replay of mode lowmem (attack not accepted, control accepted): crafted_all.sh, kind lowmem, runs leanleg.sh on
# the cves, kernel-issues, issue-analogues, c2s and implicit exports and test_c1c2_edge_cases.py --modes lowmem;
# plain_variants.sh runs forged-ctor. Accepted, attacks included: c1only (crafted_all.sh: "the ultra-low-memory
# leg accepts them by design - its C1 covers exactly the blocks it hands to the kernel"). Any other group: no
# test states an outcome for this leg.
STREAMING_AS_PLAIN = ('cves', 'kernel-issues', 'issue-analogues', 'c2s', 'implicit', 'c1c2-edge', 'forged-ctor')
STREAMING_ACCEPTS = ('c1only',)
COUNTS = {'PASS': 0, 'FAIL': 0, 'INFO': 0}


class Setup(Exception):
    """The checks could not run."""


class Case:
    """One export: where it comes from, what is expected of it, and what each program did."""
    def __init__(self, group, name, export, control, lean, second):
        self.group, self.name, self.export, self.control = group, name, export, control
        self.lean = lean          # exit status wanted from the replay of mode lowmem: 0, 1 or ABORT
        self.second = second      # outcome wanted from the second kernel: accepted, rejected, declined, or None
        self.ran = {}             # 'parallel', 'seq', 'streaming': exit status; 'second': outcome

    @property
    def label(self):
        return f'{self.group}/{self.name}'


def row(status, name, detail):
    COUNTS[status] += 1
    print(f'{status} {name}: {detail}', flush=True)


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def own_selftest(support, dest):
    """The self-test inputs of the tree, compared with the digests the driver pins and copied."""
    dest.mkdir()
    pins = support.TreePins().files
    for name in ('selftest_comparator', 'selftest_challenge', 'selftest_good'):
        source, pin = pins[name]
        filename = source.name
        if not source.is_file() or digest(source) != pin:
            raise Setup(f'self-test input missing or changed: {source}')
        shutil.copyfile(source, dest / filename)
        if digest(dest / filename) != pin:
            raise Setup(f'copy of the self-test differs: {filename}')
    return dest


def unpack(corpus, dest):
    """Extract tests/lean-leg-record-checks/corpora/NAME.tar.xz and compare every file with NAME.sha256."""
    archive = TESTS / LEG_CHECKS / 'corpora' / (corpus + '.tar.xz')
    listing = TESTS / LEG_CHECKS / 'corpora' / (corpus + '.sha256')
    dest.mkdir()
    done = subprocess.run(['/usr/bin/tar', '-xJf', str(archive), '-C', str(dest)], stdin=subprocess.DEVNULL,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if done.returncode != 0:
        raise Setup(f'cannot extract {archive}: {done.stdout.decode(errors="replace")[:300]}')
    expected = dict(reversed(line.split(maxsplit=1)) for line in listing.read_text().splitlines() if line.strip())
    found = {str(path.relative_to(dest)) for path in dest.rglob('*') if path.is_file()}
    if found != set(expected) or any(digest(dest / name) != value for name, value in expected.items()):
        raise Setup(f'{archive} does not match {listing}')
    return dest


def is_control(name):
    """tests/lean-leg-record-checks/leanleg.sh st_want: the inputs that must be accepted."""
    return any(word in name for word in ('control', 'baseline', 'honest')) or name.startswith('C0') or name == 'base'


def streaming_wanted(case):
    """Exit status expected of the streaming replay on a case: that of the replay of mode lowmem, 0 for the
    group it accepts by design, or None where no test states one for that leg."""
    if case.group in STREAMING_ACCEPTS:
        return 0
    if case.group in STREAMING_AS_PLAIN:
        return case.lean
    return None


def lean_wanted(group, name, control):
    """Exit status expected of the replay of mode lowmem for a case outside forged-records."""
    return 0 if control else ABORT if (group, name) in PANICS else 1


def second_wanted(group, name, control):
    """What is expected of the second kernel for a case outside forged-records."""
    if control:
        return None if group in LEAN_ONLY_CONTROLS else 'accepted'
    return 'declined' if (group, name) in SECOND_DECLINES else 'rejected'


def tree_inputs(work):
    """The cases whose exports are in this tree."""
    cases = []
    forged = TESTS / 'forged-inductive-records/x'
    for name, (lean, second) in FORGED.items():
        cases.append(Case('forged-records', name, forged / (name + '.export'), lean == 0, lean,
                          ('accepted', 'rejected', 'declined')[second]))
    issues = unpack('kernel-crafted', work / 'kernel-crafted')
    for path in sorted((issues / 'crafted').glob('*.export')):
        control = is_control(path.stem)
        cases.append(Case('kernel-issues', path.stem, path, control, lean_wanted('kernel-issues', path.stem, control),
                          second_wanted('kernel-issues', path.stem, control)))
    cases.append(Case('kernel-issues', 'base', issues / 'so/Solution.export', True, 0, 'accepted'))
    ctor = unpack('forged-ctor', work / 'forged-ctor')
    for path in sorted(ctor.glob('*.export')):
        control = path.stem == 'honest'
        cases.append(Case('forged-ctor', path.stem, path, control, lean_wanted('forged-ctor', path.stem, control),
                          second_wanted('forged-ctor', path.stem, control)))
    for case in cases:
        if not case.export.is_file():
            raise Setup(f'fixture missing: {case.export}')
    if len(cases) != len(FORGED) + 15 + 8:
        raise Setup(f'unexpected number of fixtures in the tree: {len(cases)}')
    return cases


def run_python(arguments, cwd):
    """Exit status, stdout and last line of output of `python3 ARGUMENTS`."""
    try:
        # -B: no bytecode files next to the scripts, whatever the interpreter's default is.
        done = subprocess.run(['/usr/bin/python3', '-I', '-B', *map(str, arguments)], cwd=cwd,
                              env={'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8'}, stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600)
    except subprocess.TimeoutExpired:
        return 'timeout', '', 'no result after 600 s'
    stdout = done.stdout.decode('utf-8', errors='replace')
    lines = [line for line in (stdout + done.stderr.decode('utf-8', errors='replace')).splitlines() if line.strip()]
    return done.returncode, stdout, (lines[-1] if lines else '')[:200]


def generated_inputs(work, selftest):
    """The cases the generators make from the self-test. One row per generator."""
    cases = []
    (work / 'generated').mkdir()
    for group, scripts, arguments, where, count in GENERATORS:
        names = ', '.join(Path(script).name for script in scripts)
        out = work / 'generated' / group
        out.mkdir()
        labels, failure = None, None
        for script in scripts:
            if arguments is None:
                rc, stdout, last = run_python(['-c', RUN_BUILD_CASES, TESTS / script, selftest, out], work)
                if rc == 0:
                    try:
                        labels = {Path(name).stem: kind for _cid, kind, name in json.loads(stdout)}
                    except (ValueError, TypeError):
                        rc, last = 'unreadable', 'build_cases() did not return its list of cases'
            else:
                rc, _stdout, last = run_python(
                    [TESTS / script, *(word.format(st=selftest, out=out) for word in arguments)], work)
            if rc != 0:
                failure = f'{Path(script).name} failed (exit {rc}): {last}'
                break
        exports = sorted((out / where).glob('*.export')) if failure is None else []
        if failure is None and len(exports) != count:
            failure = f'{len(exports)} exports, the code of {names} writes {count}'
        if failure is None and labels is not None and (
                set(labels) != {path.stem for path in exports} or not set(labels.values()) <= {'attack', 'control'}):
            failure = f'build_cases() of {names} does not label exactly the exports it wrote'
        if failure is not None:
            row('FAIL', f'programs generator {group}', failure + '; its cases are missing below')
            continue
        row('PASS', f'programs generator {group}', f'{count} exports from {names} on the self-test')
        for path in exports:
            control = is_control(path.stem) if labels is None else labels[path.stem] == 'control'
            cases.append(Case(group, path.stem, path, control, lean_wanted(group, path.stem, control),
                              second_wanted(group, path.stem, control)))
    return cases


def replay(program, flags, export, threads, scratch):
    """Exit status and last stdout line of one replay, with the environment of the judge's Lean leg."""
    env = {'PATH': '/usr/bin:/bin', 'LEAN_STACK_SIZE_KB': '917376', 'LEAN_ABORT_ON_PANIC': '1'}
    if '--low-mem' in flags:
        env.update(MIMALLOC_PURGE_DELAY='0', MIMALLOC_PURGE_DECOMMITS='1')
    with tempfile.TemporaryDirectory(dir=scratch) as cwd, open(Path(cwd) / 'stderr', 'wb') as errors:
        try:
            done = subprocess.run([str(program), *flags, f'-j{threads}', '-v', '--from-export', str(export)], cwd=cwd,
                                  env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=errors, timeout=900)
        except subprocess.TimeoutExpired:
            return 'timeout', ''
    lines = [line for line in done.stdout.decode('utf-8', errors='replace').splitlines() if line.strip()]
    return done.returncode, (lines[-1] if lines else '')[:150]


def second_kernel(programs, export, threads, scratch):
    """Outcome of the second kernel on one export: `gruszka EXPORT WORKERS`, as the judge's k2 leg starts
    it. gruszka packs the export in its own memory.

    Returns (outcome, text). `accepted`: exit 0, the line `accepted`, no `rejected: ` or `error:` line.
    `rejected`: exit 1 and a `rejected: ` line. `declined`: exit 2 and a `declined: ` line; an export that
    gruszka's packer finds invalid is one of these. Anything else, a timeout or a signal included, is
    `unexpected`."""
    with tempfile.TemporaryDirectory(dir=scratch) as cwd:
        env = {'PATH': '/usr/bin:/bin', 'HOME': cwd, 'TMPDIR': cwd, 'LANG': 'C.UTF-8', 'LEAN_ABORT_ON_PANIC': '1',
               'LEAN_NUM_THREADS': str(threads)}
        try:
            done = subprocess.run([str(programs['gruszka']), str(export), str(threads)], cwd=cwd, env=env,
                                  stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  timeout=900)
        except subprocess.TimeoutExpired:
            return 'unexpected', 'gruszka gave no result in 900 s'
        rc = done.returncode
        output = done.stdout.decode('utf-8', errors='replace').splitlines()
        lines = [line.replace(str(export), export.name) for line in output if line.strip()]
        rejected = [line for line in lines if line.startswith('rejected: ')]
        if rc == 0 and 'accepted' in lines and not rejected and not any(line.startswith('error:') for line in lines):
            return 'accepted', 'accepted'
        if rc == 1 and rejected and 'accepted' not in lines:
            return 'rejected', rejected[0][:150]
        said = [line for line in lines if line.startswith('declined: ')]
        if rc == 2 and said and 'accepted' not in lines and not rejected:
            return 'declined', said[0][:150]
        return 'unexpected', f'gruszka exit {rc} | {(lines[-1] if lines else "")[:150]}'


def stops(rc):
    """A replay that ended without accepting: exit 1, or an abort. A timeout is neither."""
    return rc not in (0, 'timeout')


def shown(wanted):
    return 'an abort (the kernel panics)' if wanted == ABORT else wanted


def programs_section(programs, cases, threads, scratch):
    for label, flags in (('parallel', []), ('seq', ['--seq'])):
        for case in cases:
            rc, message = replay(programs['pleanchecker'], flags, case.export, threads, scratch)
            case.ran[label] = rc
            status = 'PASS' if rc == case.lean else 'FAIL'
            note = ' (only the export-record check rejects this one)' if case.name in RECORD_CHECK_ONLY else ''
            row(status, f'programs pleanchecker {label} {case.label}',
                f'rc={rc}, wanted {shown(case.lean)}{note} | {message}')
    # Mode `lowmem`: the streaming replay, by the criteria stated for that leg.
    accepted = []
    for case in cases:
        rc, message = replay(programs['pleanchecker_lowmem'], ['--low-mem', '--evict=smart'], case.export, threads,
                             scratch)
        case.ran['streaming'] = rc
        if case.lean != 0 and rc == 0:
            accepted.append(case.label)
        wanted = streaming_wanted(case)
        if wanted is None:
            differs = rc != case.lean
            row('INFO', f'programs pleanchecker_lowmem {case.label}',
                f'rc={rc}, the replay of mode lowmem gives {case.lean}{" - DIFFERS" if differs else ""}; no test '
                f'states an outcome for this leg on {case.group} | {message}')
        else:
            design = ' (accepted by design: an unsafe block is skipped)' if case.group in STREAMING_ACCEPTS else ''
            row('PASS' if rc == wanted else 'FAIL', f'programs pleanchecker_lowmem {case.label}',
                f'rc={rc}, wanted {shown(wanted)}{design} | {message}')
    row('INFO', 'programs pleanchecker_lowmem summary',
        f'{len(accepted)} input(s) accepted that the replay of mode lowmem rejects: {", ".join(accepted) or "none"}')
    # The second kernel: the other kernel between an export and ACCEPTED.
    for case in cases:
        outcome, text = second_kernel(programs, case.export, threads, scratch)
        case.ran['second'] = outcome
        if case.second is None:
            row('INFO', f'programs second-kernel {case.label}',
                f'{outcome}; the outcome of this control is stated only for the Lean-leg programs alone '
                f'({LEAN_ONLY_CONTROLS[case.group]}: accepted) | {text}')
        else:
            row('PASS' if outcome == case.second else 'FAIL', f'programs second-kernel {case.label}',
                f'{outcome}, wanted {case.second} | {text}')
    attacks = [case for case in cases if not case.control]
    exposed = [case for case in attacks if case.ran['streaming'] == 0]
    count = {outcome: sum(case.ran['second'] == outcome for case in exposed) for outcome in ('rejected', 'declined')}
    through = [f'{case.label} ({case.ran["second"]})' for case in exposed
               if case.ran['second'] not in ('rejected', 'declined')]
    row('FAIL' if through else 'PASS', 'programs second-kernel stops what the streaming replay accepts',
        f'{len(exposed)} attack input(s) accepted by the streaming replay, '
        f'{sum(stops(case.ran["parallel"]) for case in exposed)} of them stopped by the replay of mode lowmem; '
        f'second kernel: {count["rejected"]} rejected, {count["declined"]} declined; '
        f'not stopped: {", ".join(through) or "none"}')
    stopped = [case.ran['parallel'] for case in attacks if stops(case.ran['parallel'])]
    count = {outcome: sum(case.ran['second'] == outcome for case in attacks)
             for outcome in ('rejected', 'declined', 'accepted', 'unexpected')}
    row('INFO', 'programs attack totals',
        f'{len(attacks)} attack input(s); replay of mode lowmem: {len(stopped)} stopped ({stopped.count(1)} exit 1, '
        f'{len(stopped) - stopped.count(1)} other); streaming replay: {len(exposed)} accepted; second kernel: '
        f'{count["accepted"]} accepted, {count["rejected"]} rejected, {count["declined"]} declined, '
        f'{count["unexpected"]} unexpected')


def anonymous_axiom_export(source, dest, theorem):
    """The anonymous-axiom input, as tests/anonymous-axiom makes it, from an export of this tree.

    An axiom whose name is index 0 (`[anonymous]`) gets the statement of `theorem`, and the theorem's
    proof becomes that axiom. The proof then rests on an axiom the config does not permit."""
    lines = source.read_bytes().split(b'\n')
    if lines[-1] == b'':
        lines.pop()
    records = [json.loads(line) for line in lines[1:]]
    names, next_expr = {0: ()}, 0
    for record in records:
        if 'in' in record:
            kind = 'str' if 'str' in record else 'num'
            part = record[kind]['str'] if kind == 'str' else record[kind]['i']
            names[record['in']] = names[record[kind]['pre']] + (part,)
        elif 'ie' in record:
            next_expr = max(next_expr, record['ie'] + 1)
    targets = [index for index, name in names.items() if name == (theorem,)]
    found = [i for i, record in enumerate(records) if 'thm' in record and record['thm']['name'] in targets]
    if len(targets) != 1 or len(found) != 1 or records[found[0]]['thm']['levelParams']:
        raise Setup(f'{source}: no single theorem {theorem} without universe parameters')
    thm = records.pop(found[0])['thm']
    records.append({'axiom': {'isUnsafe': False, 'levelParams': [], 'name': 0, 'type': thm['type']}})
    records.append({'ie': next_expr, 'const': {'name': 0, 'us': []}})
    records.append({'thm': dict(thm, value=next_expr)})
    with open(dest, 'w', encoding='utf-8') as out:
        out.write(lines[0].decode('utf-8') + '\n')
        for record in records:
            out.write(json.dumps(record, sort_keys=True, separators=(',', ':'), ensure_ascii=False) + '\n')


def judge(mode, arguments, threads, scratch, pins):
    """Exit status and result of one run of the judge through its entry script. The result is the one line on
    stdout, which the JSON file must hold too; anything else is no result, and its `reason` says what was found.
    The options of this function stand in front of the row's own, so that a refused argument of the row is
    written to the file like every other end."""
    work = Path(tempfile.mkdtemp(prefix=mode + '-', dir=scratch))
    result = work / 'result.json'
    words = [str(word) for word in arguments]
    front = 1 if words[:1] == ['--preflight'] else 3
    cmd = ['/bin/bash', str(ENTRY[mode]), *words[:front], '--threads', str(threads), '--workdir', str(work),
           '--json', str(result), '--log', str(work / 'judge.log'), *pins, *words[front:]]
    try:
        done = subprocess.run(cmd, cwd=work, env={'PATH': '/usr/bin:/bin'}, stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, timeout=3600)
    except subprocess.TimeoutExpired:
        return 'timeout', {}
    lines = done.stdout.decode('utf-8', errors='replace').splitlines()
    try:
        if len(lines) != 1:
            record = {'reason': f'{len(lines)} lines on stdout, not one'}
        elif not result.is_file() or result.read_bytes() != done.stdout:
            record = {'reason': 'the JSON file does not hold the line on stdout'}
        else:
            record = json.loads(lines[0])
    except (OSError, ValueError):
        record = {}
    return done.returncode, record if isinstance(record, dict) else {}


def decided_by(record):
    """What decided a run of the judge: `arguments` (also the record and the caller's digests), `gate`,
    `self-tests`, `all legs` when the three accepted, or the leg that ended the run. The legs run in the order
    compare, lean, k2, and the first that does not accept ends the run: it is the last one in `legs`."""
    legs = record.get('legs')
    if isinstance(legs, dict) and legs:
        accepted = [name for name, leg in legs.items() if isinstance(leg, dict) and leg.get('rc') == 0]
        return 'all legs' if accepted == ['compare', 'lean', 'k2'] == list(legs) else list(legs)[-1]
    if 'selftests' in record:
        return 'self-tests'
    return 'gate' if isinstance(record.get('xversion'), dict) else 'arguments'


def expect(name, outcome, rc, verdict, by, reason=''):
    got_rc, record = outcome
    ok = got_rc == rc and record.get('verdict') == verdict and record.get('exit') == got_rc \
        and reason in str(record.get('reason', '')) and decided_by(record) == by
    if ok and verdict == 'REJECTED' and by in ('compare', 'lean', 'k2'):
        ok = record['legs'][by].get('rc') == 1
    row('PASS' if ok else 'FAIL', 'judge ' + name,
        f'rc={got_rc} {record.get("verdict")} by {decided_by(record)}, wanted rc={rc} {verdict} by {by}'
        f'{" with " + repr(reason) if reason else ""} | {str(record.get("reason", ""))[:160]}')
    return record


def expect_leg(mode, record, programs):
    """An ACCEPTED result names the programs that ran, with the digest of the official-kernel leg of the mode."""
    program, checker = {'lowmem': ('pleanchecker', 'checkSoundLowMem'),
                        'ultralowmem': ('pleanchecker_lowmem', 'checkSoundUltraLowMem')}[mode]
    ran = record.get('binaries_sha256') or {}
    ok = (ran.get(program) == digest(programs[program]) and record.get('checker') == checker
          and not {'pleanchecker', 'pleanchecker_lowmem'} - {program} & set(ran))
    row('PASS' if ok else 'FAIL', f'judge {mode} leg', f'program={program} sha256={str(ran.get(program))[:12]}')


def judge_section(threads, scratch, pins, programs):
    hole, gate = TESTS / 'definition-hole/x', TESTS / 'cross-version-regress/x'
    challenge, config, honest = hole / 'Challenge.export', hole / 'comparator.json', hole / 'SolutionHonest.export'
    anonymous = scratch / 'anonymous-axiom.export'
    anonymous_axiom_export(honest, anonymous, 't')
    # A challenge whose meta line holds "lean" twice, and a config without definition holes.
    lines = challenge.read_bytes().split(b'\n', 1)
    meta = json.loads(lines[0])['meta']
    twice = ('{"meta":{"exporter":%s,"format":%s,"lean":%s,"lean":{"githash":"%s","version":"4.37.0-rc1"}}}' % (
        json.dumps(meta['exporter'], separators=(',', ':')), json.dumps(meta['format'], separators=(',', ':')),
        json.dumps(meta['lean'], separators=(',', ':')), '0b77e12952ad39077d80d8bd6b66d601f225c321')).encode()
    twice_challenge, plain_config = scratch / 'lean-twice.export', scratch / 'no-holes.json'
    twice_challenge.write_bytes(twice + b'\n' + lines[1])
    plain = json.loads(config.read_text())
    plain.pop('definition_names')
    plain_config.write_text(json.dumps(plain))
    for mode in ('lowmem', 'ultralowmem'):
        expect(f'{mode} preflight', judge(mode, ['--preflight'], threads, scratch, pins), 0, 'PREFLIGHT_OK',
               'self-tests')
        record = expect(f'{mode} definition-hole honest',
                        judge(mode, [honest, challenge, config], threads, scratch, pins), 0, 'ACCEPTED', 'all legs')
        expect_leg(mode, record, programs)
        expect(f'{mode} no-hole config, honest', judge(mode, [honest, challenge, plain_config], threads, scratch, pins),
               0, 'ACCEPTED', 'all legs')
        expect(f'{mode} gate no-hole config, meta line with lean twice',
               judge(mode, [honest, twice_challenge, plain_config], threads, scratch, pins),
               2, 'DECLINED', 'gate', 'meta line (release identity) refused')
        # Rows duplicate-meta-check-sound-canonical-meta / -dupmeta and duplicate-meta-check-lowmem-dupmeta of
        # tests/cross-version-regress.
        canonical = [gate / 'dupmeta_sol37.export', gate / 'dupmeta_chal37.export', gate / 'dupmeta_cfg.json']
        dup = [canonical[0], gate / 'dupmeta_chal37_dupmeta.export', canonical[2]]
        expect(f'{mode} gate duplicate-meta canonical meta', judge(mode, canonical, threads, scratch, pins),
               1, 'REJECTED', 'gate', "xversion: Challenge definition is not sorried: 'secret'")
        expect(f'{mode} gate duplicate-meta lean twice', judge(mode, dup, threads, scratch, pins),
               2, 'DECLINED', 'gate', 'meta line (release identity) refused')
        expect(f'{mode} gate duplicate-meta lean twice, --require-sorried-holes',
               judge(mode, [*dup, '--require-sorried-holes'], threads, scratch, pins),
               2, 'DECLINED', 'gate', 'meta line (release identity) refused')
        expect(f'{mode} definition-hole sorried',
               judge(mode, [hole / 'Solution.export', challenge, config], threads, scratch, pins),
               1, 'REJECTED', 'compare', 'sorryAx')
        # tests/anonymous-axiom passes on any verdict but ACCEPTED and gets REJECTED from the axiom check.
        # Here only that passes: REJECTED by the comparison, with its line about the axiom.
        expect(f'{mode} anonymous-axiom', judge(mode, [anonymous, challenge, config], threads, scratch, pins),
               1, 'REJECTED', 'compare', 'error: Illegal axiom detected: ')
        sums = {'--challenge-sha256': digest(challenge), '--comparator-sha256': digest(config)}
        right = [word for pair in sums.items() for word in pair]
        expect(f'{mode} caller-pins right', judge(mode, [honest, challenge, config, *right], threads, scratch, pins),
               0, 'ACCEPTED', 'all legs')
        expect(f'{mode} caller-pins wrong challenge',
               judge(mode, [honest, challenge, config, '--challenge-sha256', sums['--comparator-sha256']], threads,
                     scratch, pins), 2, 'DECLINED', 'arguments', '!= --challenge-sha256')
        expect(f'{mode} caller-pins wrong comparator',
               judge(mode, [honest, challenge, config, '--comparator-sha256', sums['--challenge-sha256']], threads,
                     scratch, pins), 2, 'DECLINED', 'arguments', '!= --comparator-sha256')
    # Rows of tests/cross-version-regress/run.sh that the cross-version gate decides before any program starts.
    shl = gate / 'comparator_shl.json'
    expect('ultralowmem gate 4.37 challenge, escaped name, --require-sorried-holes',
           judge('ultralowmem', [gate / 'sol37_prove_false.export', gate / 'chal37_uesc.export', shl,
                            '--require-sorried-holes'], threads, scratch, pins), 1, 'REJECTED', 'gate', 'xversion: ')
    expect('ultralowmem gate 4.36 challenge, kernel-closure rule',
           judge('ultralowmem', [gate / 'sol36_prove_false.export', gate / 'chal36_canon.export', shl], threads,
                 scratch, pins), 2, 'DECLINED', 'gate', 'xversion gate failed')
    expect('lowmem gate 4.36 challenge, escaped name, --require-sorried-holes',
           judge('lowmem', [gate / 'sol36_prove_false.export', gate / 'chal36_uesc.export', shl,
                           '--require-sorried-holes'], threads, scratch, pins),
           2, 'DECLINED', 'gate', 'xversion gate failed')
    expect('lowmem extra-kernel --kernel nanoda',
           judge('lowmem', [honest, challenge, config, '--kernel', 'nanoda'], threads, scratch, pins),
           2, 'DECLINED', 'arguments', "unknown argument '--kernel'")


def lean_leg_accepted(record):
    """Whether the Lean leg of a run accepted. None: the run ended before that leg."""
    legs = record.get('legs')
    lean = legs.get('lean') if isinstance(legs, dict) else None
    if not isinstance(lean, dict):
        return None
    return lean.get('rc') == 0 and lean.get('message') == 'Lean default kernel accepts the solution'


def expect_crafted(mode, label, outcome, by):
    """One crafted export through the whole judge. `by` is `all legs` for a control, which must be ACCEPTED, or
    the leg that must reject an attack, which must be REJECTED."""
    rc, record = outcome
    wanted = (0, 'ACCEPTED') if by == 'all legs' else (1, 'REJECTED')
    ok = (rc, record.get('verdict')) == wanted and record.get('exit') == rc and decided_by(record) == by
    if ok and by != 'all legs':
        ok = record['legs'][by].get('rc') == 1
    row('PASS' if ok else 'FAIL', f'judge {mode} crafted {label}',
        f'rc={rc} {record.get("verdict")} by {decided_by(record)}, wanted {wanted[1]} by {by} | '
        f'{str(record.get("reason", ""))[:160]}')
    return record


def crafted_section(threads, scratch, pins, cases, selftest):
    """Crafted exports through the whole judge, both modes, with the leg that ended each run."""
    by_group = {}
    for case in cases:
        by_group.setdefault(case.group, {})[case.name] = case
    runs = []                                  # (label, case, arguments, what must decide)
    cves = by_group.get('cves', {})
    if set(cves) != set(CVE_CASES):
        row('FAIL', 'judge crafted cves', 'not run: the cves exports were not generated as craft_cves.py writes them')
    for name in (CVE_CASES if set(cves) == set(CVE_CASES) else ()):
        config, status = CVE_CASES[name]
        # craft_cves.py writes comparator_noquot.json next to its exports.
        config = (selftest if config == 'comparator.json' else cves[name].export.parent) / config
        runs.append((f'cves/{name}', cves[name], [cves[name].export, selftest / 'challenge.export', config],
                     ('all legs', 'lean')[status]))
    issues = by_group['kernel-issues']
    issues_config = scratch / 'kernel-issues-comparator.json'
    issues_config.write_text(json.dumps(KERNEL_ISSUES_CONFIG))
    for name, case in issues.items():
        runs.append((f'kernel-issues/{name}', case, [case.export, issues['base'].export, issues_config],
                     'all legs' if case.control else 'compare' if name in COMPARISON_REJECTS else 'lean'))
    for mode, alone in (('lowmem', 'parallel'), ('ultralowmem', 'streaming')):
        ended, verdicts, differs, reached, second_alone = {}, {}, [], 0, []
        for label, case, arguments, by in runs:
            record = expect_crafted(mode, label, judge(mode, arguments, threads, scratch, pins), by)
            accepted = lean_leg_accepted(record)
            if accepted is not None:
                reached += 1
                if accepted != (case.ran[alone] == 0):
                    differs.append(label)
            if not case.control:
                leg = decided_by(record)
                ended[leg] = ended.get(leg, 0) + 1
                verdicts[record.get('verdict')] = verdicts.get(record.get('verdict'), 0) + 1
                if leg == 'k2':
                    second_alone.append(f'{label} ({record.get("verdict")})')
        row('FAIL' if differs else 'PASS', f'judge {mode} crafted lean leg as the program alone',
            f'{reached} run(s) reached the Lean leg; it decided otherwise than the program alone for: '
            f'{", ".join(differs) or "none"}')
        row('INFO', f'judge {mode} crafted summary',
            f'{sum(ended.values())} attack run(s): ended by '
            + ', '.join(f'{leg} {n}' for leg, n in sorted(ended.items()))
            + '; verdicts ' + ', '.join(f'{verdict} {n}' for verdict, n in sorted(verdicts.items(), key=str))
            + f'; ended by the second kernel after the Lean leg accepted: {", ".join(second_alone) or "none"}')
        # The synthetic controls, end to end, paired like the cves exports with the self-test's challenge and config.
        for case in cases:
            if case.control and case.group in LEAN_ONLY_CONTROLS:
                rc, record = judge(mode, [case.export, selftest / 'challenge.export', selftest / 'comparator.json'],
                                   threads, scratch, pins)
                ended = '' if rc == 0 else f', ended by {decided_by(record)}'
                row('INFO', f'judge {mode} crafted synthetic control {case.label}',
                    f'rc={rc} {record.get("verdict")}{ended}; the outcome of this control is stated only for '
                    f'the Lean-leg programs alone ({LEAN_ONLY_CONTROLS[case.group]}: accepted) | '
                    f'{str(record.get("reason", ""))[:160]}')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--fv', type=Path, default=FV)
    parser.add_argument('--fixtures-fv', type=Path)
    parser.add_argument('--pins-sha256')
    parser.add_argument('--threads', type=int, default=4)
    parser.add_argument('--programs-only', action='store_true')
    args = parser.parse_args()
    fv = args.fv.resolve()
    record = fv / 'config/pins-macos.env'
    if sys.platform != 'darwin' or not record.is_file():
        print('SKIP macos-judge programs: needs macOS and the programs built by check/sound/macos/build-judge-macos.sh')
        return 0
    try:
        if args.threads < 1 or not args.work.is_dir():
            raise Setup('--work must be an existing directory and --threads positive')
        if not (args.pins_sha256 or args.programs_only):
            raise Setup('--pins-sha256 is required: the SHA-256 of the record that build-judge-macos.sh printed '
                        '(--programs-only runs the programs alone without it)')
        global TESTS
        TESTS = (args.fixtures_fv or fv).resolve(strict=True) / 'tests'
        ENTRY.update(lowmem=fv / 'check/lowmem/check-sound-lowmem.sh',
                     ultralowmem=fv / 'check/lowmem/check-sound-ultralowmem.sh')
        generators = {TESTS / script for _group, scripts, *_rest in GENERATORS for script in scripts}
        for needed in (*ENTRY.values(), TESTS / 'definition-hole/x', TESTS / 'forged-inductive-records/x',
                       TESTS / LEG_CHECKS / 'corpora', TESTS / 'cross-version-regress/x', *sorted(generators)):
            if not needed.exists():
                raise Setup(f'missing: {needed}')
        # The record is read and the programs are hashed by the driver's own reader.
        sys.dont_write_bytecode = True
        sys.path.insert(0, str(fv / 'check/sound/macos'))
        import support
        try:
            pins = support.Record(record, expected_sha256=args.pins_sha256)
        except support.Declined as error:
            raise Setup(str(error)) from None
        if set(pins.paths) != set(support.PROGRAMS):
            raise Setup('the record does not name the four programs')
        programs = dict(pins.paths)
        for name, path in sorted(programs.items()):
            if not path.is_file() or digest(path) != pins.digests[name]:
                raise Setup(f'{path} is not the program {name} that the record names')
        scratch = Path(tempfile.mkdtemp(prefix='judge-programs-', dir=args.work.resolve())).resolve()
        print(f'work files: {scratch}', flush=True)
        print(f'judge {fv}', flush=True)
        print(f'fixtures {TESTS}', flush=True)
        print(f'record {record} sha256 {pins.sha256}', flush=True)
        for name in sorted(programs):
            print(f'program {name} {pins.digests[name]} {programs[name]}', flush=True)
        selftest = own_selftest(support, scratch / 'selftest')
        cases = tree_inputs(scratch) + generated_inputs(scratch, selftest)
        programs_section(programs, cases, args.threads, scratch)
        if not args.programs_only:
            caller = ['--pins-sha256', args.pins_sha256]
            judge_section(args.threads, scratch, caller, programs)
            crafted_section(args.threads, scratch, caller, cases, selftest)
    except Setup as error:
        print(f'could not run: {error}', file=sys.stderr)
        return 2
    print('RESULT pass={PASS} fail={FAIL} info={INFO}'.format(**COUNTS))
    return 1 if COUNTS['FAIL'] else 0


if __name__ == '__main__':
    sys.exit(main())
