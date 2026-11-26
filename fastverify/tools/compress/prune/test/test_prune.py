#!/usr/bin/python3 -I
"""Regression tests of the closure pruner's planning rules + Lean 4 module-system / barrel-trimming / fixlake rules
on synthetic projects (no Lean needed).
Run: python3 -I fastverify/tools/compress/prune/test/test_prune.py   -> prints PASS/FAIL per case, exit 0 iff all pass."""
import os, sys, pickle, tempfile, subprocess, shutil, json

HERE = os.path.dirname(os.path.abspath(__file__))
PRUNE = os.path.join(HERE, '..', 'prune.py')
FIXLAKE = os.path.join(HERE, '..', 'fixlake.py')
sys.path.insert(0, os.path.join(HERE, '..'))
import leansrc

FILES = {
    'A': """import Mathlib

namespace Foo

def live1 : Nat := 1

def dead1 : Nat := 2

def Mt : Nat := 3

theorem dead_used_by_name : True := trivial

@[simp] theorem dead_simp : dead1 = 2 := rfl

private theorem dead_priv : True := trivial

theorem dead_chain_a : True := dead_chain_b

theorem dead_chain_b : True := trivial

end Foo
""",
    'B': """import A

namespace Bar

theorem live2 : Foo.live1 = 1 := by
  have := Foo.Mt⁻¹
  simp [dead_used_by_name]

end Bar
""",
    'C': """import A

namespace Gone

theorem dead_c : True := trivial

end Gone
""",
    'D': """import C

open Gone

theorem live3 : True := trivial
""",
    'E': """import A

open Foo hiding dead1

theorem live4 : True := trivial
""",
    'G': """import Mathlib

namespace Gone2

theorem dead_g : True := trivial

end Gone2
""",
    'F': """import G

open Gone2

namespace Gone2.Sub

theorem live5 : True := trivial

end Gone2.Sub
""",
    'Root': """import A
""",
    'U': """import A

namespace Uni

open Foo in
universe u in
theorem live_univ : True := trivial

end Uni
""",
    'Main': """import B
import U
import D
import E
import F

theorem target : True := trivial
""",
}

MODSYS_FILES = {
    'Pkg.Base': """module

@[expose] public def liveBase : Nat := 42

@[expose] public def deadExposed : Nat := 99

@[simp] public theorem deadSimpAttr : liveBase = 42 := rfl
""",
    'Pkg.EmptyMid': """module

public import Pkg.Base

public theorem deadMid : True := trivial
""",
    'Pkg.Live': """module

public import Pkg.EmptyMid

public theorem targetMod : liveBase = 42 := rfl
""",
    'Pkg.DeadSub': """module

public structure UnusedStruct where
  x : Nat

public theorem deadSubThm : True := trivial
""",
    'Pkg': """module

public import Pkg.Live
public import Pkg.DeadSub
""",
}


def build_index(files_dict, live_set, nss_dict, targets_list):
    consts = {}; ranges = {}; imps = {}
    for m, text in files_dict.items():
        lines = text.split('\n')
        cmds, code = leansrc.split_commands(lines)
        ns = leansrc.namespaces(cmds, code)
        cl = []; rl = []; ml = []
        for l in lines:
            toks = l.split()
            if 'import' in toks and toks[0] in ('import', 'public', 'private'):
                ml.append(toks[toks.index('import') + 1])
        for k, c in enumerate(cmds):
            if c.kind in ('def', 'theorem', 'structure') and c.name:
                full = (ns[k] + '.' if ns[k] else '') + c.name
                if 'private' in c.mods:
                    full = '_private.%s.0.%s' % (m, full)
                cl.append((full, 'd' if c.kind != 'theorem' else 't'))
                rl.append((full, c.text_start + 1, 0, c.end, 0))
        consts[m] = cl; ranges[m] = rl; imps[m] = ml
    return {'mods': imps, 'consts': consts, 'ranges': ranges, 'live': set(live_set), 'ext_live': 0,
            'targets': list(targets_list), 'hashes': {}, 'nss': dict(nss_dict)}


def main():
    tmp = tempfile.mkdtemp(prefix='p01-prunetest.')
    src = os.path.join(tmp, 'proj'); os.makedirs(os.path.join(src, 'src'))
    for m, t in FILES.items():
        open(os.path.join(src, 'src', m + '.lean'), 'w').write(t)
    open(os.path.join(src, 'lakefile.toml'), 'w').write('name = "t"\nsrcDir = "src"\n\n[[lean_lib]]\nname = "Root"\n')
    idx = os.path.join(tmp, 'idx.pkl')
    live0 = {'target', 'Bar.live2', 'Foo.live1', 'live3', 'live4', 'Gone2.Sub.live5', 'Uni.live_univ'}
    nss0 = {'Root': [], 'A': ['Foo'], 'B': ['Bar'], 'C': ['Gone'], 'D': [], 'E': [], 'G': ['Gone2'],
            'F': ['Gone2', 'Gone2.Sub'], 'Main': [], 'U': ['Uni']}
    pickle.dump(build_index(FILES, live0, nss0, ['target']), open(idx, 'wb'))
    ext = os.path.join(tmp, 'ext.txt'); open(ext, 'w').write('Nat\n')
    out = os.path.join(tmp, 'out'); rep = os.path.join(tmp, 'rep.json')
    r = subprocess.run([sys.executable, '-I', PRUNE, idx, src, out, '--drop-empty-modules', '--ext-namespaces', ext,
                        '--report', rep], capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stderr); print('FAIL run'); return 1
    deleted = set(l.split('\t')[2] for l in open(rep + '.deleted.tsv'))
    dropped = set(open(rep + '.dropped.txt').read().split())
    res = []
    def check(name, cond):
        res.append(cond); print(('PASS ' if cond else 'FAIL ') + name)

    check('dead decl without references is deleted', 'Foo.dead_chain_a' in deleted)
    check('chain of dead lemmas is deleted together (fixpoint)', 'Foo.dead_chain_b' in deleted)
    check('dead decl named in a surviving simp [..] is kept', 'Foo.dead_used_by_name' not in deleted)
    check("superscript is not an identifier char: Mt in 'Mt⁻¹' keeps Foo.Mt", 'Foo.Mt' not in deleted)
    check('dead decl with an attribute is kept', 'Foo.dead_simp' not in deleted)
    check('dead decl named by @[simp] lemma text / open hiding is kept', 'Foo.dead1' not in deleted)
    check('dead private decl is deleted', '_private.A.0.Foo.dead_priv' in deleted)
    check('live decl is kept', 'Foo.live1' not in deleted and 'Bar.live2' not in deleted)
    check("module whose only registration of an OPENED namespace (open Gone) would vanish is kept",
          'C' not in dropped)
    check('a Lake library root module (import-only) is never dropped', 'Root' not in dropped)
    check("a live theorem behind `open .. in` + `universe u in` prefixes keeps its module (D17: was classified 'universe')",
          'U' not in dropped and 'Uni.live_univ' not in deleted)
    check("an open BEFORE the file's own `namespace X.Sub` still needs X from an import (G kept)", 'G' not in dropped)
    oe = os.path.join(tmp, 'other.tsv')
    open(oe, 'w').write('E\t4\t4\tinsert_before\tTEST\texample : True := Foo.dead_chain_a\n')
    r = subprocess.run([sys.executable, '-I', PRUNE, idx, src, out + '2', '--drop-empty-modules', '--ext-namespaces',
                        ext, '--report', rep + '2', '--other-edits', oe], capture_output=True, text=True)
    deleted2 = set(l.split('\t')[2] for l in open(rep + '2.deleted.tsv'))
    check('--other-edits: a name used in another owner\'s replacement text is kept', 'Foo.dead_chain_a' not in deleted2)
    # D17: other-edits that ADD an import (P03 IMPORT-mode alias in D of a dead target in G that D cannot see in the
    # original graph): the new edge counts for visibility, so the target named in D's new text is kept
    check('dead_g is deleted without other edits (precondition)', 'Gone2.dead_g' in deleted)
    oe3 = os.path.join(tmp, 'other3.tsv')
    open(oe3, 'w').write('D\t2\t1\tinsert_before\tTEST\timport G\nD\t5\t5\treplace\tTEST\ttheorem live3 : True := Gone2.dead_g\n')
    r = subprocess.run([sys.executable, '-I', PRUNE, idx, src, out + '3', '--drop-empty-modules', '--ext-namespaces',
                        ext, '--report', rep + '3', '--other-edits', oe3], capture_output=True, text=True)
    deleted3 = set(l.split('\t')[2] for l in open(rep + '3.deleted.tsv'))
    check('--other-edits: a target made visible by an ADDED import and named in the new text is kept',
          'Gone2.dead_g' not in deleted3)
    ed = [l.rstrip('\n').split('\t') for l in open(rep + '.edits.tsv')]
    check('edit list has one delete per deleted decl', sum(1 for e in ed if e[3] == 'delete') == len(deleted))

    # --- D20 Module-System + Barrel-Trimming + Fixlake Tests ---
    msrc = os.path.join(tmp, 'mproj'); os.makedirs(msrc)
    for m, t in MODSYS_FILES.items():
        p = os.path.join(msrc, *m.split('.')) + '.lean'
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'w').write(t)
    # Add an unbuilt test file + secondary [[lean_exe]] with srcDir = "scripts"
    os.makedirs(os.path.join(msrc, 'PkgTests'))
    open(os.path.join(msrc, 'PkgTests.lean'), 'w').write('module\npublic import Pkg\n')
    open(os.path.join(msrc, 'lakefile.toml'), 'w').write(
        'name = "pkg"\ndefaultTargets = ["Pkg"]\ntestDriver = "PkgTests"\n\n'
        '[[lean_lib]]\nname = "Pkg"\n\n[[lean_lib]]\nname = "PkgTests"\n\n'
        '[[lean_exe]]\nname = "chk"\nsrcDir = "scripts"\nroot = "Check"\n'
    )
    midx = os.path.join(tmp, 'midx.pkl')
    pickle.dump(build_index(MODSYS_FILES, {'targetMod', 'liveBase'}, {m: [] for m in MODSYS_FILES}, ['targetMod']),
                open(midx, 'wb'))
    mout = os.path.join(tmp, 'mout'); mrep = os.path.join(tmp, 'mrep.json')
    r = subprocess.run([sys.executable, '-I', PRUNE, midx, msrc, mout, '--protect', 'Pkg',
                        '--only-protect-explicit', '--drop-unbuilt', '--trim-barrels', '--drop-empty-modules',
                        '--report', mrep], capture_output=True, text=True)
    check('module-system prune runs cleanly (rc=0)', r.returncode == 0)
    mdel = set(l.split('\t')[2] for l in open(mrep + '.deleted.tsv'))
    mdrop = set(open(mrep + '.dropped.txt').read().split())
    check('dead @[expose]-only decl is G1-deleted while @[simp] decl is kept',
          'deadExposed' in mdel and 'deadSimpAttr' not in mdel)
    check('emptied `module` file (Pkg.EmptyMid) is dropped (`module` in FILELOCAL)', 'Pkg.EmptyMid' in mdrop)
    live_txt = open(os.path.join(mout, 'Pkg', 'Live.lean')).read()
    live_lines = [x.strip() for x in live_txt.split('\n') if x.strip()]
    check('flattened `public import` stays AFTER `module` header and keeps `public import`',
          live_lines[:2] == ['module', 'public import Pkg.Base'])
    pkg_txt = open(os.path.join(mout, 'Pkg.lean')).read()
    check('--trim-barrels trims dead barrel import (Pkg.DeadSub) and drops unreachable file',
          'Pkg.DeadSub' not in pkg_txt and 'public import Pkg.Live' in pkg_txt
          and not os.path.exists(os.path.join(mout, 'Pkg', 'DeadSub.lean'))
          and not os.path.exists(os.path.join(mout, 'PkgTests.lean')))
    rf = subprocess.run([sys.executable, '-I', FIXLAKE, mout], capture_output=True, text=True)
    lf_after = open(os.path.join(mout, 'lakefile.toml')).read()
    check('fixlake preserves main library when [[lean_exe]] has srcDir="scripts" and drops missing testDriver/exe',
          rf.returncode == 0 and 'name = "Pkg"' in lf_after and 'PkgTests' not in lf_after and 'chk' not in lf_after)

    shutil.rmtree(tmp)
    print('ALL PASS' if all(res) else 'SOME FAILED')
    return 0 if all(res) else 1


if __name__ == '__main__':
    sys.exit(main())
