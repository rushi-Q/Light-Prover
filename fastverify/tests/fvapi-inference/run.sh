#!/bin/bash
# tests/fvapi-inference/run.sh [PKGROOT] - regression test of theorem inference and JSON parsing in tools/http/fvapi.py:
#   (1) theorem inference (--allow-theorem-inference) must read the source like Lean: a theorem hidden from the old regex
#       comment stripper by string literals (`def s1 := "/-"` ... `def s2 := "-/"`), by Lean's comment-opener quirk
#       (`/-/-/` closes), by a raw string r"\", by `2theorem`, ... is still counted -> two theorems -> NO-VERDICT;
#       sources the lexer cannot read exactly (divergent interpolated strings, macros, #eval, syntax quotations,
#       unterminated literals) -> NO-VERDICT; never a silently wrong single theorem;
#   (2) `@[simp] theorem easy_thm ...` (attributes, doc comments, modifiers) is inferred (was: REJECTED);
#   (3) a JSON body with a duplicate key (two "theorem" fields) is refused (was: last key wins).
#   also: `]'` / `='` tokens (g1), `--` after `/--` (4.33 vs 4.36+, d8), run_tac / by_elab / generators / the
#   meta-programming layer, named (Prop) instances; the safe-symbol set re-derived from the deployed token tables.
# Unit rows import fvapi.py of PKGROOT (default: the package containing this test); end-to-end rows (the reproduction
# case) run bin/fv init-challenge + fvserve + fvapi on
# 127.0.0.1 when the Lean 4.33.1 toolchain and bwrap are present (else one SKIP line). Rows 'PASS|FAIL|SKIP name: ...';
# last line 'RESULT pass=N fail=M'; exit 0 iff no FAIL. Env: E2E=0 skips the end-to-end rows; WORK=DIR (default /scratch).
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PKG=$(readlink -f "${1:-$HERE/../..}")
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }

# ---------- (a) unit rows: resolve_theorem_name / strict_json_loads of PKG's fvapi.py ----------
UNIT=$(python3 -I - "$PKG" "$HERE" <<'PY' 2>&1
import sys
pkg = sys.argv[1]
here = sys.argv[2]
sys.path.insert(0, pkg + "/tools/http")
sys.argv = [sys.argv[0]]
import fvapi  # noqa: E402
R = fvapi.resolve_theorem_name
E = "theorem easy_thm : True := trivial\n"
H = "theorem hard_thm : True := trivial\n"
NV, REJ = "NO-VERDICT", "REJECTED"
def LEAN(full):
    """a positive row's expectation derived from LEAN's full theorem list for that source
    (DeclaredTheorems.lean on 4.33.1 and 4.36.0, recorded in the row): the documented contract keeps the undotted names
    (dotted generated auxiliaries - S.mk.inj, t._simp_1, t._proof_N - are never inference targets); exactly one -> it"""
    import re as _re
    # only the GENERATED dotted forms are dropped; a user-declared dotted theorem stays (and then
    # makes the expectation NO-VERDICT, as fvapi answers)
    gen = _re.compile(r"\.(mk\.inj|mk\.injEq|mk\.sizeOf_spec|_simp_\d+(_\d+)*|_proof_\d+(_\d+)*|_auxLemma[.\w]*|eq_\d+|eq_def)$")
    u = [x for x in full if not gen.search(x)]
    return u[0] if len(u) == 1 else NV
assert LEAN(["Garden.four'", "easy_thm"]) == NV and LEAN(["easy_thm", "easy_thm._simp_1"]) == "easy_thm"
rows = [  # name, source, expected: a theorem name | NO-VERDICT | REJECTED
    ("evidence-string-literal-bypass", 'import Init\ndef s1 : String := "/-"\n' + H + 'def s2 : String := "-/"\n' + E, NV),
    ("control-two-theorems", "import Init\n" + H + E, NV),
    ("attr-simp", "import Init\n@[simp] " + E, "easy_thm"),
    ("attr-simp-deprecated-string", '@[simp, deprecated "x"] ' + E, "easy_thm"),   # (to_additive generates theorems, refused below)
    ("private", "private " + E, NV),   # Lean names it _private.<module>.0.easy_thm
    ("protected", "protected " + E, "easy_thm"),
    ("docstring-and-attr", "/-- the easy one -/\n@[simp]\n" + E, "easy_thm"),
    ("comment-opener-skips-a-char", "/-/-/ " + H.strip() + " -/\n" + E, NV),   # Lean: `/-/-/` is a whole comment
    ("nested-comment-hides", "/- a /- b -/ " + H.strip() + " -/\n" + E, "easy_thm"),
    ("raw-string-backslash", 'def s := r"\\"\n' + H + 'def t := "x"\n' + E, NV),
    ("raw-string-hashes", 'def s := r#"a"b -/ /-"#\n' + E, "easy_thm"),
    ("char-literal-quote", "def c := '\"'\n" + H + 'def d := "x"\n' + E, NV),
    ("interpolated-divergence", 'def s := s!"{"}"}"\n' + E, NV),
    ("interpolated-ok", 'def s (x : Nat) := s!"a{x}b"\n' + E, "easy_thm"),
    # `--` right after `/--`: comment in 4.33.1, doc text in 4.36+ (case d8) -> refused
    ("doc-comment-line-comment", "/-- -- -/\n" + H.strip() + " -/\n" + E, NV),
    ("doc-comment-d8", '/-- -- -/\ntheorem hard_thm : True := (fun _ => trivial) "-/"\n-- "\n' + E, NV),
    ("doc-comment-block-comment", "/-- /- x -/ y -/\n" + E, NV),
    ("doc-comment-nested-doc-ok", "/-- /-- x -/ y -/\n" + E, "easy_thm"),
    # core token `]'` (xs[i]'h): case g1 declares TWO theorems in Lean 4.33.1 / 4.36.0
    ("bracket-quote-g1", 'def String.pf (_ : String) : 0 < #[(1:Nat)].size := by decide\ndef a : Nat := #[(1:Nat)][0]\'"\'".pf\n'
                         + H + '-- "\n' + E, NV),
    ("eq-quote-mathlib-token", "def x := 1 ='a'\n" + E, NV),   # Mathlib token `='`
    ("getelem-ok", "def a : Nat := #[1][0]\n" + E, "easy_thm"),
    # code runners / generators / meta-programming layer; named instances count
    ("run_tac-refused", "theorem easy_thm : True := by\n  run_tac pure ()\n  trivial\n", NV),
    ("by_elab-refused", "def x : Nat := by_elab pure (Lean.mkNatLit 1)\n" + E, NV),
    ("to_additive-refused", "@[to_additive] " + E, NV),
    ("simproc-refused", "simproc foo (_) := fun _ => pure .continue\n" + E, NV),
    ("declare-refused", "declare_syntax_cat foo\n" + E, NV),
    ("meta-layer-refused", "open Lean Elab in\n" + E, NV),
    ("addDecl-namelit-refused", "def n := `Lean.addDecl\n" + E, NV),
    ("named-prop-instance-counts", "class C : Prop where h : True\ninstance hard_thm : C := ⟨trivial⟩\n" + E, NV),
    ("instance-priority-refused", "class C : Prop where h : True\ninstance (priority := low) hard_thm : C := ⟨trivial⟩\n" + E, NV),
    ("anonymous-prop-instance-counts", "class C : Prop where h : True\ninstance : C := ⟨trivial⟩\n" + E, NV),   # generated theorem name
    ("namespace-name", "namespace N\n" + E + "end N\n", NV),   # Lean: N.easy_thm (dotted: no inference target)
    ("namespace-closed", "namespace N\ntheorem h : True := trivial\nend N\n" + E, NV),   # two theorems: N.h, easy_thm
    ("root-name", "namespace N\ntheorem _root_.easy_thm : True := trivial\nend N\n", "easy_thm"),
    ("escaped-name", "theorem «easy_thm» : True := trivial\n", "easy_thm"),
    ("private-name", "private " + E, NV),   # kernel name _private.<module>.0.easy_thm
    ("guard-msgs-refused", "#guard_msgs (drop error) in\ntheorem ghost : Nat := 0\n" + E, NV),
    ("exit-refused", E + "#exit\n" + H, NV),
    ("module-refused", "module\n\n" + E, NV),
    ("bom-refused", "\ufeff" + E, NV),
    ("plain-brace-ok", 'def s := "{"\n' + E, "easy_thm"),
    ("plain-interp-ghost-not-counted", 'def s := "{theorem ghost}"\n' + E, "easy_thm"),
    ("fraction-in-string-no-crash", 'def s := "{1.2_}"\n' + E, "easy_thm"),
    ("event_parser-binder-ok", "theorem easy_thm (event_parser : True) : True := event_parser\n", "easy_thm"),
    ("lt-char-ok", "theorem easy_thm : 'a'<'b' := by decide\n", "easy_thm"),
    # the inferred name is Lean's exact name: trailing primes kept, «» decoded, digits kept; a name
    # fvapi cannot address (subscript, space, !, ?) -> NO-VERDICT, never a shortened spelling
    ("prime-name", "theorem qaAddZero' : 0 + 0 = 0 := rfl\n", "qaAddZero'"),
    # the exact reproduction attempt (sha256 bd712a3e...): Lean's name qaAddZero'
    ("evidence-attempt-prime-kept", "theorem qaAddZero' (n : Nat) : n + 0 = n := Nat.add_zero n\n", "qaAddZero'"),
    ("double-prime-name", "theorem foo'' : True := trivial\n", "foo''"),
    ("guillemet-prime-name", "theorem «foo'» : True := trivial\n", "foo'"),
    ("guillemet-space-name", "theorem «foo bar» : True := trivial\n", NV),
    ("digit-name", "theorem foo1 : True := trivial\n", "foo1"),
    ("subscript-name", "theorem foo₁ : True := trivial\n", NV),
    ("guillemet-subscript-name", "theorem «foo₁» : True := trivial\n", NV),
    ("bang-name", "theorem x! : True := trivial\n", NV),
    # section / end never take a keyword as their name; raw string after a symbol; generators with !/?
    ("section-keyword-s1", "section theorem hard_thm : True := trivial\n" + E, NV),
    ("noncomputable-section-keyword-s2", E + "noncomputable section theorem hard_thm : True := trivial\nend\n", NV),
    ("end-deriving-ed2", "structure Foo where\n  x : Nat\nsection\nend deriving instance Nonempty for Foo\n" + E, NV),
    ("end-modifier", "section\nend private theorem h : True := trivial\n" + E, NV),
    ("section-named-ok", "section S\n" + E + "end S\n", "easy_thm"),
    ("section-indented-name-refused", "section\n  S\n" + E + "end S\n", NV),
    ("namespace-keyword-refused", "namespace theorem\n" + E, NV),
    ("theorem-keyword-name-refused", "theorem theorem : True := trivial\n", NV),
    ("dot-theorem-dot1", "inductive Foo where\n  | «theorem»\ndef f : Foo := .theorem\n" + H, NV),   # refused
    ("raw-after-tilde", 'example : True := (fun _ => trivial) ([] ~r"\\" x")\n' + H + '-- "\n' + E, NV),
    ("raw-after-lt", 'def x := 1 <r"a"\n' + E, NV),
    ("simps-bang-refused", "@[simps!] def p : Nat × Nat := (1, 2)\n" + E, NV),
    ("simps-question-refused", "@[simps?] def p : Nat × Nat := (1, 2)\n" + E, NV),
    ("to_additive-question-refused", "@[to_additive?] " + E, NV),
    ("higher_order-refused", "@[higher_order h] " + E, NV),
    ("ext-attribute-counts-e1", "structure P : Prop where\n  x : True\n@[ext] theorem my_ext (a b : P) : a = b := rfl\n", NV),
    # attribute allow-list, rawIdent keywords, with_weak_namespace, lemma imports
    ("ellipsis-dot-theorem", "def f [Inhabited Nat] : Nat := 0\ndef r : Nat := f ..theorem hard_thm : True := trivial\n" + E, NV),
    ("pipe-dot-end", "structure S where\n  x : Nat\nnamespace N\ndef g (s : S) := s |>.end\n" + E, NV),
    ("ctor-section", "namespace N\ninductive Foo where\n  | section : Foo\nend N\n" + E, NV),
    ("prev-private", "structure S where\n  x : Nat\ndef x (s : S) : Nat := s |>.private\n" + E, NV),
    ("weak-namespace", "with_weak_namespace N " + E, NV),
    ("local-ext", "structure P : Prop where\n  x : True\n@[local ext] theorem my_ext (a b : P) : a = b := rfl\n", NV),
    ("scoped-ext", "structure P : Prop where\n  x : True\n@[scoped ext] theorem my_ext (a b : P) : a = b := rfl\n", NV),
    ("to_fun", "@[to_fun hard_thm] " + E, NV),
    ("attribute-to_set_notation", E + "attribute [to_set_notation] easy_thm\n", NV),
    ("unknown-attribute", "@[my_attr] " + E, NV),
    # both positive sources compile on Lean 4.33.1 / 4.36.0 (checked with DeclaredTheorems.lean)
    ("allowed-attributes", "@[simp high, deprecated \"x\" (since := \"2025\")] " + E, LEAN(["easy_thm", "easy_thm._simp_1"])),
    ("deprecated-attribute-exact", "@[deprecated \"x\" (since := \"2025\")] " + E, LEAN(["easy_thm"])),   # Lean's list = [easy_thm] exactly
    ("attribute-instance-ok", "class C : Prop where h : True\ntheorem c : C := ⟨trivial⟩\nattribute [local instance] c\n", "c"),
    ("batteries-submodule-lemma", "import Batteries.Logic\ndef f (lemma ghost : Nat) : Nat := «lemma» + ghost\n", NV),
    ("batteries-lemma-module", "import Batteries.Tactic.Lemma\nset_option lang.lemmaCmd true\nlemma easy_thm : True := trivial\n", "easy_thm"),
    # a named DATA instance is never the inferred theorem; `where` / `let rec` helpers are refused
    ("named-data-instance-only", "instance reviewDefault : Inhabited Nat := ⟨0⟩\n", NV),
    ("where-helper", "theorem sumFour : 2 + 2 = 4 := step\nwhere step : 2 + 2 = 4 := rfl\n", NV),
    ("let-rec", "theorem easy_thm : True :=\n  let rec h : True := trivial\n  h\n", NV),
    ("structure-where-ok", "structure S where\n  x : Nat\n" + E, LEAN(["S.mk.inj", "S.mk.injEq", "S.mk.sizeOf_spec", "easy_thm"])),
    ("hash-where-command", "theorem whereCommandReview : True := trivial\n#where\n", LEAN(["whereCommandReview"])),
    ("mathlib-submodule-lemma", "import Mathlib.Data.Nat.Basic\nlemma easy_thm : True := trivial\n", NV),
    ("ext-tactic-ok", "theorem easy_thm (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by ext x; exact h x\n", "easy_thm"),
    ("deriving-instance-ok", "structure S where x : Nat\nderiving instance Repr for S\n" + E, "easy_thm"),
    ("theorem-in-string", 'def s := "theorem hard_thm : True := trivial"\n' + E, "easy_thm"),
    ("theorem-in-line-comment", "-- " + H + E, "easy_thm"),
    ("theorem-in-doc-comment", "/-! " + H + "-/\n" + E, "easy_thm"),
    ("digit-adjacent-keyword", "def x := 2" + H + E, NV),
    ("macro-refused", 'macro "x" : term => `(1)\n' + E, NV),
    ("eval-refused", "#eval 1\n" + E, NV),
    ("syntax-quotation-refused", "def f := `(x)\n" + E, NV),
    ("unterminated-comment", E + "/- open", NV),
    ("unterminated-string", E + 'def s := "open', NV),
    ("plain-single", E, "easy_thm"),
    ("lemma-single-mathlib", "import Mathlib\nlemma easy_thm : True := trivial\n", "easy_thm"),
    ("lemma-without-mathlib-refused", "lemma easy_thm : True := trivial\n", NV),   # an identifier in core Lean
    ("crlf", E.replace("\n", "\r\n"), "easy_thm"),
    ("no-theorem", "example : True := trivial\n", NV),   # no check ran -> no verdict
    ("projection-index", "theorem easy_thm (h : True ∧ True) : True := h.1\n", "easy_thm"),
]
for name, src, want in rows:
    try:
        thm, v, why = R(src, allow_inference=True)
        got = thm if thm else v
    except Exception as e:   # noqa: BLE001
        got, why = "EXC", repr(e)
    print("%s u/%s: got %s want %s %s" % ("PASS" if got == want else "FAIL", name, got, want, ("(%s)" % why)[:120] if why else ""))
# explicit theorem: unchanged (no inference)
t = R('def s1 := "/-"\n' + H + 'def s2 := "-/"\n' + E, explicit_name="hard_thm", allow_inference=True)
print("%s u/explicit-theorem-unchanged: %r" % ("PASS" if t == ("hard_thm", None, None) else "FAIL", t))
# a trailing line feed is not part of a valid target name (explicit and custom-id)
t = R(E, explicit_name="easy_thm\n", allow_inference=True)
print("%s u/explicit-trailing-newline-refused: %r" % ("PASS" if t[0] is None and t[1] == NV else "FAIL", t))
t = R(E, custom_id="easy_thm\n", custom_id_is_theorem=True)
print("%s u/custom-id-trailing-newline-refused: %r" % ("PASS" if t[0] is None and t[1] == NV else "FAIL", t))
t = R(E, explicit_name="qaAddZero'", allow_inference=True)
print("%s u/explicit-prime-kept: %r" % ("PASS" if t == ("qaAddZero'", None, None) else "FAIL", t))
t = R(E, explicit_name="bad name", allow_inference=True)
print("%s u/explicit-bad-name: %r" % ("PASS" if t[1] == NV else "FAIL", t))
t = R(E)
print("%s u/inference-off-by-default: %r" % ("PASS" if t[1] == NV else "FAIL", t))
# case sets lexer-core/ (33 cases), lexer-short/ (20) and lexer-scopes/ (14), sha256-checked: the lexer gives
# Lean's answer (theorems Lean declares under user-chosen names; private / generated = null; dotted generated auxiliaries
# not listed, documented) or UNCLEAR - never a crash; inference infers a name only for exactly one plain undotted name
import hashlib, json as _json, os as _os
def _key(xs):
    return sorted(("\x00" if x is None else x) for x in xs) if isinstance(xs, list) else xs
for cset in ("lexer-core", "lexer-short", "lexer-scopes"):   # the three case sets (lexer-short: s1, s2, ed2, r1, h1, ...)
    cx = _os.path.join(here, cset)
    sums = dict((ln.split()[1], ln.split()[0]) for ln in open(_os.path.join(cx, "SHA256SUMS"), encoding="utf-8"))
    expd = _json.load(open(_os.path.join(cx, "expected.json"), encoding="utf-8"))
    for name in sorted(expd):
        fp = _os.path.join(cx, name + ".lean")
        raw = open(fp, "rb").read()
        if hashlib.sha256(raw).hexdigest() != sums.get(name + ".lean"):
            print("FAIL %s/%s: case file sha256 differs from SHA256SUMS" % (cset, name)); continue
        src = raw.decode("utf-8")
        try:
            got = fvapi.lean_declared_theorems(src)
        except fvapi.LeanSourceUnclear:
            got = "UNCLEAR"
        except Exception as e:   # noqa: BLE001
            got = "CRASH %s" % type(e).__name__
        want = expd[name]["want"]
        r = R(src, allow_inference=True)
        rv = r[0] if r[0] else r[1]
        single = isinstance(want, list) and len(want) == 1 and want[0] is not None and fvapi.fv_schema.validate_theorem_name(want[0], allow_dotted=False)
        ok_res = (rv == want[0]) if single else (rv == NV)
        print("%s %s/%s: lexer %s want %s; inference %s" % ("PASS" if _key(got) == _key(want) and ok_res else "FAIL", cset, name,
              _json.dumps(got, ensure_ascii=False), _json.dumps(want, ensure_ascii=False), rv))
# the attempt handler: an unresolved target is never REJECTED with trust 'sound' (no check ran)
import argparse as _ap
st = fvapi.ApiState(_ap.Namespace(fvserve_state="/nonexistent-fvserve-state", default_pset="p", max_body_bytes=2**20,
     max_source_bytes=2**16, max_batch=4, request_timeout=5, socket_timeout=5, header_timeout=5, body_timeout=5,
     max_concurrent=1, max_connections=8, custom_id_is_theorem=False, allow_theorem_inference=True, max_backend_concurrent=1,
     api_key_file=None, audit_log=None))
for name, src, thm in [("no-theorem", "example : True := trivial\n", None), ("unclear", "#eval 1\n" + E, None),
                       ("ambiguous", H + E, None), ("bad-explicit-name", E, "../x"), ("private-only", "private " + E, None)]:
    env, _ = st.verify_one("p", thm, src)
    good = env["verdict"] != "REJECTED" and env["trust"] != "sound" and env["reward"] == 0.0 and env["accepted"] is False
    print("%s attempt-handler/%s: verdict %s trust %s exit %s" % ("PASS" if good else "FAIL", name, env["verdict"], env["trust"], env.get("exit_code")))
# an explicit (supported path) target that is not a theorem of the problem set, or that fvserve refuses
# before any check, is NO-VERDICT with trust 'none' - never REJECTED
import tempfile as _tf, json as _j2
_sd = _tf.mkdtemp(prefix="z0310-state-", dir=_os.environ.get("WORK") or "/tmp")
_os.makedirs(_os.path.join(_sd, "psets", "p"))
open(_os.path.join(_sd, "psets", "p", "comparator.json"), "w").write(_j2.dumps({"theorem_names": ["easy_thm", "hard_thm"]}))
st2 = fvapi.ApiState(_ap.Namespace(fvserve_state=_sd, default_pset="p", max_body_bytes=2**20, max_source_bytes=2**16, max_batch=4,
      request_timeout=5, socket_timeout=5, header_timeout=5, body_timeout=5, max_concurrent=1, max_connections=8,
      custom_id_is_theorem=False, allow_theorem_inference=False, max_backend_concurrent=1, api_key_file=None, audit_log=None))
if hasattr(st2, "pset_theorems"):
    env, _ = st2.verify_one("p", "not_in_set", E)
    good = env["verdict"] == "NO-VERDICT" and env["trust"] == "none" and "not a theorem of problem set" in env["reason"]
    print("%s explicit-name/explicit-name-not-in-pset: %s %s %s" % ("PASS" if good else "FAIL", env["verdict"], env["trust"], env["reason"][:70]))
else:
    print("FAIL explicit-name/explicit-name-not-in-pset: no problem-set membership check (older fvapi)")
_orig = fvapi.fvserve.request
for wname, reply in [("fvserve-bad-name-REJECTED-word", {"verdict": "REJECTED", "why": "bad theorem name"}),
                     ("fvserve-unknown-pset", {"verdict": "NO-VERDICT", "why": "unknown problem set"})]:
    fvapi.fvserve.request = lambda *a, _r=reply, **k: dict(_r)
    try:
        env, _ = st2.verify_one("p", "easy_thm", E)
    finally:
        fvapi.fvserve.request = _orig
    good = env["verdict"] == "NO-VERDICT" and env["trust"] == "none"
    print("%s explicit-name/%s: %s %s" % ("PASS" if good else "FAIL", wname, env["verdict"], env["trust"]))
# only fvserve's EXACT gate text is a rejection (refusal/gate-reason-exact-kept below); a reply that
# merely starts with the gate's words is a refusal: NO-VERDICT, trust none (earlier versions kept it REJECTED)
fvapi.fvserve.request = lambda *a, **k: {"verdict": "REJECTED", "why": "REJECTED by the cross-version gate (rule)"}
try:
    env, _ = st2.verify_one("p", "easy_thm", E)
finally:
    fvapi.fvserve.request = _orig
print("%s service-errors/xversion-gate-prefix-only-refused: %s %s" % ("PASS" if (env["verdict"], env["trust"]) == ("NO-VERDICT", "none") else "FAIL",
      env["verdict"], env["trust"]))
# a NORMAL fvserve result also carries "why" (with id / batch / ...): it is passed through, never treated as a refusal
fvapi.fvserve.request = lambda *a, **k: {"id": 7, "pset": "p", "theorem": "easy_thm", "batch": 1, "batch_size": 1,
                                         "verdict": "ACCEPTED", "why": "check-sound.sh ACCEPTED", "total_s": 0.1}
try:
    env, _ = st2.verify_one("p", "easy_thm", E)
finally:
    fvapi.fvserve.request = _orig
print("%s explicit-name/normal-result-with-why-passed-through: %s (%s)" % ("PASS" if "refused the request" not in env["verdict_basis"]
      else "FAIL", env["verdict"], env["verdict_basis"][:60]))
# only batchverify's EXACT lookup refusal with no build is "no check ran"; the same text in a Lean error
# (copied into `why` by batchverify, with a build exit) stays a judged REJECTED with trust sound
for wname, reply, want in [
        ("lookup-refusal-no-build", {"id": 8, "pset": "p", "theorem": "easy_thm", "batch": 1, "batch_size": 1, "verdict": "REJECTED",
                                     "why": "not a theorem name of the problem set", "build_exit": None, "total_s": 0.1}, ("NO-VERDICT", "none")),
        ("forged-error-text-contains", {"id": 9, "pset": "p", "theorem": "easy_thm", "batch": 1, "batch_size": 1, "verdict": "REJECTED",
                                        "why": "error: not a theorem name of the problem set", "build_exit": 1, "total_s": 0.1}, ("REJECTED", "sound")),
        ("forged-error-text-exact-with-build", {"id": 10, "pset": "p", "theorem": "easy_thm", "batch": 1, "batch_size": 1, "verdict": "REJECTED",
                                                "why": "not a theorem name of the problem set", "build_exit": 1, "total_s": 0.1}, ("REJECTED", "sound"))]:
    fvapi.fvserve.request = lambda *a, _r=reply, **k: dict(_r)
    try:
        env, _ = st2.verify_one("p", "easy_thm", E)
    finally:
        fvapi.fvserve.request = _orig
    print("%s reply-mapping/%s: %s %s (want %s %s)" % ("PASS" if (env["verdict"], env["trust"]) == want else "FAIL", wname, env["verdict"],
          env["trust"], *want))
# a two-field reply is a refusal unless it is the cross-version gate's own reason with verdict REJECTED;
# refusals keep the caller's custom_id and are counted
for wname, reply, want in [("refusal-first-word-REJECTED", {"verdict": "REJECTED", "why": "REJECTED before checking: problem set unavailable"}, ("NO-VERDICT", "none")),
                           ("gate-reason-exact-kept", {"verdict": "REJECTED", "why": "REJECTED by the cross-version gate (a rule of the challenge release's own comparator fails)"}, ("REJECTED", "sound"))]:
    fvapi.fvserve.request = lambda *a, _r=reply, **k: dict(_r)
    try:
        env, _ = st2.verify_one("p", "easy_thm", E)
    finally:
        fvapi.fvserve.request = _orig
    print("%s refusal/%s: %s %s (want %s %s)" % ("PASS" if (env["verdict"], env["trust"]) == want else "FAIL", wname, env["verdict"], env["trust"], *want))
n0 = sum(st2.verdict_counts.values())
fvapi.fvserve.request = lambda *a, **k: {"verdict": "NO-VERDICT", "why": "queue full (9 attempts waiting): retry later"}
try:
    env, _ = st2.verify_one("p", "easy_thm", E, custom_id="job42")
finally:
    fvapi.fvserve.request = _orig
good = env["target"].get("custom_id") == "job42" and sum(st2.verdict_counts.values()) == n0 + 1 and env["trust"] == "none"
print("%s refusal/refusal-keeps-custom-id-and-counts: %s %s" % ("PASS" if good else "FAIL", env["target"], dict(st2.verdict_counts)))
# the answers produced before / instead of a backend reply keep the caller's custom_id and are
# counted too: a target not in the problem set, an unresolved target, a backend timeout, a backend error
import socket as _sock
def _raise_timeout(*a, **k):
    raise _sock.timeout("timed out")
def _raise_err(*a, **k):
    raise RuntimeError("backend down")
for wname, req, thm, src in [("not-in-pset", None, "not_in_set", E), ("unresolved-target", None, "../x", E),
                             ("timeout", _raise_timeout, "easy_thm", E), ("backend-error", _raise_err, "easy_thm", E)]:
    n0 = sum(st2.verdict_counts.values())
    if req is not None:
        fvapi.fvserve.request = req
    try:
        env, _ = st2.verify_one("p", thm, src, custom_id="job-" + wname)
    finally:
        fvapi.fvserve.request = _orig
    good = (env.get("target") or {}).get("custom_id") == "job-" + wname and sum(st2.verdict_counts.values()) == n0 + 1 \
        and env["verdict"] == "NO-VERDICT" and env["trust"] == "none"
    print("%s service-errors/%s-keeps-custom-id-and-counts: %s %s %s" % ("PASS" if good else "FAIL", wname, env["verdict"], env["trust"],
          (env.get("target") or {}).get("custom_id")))
# end to end through verify_one with inference on: the theorem sent to the backend is qaAddZero' (prime kept)
_seen = []
def _cap(state, req, timeout=None):
    _seen.append(req.get("theorem"))
    return {"id": 1, "pset": "p", "theorem": req.get("theorem"), "batch": 1, "batch_size": 1, "verdict": "ACCEPTED",
            "why": "check-sound.sh ACCEPTED", "total_s": 0.1}
fvapi.fvserve.request = _cap
try:
    env, _ = st.verify_one("p", None, "theorem qaAddZero' (n : Nat) : n + 0 = n := Nat.add_zero n\n")
finally:
    fvapi.fvserve.request = _orig
print("%s service-errors/inferred-prime-sent-to-backend: sent %r, target %r" % ("PASS" if _seen == ["qaAddZero'"] and
      env["target"].get("theorem") == "qaAddZero'" else "FAIL", _seen, env["target"].get("theorem")))
# the gate-service error reply (starts like the gate text) is a refusal; a FULL
# fvserve result without a judged verdict (service / worker error before the check) has trust 'none', on the item and on the
# batch aggregate (in-process HTTP server, fvserve.request replaced)
fvapi.fvserve.request = lambda *a, **k: {"verdict": "REJECTED", "why": "REJECTED by the cross-version gate service: checker unavailable before verification"}
try:
    env, _ = st2.verify_one("p", "easy_thm", E)
finally:
    fvapi.fvserve.request = _orig
print("%s service-errors/gate-service-unavailable-refused: %s %s" % ("PASS" if (env["verdict"], env["trust"]) == ("NO-VERDICT", "none") else "FAIL",
      env["verdict"], env["trust"]))
_svc_err = {"id": 5, "pset": "p", "theorem": "easy_thm", "batch": 4, "batch_size": 1, "queue_s": 0, "batch_s": 1,
            "verdict": "NO-VERDICT", "why": "service error: worker unavailable before build", "total_s": 1}
import threading as _th, urllib.request as _ur
st3 = fvapi.ApiState(_ap.Namespace(fvserve_state=_sd, default_pset="p", max_body_bytes=2**20, max_source_bytes=2**16, max_batch=4,
      request_timeout=5, socket_timeout=5, header_timeout=5, body_timeout=5, max_concurrent=2, max_connections=8,
      custom_id_is_theorem=False, allow_theorem_inference=False, max_backend_concurrent=1, api_key_file=None, audit_log=None,
      verbose=False))
_srv = fvapi.ThreadedHTTPServer(("127.0.0.1", 0), fvapi.ApiHandler); _srv.api = st3
_th.Thread(target=_srv.serve_forever, daemon=True).start()
fvapi.fvserve.request = lambda *a, **k: dict(_svc_err)
try:
    _rq = _ur.Request("http://127.0.0.1:%d/v1/verify/batch" % _srv.server_address[1], headers={"Content-Type": "application/json"},
                      data=_json.dumps({"items": [{"custom_id": "c1", "theorem": "easy_thm", "source": E}]}).encode())
    _bj = _json.loads(_ur.urlopen(_rq, timeout=60).read())
except Exception as _e:   # noqa: BLE001
    _bj = {"error": repr(_e)}
finally:
    fvapi.fvserve.request = _orig
    _srv.shutdown()
_it = (_bj.get("results") or [{}])[0]
print("%s service-errors/service-error-item-trust-none: %s %s" % ("PASS" if (_it.get("verdict"), _it.get("trust")) == ("NO-VERDICT", "none") else "FAIL",
      _it.get("verdict"), _it.get("trust")))
print("%s service-errors/service-error-batch-aggregate-none: %s" % ("PASS" if _bj.get("trust") == "none" else "FAIL", _bj.get("trust") or _bj.get("error")))
import shutil as _sh
_sh.rmtree(_sd, ignore_errors=True)
env, _ = st.verify_one("p", None, "@[simp] theorem easy_thm : True := trivial\n")   # inferred; the (absent) backend answers
print("%s attempt-handler/attr-simp-reaches-backend: %s %s" % ("PASS" if env["target"]["theorem"] == "easy_thm" and env["verdict"] == "NO-VERDICT" else "FAIL",
      env["verdict"], env["reason"][:60]))
# the backend-error answer of an inferred target keeps both labels, inside result-v1 (target allows extra
# members; the top level does not): schema-conformant envelope
_sch = _json.load(open(pkg + "/schemas/result-v1.schema.json", encoding="utf-8"))
_tops = set(_sch["properties"])
lab = (env.get("target") or {}).get("theorem_inference") == "experimental" and (env.get("target") or {}).get("theorem_inferred") is True
print("%s envelope/backend-error-keeps-inference-labels: %s" % ("PASS" if lab else "FAIL", env.get("target")))
# a REFUSED inference keeps the experimental-mode label but not the success flag / wording
for wname, srcx in [("no-theorem", "def d : Nat := 0\n"), ("ambiguous", H + E)]:
    envr, _ = st.verify_one("p", None, srcx)
    t_ = envr.get("target") or {}
    good = (envr["verdict"] == "NO-VERDICT" and t_.get("theorem_inference") == "experimental" and t_.get("theorem_inferred") is False
            and not any("inferred from the source" in w for w in envr.get("warnings") or []))
    print("%s refusal/refused-inference-not-flagged-inferred-%s: %s %s" % ("PASS" if good else "FAIL", wname, t_, envr.get("warnings")))
t = R("instance reviewDefault : Inhabited Nat := ⟨0⟩\n", allow_inference=True)
print("%s refusal/instance-only-advice: %r" % ("PASS" if t[1] == NV and "kind or its name cannot be determined" in t[2] else "FAIL", t[2][:80]))
t = R("namespace Garden\ntheorem four' : 2 + 2 = 4 := rfl\nend Garden\n", allow_inference=True)
print("%s refusal/dotted-name-advice: %r" % ("PASS" if t[1] == NV and "cannot address" in t[2] else "FAIL", t[2][:80]))
extra = sorted(set(env) - _tops)
errs = fvapi.fv_schema.validate_v1(env)
print("%s envelope/inferred-envelope-schema-v1: extra top-level %s, validate_v1 %s" % ("PASS" if not extra and not errs else "FAIL", extra, errs[:3]))
for name, raw, want_ok in [("dup-theorem-key", b'{"theorem":"hard_thm","theorem":"easy_thm","source":"x"}', False),
                           ("dup-nested-key", b'{"a":{"x":1,"x":2}}', False),
                           ("no-dup", b'{"theorem":"easy_thm","source":"x"}', True),
                           ("nan-still-refused", b'{"x":NaN}', False)]:
    try:
        fvapi.strict_json_loads(raw)
        got = True
    except ValueError:
        got = False
    print("%s j/%s: parsed=%s want %s" % ("PASS" if got == want_ok else "FAIL", name, got, want_ok))
PY
)
while IFS= read -r ln; do
  case "$ln" in
    PASS\ *) echo "$ln"; pass=$((pass+1));;
    FAIL\ *) echo "$ln"; fail=$((fail+1));;
    *) [ -n "$ln" ] && { echo "FAIL unit/harness: $ln"; fail=$((fail+1)); };;
  esac
done <<< "$UNIT"

# ---------- (a1) theorem inference is EXPERIMENTAL - the old flag name is refused, the new one announced ----------
if grep -q -- '--experimental-theorem-inference' "$PKG/tools/http/fvapi.py"; then
  out=$(timeout 30 python3 -I "$PKG/tools/http/fvapi.py" --fvserve-state /nonexistent --allow-theorem-inference --port 0 2>&1); rc=$?
  [ $rc = 2 ] && printf '%s' "$out" | grep -q 'experimental-theorem-inference' && ok flag/old-name-refused "exit 2, renamed (EXPERIMENTAL)" || ko flag/old-name-refused "exit $rc $(printf '%s' "$out" | tail -c 200)"
  python3 -I "$PKG/tools/http/fvapi.py" --help 2>&1 | tr -s ' \n' ' ' | grep -q 'EXPERIMENTAL, off by default' && ok flag/help-says-experimental "--help" || ko flag/help-says-experimental "--help lacks EXPERIMENTAL"
else ko flag/experimental "fvapi.py has no --experimental-theorem-inference (older fvapi)"; fi

# ---------- (a2) token tables: _LEAN_SAFE_BEFORE re-derived from the deployed toolchains (+ the Mathlib workspace) ----------
# TokenDump.lean dumps every token (global table + every scoped token) of `import Lean` (each registered
# toolchain) and of `import Mathlib` (FV_PACKAGES workspace, default the challenge workspace); no token may continue a
# character of _LEAN_SAFE_BEFORE with a quote, a backtick, `--`, `/-` or a raw-string opener, and every identifier-shaped
# token must be in _LEAN_KEYWORDS (a keyword is never a scope / declaration name). bwrap, no network. TOKENS=0 skips.
SAFE=$(python3 -I -c 'import sys; sys.path.insert(0, sys.argv[1] + "/tools/http"); sys.argv = sys.argv[:1]; import fvapi; print("".join(sorted(fvapi._LEAN_SAFE_BEFORE)))' "$PKG" 2>/dev/null)
tokcheck() {  # tokcheck NAME TOKFILE : "<ntokens> <offending tokens...>" (+ identifier-shaped tokens missing from _LEAN_KEYWORDS)
  python3 -I - "$2" "$SAFE" "$PKG" <<'PY2'
import sys
toks = [l.rstrip("\n") for l in open(sys.argv[1], encoding="utf-8") if l.rstrip("\n")]
safe = set(sys.argv[2])
sys.path.insert(0, sys.argv[3] + "/tools/http"); sys.argv = sys.argv[:1]
import fvapi
openers = ("--", "/-", 'r"', "r#")   # a raw-string opener too
bad = sorted(t for t in toks for k in range(len(t) - 1) if t[k] in safe and (t[k + 1] in "\"'`" or t[k + 1:k + 3] in openers))
kw = getattr(fvapi, "_LEAN_KEYWORDS", None)
if kw is not None:
    bad += sorted("KW:" + t for t in toks if fvapi._lean_id_first(t[0]) and all(fvapi._lean_id_rest(c) for c in t[1:]) and t not in kw)
print("%d %s" % (len(toks), " ".join(bad[:10])))
PY2
}
tokrun() {  # tokrun TCPREFIX OUT [LEAN_PATH_EXTRA] [MATHLIB]
  local D; D=$(mktemp -d "${WORK:-${TMPDIR:-/tmp}}/fvapi-inference-tok.XXXXXX"); cp "$HERE/TokenDump.lean" "$D/T.lean"
  [ -n "${4:-}" ] && sed -i 's/^import Lean$/import Mathlib/' "$D/T.lean"
  /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /tmp --dev /dev --proc /proc --bind "$D" "$D" \
    --clearenv --setenv PATH "$1/bin:/usr/bin:/bin" --setenv LEAN_PATH "${3:+$3:}$1/lib/lean" --setenv TOKOUT "$D/tokens.txt" \
    --setenv LANG C.UTF-8 --chdir "$D" -- "$1/bin/lean" "$D/T.lean" > "$D/log" 2>&1
  cp "$D/tokens.txt" "$2" 2>/dev/null; local rc=$?; rm -rf "$D"; return $rc
}
if [ "${TOKENS:-1}" = 0 ] || [ ! -x /usr/bin/bwrap ] || [ -z "$SAFE" ]; then echo "SKIP tokens: TOKENS=0, no bwrap, or fvapi without _LEAN_SAFE_BEFORE"
else
  TW=$(mktemp -d "${WORK:-${TMPDIR:-/tmp}}/fvapi-inference-tokens.XXXXXX")
  for v in 4.33.1 4.36.0 4.37.0-rc1; do
    P=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v"+sys.argv[2]]["prefix"])' "$PKG/config/components.json" "$v" 2>/dev/null)
    if [ -z "$P" ] || [ ! -x "$P/bin/lean" ]; then echo "SKIP tokens/core-$v: toolchain not present"; continue; fi
    if tokrun "$P" "$TW/core-$v.txt"; then r=$(tokcheck core "$TW/core-$v.txt"); n=${r%% *}; b=${r#* }
      [ -z "$b" ] && [ "$n" -gt 100 ] && ok "tokens/core-$v" "$n tokens, none continues a safe symbol with a quote/comment" || ko "tokens/core-$v" "$n tokens, offending: $b"
    else ko "tokens/core-$v" "token dump failed"; fi
  done
  WS=${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}
  P=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$PKG/config/components.json" 2>/dev/null)
  if [ -f "$WS/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ] && [ "$(cat "$WS/lean-toolchain" 2>/dev/null)" = "leanprover/lean4:v4.33.1" ] && [ -x "$P/bin/lean" ]; then
    LP=$(for d in "$WS"/.lake/packages/*/.lake/build/lib/lean; do printf '%s:' "$d"; done); LP=${LP%:}
    if tokrun "$P" "$TW/mathlib.txt" "$LP" mathlib; then r=$(tokcheck mathlib "$TW/mathlib.txt"); n=${r%% *}; b=${r#* }
      [ -z "$b" ] && [ "$n" -gt 1000 ] && ok "tokens/mathlib" "$n tokens (incl. scoped), none continues a safe symbol with a quote/comment" || ko "tokens/mathlib" "$n tokens, offending: $b"
    else ko "tokens/mathlib" "token dump failed"; fi
  else echo "SKIP tokens/mathlib: no built Mathlib workspace on 4.33.1 at $WS"; fi
  rm -rf "$TW"
fi

# ---------- (b) end-to-end rows: the reproduction case through bin/fv init-challenge + fvserve + fvapi ----------
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$PKG/config/components.json" 2>/dev/null)
if [ "${E2E:-1}" = 0 ]; then echo "SKIP e2e: E2E=0"
elif [ -z "$TC" ] || [ ! -x "$TC/bin/lean" ] || [ ! -x /usr/bin/bwrap ]; then echo "SKIP e2e: Lean 4.33.1 toolchain or bwrap not present"
else
  W=$(mktemp -d "${WORK:-${TMPDIR:-/tmp}}/fvapi-inference-e2e.XXXXXX")
  mkdir -p "$W/chal_src" "$W/empty_ws/.lake/packages"
  printf 'leanprover/lean4:v4.33.1\n' > "$W/chal_src/lean-toolchain"
  printf 'name = "ApiTest"\ndefaultTargets = ["ApiTest"]\n[[lean_lib]]\nname = "ApiTest"\n' > "$W/chal_src/lakefile.toml"
  printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n' > "$W/chal_src/lake-manifest.json"
  printf 'theorem easy_thm : True := by sorry\ntheorem hard_thm : False := by sorry\n' > "$W/chal_src/ApiTest.lean"
  printf '{"challenge_module":"ApiTest","solution_module":"ApiTest","theorem_names":["easy_thm","hard_thm"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}\n' > "$W/chal_src/comparator.json"
  if ! "$PKG/bin/fv" init-challenge "$W/chal_src" "$W/pinned_chal" --threads 4 --json > "$W/init.json" 2> "$W/init.err"; then
    ko e2e/setup "fv init-challenge failed: $(tail -c 300 "$W/init.err")"
  else
    PIN=$(awk '{print $1}' "$W/pinned_chal/challenge.export.sha256")
    python3 -I "$PKG/tools/fvserve/fvserve.py" serve --state "$W/fvs" --pset "p=$W/pinned_chal:$PIN" \
      --packages "$W/empty_ws" --toolchain "$TC" --fv "$PKG" --snapshot-header "import Init" --threads 4 --svc-check > "$W/fvs.log" 2>&1 &
    FVS_PID=$!
    for _ in $(seq 1 120); do grep -q '"ready"' "$W/fvs.log" 2>/dev/null && break; sleep 0.5; done
    INFER_FLAG=--allow-theorem-inference   # renamed; the old name is refused
    grep -q -- '--experimental-theorem-inference' "$PKG/tools/http/fvapi.py" && INFER_FLAG=--experimental-theorem-inference
    python3 -I "$PKG/tools/http/fvapi.py" --fvserve-state "$W/fvs" --default-pset p $INFER_FLAG --custom-id-is-theorem \
      --host 127.0.0.1 --port 0 > "$W/api.log" 2>&1 &
    API_PID=$!
    for _ in $(seq 1 60); do grep -q '"ready"' "$W/api.log" 2>/dev/null && break; sleep 0.25; done
    URL=$(python3 -I -c 'import json,sys; print(json.loads([l for l in open(sys.argv[1]) if "\"ready\"" in l][-1])["url"])' "$W/api.log" 2>/dev/null)
    if [ -z "$URL" ]; then
      ko e2e/setup "fvserve/fvapi did not start: $(tail -c 300 "$W/fvs.log") $(tail -c 300 "$W/api.log")"
    else
      E2EOUT=$(python3 -I - "$URL" <<'PY' 2>&1
import json, sys, urllib.error, urllib.request
url = sys.argv[1]
def post(raw):
    req = urllib.request.Request(url + "/v1/verify", data=raw, headers={"Content-Type": "application/json"}, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=300) as r:
            return r.status, json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        try:
            return e.code, json.loads(e.read().decode())
        except Exception:   # noqa: BLE001
            return e.code, {}
def row(name, cond, info):
    print("%s e2e/%s: %s" % ("PASS" if cond else "FAIL", name, json.dumps(info)[:220]))
def pick(j):
    return {k: j.get(k) for k in ("verdict", "accepted", "reward", "reason", "error") if k in j}
s, r = post(json.dumps({"source": "import Init\ntheorem hard_thm : True := trivial\ntheorem easy_thm : True := trivial\n"}).encode())
row("control-two-theorems-no-verdict", r.get("verdict") == "NO-VERDICT" and r.get("accepted") is False, pick(r))
src = 'import Init\ndef s1 : String := "/-"\ntheorem hard_thm : True := trivial\ndef s2 : String := "-/"\ntheorem easy_thm : True := trivial\n'
s, r = post(json.dumps({"source": src}).encode())
row("string-literal-bypass-no-verdict", r.get("verdict") == "NO-VERDICT" and r.get("accepted") is False and r.get("reward") == 0.0, pick(r))
s, r = post(json.dumps({"source": "import Init\n@[simp] theorem easy_thm : True := trivial\n"}).encode())
row("attr-simp-inferred-accepted", r.get("verdict") == "ACCEPTED" and r.get("accepted") is True, pick(r))
row("inferred-answer-labelled-experimental", (r.get("target") or {}).get("theorem_inference") == "experimental" and "theorem_inference" not in r,
    {"target": r.get("target")})
s, r = post(json.dumps({"theorem": "easy_thm", "source": "import Init\n@[simp] theorem easy_thm : True := trivial\n"}).encode())
row("explicit-theorem-accepted", r.get("verdict") == "ACCEPTED" and r.get("accepted") is True, pick(r))
row("explicit-answer-not-labelled", "theorem_inference" not in r and "theorem_inference" not in (r.get("target") or {}), {"target": r.get("target")})
# a batch item without custom_id: the generated item_<i> is never the target (fvapi runs with
# --custom-id-is-theorem too) - the item is inferred like the single request
req = urllib.request.Request(url + "/v1/verify/batch", data=json.dumps({"items": [{"source": "import Init\ntheorem easy_thm : True := trivial\n"}]}).encode(),
                             headers={"Content-Type": "application/json"}, method="POST")
with urllib.request.urlopen(req, timeout=300) as rr:
    bj = json.loads(rr.read().decode())
it0 = (bj.get("results") or [{}])[0]
req = urllib.request.Request(url + "/v1/verify/batch", data=json.dumps({"items": [{"pset": "nonexistent_pset", "theorem": "easy_thm", "source": "import Init\ntheorem easy_thm : True := trivial\n"}]}).encode(),
                             headers={"Content-Type": "application/json"}, method="POST")
with urllib.request.urlopen(req, timeout=300) as rr:
    bj2 = json.loads(rr.read().decode())
row("batch-unknown-pset-aggregate-trust-none", bj2.get("trust") == "none" and bj2.get("accepted_count") == 0, {"trust": bj2.get("trust"), "items": [x.get("trust") for x in bj2.get("results") or []]})
row("batch-without-custom-id-not-a-target", it0.get("verdict") == "ACCEPTED" and it0.get("theorem") == "easy_thm", {k: it0.get(k) for k in ("custom_id", "theorem", "verdict")})
# explicit name that is not a theorem of the problem set: NO-VERDICT, trust none (never REJECTED)
s, r = post(json.dumps({"theorem": "not_in_set", "source": "import Init\ntheorem not_in_set : True := trivial\n"}).encode())
row("explicit-name-not-in-pset-no-verdict", r.get("verdict") == "NO-VERDICT" and r.get("trust") == "none" and r.get("reward") == 0.0, dict(pick(r), trust=r.get("trust")))
# a proof whose Lean error IS the lookup-refusal text: judged, REJECTED with trust sound (not "no check ran")
s, r = post(json.dumps({"theorem": "easy_thm", "source": 'import Init\ntheorem easy_thm : True := by fail "not a theorem name of the problem set"\n'}).encode())
row("forged-lookup-text-stays-rejected", r.get("verdict") == "REJECTED" and r.get("trust") == "sound" and r.get("reward") == 0.0, dict(pick(r), trust=r.get("trust")))
s, r = post(json.dumps({"source": "import Init\ntheorem easy_thm : True := trivial\n"}).encode())
row("plain-single-inferred-accepted", r.get("verdict") == "ACCEPTED", pick(r))
s, r = post(b'{"theorem":"hard_thm","theorem":"easy_thm","source":"import Init\\ntheorem easy_thm : True := trivial\\n"}')
row("duplicate-json-key-refused", s == 400 and r.get("verdict") != "ACCEPTED", dict(pick(r), status=s))
# g1: Lean declares hard_thm AND easy_thm (core token `]'`); an earlier version inferred easy_thm -> ACCEPTED 1.0
g1 = ('import Init\ndef String.pf (_ : String) : 0 < #[(1:Nat)].size := by decide\ndef a : Nat := #[(1:Nat)][0]\'"\'".pf\n'
      'theorem hard_thm : True := trivial\n-- "\ntheorem easy_thm : True := trivial\n')
s, r = post(json.dumps({"source": g1}).encode())
row("bracket-quote-g1-no-verdict", r.get("verdict") == "NO-VERDICT" and r.get("accepted") is False and r.get("reward") == 0.0, pick(r))
s, r = post(json.dumps({"theorem": "easy_thm", "source": g1}).encode())
row("bracket-quote-g1-explicit-accepted", r.get("verdict") == "ACCEPTED", pick(r))
# s1: `section theorem hard_thm ...` - Lean declares both; an earlier version inferred easy_thm -> ACCEPTED 1.0
s1 = "import Init\nsection theorem hard_thm : True := trivial\ntheorem easy_thm : True := trivial\n"
s, r = post(json.dumps({"source": s1}).encode())
row("section-keyword-s1-no-verdict", r.get("verdict") == "NO-VERDICT" and r.get("accepted") is False and r.get("trust") == "none", dict(pick(r), trust=r.get("trust")))
PY
)
      while IFS= read -r ln; do
        case "$ln" in PASS\ *) echo "$ln"; pass=$((pass+1));; FAIL\ *) echo "$ln"; fail=$((fail+1));; *) [ -n "$ln" ] && { echo "FAIL e2e/harness: $ln"; fail=$((fail+1)); };; esac
      done <<< "$E2EOUT"
    fi
    python3 -I "$PKG/tools/fvserve/fvserve.py" stop --state "$W/fvs" > /dev/null 2>&1 || true
    kill "$API_PID" "$FVS_PID" 2>/dev/null; wait "$API_PID" "$FVS_PID" 2>/dev/null
  fi
  [ "${KEEP_WORK:-0}" = 1 ] || rm -rf "$W"
fi
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
