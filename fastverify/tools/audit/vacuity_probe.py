#!/usr/bin/python3 -I
"""vacuity_probe.py — Sandboxed kernel-certified dynamic vacuity, triviality & counterexample prober (D16).

Runs official `lean` strictly inside `bwrap --unshare-all` (no network, home hidden, clean env, read-only `/`,
toolchain and dependency packages) on a temporary copy of a challenge file appended with a MetaM + Kernel.addDecl
probe harness.

Every dynamic finding (`D01_CONTRADICTORY_PREMISES`, `D02a_UNUSED_HYPOTHESIS_PROOF`,
`D02b_TRIVIALLY_PROVABLE`, `D03_FALSIFIABLE_STATEMENT`) is accepted ONLY if the unmodified Lean kernel
(`Lean.addDecl`) accepts the synthesized proof term with zero `sorryAx` and only standard axioms
`{propext, Quot.sound, Classical.choice}` — guaranteeing 0% false positives on vacuity and refutation!
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time

BWRAP = "/usr/bin/bwrap"
STD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
_MOD_COMP = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*$")


def module_rel_parts(mod):
    """the path components of a Lean module name read from client source (an import
    line): dotted Lean identifier components only, else None. `import .var.tmp.X` made mod.replace(".", "/") start with
    '/', so os.path.join discarded the work / challenge directory and named a host path (existence oracle, -o outside)"""
    if not isinstance(mod, str) or not mod or not all(_MOD_COMP.match(c) for c in mod.split(".")):
        return None
    return mod.split(".")


def is_toolchain_dir(tc):
    """a Lean toolchain prefix (bin/lean + lib/lean): never e.g. ~/.elan (from a client
    lean-toolchain '..'), whose ro-bind would pierce bwrap's --tmpfs /home"""
    if not isinstance(tc, str) or not tc:
        return False
    r = os.path.realpath(tc)
    return os.path.isfile(os.path.join(r, "bin", "lean")) and os.path.isdir(os.path.join(r, "lib", "lean"))


def fv_paths():
    """the package's no-follow path primitives (tools/mcp/mcp_server.py beside this tools/audit directory)"""
    d = os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(__file__))), "mcp")
    if d not in sys.path:
        sys.path.insert(0, d)
    import mcp_server
    return mcp_server


def bwrap_cmd(tc, ro_paths, rw_paths, env_vars, chdir):
    cmd = [
        BWRAP,
        "--ro-bind", "/", "/",
        "--tmpfs", "/home",
        "--tmpfs", "/root",
        "--tmpfs", "/run/user",
        "--tmpfs", "/tmp",
        "--dir", "/tmp/home",
        "--tmpfs", "/run",
        "--tmpfs", "/var",
        "--dev", "/dev",
        "--proc", "/proc",
        "--clearenv",
        "--ro-bind", tc, tc,
    ]
    seen = {os.path.realpath(tc)}
    for p in ro_paths:
        rp = os.path.realpath(p)
        if rp not in seen and os.path.exists(rp):
            seen.add(rp)
            cmd += ["--ro-bind", rp, rp]
    for p in rw_paths:
        rp = os.path.realpath(p)
        cmd += ["--bind", rp, rp]
    env = {"PATH": f"{tc}/bin:/usr/bin:/bin", "HOME": "/tmp/home", "LANG": "C.UTF-8"}
    env.update(env_vars or {})
    for k, v in env.items():
        cmd += ["--setenv", k, str(v)]
    cmd += ["--unshare-all", "--die-with-parent", "--new-session", "--chdir", chdir, "--"]
    return cmd


def lake_packages_dir(ws):
    """the packages directory Lake uses for workspace ws: the manifest's packagesDir,
    else the lakefile.toml packagesDir, else .lake/packages (bin/fv's cli_packages checks every one of these and .lake/packages
    itself); an unusable value falls back to .lake/packages"""
    wsr = os.path.realpath(ws)
    pd = None
    try:
        with open(os.path.join(wsr, "lake-manifest.json"), encoding="utf-8") as f_:
            man = json.load(f_)
        pd = man.get("packagesDir") if isinstance(man, dict) else None
    except (OSError, ValueError):
        pd = None
    if not (isinstance(pd, str) and pd.strip()):
        try:
            with open(os.path.join(wsr, "lakefile.toml"), encoding="utf-8") as f_:
                m_ = re.search(r'(?m)^\s*packagesDir\s*=\s*"([^"\\]*)"\s*(#.*)?$', f_.read())
            pd = m_.group(1) if m_ else None
        except OSError:
            pd = None
    if not (isinstance(pd, str) and pd.strip()):
        pd = ".lake/packages"
    pd = pd[2:] if pd.startswith("./") else pd
    comps = pd.rstrip("/").split("/")
    if pd.startswith("/") or any(c in ("", ".", "..") for c in comps):
        pd = ".lake/packages"
    return os.path.join(wsr, pd)


def workspace_lean_path(ws):
    if not ws:
        return "", []
    pk = lake_packages_dir(ws)   # the directory Lake uses (checked by bin/fv's cli_packages)
    if not os.path.isdir(pk):
        return "", []
    entries = []
    for d in sorted(os.listdir(pk)):
        lib = os.path.join(pk, d, ".lake", "build", "lib", "lean")
        if os.path.isdir(lib):
            entries.append(lib)
    ws_lib = os.path.join(os.path.realpath(ws), ".lake", "build", "lib", "lean")
    if os.path.isdir(ws_lib):
        entries.append(ws_lib)
    return ":".join(entries), [os.path.realpath(ws)]


def extract_header(src_text):
    lines = src_text.splitlines()
    hdr = []
    for ln in lines:
        s = ln.strip()
        if not s or s.startswith("--"):
            continue
        if s.startswith("import "):
            hdr.append(" ".join(s.split()))
            continue
        break
    return tuple(hdr)


def normalize_module_source(src_text):
    """If source uses Lean 4.33+ `module` keyword, normalize to standard file mode so appended
    Lean MetaM probe commands can import `Lean` cleanly in the same compilation unit."""
    lines = src_text.splitlines()
    has_module_kw = False
    out = []
    in_block_comment = 0
    for ln in lines:
        s = ln.strip()
        in_block_comment += ln.count("/-") - ln.count("-/")
        if in_block_comment <= 0:
            in_block_comment = 0
            if s == "module":
                has_module_kw = True
                continue
            if has_module_kw:
                ln = re.sub(r"^(\s*)public\s+meta\s+import\b", r"\1import", ln)
                ln = re.sub(r"^(\s*)public\s+import\b", r"\1import", ln)
                ln = re.sub(r"^(\s*)meta\s+import\b", r"\1import", ln)
                if re.match(r"^\s*(@\[expose\]\s*)?public\s+section\s*$", ln):
                    ln = "section"
                elif re.match(r"^\s*public\s+meta\s+section\s*$", ln):
                    ln = "section"
        out.append(ln)
    # Insert `import Lean` right after existing imports if not already imported
    res_lines = []
    inserted = False
    last_imp = -1
    for idx, ln in enumerate(out):
        if re.match(r"^\s*import\s+", ln):
            last_imp = idx
    if last_imp >= 0:
        for idx, ln in enumerate(out):
            res_lines.append(ln)
            if idx == last_imp:
                res_lines.append("import Init")
                res_lines.append("import Lean")
                inserted = True
    if not inserted:
        res_lines = ["import Init", "import Lean"] + out
    return "\n".join(res_lines) + "\n"


LEAN_PROBE_HARNESS_TEMPLATE = r"""
section _FVAuditDynamicProbes
open Lean Elab Command Term Tactic Meta

private def _fvAllowedAxioms : List Name := [`propext, `Quot.sound, `Classical.choice]

private def _fvEmit (fields : List (String × Json)) : IO Unit :=
  IO.println ("FV_PROBE_JSON:" ++ (Json.mkObj fields).compress)

private partial def _fvCollectConsts (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => _fvCollectConsts a (_fvCollectConsts f acc)
  | .lam _ t b _ => _fvCollectConsts b (_fvCollectConsts t acc)
  | .forallE _ t b _ => _fvCollectConsts b (_fvCollectConsts t acc)
  | .letE _ t v b _ => _fvCollectConsts b (_fvCollectConsts v (_fvCollectConsts t acc))
  | .mdata _ b => _fvCollectConsts b acc
  | .proj _ _ b => _fvCollectConsts b acc
  | _ => acc

private def _fvIsImportedBase (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | none => false
    | some modName =>
      let s := modName.toString
      s == "Init" || s.startsWith "Init." ||
      s == "Std" || s.startsWith "Std." ||
      s == "Lean" || s.startsWith "Lean." ||
      s == "Mathlib" || s.startsWith "Mathlib." ||
      s == "Batteries" || s.startsWith "Batteries." ||
      s == "Aesop" || s.startsWith "Aesop." ||
      s == "Qq" || s.startsWith "Qq." ||
      s == "ProofWidgets" || s.startsWith "ProofWidgets." ||
      s == "Lake" || s.startsWith "Lake." ||
      s == "ImportGraph" || s.startsWith "ImportGraph." ||
      s == "Plausible" || s.startsWith "Plausible." ||
      s == "Cli" || s.startsWith "Cli."

private def _fvLocalDefTerms (env : Environment) (ty : Expr) : TermElabM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  let cs1 := _fvCollectConsts ty
  let mut cs := cs1
  for n in cs1 do
    if !_fvIsImportedBase env n && !n.isInternal then
      if let some (.defnInfo dv) := env.find? n then
        cs := _fvCollectConsts dv.value cs
  let mut out : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for n in cs do
    if !_fvIsImportedBase env n && !n.isInternal && !env.isProjectionFn n then
      let isInst ← Meta.isInstance n
      if !isInst then
        if let some (.defnInfo dv) := env.find? n then
          let cconsts := _fvCollectConsts dv.value
          if !cconsts.contains ``sorryAx && !cconsts.contains n then
            let idStx := mkIdent n
            let lem ← `(Lean.Parser.Tactic.simpLemma| $idStx:ident)
            out := out.push lem
  return out

private def _fvKernelCertify (lparams : List Name) (goalTy : Expr) (tacStx : TSyntax `tactic) (preIntro : Bool := true) :
    TermElabM (Option Expr) := do
  withoutModifyingEnv <| withoutModifyingState <| withCurrHeartbeats do
    tryCatchRuntimeEx
        (do
          let mvar ← mkFreshExprMVar (some goalTy) MetavarKind.syntheticOpaque
          let unsolved ← Tactic.run mvar.mvarId! do
            if preIntro then
              Tactic.liftMetaTactic1 fun mv => do
                let (_, mv') ← mv.intros
                return mv'
            evalTactic tacStx
          if !unsolved.isEmpty then
            return none
          let pf ← instantiateMVars mvar
          if pf.hasSorry || pf.hasExprMVar || pf.hasLevelMVar then
            return none
          let directConsts := _fvCollectConsts pf
          if directConsts.contains ``sorryAx then
            return none
          let decl := Declaration.thmDecl {
            name := `_fv_cert_check_decl
            levelParams := lparams
            type := goalTy
            value := pf
          }
          -- Official Lean kernel verification!
          addDecl decl
          -- Native transitive axiom check across the whole kernel Environment
          let usedAxioms ← Lean.collectAxioms `_fv_cert_check_decl
          for ax in usedAxioms do
            if !_fvAllowedAxioms.contains ax then
              return none
          return some pf)
        (fun _ => return none)

private def _fvRunTargetProbes (targetStr : String) : CommandElabM Unit := do
  let env ← getEnv
  let tname := targetStr.toName
  let some ci := env.find? tname
    | _fvEmit [("decl", Json.str targetStr), ("error", Json.str "not_found")]
      return
  liftTermElabM do
    let ty := ci.type
    let lps := ci.levelParams
    let ldefs ← _fvLocalDefTerms env ty
    let unfoldAll ← if ldefs.isEmpty then `(tactic| skip) else `(tactic| try simp only [$ldefs,*] at *)
    -- 1. Check Contradictory Premises (Vacuity): ∀ xs, False
    let (hasPropHyp, vacGoal, propHypCount, conclIsExists, conclIsIff) ← forallTelescope ty fun xs concl => do
      let mut nProp := 0
      for x in xs do
        let xty ← inferType x
        if (← isProp xty) then
          nProp := nProp + 1
      let vg ← mkForallFVars xs (mkConst ``False)
      let c := concl.consumeMData
      return (nProp != 0, vg, nProp, c.isAppOf ``Exists, c.isAppOf ``Iff)

    let vacTac ← `(tactic| (
      $unfoldAll:tactic;
      first
      | contradiction
      | trivial
      | omega
      | ((try subst_vars); omega)
      __EXTRA_VAC_TACS__
      | simp_all (config := { maxSteps := 400, maxDischargeDepth := 1 }) [$ldefs,*]
    ))
    if hasPropHyp then
      if let some _ ← _fvKernelCertify lps vacGoal vacTac true then
        _fvEmit [
          ("decl", Json.str targetStr),
          ("kind", Json.str "D01_CONTRADICTORY_PREMISES"),
          ("severity", Json.str "CRITICAL"),
          ("detail", Json.str s!"premises kernel-certifiably imply False ({propHypCount} hypothesis/es)")
        ]
        return

    -- 2. Check Falsifiability (Counterexample): ¬ ty (`negGoal` is already `Not ty`!)
    let negGoal := mkNot ty
    let falsTac ← `(tactic| (
      $unfoldAll:tactic;
      first
      | omega
      | decide
      | (intro _h_fv;
         first
         | (have _h1 := _h_fv 0; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 1; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 2; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 3; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 4; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 5; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 6; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 8; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 10; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 41; revert _h1; $unfoldAll:tactic; omega)
         | (have _h1 := _h_fv 0 0; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 0 1; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 1 1; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 1 2; revert _h1; $unfoldAll:tactic; first | omega | decide)
         | (have _h1 := _h_fv 2 2; revert _h1; $unfoldAll:tactic; first | omega | decide))
      __EXTRA_FALS_TACS__
    ))
    if let some _ ← _fvKernelCertify lps negGoal falsTac false then
      _fvEmit [
        ("decl", Json.str targetStr),
        ("kind", Json.str "D03_FALSIFIABLE_STATEMENT"),
        ("severity", Json.str "CRITICAL"),
        ("detail", Json.str "negation (¬ statement) is kernel-provable by small counterexample")
      ]
      return

    -- 3. Check Dropped-Hypothesis / Degenerate-Witness / Trivial Provability
    -- 3a. Can we prove conclusion while DROPPING ALL explicit proof hypotheses?
    if hasPropHyp then
      let strippedOpt ← forallTelescope ty fun xs concl => do
        let mut kept : Array Expr := #[]
        let mut droppedNames : Array String := #[]
        for i in [:xs.size] do
          let x := xs[i]!
          let ldecl ← x.fvarId!.getDecl
          let isP ← isProp ldecl.type
          let mut dep := concl.containsFVar x.fvarId!
          for j in [i+1:xs.size] do
            let laterDecl ← xs[j]!.fvarId!.getDecl
            if laterDecl.type.containsFVar x.fvarId! then
              dep := true
          if isP && ldecl.binderInfo.isExplicit && !dep then
            droppedNames := droppedNames.push ldecl.userName.toString
          else
            kept := kept.push x
        if droppedNames.isEmpty then
          return none
        else
          let g ← mkForallFVars kept concl
          return some (g, String.intercalate "," droppedNames.toList)

      if let some (strippedGoal, droppedStr) := strippedOpt then
        let degTac ← `(tactic| (
          $unfoldAll:tactic;
          first
          | rfl | trivial | omega | decide
          __EXTRA_DEG_TACS__
          | (exists 0 <;> $unfoldAll:tactic <;> first | done | omega | decide)
          | simp_all (config := { maxSteps := 400, maxDischargeDepth := 1 }) [$ldefs,*]
        ))
        if let some _ ← _fvKernelCertify lps strippedGoal degTac true then
          _fvEmit [
            ("decl", Json.str targetStr),
            ("kind", Json.str "D02a_PROVABLE_WITHOUT_HYPOTHESES"),
            ("severity", Json.str "HIGH"),
            ("detail", Json.str s!"conclusion is kernel-provable after dropping explicit hypothesis/es [{droppedStr}]")
          ]
          return

    -- 3b. Degenerate existential witness (`0`, `∅`, `{0}, {1}`, `(0, ⊥)`) or degenerate `False ↔ ∀ ...` (`p=q=2`)
    if conclIsExists || conclIsIff then
      let trivDegTac ← `(tactic| (
        $unfoldAll:tactic;
        first
        | (exists 0 <;> $unfoldAll:tactic <;> first | done | omega | decide)
        __EXTRA_TRIV_DEG_TACS__
      ))
      if let some _ ← _fvKernelCertify lps ty trivDegTac true then
        _fvEmit [
          ("decl", Json.str targetStr),
          ("kind", Json.str "D02b_DEGENERATE_WITNESS_PROVABLE"),
          ("severity", Json.str "HIGH"),
          ("detail", Json.str "statement is kernel-provable via degenerate witness (0 / ∅ / {0},{1} / p=q=2)")
        ]
        return

    let elemTac ← `(tactic| (
      $unfoldAll:tactic;
      first | rfl | trivial | omega | decide __EXTRA_ELEM_TACS__ | simp_all (config := { maxSteps := 400, maxDischargeDepth := 1 }) [$ldefs,*]
    ))
    if let some _ ← _fvKernelCertify lps ty elemTac true then
      _fvEmit [
        ("decl", Json.str targetStr),
        ("kind", Json.str "D02c_ELEMENTARY_TAUTOLOGY"),
        ("severity", Json.str "WARN"),
        ("detail", Json.str "statement is kernel-provable immediately by elementary automation")
      ]
      return

    _fvEmit [("decl", Json.str targetStr), ("kind", Json.str "CLEAN")]

__TARGET_CALLS__
end _FVAuditDynamicProbes
"""


def run_probes(
    challenge_lean,
    targets,
    toolchain,
    packages_ws=None,
    extra_lean_path="",
    extra_ro=(),
    timeout_s=45,
    conjecture_mode=False,
):
    t0 = time.time()
    if os.path.islink(challenge_lean):   # never probe through a link on the host
        return {"ran": False, "reason": f"source {challenge_lean} is a symlink (refused)", "wall_s": 0.0, "findings": []}
    if not is_toolchain_dir(toolchain):
        return {"ran": False, "reason": f"toolchain {toolchain!r} is not a Lean toolchain prefix (bin/lean + lib/lean)",
                "wall_s": 0.0, "findings": []}
    src_real = os.path.realpath(challenge_lean)
    if not os.path.isfile(src_real):
        return {"ran": False, "reason": f"missing source {challenge_lean}", "wall_s": 0.0, "findings": []}

    raw_src = open(src_real, encoding="utf-8", errors="replace").read()
    norm_src = normalize_module_source(raw_src)

    calls = []
    for t in targets:
        if not isinstance(t, str) or not t or any(ord(c) < 32 or ord(c) == 127 for c in t):
            continue   # a theorem name from client config with a control character is never probed
        esc = t.replace("\\", "\\\\").replace('"', '\\"')
        calls.append(f'set_option maxHeartbeats 400000 in\n#eval! show CommandElabM Unit from _fvRunTargetProbes "{esc}"')
    if not calls:
        return {"ran": False, "reason": "no targets", "wall_s": 0.0, "findings": []}

    has_mathlib = bool(packages_ws) and any(
        re.match(r"^\s*(?:public\s+)?import\s+(?:Mathlib|Batteries|Aesop)\b", ln)
        for ln in raw_src.splitlines()
    )
    if has_mathlib:
        extra_vac = "| ((try subst_vars); norm_num at *; done)\n      | (norm_num; done)"
        extra_fals = """| (norm_num; done)
      | (push_neg;
         first
         | (norm_num; done) | omega | decide
         | (refine ⟨0, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega | decide)
         | (refine ⟨1, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega | decide)
         | (refine ⟨2, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega | decide)
         | (refine ⟨3, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega | decide)
         | (refine ⟨4, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega | decide)
         | (refine ⟨5, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega | decide)
         | (refine ⟨41, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega)
         | (refine ⟨(-1), ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega)
         | (refine ⟨1, 1, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega | decide)
         | (refine ⟨1, 2, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega | decide)
         | (refine ⟨2, 2, ?_⟩ <;> $unfoldAll:tactic <;> first | done | (norm_num <;> done) | omega | decide))"""
        extra_deg = """| (norm_num; done) | (ring; done) | (tauto; done)
          | (exists 0, ⊥ <;> first | done | decide | (refine ⟨⟨⟨Fin.elim0, fun {_a} => Fin.elim0 _a⟩⟩, fun _v => Fin.elim0 _v⟩) | (intro _v; exact Fin.elim0 _v))
          | (refine ⟨∅, ?_⟩ <;> $unfoldAll:tactic <;> first | done | decide | (norm_num <;> done) | (simp (config := { maxSteps := 400 }) [$ldefs,*] <;> done))
          | (refine ⟨{0}, {1}, ?_⟩ <;> $unfoldAll:tactic <;> first | done | decide | (norm_num <;> done) | omega | (simp (config := { maxSteps := 400 }) [$ldefs,*] <;> done))"""
        extra_triv = """| (exists 0, ⊥ <;> first | done | decide | (refine ⟨⟨⟨Fin.elim0, fun {_a} => Fin.elim0 _a⟩⟩, fun _v => Fin.elim0 _v⟩) | (intro _v; exact Fin.elim0 _v))
        | (refine ⟨∅, ?_⟩ <;> $unfoldAll:tactic <;> first | done | decide | (norm_num <;> done) | (simp (config := { maxSteps := 400 }) [$ldefs,*] <;> done))
        | (refine ⟨{0}, ?_⟩ <;> $unfoldAll:tactic <;> first | done | decide | (norm_num <;> done) | omega | (simp (config := { maxSteps := 400 }) [$ldefs,*] <;> done))
        | (refine ⟨{0}, {1}, ?_⟩ <;> $unfoldAll:tactic <;> first | done | decide | (norm_num <;> done) | omega | (simp (config := { maxSteps := 400 }) [$ldefs,*] <;> done))
        | (constructor;
           · intro _h_f; cases _h_f
           · intro _h_all;
             exfalso;
             revert _h_all;
             $unfoldAll:tactic;
             change ¬ _;
             push_neg;
             first
             | (norm_num; done) | omega | decide
             | (refine ⟨0, ?_⟩ <;> first | done | (norm_num <;> done) | omega | decide)
             | (refine ⟨1, ?_⟩ <;> first | done | (norm_num <;> done) | omega | decide)
             | (refine ⟨2, ?_⟩ <;> first | done | (norm_num <;> done) | omega | decide)
             | (refine ⟨2, 2, ?_⟩ <;> first | done | (norm_num <;> done) | omega | decide | (refine ⟨by decide, by decide, ?_⟩; intro _n; omega)))"""
        extra_elem = "| (norm_num; done) | (ring; done) | (tauto; done)"
    else:
        extra_vac = ""
        extra_fals = ""
        extra_deg = ""
        extra_triv = ""
        extra_elem = ""

    harness = (
        LEAN_PROBE_HARNESS_TEMPLATE
        .replace("__EXTRA_VAC_TACS__", extra_vac)
        .replace("__EXTRA_FALS_TACS__", extra_fals)
        .replace("__EXTRA_DEG_TACS__", extra_deg)
        .replace("__EXTRA_TRIV_DEG_TACS__", extra_triv)
        .replace("__EXTRA_ELEM_TACS__", extra_elem)
        .replace("__TARGET_CALLS__", "\n".join(calls))
    )
    combined = norm_src + "\n" + harness

    tc_real = os.path.realpath(toolchain)
    tc_lib = os.path.join(tc_real, "lib", "lean")
    lp_ws, ro_ws = workspace_lean_path(packages_ws)
    lp_parts = [x for x in [tc_lib, lp_ws, extra_lean_path] if x]
    lean_path = ":".join(lp_parts)

    tmp_base = "/scratch" if os.path.isdir("/scratch") and os.access("/scratch", os.W_OK) else "/tmp"
    work = tempfile.mkdtemp(prefix="fvaudit-probe-", dir=tmp_base)
    try:
        probe_file = os.path.join(work, "_FVAuditProbeMain.lean")
        with open(probe_file, "w", encoding="utf-8") as f:
            f.write(combined)
        # Also copy sibling .lean files from the challenge directory (e.g. MainResults.lean if imported)
        cdir = os.path.dirname(src_real)
        for root_d, dns, fns in os.walk(cdir):
            dns[:] = [d for d in dns if d not in (".lake", ".git") and not os.path.islink(os.path.join(root_d, d))]
            rel_d = os.path.relpath(root_d, cdir)
            for fn in fns:
                sp = os.path.join(root_d, fn)
                if fn.endswith(".lean") and os.path.realpath(sp) != src_real:
                    # never follow a link on the host: only single-link regular files are
                    # copied (opened O_NOFOLLOW, re-checked with fstat); a symlink / hard link / special file is skipped
                    try:
                        fd = os.open(sp, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
                    except OSError:
                        continue
                    try:
                        fst = os.fstat(fd)
                        if not stat.S_ISREG(fst.st_mode) or fst.st_nlink != 1:
                            continue
                        dst_d = work if rel_d == "." else os.path.join(work, rel_d)
                        os.makedirs(dst_d, exist_ok=True)
                        with os.fdopen(os.dup(fd), "rb") as fi, open(os.path.join(dst_d, fn), "wb") as fo:
                            shutil.copyfileobj(fi, fo)
                    finally:
                        os.close(fd)

        tc_real = os.path.realpath(toolchain)
        lean_bin = os.path.join(tc_real, "bin", "lean")
        # If there are local sibling imports (like `import MainResults`), precompile them inside bwrap if needed
        local_imps = []
        for ln in norm_src.splitlines():
            m = re.match(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", ln)
            if m:
                mod = m.group(1)
                parts = module_rel_parts(mod)   # never a path outside work
                if parts is None:
                    return {"ran": False, "reason": f"invalid import module name {mod!r} (refused)",
                            "wall_s": round(time.time() - t0, 3), "findings": []}
                cand = os.path.join(work, *parts) + ".lean"
                if os.path.isfile(cand) and not os.path.islink(cand):
                    local_imps.append((mod, cand))

        lp_full = (lean_path + ":" + work) if lean_path else work
        ro_all = list(ro_ws) + list(extra_ro)
        for mod, cand in local_imps:
            ol = os.path.join(work, *mod.split(".")) + ".olean"
            os.makedirs(os.path.dirname(ol), exist_ok=True)
            argv_dep = bwrap_cmd(tc_real, ro_all, [work], {"LEAN_PATH": lp_full}, work) + [
                lean_bin, "-Dlinter.all=false", "-o", ol, cand
            ]
            subprocess.run(argv_dep, capture_output=True, text=True, env={}, timeout=timeout_s)

        argv = bwrap_cmd(tc_real, ro_all, [work], {"LEAN_PATH": lp_full}, work) + [
            lean_bin, "-Dlinter.all=false", probe_file
        ]
        try:
            p = subprocess.run(argv, capture_output=True, text=True, env={}, timeout=timeout_s)
            timed_out = False
            out_text = (p.stdout or "") + "\n" + (p.stderr or "")
            rc = p.returncode
        except subprocess.TimeoutExpired as e:
            timed_out = True
            so = e.stdout.decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
            se = e.stderr.decode("utf-8", "replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
            out_text = so + "\n" + se
            rc = 124

        findings = []
        probed_targets = 0
        for ln in out_text.splitlines():
            if "FV_PROBE_JSON:" in ln:
                js_part = ln.split("FV_PROBE_JSON:", 1)[1].strip()
                try:
                    rec = json.loads(js_part)
                except Exception:
                    continue
                probed_targets += 1
                kind = rec.get("kind", "")
                if kind and kind != "CLEAN":
                    sev = rec.get("severity", "WARN")
                    if kind == "D02c_ELEMENTARY_TAUTOLOGY" and conjecture_mode:
                        sev = "HIGH"
                    summaries = {
                        "D01_CONTRADICTORY_PREMISES": "Hypotheses are kernel-provably contradictory (`premises ⊢ False`) — theorem holds vacuously!",
                        "D03_FALSIFIABLE_STATEMENT": "Statement is kernel-provably FALSE (`⊢ ¬ statement` via small counterexample)!",
                        "D02a_PROVABLE_WITHOUT_HYPOTHESES": "Conclusion is kernel-provable while dropping explicit hypothesis/es (dead premise or degenerate witness)!",
                        "D02b_DEGENERATE_WITNESS_PROVABLE": "Statement is kernel-provable immediately via a degenerate witness (0 / ∅ / {0},{1} / p=q=2)!",
                        "D02c_ELEMENTARY_TAUTOLOGY": "Statement is proved immediately by elementary automation (<1s)",
                    }
                    findings.append({
                        "id": kind,
                        "severity": sev,
                        "source": "dynamic_kernel_probe",
                        "decl": rec.get("decl", ""),
                        "summary": summaries.get(kind, kind),
                        "detail": rec.get("detail", ""),
                    })

        err_ls = [ln for ln in out_text.splitlines() if ": error" in ln]
        return {
            "ran": probed_targets > 0,
            "timed_out": timed_out,
            "lean_rc": rc,
            "probed_targets": probed_targets,
            "wall_s": round(time.time() - t0, 4),
            "findings": findings,
            "log_tail": "\n".join(err_ls[:10] if err_ls else out_text.splitlines()[-15:]) if probed_targets == 0 else "",
        }
    finally:
        shutil.rmtree(work, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser(description="Sandboxed kernel-certified vacuity & counterexample prober")
    ap.add_argument("challenge_lean", help="Path to Challenge.lean")
    ap.add_argument("--targets", required=True, help="Comma/whitespace-separated target theorem names or file")
    ap.add_argument("--toolchain", required=True, help="Official Lean toolchain prefix")
    ap.add_argument("--packages", default=None, help="Trusted Lake workspace holding .lake/packages")
    ap.add_argument("--extra-lean-path", default="", help="Additional LEAN_PATH entries")
    ap.add_argument("--timeout", type=int, default=45, help="Wall timeout in seconds")
    ap.add_argument("--conjecture-mode", action="store_true", help="Treat elementary tautologies as HIGH severity")
    ap.add_argument("--json", default=None, help="Write JSON output to file")
    args = ap.parse_args()

    # the standalone prober reads a private no-follow copy of the challenge file's directory (.lean files only)
    # and writes --json without following links (bin/fv's local path policy, mcp_server.cli_roots)
    mp = fv_paths()
    roots = mp.cli_roots()
    ptmp = tempfile.mkdtemp(prefix="fvaudit-vp-in.")
    try:
        try:
            src = mp.client_abspath(args.challenge_lean, roots, must_exist=True, expect_dir=False, allow_dotdot=True)
            dfd = mp.open_nofollow_under(os.path.dirname(src), roots, want_dir=True)
            try:
                mp.copy_client_tree(dfd, os.path.join(ptmp, "c"), file_filter=lambda n: n.endswith(".lean"))
            finally:
                os.close(dfd)
            if args.targets and (os.sep in args.targets or os.path.lexists(args.targets)):
                tlist = mp.read_client_file(mp.local_path_under(args.targets, roots), roots, 4 << 20).decode(
                    "utf-8", "replace").split()
            else:
                tlist = args.targets.replace(",", " ").split()
            jout = mp.client_abspath(args.json, roots, must_exist=False, expect_dir=False, allow_dotdot=True) if args.json else None
            # the toolchain and packages dirs: no link at any component
            tcx = mp.client_abspath(args.toolchain, roots, must_exist=True, expect_dir=True, allow_dotdot=True)
            pkx = mp.client_abspath(args.packages, roots, must_exist=True, expect_dir=True, allow_dotdot=True) \
                if args.packages else None
        except (mp.ClientPathError, OSError) as e:
            print(json.dumps({"ran": False, "reason": f"refused: {e}", "findings": []}))
            sys.exit(2)
        res = run_probes(
            os.path.join(ptmp, "c", os.path.basename(src)),
            tlist,
            tcx,
            packages_ws=pkx,
            extra_lean_path=args.extra_lean_path,
            timeout_s=args.timeout,
            conjecture_mode=args.conjecture_mode,
        )
    finally:
        shutil.rmtree(ptmp, ignore_errors=True)
    js = json.dumps(res, indent=2, ensure_ascii=False)
    if jout:
        dfd = mp.open_nofollow_under(os.path.dirname(jout), roots, want_dir=True, create=True)
        try:
            mp.write_file_at(dfd, os.path.basename(jout), js + "\n")
        finally:
            os.close(dfd)
    print(js)


if __name__ == "__main__":
    main()
