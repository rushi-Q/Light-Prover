//! expaudit — kernel-AST statement fidelity & challenge anti-gaming auditor.
//!
//! Reads lean4export 3.x NDJSON exports using the parallel loader of kcompare/expdiff (std-only Rust,
//! zero external dependencies). Purely an analysis/audit tool outside the trusted kernel base.
//!
//! Modes:
//!   expaudit index-base [-j N] [-v] -o OUT.baseidx BASE.export
//!   expaudit [audit] [-j N] [-v] [--config COMPARATOR.json] [--targets FILE|A,B]
//!            [--base BASE.export] [--base-index BASE.baseidx]
//!            [--reading-set OUT.lean] [--json OUT.json] [--tsv OUT.tsv]
//!            [--fail-on WARN|HIGH|CRITICAL] CHALLENGE.export

#![allow(dead_code, unused_parens)]

include!("base.rs");

use std::io::{Read as IoRead, Write as IoWrite};
use std::sync::atomic::{AtomicUsize, Ordering};

const SEED1: u64 = 0x1234_5678_9abc_def1;
const SEED2: u64 = 0x0fed_cba9_8765_4321;
const BASE_MAGIC: &[u8; 8] = b"FVBASE01";

#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
struct D128(u64, u64);

struct Hashes {
    hn: Vec<u64>,
    he_alpha: Vec<u64>,
}

fn hashes(env: &Env, seed: u64) -> Hashes {
    let nn = env.names.len();
    let mut hn = vec![0u64; nn];
    hn[0] = hparts(seed, 1, &[]);
    for i in 1..nn {
        let r = env.names[i];
        let pre = hn[r.pre as usize];
        hn[i] = match env.comp_ref(i as u32) {
            CompRef::Str(b) => hparts(seed, 2, &[pre, hbytes(seed, &b)]),
            CompRef::Num(n) => hparts(seed, 3, &[pre, n]),
        };
    }
    let nl = env.levels.len();
    let mut hl = vec![0u64; nl];
    hl[0] = hparts(seed, 10, &[]);
    for i in 1..nl {
        let l = env.levels[i];
        hl[i] = match l.kind {
            L_SUCC => hparts(seed, 11, &[hl[l.a as usize]]),
            L_MAX => hparts(seed, 12, &[hl[l.a as usize], hl[l.b as usize]]),
            L_IMAX => hparts(seed, 13, &[hl[l.a as usize], hl[l.b as usize]]),
            L_PARAM => hparts(seed, 14, &[hn[l.a as usize]]),
            _ => hparts(seed, 10, &[]),
        };
    }
    let ne = env.exprs.len();
    let mut ha = vec![0u64; ne];
    let mut v: Vec<u64> = Vec::new();
    for i in 0..ne {
        let e = env.exprs[i];
        ha[i] = match e.kind {
            E_BVAR => hparts(seed, 20, &[e.a as u64 | ((e.b as u64) << 32)]),
            E_SORT => hparts(seed, 21, &[hl[e.a as usize]]),
            E_CONST => {
                v.clear();
                v.push(hn[e.a as usize]);
                for k in 0..e.c {
                    v.push(hl[env.pool[(e.b + k) as usize] as usize]);
                }
                hparts(seed, 22, &v)
            }
            E_APP => hparts(seed, 23, &[ha[e.a as usize], ha[e.b as usize]]),
            E_LAM | E_PI => {
                let tag = if e.kind == E_LAM { 24 } else { 25 };
                hparts(seed, tag, &[ha[e.a as usize], ha[e.b as usize]])
            }
            E_LET => hparts(seed, 26, &[ha[e.a as usize], ha[e.b as usize], ha[e.c as usize], e.flag as u64]),
            E_PROJ => hparts(seed, 27, &[hn[e.a as usize], e.c as u64, ha[e.b as usize]]),
            E_NAT => hparts(seed, 28, &[hbytes(seed, env.lit(&e))]),
            E_STR => {
                let raw = env.lit(&e);
                let b = if e.flag != 0 { decode_json_string(raw) } else { raw.to_vec() };
                hparts(seed, 29, &[hbytes(seed, &b)])
            }
            E_MDATA => ha[e.a as usize],
            _ => 0,
        };
    }
    Hashes { hn, he_alpha: ha }
}

fn decl_alpha(h: &Hashes, d: &Decl, seed: u64) -> u64 {
    let names = |v: &[u32]| -> Vec<u64> { v.iter().map(|&n| h.hn[n as usize]).collect() };
    let he = &h.he_alpha;
    let mut v = vec![h.hn[d.name as usize], hparts(seed, 40, &names(&d.lparams)), he[d.ty as usize]];
    match d.kind {
        D_AXIOM => v.push(d.is_unsafe as u64),
        D_DEFN => {
            v.extend([he[d.val as usize], d.hints_kind as u64, d.hints_val as u64, d.safety as u64]);
            v.push(hparts(seed, 41, &names(&d.all)));
        }
        D_THM => {
            v.push(he[d.val as usize]);
            v.push(hparts(seed, 41, &names(&d.all)));
        }
        D_OPAQUE => {
            v.extend([he[d.val as usize], d.is_unsafe as u64]);
            v.push(hparts(seed, 41, &names(&d.all)));
        }
        D_QUOT => v.push(d.quot_kind as u64),
        D_INDUCT => {
            v.extend(d.nums[..3].iter().copied());
            v.push(hparts(seed, 41, &names(&d.all)));
            v.push(hparts(seed, 42, &names(&d.ctors)));
            v.extend([d.is_rec as u64, d.is_unsafe as u64, d.is_reflexive as u64]);
        }
        D_CTOR => {
            v.push(h.hn[d.induct as usize]);
            v.extend(d.nums[..3].iter().copied());
            v.push(d.is_unsafe as u64);
        }
        D_REC => {
            v.push(hparts(seed, 41, &names(&d.all)));
            v.extend(d.nums.iter().copied());
            v.extend([d.k as u64, d.is_unsafe as u64]);
            for &(c, nf, rhs) in &d.rules {
                v.push(hparts(seed, 43, &[h.hn[c as usize], nf, he[rhs as usize]]));
            }
        }
        _ => {}
    }
    hparts(seed, 50 + d.kind as u64, &v)
}

struct EnvDigests {
    name: Vec<D128>,
    alpha: Vec<D128>,
    h1: Hashes,
}

fn compute_digests(env: &Env) -> EnvDigests {
    let (h1, h2) = std::thread::scope(|s| {
        let a = s.spawn(|| hashes(env, SEED1));
        let b = hashes(env, SEED2);
        (a.join().unwrap(), b)
    });
    let n = env.decls.len();
    let mut name = Vec::with_capacity(n);
    let mut alpha = Vec::with_capacity(n);
    for d in &env.decls {
        name.push(D128(h1.hn[d.name as usize], h2.hn[d.name as usize]));
        alpha.push(D128(decl_alpha(&h1, d, SEED1), decl_alpha(&h2, d, SEED2)));
    }
    EnvDigests { name, alpha, h1 }
}

// ---------------------------------------------------------------------------------------------------
// Base Index & Base Classification
// ---------------------------------------------------------------------------------------------------

fn is_auto_boilerplate_name(s: &str) -> bool {
    if s.starts_with("_private.") {
        return s.contains("._proof_") || s.contains(".proof_") || s.contains(".match_") || s.contains(".eq_");
    }
    let last = s.rsplit('.').next().unwrap_or(s);
    if last.starts_with("_proof_")
        || last.starts_with("proof_")
        || s.contains("._proof_")
        || last.starts_with("match_")
        || s.contains(".match_")
        || last.starts_with("eq_")
        || last == "eq_def"
        || last.starts_with("eq_unfold")
        || last == "congr_simp"
        || last.ends_with("_congr_simp")
        || last.starts_with("_sizeOf")
        || last.starts_with("_sunfold")
        || last.starts_with("_unary")
        || last.starts_with("_mutual")
    {
        return true;
    }
    matches!(
        last,
        "rec"
            | "recOn"
            | "casesOn"
            | "noConfusion"
            | "noConfusionType"
            | "below"
            | "brecOn"
            | "binductionOn"
            | "ibelow"
            | "inj"
            | "injEq"
            | "sizeOf_spec"
            | "ctorIdx"
            | "toCtorIdx"
            | "elim"
    )
}

fn is_generic_short_name(short: &str) -> bool {
    if short.len() < 5 || short.starts_with("inst") || short.starts_with('_') {
        return true;
    }
    matches!(
        short,
        "Config"
            | "State"
            | "Params"
            | "Param"
            | "Input"
            | "Output"
            | "Result"
            | "Error"
            | "Action"
            | "Entity"
            | "Context"
            | "Request"
            | "Response"
            | "Policy"
            | "Schema"
            | "Value"
            | "Header"
            | "Entry"
            | "Model"
            | "Problem"
            | "Instance"
            | "Witness"
            | "Solution"
            | "Challenge"
            | "Basic"
            | "Default"
            | "answer"
            | "count"
            | "index"
            | "length"
            | "width"
            | "depth"
            | "height"
            | "weight"
            | "score"
            | "valid"
            | "check"
            | "empty"
            | "start"
            | "total"
            | "bound"
            | "upper"
            | "lower"
            | "first"
            | "second"
            | "third"
            | "graph"
            | "edges"
            | "nodes"
            | "verts"
            | "color"
            | "field"
            | "group"
            | "space"
            | "point"
            | "curve"
            | "const"
            | "coeff"
            | "terms"
            | "level"
            | "stage"
            | "phase"
            | "trace"
            | "proof"
            | "lemma"
            | "claim"
    )
}

struct BaseLookup {
    mode: &'static str,
    by_name: FxMap<(u64, u64), (u64, u64, u8)>,
    short_defs: FxMap<u64, String>,
}

impl BaseLookup {
    fn from_env(b: &Env) -> Self {
        let bd = compute_digests(b);
        let mut by_name: FxMap<(u64, u64), (u64, u64, u8)> = FxMap::default();
        by_name.reserve(b.decls.len());
        let mut short_defs: FxMap<u64, String> = FxMap::default();
        for (i, d) in b.decls.iter().enumerate() {
            by_name.insert((bd.name[i].0, bd.name[i].1), (bd.alpha[i].0, bd.alpha[i].1, d.kind));
            if matches!(d.kind, D_DEFN | D_INDUCT) {
                let full = b.name_str(d.name);
                if !is_auto_boilerplate_name(&full) && !full.starts_with("_private.") {
                    let short = full.rsplit('.').next().unwrap_or(&full);
                    if !is_generic_short_name(short) {
                        let sh = hbytes(SEED1, short.as_bytes());
                        short_defs
                            .entry(sh)
                            .and_modify(|cur| {
                                if full.len() < cur.len() {
                                    *cur = full.clone();
                                }
                            })
                            .or_insert(full);
                    }
                }
            }
        }
        BaseLookup { mode: "exact_export", by_name, short_defs }
    }

    fn save_index(&self, path: &str) -> R<()> {
        let mut f = std::io::BufWriter::with_capacity(
            1 << 20,
            File::create(path).map_err(|e| Fail::Decline(format!("cannot create {}: {}", path, e)))?,
        );
        f.write_all(BASE_MAGIC).map_err(|e| Fail::Decline(e.to_string()))?;
        let n = self.by_name.len() as u64;
        f.write_all(&n.to_le_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
        for (&(nh0, nh1), &(ah0, ah1, kind)) in &self.by_name {
            f.write_all(&nh0.to_le_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
            f.write_all(&nh1.to_le_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
            f.write_all(&ah0.to_le_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
            f.write_all(&ah1.to_le_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
            let mut tail = [0u8; 8];
            tail[0] = kind;
            f.write_all(&tail).map_err(|e| Fail::Decline(e.to_string()))?;
        }
        let ns = self.short_defs.len() as u64;
        f.write_all(&ns.to_le_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
        for (&sh, s) in &self.short_defs {
            let bs = s.as_bytes();
            let len = bs.len().min(u16::MAX as usize) as u16;
            f.write_all(&sh.to_le_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
            f.write_all(&len.to_le_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
            f.write_all(&bs[..len as usize]).map_err(|e| Fail::Decline(e.to_string()))?;
        }
        f.flush().map_err(|e| Fail::Decline(e.to_string()))?;
        Ok(())
    }

    fn load_index(path: &str) -> R<Self> {
        let mut buf = Vec::new();
        File::open(path)
            .and_then(|mut f| f.read_to_end(&mut buf))
            .map_err(|e| Fail::Decline(format!("cannot read base index {}: {}", path, e)))?;
        if buf.len() < 16 || &buf[0..8] != BASE_MAGIC {
            decline!("invalid base index header in {}", path);
        }
        let n = u64::from_le_bytes(buf[8..16].try_into().unwrap()) as usize;
        let rec_end = 16usize.checked_add(n.checked_mul(40).ok_or_else(|| Fail::Decline("overflow".into()))?).unwrap();
        if buf.len() < rec_end + 8 {
            decline!("truncated base index {}", path);
        }
        let mut by_name: FxMap<(u64, u64), (u64, u64, u8)> = FxMap::default();
        by_name.reserve(n);
        let mut p = 16usize;
        for _ in 0..n {
            let nh0 = u64::from_le_bytes(buf[p..p + 8].try_into().unwrap());
            let nh1 = u64::from_le_bytes(buf[p + 8..p + 16].try_into().unwrap());
            let ah0 = u64::from_le_bytes(buf[p + 16..p + 24].try_into().unwrap());
            let ah1 = u64::from_le_bytes(buf[p + 24..p + 32].try_into().unwrap());
            let kind = buf[p + 32];
            by_name.insert((nh0, nh1), (ah0, ah1, kind));
            p += 40;
        }
        let ns = u64::from_le_bytes(buf[p..p + 8].try_into().unwrap()) as usize;
        p += 8;
        let mut short_defs: FxMap<u64, String> = FxMap::default();
        short_defs.reserve(ns);
        for _ in 0..ns {
            if p + 10 > buf.len() {
                decline!("truncated short table in {}", path);
            }
            let sh = u64::from_le_bytes(buf[p..p + 8].try_into().unwrap());
            let len = u16::from_le_bytes(buf[p + 8..p + 10].try_into().unwrap()) as usize;
            p += 10;
            if p + len > buf.len() {
                decline!("truncated short entry in {}", path);
            }
            let s = String::from_utf8_lossy(&buf[p..p + len]).into_owned();
            short_defs.insert(sh, s);
            p += len;
        }
        Ok(BaseLookup { mode: "exact_index", by_name, short_defs })
    }

    fn heuristic() -> Self {
        let mut short_defs: FxMap<u64, String> = FxMap::default();
        for &w in &[
            "RiemannHypothesis",
            "riemannZeta",
            "Prime",
            "Infinite",
            "Continuous",
            "Differentiable",
            "Measurable",
            "Integrable",
            "IsSimpleGroup",
            "IsCompact",
            "Connected",
            "Collinear",
            "FermatLastTheorem",
        ] {
            short_defs.insert(hbytes(SEED1, w.as_bytes()), w.to_string());
        }
        BaseLookup { mode: "namespace_heuristic", by_name: FxMap::default(), short_defs }
    }
}

fn is_heuristic_base_name(name: &str) -> bool {
    if [
        "._@.Init.",
        "._@.Std.",
        "._@.Lean.",
        "._@.Mathlib.",
        "._@.Batteries.",
        "._@.Aesop.",
        "._@.Lake.",
    ]
    .iter()
    .any(|m| name.contains(m))
    {
        return true;
    }
    let prefixes = [
        "Init.", "Std.", "Lean.", "Mathlib.", "Batteries.", "Aesop.", "Qq.", "Plausible.", "ProofWidgets.",
        "ImportGraph.", "Lake.", "Nat.", "Int.", "Rat.", "Real.", "Complex.", "ENNReal.", "NNReal.", "NNRat.",
        "Finset.", "Set.", "Multiset.", "List.", "Array.", "ByteArray.", "Substring.", "Vector.", "String.", "Char.",
        "Fin.", "ZMod.", "Bool.", "Option.", "Sum.", "Prod.", "Sigma.", "Subtype.", "Quot.", "Quotient.", "Classical.",
        "WellFounded.", "Function.", "Filter.", "Topology.", "MeasureTheory.", "Asymptotics.", "Polynomial.",
        "MvPolynomial.", "Matrix.", "LinearMap.", "Submodule.", "Ideal.", "Subgroup.", "SimpleGraph.", "CategoryTheory.",
        "Order.", "Lattice.", "WithTop.", "WithBot.", "Equiv.", "RingHom.", "MonoidHom.", "AddMonoidHom.",
        "MulAction.", "SubMulAction.", "DirichletCharacter.", "ArithmeticFunction.", "padicValNat.", "BitVec.",
        "UInt8.", "UInt16.", "UInt32.", "UInt64.", "USize.", "Float.", "IO.", "System.", "Task.",
        "Finsupp.", "Module.", "Algebra.", "Units.", "AddUnits.", "DivInvMonoid.", "SubNegMonoid.", "Small.", "UnivLE.",
    ];
    if prefixes.iter().any(|p| name.starts_with(p)) {
        return true;
    }
    let bare = [
        "Nat", "Int", "Rat", "Real", "Complex", "ENNReal", "NNReal", "NNRat", "Bool", "Prop", "True", "False", "And", "Or",
        "Not", "Iff", "Exists", "Eq", "Ne", "HEq", "LT", "LE", "GT", "GE", "HAdd", "HSub", "HMul", "HDiv", "HPow",
        "HMod", "HAnd", "HOr", "HXor", "HShiftLeft", "HShiftRight", "HAppend", "Add", "Sub", "Mul", "Div", "Mod", "Pow",
        "Neg", "Inv", "Zero", "One", "OfNat", "OfScientific", "NNRatCast", "RatCast", "IntCast", "NatCast",
        "Coe", "CoeTC", "CoeHTCT", "CoeDep", "CoeFun", "CoeSort", "OutParam", "SemiOutParam", "outParam", "semiOutParam",
        "optParam", "autoParam", "id", "Function", "Empty", "PEmpty", "Unit", "PUnit", "ULift", "PLift", "Quot",
        "Quotient", "Setoid", "Equivalence", "ByteArray", "Substring",
        "List", "Array", "String", "Char", "Fin", "Option", "Sum", "Prod", "Sigma", "PSigma", "Subtype", "PProd",
        "MProd", "Decidable", "DecidablePred", "DecidableRel", "DecidableEq", "BEq", "Hashable", "Ord", "Inhabited",
        "Nonempty", "Subsingleton", "Unique", "Fintype", "Finite", "Countable", "Encodable", "FunLike", "Set", "setOf",
        "Finset", "Multiset", "SimpleGraph", "Filter", "TopologicalSpace", "MetricSpace", "NormedAddCommGroup",
        "NormedSpace", "InnerProductSpace", "MeasureSpace", "MeasurableSpace", "Group", "AddGroup", "CommGroup",
        "AddCommGroup", "Monoid", "AddMonoid", "CommMonoid", "AddCommMonoid", "Semigroup", "AddSemigroup", "MulZeroClass",
        "Semiring", "CommSemiring", "Ring", "CommRing", "Field", "LinearOrder", "PartialOrder", "Preorder",
        "CompleteLattice", "ConditionallyCompleteLattice", "SupSet", "InfSet", "Max", "Min", "Bot", "Top",
        "Membership", "HasSubset", "HasSSubset", "Insert", "Singleton", "Union", "Inter", "SDiff", "Compl",
        "NeZero", "Fact", "ite", "dite", "decide", "eagerReduce", "mixHash", "propext", "sorryAx",
        "RiemannHypothesis", "riemannZeta", "UInt8", "UInt16", "UInt32", "UInt64", "USize",
    ];
    bare.iter().any(|&b| {
        name == b || (name.len() > b.len() && name.starts_with(b) && name.as_bytes()[b.len()] == b'.')
    })
}

// 0 = project, 1 = base, 2 = base-changed
fn classify_decls(env: &Env, dg: &EnvDigests, names_str: &[String], base: &BaseLookup) -> Vec<u8> {
    let mut cls = vec![0u8; env.decls.len()];
    if base.mode == "namespace_heuristic" {
        for (j, s) in names_str.iter().enumerate() {
            let root = if let Some(rest) = s.strip_prefix("_private.") {
                // _private.Mathlib.Foo.0.bar -> Mathlib.Foo...
                rest
            } else {
                s.as_str()
            };
            if is_heuristic_base_name(root) {
                cls[j] = 1;
            }
        }
    } else {
        for (j, n) in dg.name.iter().enumerate() {
            if let Some(&(ah0, ah1, _)) = base.by_name.get(&(n.0, n.1)) {
                cls[j] = if ah0 == dg.alpha[j].0 && ah1 == dg.alpha[j].1 { 1 } else { 2 };
            }
        }
    }
    cls
}

// ---------------------------------------------------------------------------------------------------
// Comparator Config Reader
// ---------------------------------------------------------------------------------------------------

#[derive(Default)]
struct CompConfig {
    challenge_module: Option<String>,
    solution_module: Option<String>,
    theorem_names: Vec<String>,
    definition_names: Vec<String>,
    permitted_axioms: Vec<String>,
    has_config: bool,
}

fn jp_str(jp: &JP, node: u32) -> R<String> {
    let nd = jp.nodes[node as usize];
    if nd.kind != J_STR {
        decline!("expected string in comparator config");
    }
    let raw = &jp.b[nd.s as usize..nd.e as usize];
    let bytes = if nd.esc { decode_json_string(raw) } else { raw.to_vec() };
    String::from_utf8(bytes).map_err(|_| Fail::Decline("invalid UTF-8 in comparator config".into()))
}

fn jp_str_arr(jp: &JP, node: u32) -> R<Vec<String>> {
    let nd = jp.nodes[node as usize];
    if nd.kind != J_ARR {
        decline!("expected string array in comparator config");
    }
    let mut out = Vec::new();
    let mut q = nd.first;
    while q != NONE {
        out.push(jp_str(jp, q)?);
        q = jp.nodes[q as usize].next;
    }
    Ok(out)
}

fn read_comp_config(path: &str) -> R<CompConfig> {
    let raw = std::fs::read(path).map_err(|e| Fail::Decline(format!("cannot read {}: {}", path, e)))?;
    let mut jp = JP::new();
    let root = jp.line(&raw).map_err(|e| Fail::Decline(format!("invalid JSON in {}: {}", path, e)))?;
    if jp.nodes[root as usize].kind != J_OBJ {
        decline!("comparator config {} must be a JSON object", path);
    }
    let mut cfg = CompConfig { has_config: true, ..Default::default() };
    let mut q = jp.nodes[root as usize].first;
    while q != NONE {
        let key = &jp.b[jp.nodes[q as usize].ks as usize..jp.nodes[q as usize].ke as usize];
        match key {
            b"challenge_module" => cfg.challenge_module = Some(jp_str(&jp, q)?),
            b"solution_module" => cfg.solution_module = Some(jp_str(&jp, q)?),
            b"theorem_names" => cfg.theorem_names = jp_str_arr(&jp, q)?,
            b"definition_names" => cfg.definition_names = jp_str_arr(&jp, q)?,
            b"permitted_axioms" => cfg.permitted_axioms = jp_str_arr(&jp, q)?,
            _ => {}
        }
        q = jp.nodes[q as usize].next;
    }
    Ok(cfg)
}

fn parse_targets_spec(spec: &str) -> R<Vec<String>> {
    let text = if std::path::Path::new(spec).is_file() {
        std::fs::read_to_string(spec).map_err(|e| Fail::Decline(format!("cannot read {}: {}", spec, e)))?
    } else {
        spec.replace(',', " ")
    };
    Ok(text.split_whitespace().map(String::from).collect())
}

// ---------------------------------------------------------------------------------------------------
// Pretty-printer & AST Utilities
// ---------------------------------------------------------------------------------------------------

fn kind_name(k: u8) -> &'static str {
    match k {
        D_AXIOM => "axiom",
        D_DEFN => "def",
        D_THM => "theorem",
        D_OPAQUE => "opaque",
        D_QUOT => "quot",
        D_INDUCT => "inductive",
        D_CTOR => "ctor",
        D_REC => "recursor",
        _ => "unknown",
    }
}

fn strip_mdata(env: &Env, mut e: u32) -> u32 {
    while env.exprs[e as usize].kind == E_MDATA {
        e = env.exprs[e as usize].a;
    }
    e
}

fn spine(env: &Env, mut e: u32, args: &mut Vec<u32>) -> u32 {
    args.clear();
    loop {
        e = strip_mdata(env, e);
        let x = env.exprs[e as usize];
        if x.kind != E_APP {
            break;
        }
        args.push(x.b);
        e = x.a;
    }
    args.reverse();
    e
}

fn pp_level(env: &Env, l: u32, out: &mut String) {
    let mut k = 0u32;
    let mut x = l;
    while env.levels[x as usize].kind == L_SUCC {
        k += 1;
        x = env.levels[x as usize].a;
    }
    let r = env.levels[x as usize];
    let base = match r.kind {
        L_ZERO => None,
        L_PARAM => Some(env.name_str(r.a)),
        L_MAX | L_IMAX => {
            let mut s = String::new();
            s.push_str(if r.kind == L_MAX { "max (" } else { "imax (" });
            pp_level(env, r.a, &mut s);
            s.push_str(") (");
            pp_level(env, r.b, &mut s);
            s.push(')');
            Some(s)
        }
        _ => None,
    };
    match base {
        None => out.push_str(&k.to_string()),
        Some(b) => {
            out.push_str(&b);
            if k > 0 {
                out.push_str(&format!("+{}", k));
            }
        }
    }
}

struct Pp<'a> {
    env: &'a Env,
    out: String,
    budget: isize,
    names: Vec<String>,
}

impl<'a> Pp<'a> {
    fn clean_bname(&self, n: u32) -> String {
        if n == NONE {
            return "_".into();
        }
        let s = self.env.name_str(n);
        let base = match s.find("._@.") {
            Some(i) => &s[..i],
            None => s.as_str(),
        };
        let base = match base.find("._hyg.") {
            Some(i) => &base[..i],
            None => base,
        };
        if base.is_empty() { "_".into() } else { base.to_string() }
    }

    fn unique_bname(&self, raw: String) -> String {
        if raw == "_" {
            return raw;
        }
        if !self.names.contains(&raw) {
            return raw;
        }
        let mut idx = 1usize;
        loop {
            let cand = format!("{}_{}", raw, idx);
            if !self.names.contains(&cand) {
                return cand;
            }
            idx += 1;
        }
    }

    fn expr(&mut self, e: u32) {
        if self.budget <= 0 {
            self.out.push_str("...");
            return;
        }
        self.budget -= 1;
        let env = self.env;
        let x = env.exprs[e as usize];
        match x.kind {
            E_BVAR => {
                let i = x.a as usize | ((x.b as usize) << 32);
                if i < self.names.len() {
                    let n = self.names[self.names.len() - 1 - i].clone();
                    self.out.push_str(&n);
                } else {
                    self.out.push_str(&format!("#{}", i));
                }
            }
            E_SORT => {
                let l = x.a;
                if env.levels[l as usize].kind == L_ZERO {
                    self.out.push_str("Prop");
                } else if env.levels[l as usize].kind == L_SUCC && env.levels[env.levels[l as usize].a as usize].kind == L_ZERO {
                    self.out.push_str("Type");
                } else {
                    self.out.push_str("Sort (");
                    pp_level(env, l, &mut self.out);
                    self.out.push(')');
                }
            }
            E_CONST => {
                self.out.push_str(&env.name_str(x.a));
            }
            E_APP => {
                let mut args = Vec::new();
                let h = spine(env, e, &mut args);
                // Readable sugar for common operators when argument count matches
                if env.exprs[h as usize].kind == E_CONST {
                    let hn = env.name_str(env.exprs[h as usize].a);
                    if hn == "Eq" && args.len() == 3 {
                        self.out.push('(');
                        self.expr(args[1]);
                        self.out.push_str(" = ");
                        self.expr(args[2]);
                        self.out.push(')');
                        return;
                    }
                    if hn == "Ne" && args.len() == 3 {
                        self.out.push('(');
                        self.expr(args[1]);
                        self.out.push_str(" ≠ ");
                        self.expr(args[2]);
                        self.out.push(')');
                        return;
                    }
                    if (hn == "And" || hn == "Or" || hn == "Iff") && args.len() == 2 {
                        let op = match hn.as_str() {
                            "And" => " ∧ ",
                            "Or" => " ∨ ",
                            _ => " ↔ ",
                        };
                        self.out.push('(');
                        self.expr(args[0]);
                        self.out.push_str(op);
                        self.expr(args[1]);
                        self.out.push(')');
                        return;
                    }
                    if hn == "Not" && args.len() == 1 {
                        self.out.push_str("¬ ");
                        self.expr(args[0]);
                        return;
                    }
                    if (hn == "LT.lt" || hn == "LE.le" || hn == "GT.gt" || hn == "GE.ge") && args.len() == 4 {
                        let op = match hn.as_str() {
                            "LT.lt" => " < ",
                            "LE.le" => " ≤ ",
                            "GT.gt" => " > ",
                            _ => " ≥ ",
                        };
                        self.out.push('(');
                        self.expr(args[2]);
                        self.out.push_str(op);
                        self.expr(args[3]);
                        self.out.push(')');
                        return;
                    }
                    if (hn == "HAdd.hAdd" || hn == "HSub.hSub" || hn == "HMul.hMul" || hn == "HDiv.hDiv" || hn == "HPow.hPow")
                        && args.len() == 6
                    {
                        let op = match hn.as_str() {
                            "HAdd.hAdd" => " + ",
                            "HSub.hSub" => " - ",
                            "HMul.hMul" => " * ",
                            "HDiv.hDiv" => " / ",
                            _ => " ^ ",
                        };
                        self.out.push('(');
                        self.expr(args[4]);
                        self.out.push_str(op);
                        self.expr(args[5]);
                        self.out.push(')');
                        return;
                    }
                    if hn == "OfNat.ofNat" && args.len() == 3 {
                        self.expr(args[1]);
                        return;
                    }
                    if hn == "Exists" && args.len() == 2 {
                        let lam = strip_mdata(env, args[1]);
                        if env.exprs[lam as usize].kind == E_LAM {
                            let lx = env.exprs[lam as usize];
                            let n = self.unique_bname(self.clean_bname(lx.c));
                            self.out.push_str("(∃ (");
                            self.out.push_str(&n);
                            self.out.push_str(" : ");
                            self.expr(lx.a);
                            self.out.push_str("), ");
                            self.names.push(n);
                            self.expr(lx.b);
                            self.names.pop();
                            self.out.push(')');
                            return;
                        }
                    }
                }
                self.out.push('(');
                self.expr(h);
                for a in args {
                    self.out.push(' ');
                    if self.budget <= 0 {
                        self.out.push_str("...");
                        break;
                    }
                    self.expr(a);
                }
                self.out.push(')');
            }
            E_LAM | E_PI => {
                // Non-dependent arrow A -> B when E_PI and bvar 0 not used in body
                if x.kind == E_PI && x.flag == 0 && !expr_uses_bvar(env, x.b, 0) {
                    self.out.push('(');
                    self.expr(x.a);
                    self.out.push_str(" → ");
                    self.names.push("_".into());
                    self.expr(x.b);
                    self.names.pop();
                    self.out.push(')');
                    return;
                }
                let (l, r) = match x.flag {
                    1 => ("{", "}"),
                    2 => ("⦃", "⦄"),
                    3 => ("[", "]"),
                    _ => ("(", ")"),
                };
                let raw = self.clean_bname(x.c);
                let n = self.unique_bname(if raw == "_" { "x".into() } else { raw });
                self.out.push_str(if x.kind == E_LAM { "(fun " } else { "(∀ " });
                self.out.push_str(&format!("{}{} : ", l, n));
                self.expr(x.a);
                self.out.push_str(r);
                self.out.push_str(if x.kind == E_LAM { " => " } else { ", " });
                self.names.push(n);
                self.expr(x.b);
                self.names.pop();
                self.out.push(')');
            }
            E_LET => {
                let raw = self.clean_bname(env.let_name.get(&e).copied().unwrap_or(NONE));
                let n = self.unique_bname(if raw == "_" { "h".into() } else { raw });
                self.out.push_str("(let ");
                self.out.push_str(&n);
                self.out.push_str(" : ");
                self.expr(x.a);
                self.out.push_str(" := ");
                self.expr(x.b);
                self.out.push_str("; ");
                self.names.push(n);
                self.expr(x.c);
                self.names.pop();
                self.out.push(')');
            }
            E_PROJ => {
                self.out.push('(');
                self.expr(x.b);
                self.out.push_str(&format!(").{}", x.c + 1));
            }
            E_NAT => self.out.push_str(&String::from_utf8_lossy(env.lit(&x))),
            E_STR => {
                self.out.push('"');
                self.out.push_str(&String::from_utf8_lossy(env.lit(&x)));
                self.out.push('"');
            }
            E_MDATA => self.expr(x.a),
            _ => self.out.push('?'),
        }
    }
}

fn pp_expr(env: &Env, e: u32, budget: isize, names: &[String]) -> String {
    let mut p = Pp { env, out: String::new(), budget, names: names.to_vec() };
    p.expr(e);
    p.out
}

// ---------------------------------------------------------------------------------------------------
// Loose Bound Variable Queries
// ---------------------------------------------------------------------------------------------------

fn expr_uses_bvar(env: &Env, root: u32, target_k: u32) -> bool {
    let mut memo: FxSet<(u32, u32)> = FxSet::default();
    let mut st: Vec<(u32, u32)> = vec![(root, target_k)];
    while let Some((e, k)) = st.pop() {
        let e = strip_mdata(env, e);
        if !memo.insert((e, k)) {
            continue;
        }
        let x = env.exprs[e as usize];
        match x.kind {
            E_BVAR => {
                let idx = x.a as u64 | ((x.b as u64) << 32);
                if idx == k as u64 {
                    return true;
                }
            }
            E_APP => {
                st.push((x.a, k));
                st.push((x.b, k));
            }
            E_LAM | E_PI => {
                st.push((x.a, k));
                st.push((x.b, k + 1));
            }
            E_LET => {
                st.push((x.a, k));
                st.push((x.b, k));
                st.push((x.c, k + 1));
            }
            E_PROJ => st.push((x.b, k)),
            _ => {}
        }
    }
    false
}

/// Collects which outer binder indices (0 = outermost in `depth` binders) occur free in `root`.
fn collect_outer_bvars(env: &Env, root: u32, outer_depth: usize, out: &mut FxSet<usize>) {
    let mut memo: FxSet<(u32, usize)> = FxSet::default();
    let mut st: Vec<(u32, usize)> = vec![(root, 0)];
    while let Some((e, inner)) = st.pop() {
        let e = strip_mdata(env, e);
        if !memo.insert((e, inner)) {
            continue;
        }
        let x = env.exprs[e as usize];
        match x.kind {
            E_BVAR => {
                let idx = x.a as usize | ((x.b as usize) << 32);
                if idx >= inner {
                    let rel = idx - inner;
                    if rel < outer_depth {
                        out.insert(outer_depth - 1 - rel);
                    }
                }
            }
            E_APP => {
                st.push((x.a, inner));
                st.push((x.b, inner));
            }
            E_LAM | E_PI => {
                st.push((x.a, inner));
                st.push((x.b, inner + 1));
            }
            E_LET => {
                st.push((x.a, inner));
                st.push((x.b, inner));
                st.push((x.c, inner + 1));
            }
            E_PROJ => st.push((x.b, inner)),
            _ => {}
        }
    }
}

/// Exact structural test for whether a type expression `ty` denotes a `Prop` (i.e. `ty : Prop`),
/// given `binder_types` of enclosing telescope binders (outermost first).
fn is_prop_valued_type(env: &Env, mut ty: u32, binder_types: &[u32]) -> bool {
    let mut extra_binders = 0usize;
    loop {
        ty = strip_mdata(env, ty);
        let x = env.exprs[ty as usize];
        match x.kind {
            E_PI => {
                extra_binders += 1;
                ty = x.b;
            }
            E_LET => {
                extra_binders += 1;
                ty = x.c;
            }
            E_SORT => {
                // Sort l has type Sort (l+1), which is NEVER Prop!
                return false;
            }
            _ => break,
        }
    }
    let mut args = Vec::new();
    let head = spine(env, ty, &mut args);
    let hx = env.exprs[head as usize];
    match hx.kind {
        E_CONST => {
            let r = env.canon[hx.a as usize];
            let di = env.decl_of[r as usize];
            if di == NONE {
                return false;
            }
            codomain_is_prop(env, env.decls[di as usize].ty)
        }
        E_BVAR => {
            let idx = hx.a as usize | ((hx.b as usize) << 32);
            if idx >= extra_binders {
                let rel = idx - extra_binders;
                if rel < binder_types.len() {
                    let bty = binder_types[binder_types.len() - 1 - rel];
                    return codomain_is_prop(env, bty);
                }
            }
            false
        }
        _ => false,
    }
}

/// Checks if a constant/binder's own type `kty` ends in `Sort 0` (`Prop`) after stripping `∀`s.
fn codomain_is_prop(env: &Env, mut kty: u32) -> bool {
    loop {
        kty = strip_mdata(env, kty);
        let x = env.exprs[kty as usize];
        match x.kind {
            E_PI => kty = x.b,
            E_LET => kty = x.c,
            E_SORT => return env.levels[x.a as usize].kind == L_ZERO,
            _ => return false,
        }
    }
}

// ---------------------------------------------------------------------------------------------------
// Statement Closure & DAG Metrics
// ---------------------------------------------------------------------------------------------------

fn dag_size_roots(env: &Env, roots: &[u32]) -> u64 {
    let mut vis: FxSet<u32> = FxSet::default();
    let mut st: Vec<u32> = roots.to_vec();
    let mut cnt = 0u64;
    while let Some(e) = st.pop() {
        if !vis.insert(e) {
            continue;
        }
        let x = env.exprs[e as usize];
        if x.kind != E_MDATA {
            cnt += 1;
        }
        match x.kind {
            E_APP | E_LAM | E_PI => {
                st.push(x.a);
                st.push(x.b);
            }
            E_LET => {
                st.push(x.a);
                st.push(x.b);
                st.push(x.c);
            }
            E_PROJ => st.push(x.b),
            E_MDATA => st.push(x.a),
            _ => {}
        }
    }
    cnt
}

fn stmt_closure(env: &Env, seed_decls: &[u32]) -> (Vec<bool>, Vec<Vec<u32>>) {
    let n = env.decls.len();
    let mut in_sc = vec![false; n];
    let mut deps: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut work: Vec<u32> = Vec::new();
    for &d in seed_decls {
        if !in_sc[d as usize] {
            in_sc[d as usize] = true;
            work.push(d);
        }
    }
    let mut st = Vec::new();
    while let Some(d) = work.pop() {
        let decl = &env.decls[d as usize];
        let mut vis = Bits::new(env.exprs.len());
        let mut found: FxSet<u32> = FxSet::default();
        let mut record = |nm: u32| -> R<()> {
            let r = env.canon[nm as usize];
            let di = env.decl_of[r as usize];
            if di != NONE && di != d {
                found.insert(di);
            }
            Ok(())
        };
        let _ = expr_consts(env, decl.ty, &mut vis, &mut st, &mut record);
        match decl.kind {
            D_DEFN | D_OPAQUE => {
                let _ = expr_consts(env, decl.val, &mut vis, &mut st, &mut record);
            }
            D_INDUCT => {
                for &c in decl.ctors.iter().chain(decl.all.iter()) {
                    let _ = record(c);
                }
            }
            D_CTOR => {
                let _ = record(decl.induct);
            }
            D_REC => {
                for &(c, _, rhs) in &decl.rules {
                    let _ = record(c);
                    let _ = expr_consts(env, rhs, &mut vis, &mut st, &mut record);
                }
            }
            _ => {}
        }
        let mut dv: Vec<u32> = found.into_iter().collect();
        dv.sort_unstable();
        for &di in &dv {
            if !in_sc[di as usize] {
                in_sc[di as usize] = true;
                work.push(di);
            }
        }
        deps[d as usize] = dv;
    }
    (in_sc, deps)
}

fn topo_sort_subset(sel: &[bool], deps: &[Vec<u32>], is_target: &[bool]) -> Vec<usize> {
    let n = sel.len();
    let mut state = vec![0u8; n];
    let mut order = Vec::new();
    // Visit non-targets first in index order, then targets last
    let mut seeds: Vec<usize> = (0..n).filter(|&i| sel[i] && !is_target[i]).collect();
    seeds.extend((0..n).filter(|&i| sel[i] && is_target[i]));
    let mut stack: Vec<(usize, bool)> = Vec::new();
    for s in seeds {
        if state[s] != 0 {
            continue;
        }
        stack.push((s, false));
        while let Some((u, done)) = stack.pop() {
            if done {
                if state[u] == 1 {
                    state[u] = 2;
                    order.push(u);
                }
                continue;
            }
            if state[u] != 0 {
                continue;
            }
            state[u] = 1;
            stack.push((u, true));
            for &v in deps[u].iter().rev() {
                let vu = v as usize;
                if sel[vu] && state[vu] == 0 {
                    stack.push((vu, false));
                }
            }
        }
    }
    order
}

// ---------------------------------------------------------------------------------------------------
// Static Fidelity & Anti-Gaming Lints
// ---------------------------------------------------------------------------------------------------

#[derive(Clone)]
struct Finding {
    id: &'static str,
    severity: &'static str, // CRITICAL, HIGH, WARN, INFO
    decl: String,
    summary: String,
    detail: String,
}

fn const_head_name<'a>(env: &'a Env, e: u32, names_str: &'a [String]) -> Option<(&'a str, usize)> {
    let e = strip_mdata(env, e);
    if env.exprs[e as usize].kind == E_CONST {
        let r = env.canon[env.exprs[e as usize].a as usize];
        let di = env.decl_of[r as usize];
        if di != NONE {
            return Some((names_str[di as usize].as_str(), di as usize));
        }
    }
    None
}

fn expr_nat_lit(env: &Env, e: u32) -> Option<u64> {
    let e = strip_mdata(env, e);
    let x = env.exprs[e as usize];
    if x.kind == E_NAT {
        return std::str::from_utf8(env.lit(&x)).ok()?.parse::<u64>().ok();
    }
    let mut args = Vec::new();
    let h = spine(env, e, &mut args);
    if env.exprs[h as usize].kind == E_CONST {
        let hn = env.name_str(env.exprs[h as usize].a);
        if hn == "OfNat.ofNat" && args.len() == 3 {
            return expr_nat_lit(env, args[1]);
        }
        if hn == "Nat.succ" && args.len() == 1 {
            return expr_nat_lit(env, args[0]).and_then(|v| v.checked_add(1));
        }
        if hn == "Nat.zero" && args.is_empty() {
            return Some(0);
        }
    }
    None
}

fn is_syntactically_nonzero(env: &Env, e: u32) -> bool {
    if let Some(n) = expr_nat_lit(env, e) {
        return n > 0;
    }
    let mut args = Vec::new();
    let h = spine(env, e, &mut args);
    if env.exprs[h as usize].kind != E_CONST {
        return false;
    }
    let hn = env.name_str(env.exprs[h as usize].a);
    match hn.as_str() {
        "Nat.succ" | "Real.pi" | "Real.exp" | "Complex.exp" | "Fintype.card" => true,
        "HPow.hPow" if args.len() == 6 => is_syntactically_nonzero(env, args[4]),
        "HMul.hMul" if args.len() == 6 => is_syntactically_nonzero(env, args[4]) && is_syntactically_nonzero(env, args[5]),
        "HAdd.hAdd" if args.len() == 6 => {
            // 1 + sq / n + 1 on Nat/NNReal
            let t = env.name_str(
                if env.exprs[strip_mdata(env, args[0]) as usize].kind == E_CONST {
                    env.exprs[strip_mdata(env, args[0]) as usize].a
                } else {
                    0
                },
            );
            (t == "Nat" || t == "NNReal" || t == "ENNReal" || t == "PNat")
                && (is_syntactically_nonzero(env, args[4]) || is_syntactically_nonzero(env, args[5]))
        }
        "Nat.cast" | "Int.cast" | "Rat.cast" if !args.is_empty() => is_syntactically_nonzero(env, *args.last().unwrap()),
        _ => false,
    }
}

/// Unwraps casts like `@Nat.cast ℝ _ x` or `@Int.cast ℝ _ x` to check if an expression is a bare bvar or `u - v`.
fn unwrap_casts(env: &Env, mut e: u32) -> u32 {
    loop {
        e = strip_mdata(env, e);
        let mut args = Vec::new();
        let h = spine(env, e, &mut args);
        if env.exprs[h as usize].kind == E_CONST && !args.is_empty() {
            let hn = env.name_str(env.exprs[h as usize].a);
            if matches!(
                hn.as_str(),
                "Nat.cast" | "Int.cast" | "Rat.cast" | "Real.cast" | "ENNReal.ofReal" | "NNReal.toReal" | "Subtype.val"
            ) {
                e = *args.last().unwrap();
                continue;
            }
        }
        return e;
    }
}

fn expr_mentions_sorry(env: &Env, root: u32) -> bool {
    let mut vis = Bits::new(env.exprs.len());
    let mut st = Vec::new();
    let mut hit = false;
    let _ = expr_consts(env, root, &mut vis, &mut st, &mut |nm| {
        if env.name_str(nm) == "sorryAx" {
            hit = true;
        }
        Ok(())
    });
    hit
}

/// Flattens top-level `And` conjuncts into `out`.
fn flatten_conjuncts(env: &Env, e: u32, out: &mut Vec<u32>) {
    let e = strip_mdata(env, e);
    let mut args = Vec::new();
    let h = spine(env, e, &mut args);
    if env.exprs[h as usize].kind == E_CONST && env.name_str(env.exprs[h as usize].a) == "And" && args.len() == 2 {
        flatten_conjuncts(env, args[0], out);
        flatten_conjuncts(env, args[1], out);
    } else {
        out.push(e);
    }
}

/// Checks if `hyp` is `¬ P` or `P → False`, returning `Some(P)`.
fn extract_negated(env: &Env, hyp: u32) -> Option<u32> {
    let hyp = strip_mdata(env, hyp);
    let mut args = Vec::new();
    let h = spine(env, hyp, &mut args);
    if env.exprs[h as usize].kind == E_CONST && env.name_str(env.exprs[h as usize].a) == "Not" && args.len() == 1 {
        return Some(strip_mdata(env, args[0]));
    }
    let hx = env.exprs[hyp as usize];
    if hx.kind == E_PI && !expr_uses_bvar(env, hx.b, 0) {
        let b = strip_mdata(env, hx.b);
        if env.exprs[b as usize].kind == E_CONST && env.name_str(env.exprs[b as usize].a) == "False" {
            return Some(strip_mdata(env, hx.a));
        }
    }
    None
}

/// Checks whether a guard hypothesis `hyp` (at binder depth `hyp_depth`) constrains any outer variable in `target_vars`.
fn hyp_guards_vars(env: &Env, hyp: u32, hyp_depth: usize, target_vars: &FxSet<usize>) -> bool {
    if target_vars.is_empty() {
        return false;
    }
    let mut hvars: FxSet<usize> = FxSet::default();
    collect_outer_bvars(env, hyp, hyp_depth, &mut hvars);
    if hvars.is_disjoint(target_vars) {
        return false;
    }
    // Check that `hyp` mentions an ordering / nonzero / membership / primality / lattice predicate
    let mut vis = Bits::new(env.exprs.len());
    let mut st = Vec::new();
    let mut guard_like = false;
    let _ = expr_consts(env, hyp, &mut vis, &mut st, &mut |nm| {
        let s = env.name_str(nm);
        if matches!(
            s.as_str(),
            "LT.lt"
                | "LE.le"
                | "GT.gt"
                | "GE.ge"
                | "Ne"
                | "Not"
                | "False"
                | "NeZero"
                | "Nat.Prime"
                | "Prime"
                | "Irreducible"
                | "IsUnit"
                | "Membership.mem"
                | "HasSubset.Subset"
                | "Set.Nonempty"
                | "Finset.Nonempty"
                | "BddAbove"
                | "BddBelow"
                | "StrictMono"
                | "StrictAnti"
                | "PosDef"
        ) {
            guard_like = true;
        }
        Ok(())
    });
    guard_like
}

#[allow(clippy::too_many_arguments)]
fn scan_expr_hazards(
    env: &Env,
    dg: &EnvDigests,
    decl_name: &str,
    e: u32,
    bnames: &mut Vec<String>,
    btypes: &mut Vec<u32>,
    b_is_pi: &mut Vec<bool>,
    leading_lam_as_pi: usize,
    hyps: &mut Vec<(u32, usize)>, // (hyp_expr, depth_when_added)
    in_attop: bool,
    parent_rel: bool, // directly an operand of <=, <, >=, >, =
    findings: &mut Vec<Finding>,
    seen_keys: &mut FxSet<(String, &'static str, u64)>,
) {
    let e = strip_mdata(env, e);
    let x = env.exprs[e as usize];
    match x.kind {
        E_PI => {
            let is_prop = is_prop_valued_type(env, x.a, btypes);
            // Scan binder domain first (not directly an inequality operand)
            scan_expr_hazards(
                env, dg, decl_name, x.a, bnames, btypes, b_is_pi, 0, hyps, in_attop, false, findings, seen_keys,
            );
            let bn = if x.c == NONE { "_".into() } else { env.name_str(x.c) };
            let cur_depth = bnames.len();
            let old_hlen = hyps.len();
            if is_prop || x.flag == 3 {
                let mut conjs = Vec::new();
                flatten_conjuncts(env, x.a, &mut conjs);
                for c in conjs {
                    hyps.push((c, cur_depth));
                }
            }
            bnames.push(bn);
            btypes.push(x.a);
            b_is_pi.push(true);
            scan_expr_hazards(
                env, dg, decl_name, x.b, bnames, btypes, b_is_pi, 0, hyps, in_attop, false, findings, seen_keys,
            );
            b_is_pi.pop();
            btypes.pop();
            bnames.pop();
            hyps.truncate(old_hlen);
        }
        E_LAM => {
            let is_prop = is_prop_valued_type(env, x.a, btypes);
            scan_expr_hazards(
                env, dg, decl_name, x.a, bnames, btypes, b_is_pi, 0, hyps, in_attop, false, findings, seen_keys,
            );
            let bn = if x.c == NONE { "_".into() } else { env.name_str(x.c) };
            let cur_depth = bnames.len();
            let old_hlen = hyps.len();
            if is_prop || x.flag == 3 {
                let mut conjs = Vec::new();
                flatten_conjuncts(env, x.a, &mut conjs);
                for c in conjs {
                    hyps.push((c, cur_depth));
                }
            }
            let treat_as_pi = leading_lam_as_pi > 0;
            let next_lam_as_pi = leading_lam_as_pi.saturating_sub(1);
            bnames.push(bn);
            btypes.push(x.a);
            b_is_pi.push(treat_as_pi);
            scan_expr_hazards(
                env, dg, decl_name, x.b, bnames, btypes, b_is_pi, next_lam_as_pi, hyps, in_attop, false, findings, seen_keys,
            );
            b_is_pi.pop();
            btypes.pop();
            bnames.pop();
            hyps.truncate(old_hlen);
        }
        E_LET => {
            scan_expr_hazards(
                env, dg, decl_name, x.a, bnames, btypes, b_is_pi, 0, hyps, in_attop, false, findings, seen_keys,
            );
            scan_expr_hazards(
                env, dg, decl_name, x.b, bnames, btypes, b_is_pi, 0, hyps, in_attop, false, findings, seen_keys,
            );
            let bn = env.let_name.get(&e).map(|&n| env.name_str(n)).unwrap_or_else(|| "h".into());
            bnames.push(bn);
            btypes.push(x.a);
            b_is_pi.push(false);
            scan_expr_hazards(
                env, dg, decl_name, x.c, bnames, btypes, b_is_pi, 0, hyps, in_attop, false, findings, seen_keys,
            );
            b_is_pi.pop();
            btypes.pop();
            bnames.pop();
        }
        E_APP => {
            let mut args = Vec::new();
            let h = spine(env, e, &mut args);
            let hn = if env.exprs[h as usize].kind == E_CONST {
                env.name_str(env.exprs[h as usize].a)
            } else {
                String::new()
            };

            // Conjunction `And P Q`: `P` guards `Q` (e.g. `x ≠ 0 ∧ 1 / x < 1` or `∃ n, n ≥ 2 ∧ 1 / (n - 1) < 1`)
            if hn == "And" && args.len() == 2 {
                scan_expr_hazards(
                    env, dg, decl_name, args[0], bnames, btypes, b_is_pi, 0, hyps, in_attop, false, findings, seen_keys,
                );
                let old_hlen = hyps.len();
                let cur_depth = bnames.len();
                let mut conjs = Vec::new();
                flatten_conjuncts(env, args[0], &mut conjs);
                for c in conjs {
                    hyps.push((c, cur_depth));
                }
                scan_expr_hazards(
                    env, dg, decl_name, args[1], bnames, btypes, b_is_pi, 0, hyps, in_attop, false, findings, seen_keys,
                );
                hyps.truncate(old_hlen);
                return;
            }

            // Check Exists-Implication: Exists α (fun x ... => P -> Q) where Q != False
            if hn == "Exists" && args.len() == 2 {
                let mut cur = strip_mdata(env, args[1]);
                let mut lam_names = bnames.clone();
                let mut lam_types = btypes.clone();
                let mut found_lam = false;
                while env.exprs[cur as usize].kind == E_LAM {
                    found_lam = true;
                    let lx = env.exprs[cur as usize];
                    lam_names.push(if lx.c == NONE { "x".into() } else { env.name_str(lx.c) });
                    lam_types.push(lx.a);
                    cur = strip_mdata(env, lx.b);
                }
                if found_lam && env.exprs[cur as usize].kind == E_PI {
                    let px = env.exprs[cur as usize];
                    if px.flag == 0 && !expr_uses_bvar(env, px.b, 0) && is_prop_valued_type(env, px.a, &lam_types) {
                        let cod = strip_mdata(env, px.b);
                        let cod_is_false = env.exprs[cod as usize].kind == E_CONST
                            && env.name_str(env.exprs[cod as usize].a) == "False";
                        if !cod_is_false && seen_keys.insert((decl_name.into(), "F08_EXISTS_IMPLICATION", dg.h1.he_alpha[e as usize])) {
                            findings.push(Finding {
                                id: "F08_EXISTS_IMPLICATION",
                                severity: "HIGH",
                                decl: decl_name.into(),
                                summary: "Existential quantifies over an implication (∃ x, P → Q) instead of a conjunction (∃ x, P ∧ Q)".into(),
                                detail: format!("subterm: {}", pp_expr(env, e, 48, bnames)),
                            });
                        }
                    }
                }
            }

            // Detect asymptotic `atTop` filter scope (Filter.Eventually / Tendsto / IsBigO / IsLittleO)
            let mut next_attop = in_attop;
            if matches!(
                hn.as_str(),
                "Filter.Eventually" | "Filter.Frequently" | "Filter.Tendsto" | "Asymptotics.IsBigO" | "Asymptotics.IsLittleO" | "Asymptotics.IsTheta"
            ) {
                for &a in &args {
                    let mut vis = Bits::new(env.exprs.len());
                    let mut st = Vec::new();
                    let _ = expr_consts(env, a, &mut vis, &mut st, &mut |nm| {
                        if env.name_str(nm) == "Filter.atTop" {
                            next_attop = true;
                        }
                        Ok(())
                    });
                }
            }

            // Skip Fin.mk / Fin.ofNat / Nat.choose arguments where truncating arithmetic is intentional or bounded
            if matches!(hn.as_str(), "Fin.mk" | "Nat.choose") {
                return;
            }

            // Track whether children are direct operands of a comparison/equality
            let is_rel = matches!(hn.as_str(), "LT.lt" | "LE.le" | "GT.gt" | "GE.ge" | "Eq" | "Ne");

            // F10a: Unguarded Nat subtraction (`HSub.hSub Nat ... a b` or `Nat.sub a b`)
            let nat_sub_pair = if hn == "Nat.sub" && args.len() == 2 {
                Some((args[0], args[1]))
            } else if hn == "HSub.hSub" && args.len() == 6 {
                let ty0 = strip_mdata(env, args[0]);
                if env.exprs[ty0 as usize].kind == E_CONST && env.name_str(env.exprs[ty0 as usize].a) == "Nat" {
                    Some((args[4], args[5]))
                } else {
                    None
                }
            } else {
                None
            };
            if let Some((lhs, rhs)) = nat_sub_pair {
                if expr_nat_lit(env, rhs) != Some(0) && !next_attop {
                    // Literal underflow e.g. 2 - 5 on Nat!
                    if let (Some(nl), Some(nr)) = (expr_nat_lit(env, lhs), expr_nat_lit(env, rhs)) {
                        if nl < nr && seen_keys.insert((decl_name.into(), "F10a_NAT_SUB_UNDERFLOW", dg.h1.he_alpha[e as usize])) {
                            findings.push(Finding {
                                id: "F10a_NAT_SUB_UNDERFLOW",
                                severity: "HIGH",
                                decl: decl_name.into(),
                                summary: format!("Literal Nat subtraction underflows to 0 ({} - {} = 0)", nl, nr),
                                detail: format!("subterm: {}", pp_expr(env, e, 40, bnames)),
                            });
                        }
                    } else {
                        let mut lvars = FxSet::default();
                        let mut rvars = FxSet::default();
                        collect_outer_bvars(env, lhs, bnames.len(), &mut lvars);
                        collect_outer_bvars(env, rhs, bnames.len(), &mut rvars);
                        // Only flag universal/parameter variables (`b_is_pi == true`), not Finset.sum/Set lambda variables
                        let uses_lam_binder = lvars.iter().chain(rvars.iter()).any(|&idx| !b_is_pi[idx]);
                        let pi_lvars: FxSet<usize> = lvars.into_iter().filter(|&idx| b_is_pi[idx]).collect();
                        let guarded = !pi_lvars.is_empty() && hyps.iter().any(|&(hp, hd)| hyp_guards_vars(env, hp, hd, &pi_lvars));
                        if !uses_lam_binder
                            && !pi_lvars.is_empty()
                            && !guarded
                            && seen_keys.insert((decl_name.into(), "F10a_NAT_SUB_UNGUARDED", dg.h1.he_alpha[e as usize]))
                        {
                            findings.push(Finding {
                                id: "F10a_NAT_SUB_UNGUARDED",
                                severity: "WARN",
                                decl: decl_name.into(),
                                summary: "Truncating Nat subtraction (a - b = 0 when a < b) with no ordering/positivity guard on `a` in scope".into(),
                                detail: format!("subterm: {}", pp_expr(env, e, 40, bnames)),
                            });
                        }
                    }
                }
            }

            // F10b: Truncating Nat division or Nat.sqrt directly in an inequality/equality bound
            let is_nat_div_or_sqrt = if hn == "Nat.sqrt" && args.len() == 1 {
                true
            } else if hn == "Nat.div" && args.len() == 2 {
                true
            } else if hn == "HDiv.hDiv" && args.len() == 6 {
                let ty0 = strip_mdata(env, args[0]);
                env.exprs[ty0 as usize].kind == E_CONST && env.name_str(env.exprs[ty0 as usize].a) == "Nat"
            } else {
                false
            };
            if is_nat_div_or_sqrt && parent_rel && seen_keys.insert((decl_name.into(), "F10b_NAT_TRUNC_IN_BOUND", dg.h1.he_alpha[e as usize])) {
                findings.push(Finding {
                    id: "F10b_NAT_TRUNC_IN_BOUND",
                    severity: "WARN",
                    decl: decl_name.into(),
                    summary: "Truncating Nat division / Nat.sqrt used directly in an inequality or equality bound".into(),
                    detail: format!("subterm: {}", pp_expr(env, e, 40, bnames)),
                });
            }

            // F10c: Division / inversion by literal 0 or unguarded bare variable / difference
            let denom_opt = if hn == "HDiv.hDiv" && args.len() == 6 {
                Some(args[5])
            } else if hn == "Inv.inv" && args.len() == 3 {
                Some(args[2])
            } else {
                None
            };
            if let Some(den) = denom_opt {
                if expr_nat_lit(env, unwrap_casts(env, den)) == Some(0) {
                    if seen_keys.insert((decl_name.into(), "F10c_DIV_BY_ZERO_LITERAL", dg.h1.he_alpha[e as usize])) {
                        findings.push(Finding {
                            id: "F10c_DIV_BY_ZERO_LITERAL",
                            severity: "CRITICAL",
                            decl: decl_name.into(),
                            summary: "Division or inversion by literal 0 (evaluates to junk value 0 in Lean/Mathlib)".into(),
                            detail: format!("subterm: {}", pp_expr(env, e, 40, bnames)),
                        });
                    }
                } else if !next_attop && !is_syntactically_nonzero(env, den) {
                    let core = unwrap_casts(env, den);
                    let cx = env.exprs[core as usize];
                    let mut c_args = Vec::new();
                    let ch = spine(env, core, &mut c_args);
                    let is_sub = env.exprs[ch as usize].kind == E_CONST
                        && matches!(env.name_str(env.exprs[ch as usize].a).as_str(), "HSub.hSub" | "Nat.sub");
                    if cx.kind == E_BVAR || is_sub {
                        let mut dvars = FxSet::default();
                        collect_outer_bvars(env, core, bnames.len(), &mut dvars);
                        let uses_lam_binder = dvars.iter().any(|&idx| !b_is_pi[idx]);
                        let pi_dvars: FxSet<usize> = dvars.into_iter().filter(|&idx| b_is_pi[idx]).collect();
                        let guarded = if is_sub && c_args.len() >= 2 {
                            // For `u - v`, if both `u` and `v` depend on distinct outer variables, a valid non-zero guard
                            // must relate BOTH sides (like `a < b` or `a ≠ b`), not merely `a > 0` and `b > 0` separately!
                            let u_expr = c_args[c_args.len() - 2];
                            let v_expr = c_args[c_args.len() - 1];
                            let mut uvars = FxSet::default();
                            let mut vvars = FxSet::default();
                            collect_outer_bvars(env, u_expr, bnames.len(), &mut uvars);
                            collect_outer_bvars(env, v_expr, bnames.len(), &mut vvars);
                            let pi_u: FxSet<usize> = uvars.into_iter().filter(|&idx| b_is_pi[idx]).collect();
                            let pi_v: FxSet<usize> = vvars.into_iter().filter(|&idx| b_is_pi[idx]).collect();
                            if !pi_u.is_empty() && !pi_v.is_empty() && pi_u != pi_v {
                                hyps.iter().any(|&(hp, hd)| hyp_guards_vars(env, hp, hd, &pi_u) && hyp_guards_vars(env, hp, hd, &pi_v))
                            } else {
                                !pi_dvars.is_empty() && hyps.iter().any(|&(hp, hd)| hyp_guards_vars(env, hp, hd, &pi_dvars))
                            }
                        } else {
                            !pi_dvars.is_empty() && hyps.iter().any(|&(hp, hd)| hyp_guards_vars(env, hp, hd, &pi_dvars))
                        };
                        if !uses_lam_binder
                            && !pi_dvars.is_empty()
                            && !guarded
                            && seen_keys.insert((decl_name.into(), "F10c_DIV_BY_UNGUARDED_VAR", dg.h1.he_alpha[e as usize]))
                        {
                            findings.push(Finding {
                                id: "F10c_DIV_BY_UNGUARDED_VAR",
                                severity: "WARN",
                                decl: decl_name.into(),
                                summary: "Division/inversion by variable or difference with no nonzero/positivity guard in scope (x / 0 = 0)".into(),
                                detail: format!("subterm: {}", pp_expr(env, e, 40, bnames)),
                            });
                        }
                    }
                }
            }

            // F10d: Conditionally complete lattice junk value (`sInf` / `sSup`) in bound without BddAbove/BddBelow/Nonempty
            if matches!(hn.as_str(), "InfSet.sInf" | "SupSet.sSup") && !args.is_empty() && parent_rel {
                let ty0 = strip_mdata(env, args[0]);
                let tname = if env.exprs[ty0 as usize].kind == E_CONST {
                    env.name_str(env.exprs[ty0 as usize].a)
                } else {
                    String::new()
                };
                if matches!(tname.as_str(), "Nat" | "Int" | "Real") {
                    let has_bdd = hyps.iter().any(|&(hp, _)| {
                        let mut vis = Bits::new(env.exprs.len());
                        let mut st = Vec::new();
                        let mut ok = false;
                        let _ = expr_consts(env, hp, &mut vis, &mut st, &mut |nm| {
                            if matches!(
                                env.name_str(nm).as_str(),
                                "BddAbove" | "BddBelow" | "Set.Nonempty" | "Finset.Nonempty" | "IsCompact" | "Set.Finite" | "Finite"
                            ) {
                                ok = true;
                            }
                            Ok(())
                        });
                        ok
                    });
                    if !has_bdd && seen_keys.insert((decl_name.into(), "F10d_COND_LATTICE_JUNK", dg.h1.he_alpha[e as usize])) {
                        findings.push(Finding {
                            id: "F10d_COND_LATTICE_JUNK",
                            severity: "WARN",
                            decl: decl_name.into(),
                            summary: format!(
                                "{} on {} used in a bound without BddAbove/BddBelow/Nonempty (junk value 0 on empty/unbounded sets)",
                                hn, tname
                            ),
                            detail: format!("subterm: {}", pp_expr(env, e, 44, bnames)),
                        });
                    }
                }
            }

            scan_expr_hazards(
                env, dg, decl_name, h, bnames, btypes, b_is_pi, 0, hyps, next_attop, false, findings, seen_keys,
            );
            let rel_arith_passthrough = parent_rel
                && matches!(
                    hn.as_str(),
                    "HAdd.hAdd"
                        | "HSub.hSub"
                        | "HMul.hMul"
                        | "HPow.hPow"
                        | "Nat.add"
                        | "Nat.mul"
                        | "Nat.pow"
                        | "Nat.cast"
                        | "Int.cast"
                        | "Rat.cast"
                        | "NatCast.natCast"
                        | "IntCast.intCast"
                        | "RatCast.ratCast"
                        | "Int.ofNat"
                        | "Neg.neg"
                );
            let is_unary_cast = matches!(
                hn.as_str(),
                "Nat.cast" | "Int.cast" | "Rat.cast" | "NatCast.natCast" | "IntCast.intCast" | "RatCast.ratCast" | "Int.ofNat" | "Neg.neg"
            );
            let rel_arg_start = if rel_arith_passthrough && is_unary_cast && !args.is_empty() {
                args.len() - 1
            } else if (is_rel || rel_arith_passthrough) && args.len() >= 2 {
                args.len() - 2
            } else if rel_arith_passthrough && args.len() == 1 {
                0
            } else {
                usize::MAX
            };
            for (idx, &a) in args.iter().enumerate() {
                scan_expr_hazards(
                    env,
                    dg,
                    decl_name,
                    a,
                    bnames,
                    btypes,
                    b_is_pi,
                    0,
                    hyps,
                    next_attop,
                    idx >= rel_arg_start,
                    findings,
                    seen_keys,
                );
            }
        }
        E_PROJ => {
            scan_expr_hazards(
                env, dg, decl_name, x.b, bnames, btypes, b_is_pi, 0, hyps, in_attop, false, findings, seen_keys,
            );
        }
        _ => {}
    }
}

fn audit_target_telescope(
    env: &Env,
    dg: &EnvDigests,
    names_str: &[String],
    bcls: &[u8],
    has_instance_for_induct: &FxSet<usize>,
    hole_decls: &FxSet<usize>,
    target_idx: usize,
    findings: &mut Vec<Finding>,
) {
    let d = &env.decls[target_idx];
    let tname = &names_str[target_idx];

    struct BinderInfo {
        name: String,
        ty: u32,
        flag: u8,
        is_prop: bool,
        is_sort: bool,
        is_prop_sort: bool, // ty == Prop (Sort 0)
    }

    let mut binders: Vec<BinderInfo> = Vec::new();
    let mut btypes: Vec<u32> = Vec::new();
    let mut bnames: Vec<String> = Vec::new();
    let mut cur = strip_mdata(env, d.ty);
    while env.exprs[cur as usize].kind == E_PI {
        let px = env.exprs[cur as usize];
        let bty = strip_mdata(env, px.a);
        let is_sort = env.exprs[bty as usize].kind == E_SORT;
        let is_prop_sort = is_sort && env.levels[env.exprs[bty as usize].a as usize].kind == L_ZERO;
        let is_prop = is_prop_valued_type(env, bty, &btypes);
        let bn = if px.c == NONE { "_".into() } else { env.name_str(px.c) };
        binders.push(BinderInfo { name: bn.clone(), ty: bty, flag: px.flag, is_prop, is_sort, is_prop_sort });
        btypes.push(bty);
        bnames.push(bn);
        cur = strip_mdata(env, px.b);
    }
    let concl = cur;
    let nb = binders.len();

    // 1. Check unused non-proof binders, autoImplicit suspects, and uninhabited custom premises
    for i in 0..nb {
        let b = &binders[i];
        let mut used_in_later_binder = false;
        let mut used_in_class_or_val_binder = false;
        for k in (i + 1)..nb {
            let mut vs = FxSet::default();
            collect_outer_bvars(env, binders[k].ty, k, &mut vs);
            if vs.contains(&i) {
                used_in_later_binder = true;
                if binders[k].flag == 3 || !binders[k].is_prop {
                    used_in_class_or_val_binder = true;
                }
            }
        }
        let mut concl_vars = FxSet::default();
        collect_outer_bvars(env, concl, nb, &mut concl_vars);
        let used_in_concl = concl_vars.contains(&i);

        if !b.is_prop && b.flag != 3 && !used_in_later_binder && !used_in_concl {
            findings.push(Finding {
                id: "F07d_UNUSED_STMT_PARAM",
                severity: "HIGH",
                decl: tname.clone(),
                summary: format!("Statement quantifies over parameter `{}` that never occurs in any hypothesis or the conclusion", b.name),
                detail: format!("binder {}: ({} : {})", i, b.name, pp_expr(env, b.ty, 30, &bnames[..i])),
            });
        } else if b.flag == 1 && b.is_prop_sort && !used_in_later_binder {
            findings.push(Finding {
                id: "F07c_AUTO_IMPLICIT_PROP",
                severity: "HIGH",
                decl: tname.clone(),
                summary: format!(
                    "Unconstrained implicit Prop binder `{{{} : Prop}}` — classic `autoImplicit` typo on a proposition/theorem name",
                    b.name
                ),
                detail: format!("conclusion: {}", pp_expr(env, concl, 40, &bnames)),
            });
        } else if b.flag == 1 && b.is_sort && !b.is_prop_sort && (!used_in_later_binder || (!used_in_concl && !used_in_class_or_val_binder)) {
            findings.push(Finding {
                id: "F07c_AUTO_IMPLICIT_SORT",
                severity: "HIGH",
                decl: tname.clone(),
                summary: format!(
                    "Implicit type/sort binder `{{{}}}` appears in zero binder/hypothesis types — likely `autoImplicit` typo",
                    b.name
                ),
                detail: format!("conclusion: {}", pp_expr(env, concl, 40, &bnames)),
            });
        } else if b.flag == 1 && !b.is_prop && !b.is_sort && !used_in_later_binder {
            let has_explicit_val = binders.iter().any(|ob| ob.flag == 0 && !ob.is_prop && !ob.is_sort);
            if has_explicit_val {
                findings.push(Finding {
                    id: "F07c_UNCONSTRAINED_IMPLICIT_VALUE",
                    severity: "WARN",
                    decl: tname.clone(),
                    summary: format!(
                        "Implicit value binder `{{{} : {}}}` has zero hypotheses/typeclasses referencing it while other parameters are explicit (possible `autoImplicit` typo)",
                        b.name,
                        pp_expr(env, b.ty, 24, &bnames[..i])
                    ),
                    detail: format!("conclusion: {}", pp_expr(env, concl, 40, &bnames)),
                });
            }
        }

        // F09: Uninhabited custom inductive / uninstantiated custom class premise
        let mut targs = Vec::new();
        let thead = spine(env, b.ty, &mut targs);
        if let Some((cname, cdi)) = const_head_name(env, thead, names_str) {
            if bcls[cdi] == 0 && env.decls[cdi].kind == D_INDUCT {
                if env.decls[cdi].ctors.is_empty() {
                    findings.push(Finding {
                        id: "F09a_EMPTY_INDUCTIVE_PREMISE",
                        severity: "CRITICAL",
                        decl: tname.clone(),
                        summary: format!("Premise `{}` has custom inductive type `{}` with ZERO constructors (vacuously true!)", b.name, cname),
                        detail: format!("binder {}: {}", i, pp_expr(env, b.ty, 36, &bnames[..i])),
                    });
                } else if b.flag == 3 && !has_instance_for_induct.contains(&cdi) {
                    findings.push(Finding {
                        id: "F09b_UNINSTANTIATED_CUSTOM_CLASS",
                        severity: "HIGH",
                        decl: tname.clone(),
                        summary: format!(
                            "Typeclass hypothesis `[{} : {} ...]` uses a custom class with zero instances in the export (potential vacuity)",
                            b.name, cname
                        ),
                        detail: format!("binder {}: {}", i, pp_expr(env, b.ty, 36, &bnames[..i])),
                    });
                }
            }
        }
    }

    // 2. Collect all proof hypotheses (lifting their alpha-hashes? Note de Bruijn indices shift by `nb - i` at conclusion depth!)
    // For syntactic contradiction checks (False, ¬True, t ≠ t, t < t, n < 0 on Nat, contradictory literal bounds), check each hyp directly!
    let mut pos_hyps_pp: FxMap<String, usize> = FxMap::default();
    let mut neg_hyps_pp: FxMap<String, usize> = FxMap::default();
    // Numeric bounds per printed expression: (lo, lo_strict, hi, hi_strict)
    let mut num_bounds: FxMap<String, (i128, bool, i128, bool)> = FxMap::default();

    for (i, b) in binders.iter().enumerate() {
        if !b.is_prop {
            continue;
        }
        let mut conjs = Vec::new();
        flatten_conjuncts(env, b.ty, &mut conjs);
        for c in conjs {
            let c = strip_mdata(env, c);
            let mut args = Vec::new();
            let h = spine(env, c, &mut args);
            let hn = if env.exprs[h as usize].kind == E_CONST {
                env.name_str(env.exprs[h as usize].a)
            } else {
                String::new()
            };
            if hn == "False" && args.is_empty() {
                findings.push(Finding {
                    id: "F07b_LITERAL_FALSE_PREMISE",
                    severity: "CRITICAL",
                    decl: tname.clone(),
                    summary: "Target theorem has literal `False` as a hypothesis (vacuously true)".into(),
                    detail: format!("binder `{}`", b.name),
                });
            }
            if hn == "Ne" && args.len() == 3 && dg.h1.he_alpha[args[1] as usize] == dg.h1.he_alpha[args[2] as usize] {
                findings.push(Finding {
                    id: "F07b_SELF_INEQUALITY_PREMISE",
                    severity: "CRITICAL",
                    decl: tname.clone(),
                    summary: "Hypothesis asserts `t ≠ t` (contradictory premise -> vacuously true)".into(),
                    detail: pp_expr(env, c, 36, &bnames[..i]),
                });
            }
            if (hn == "LT.lt" || hn == "GT.gt") && args.len() == 4 && dg.h1.he_alpha[args[2] as usize] == dg.h1.he_alpha[args[3] as usize] {
                findings.push(Finding {
                    id: "F07b_SELF_STRICT_LT_PREMISE",
                    severity: "CRITICAL",
                    decl: tname.clone(),
                    summary: "Hypothesis asserts `t < t` (contradictory premise -> vacuously true)".into(),
                    detail: pp_expr(env, c, 36, &bnames[..i]),
                });
            }
            // Check `t < 0` on Nat or inconsistent numeric bounds (discrete +1/-1 ONLY on Nat/Int, NOT dense Real/Rat!)
            if matches!(hn.as_str(), "LT.lt" | "LE.le" | "GT.gt" | "GE.ge") && args.len() == 4 {
                let ty0 = strip_mdata(env, args[0]);
                let ty_nm = if env.exprs[ty0 as usize].kind == E_CONST {
                    env.name_str(env.exprs[ty0 as usize].a)
                } else {
                    String::new()
                };
                let is_nat = ty_nm == "Nat";
                let is_discrete = ty_nm == "Nat" || ty_nm == "Int";
                let (lhs, rhs, strict) = match hn.as_str() {
                    "LT.lt" => (args[2], args[3], true),
                    "LE.le" => (args[2], args[3], false),
                    "GT.gt" => (args[3], args[2], true),
                    _ => (args[3], args[2], false),
                };
                if is_nat && strict && expr_nat_lit(env, rhs) == Some(0) {
                    findings.push(Finding {
                        id: "F07b_IMPOSSIBLE_NAT_NEG_PREMISE",
                        severity: "CRITICAL",
                        decl: tname.clone(),
                        summary: "Hypothesis asserts `e < 0` on `Nat` (impossible -> vacuously true)".into(),
                        detail: pp_expr(env, c, 36, &bnames[..i]),
                    });
                }
                if let Some(k) = expr_nat_lit(env, lhs) {
                    let key = pp_expr(env, rhs, 64, &bnames[..i]);
                    let (lo, lo_st) = if is_discrete {
                        (k as i128 + if strict { 1 } else { 0 }, false)
                    } else {
                        (k as i128, strict)
                    };
                    let entry = num_bounds.entry(key).or_insert((i128::MIN, false, i128::MAX, false));
                    if lo > entry.0 || (lo == entry.0 && lo_st) {
                        entry.0 = lo;
                        entry.1 = lo_st;
                    }
                }
                if let Some(k) = expr_nat_lit(env, rhs) {
                    let key = pp_expr(env, lhs, 64, &bnames[..i]);
                    let (hi, hi_st) = if is_discrete {
                        (k as i128 - if strict { 1 } else { 0 }, false)
                    } else {
                        (k as i128, strict)
                    };
                    let entry = num_bounds.entry(key).or_insert((i128::MIN, false, i128::MAX, false));
                    if hi < entry.2 || (hi == entry.2 && hi_st) {
                        entry.2 = hi;
                        entry.3 = hi_st;
                    }
                }
            }
            if let Some(neg_inner) = extract_negated(env, c) {
                if env.exprs[neg_inner as usize].kind == E_CONST && env.name_str(env.exprs[neg_inner as usize].a) == "True" {
                    findings.push(Finding {
                        id: "F07b_NEG_TRUE_PREMISE",
                        severity: "CRITICAL",
                        decl: tname.clone(),
                        summary: "Hypothesis asserts `¬ True` (vacuously true)".into(),
                        detail: pp_expr(env, c, 36, &bnames[..i]),
                    });
                }
                let s = pp_expr(env, neg_inner, 80, &bnames[..i]);
                neg_hyps_pp.insert(s, i);
            } else {
                let s = pp_expr(env, c, 80, &bnames[..i]);
                pos_hyps_pp.insert(s, i);
            }
        }
    }

    for (p, _) in &pos_hyps_pp {
        if neg_hyps_pp.contains_key(p) {
            findings.push(Finding {
                id: "F07b_CONTRADICTORY_HYP_PAIR",
                severity: "CRITICAL",
                decl: tname.clone(),
                summary: "Target theorem assumes both `P` and `¬ P` in its hypotheses (vacuously true)".into(),
                detail: format!("conflicting proposition: {}", p),
            });
            break;
        }
    }
    for (expr_s, &(lo, lo_st, hi, hi_st)) in &num_bounds {
        if lo > hi || (lo == hi && (lo_st || hi_st)) {
            let op_lo = if lo_st { ">" } else { "≥" };
            let op_hi = if hi_st { "<" } else { "≤" };
            findings.push(Finding {
                id: "F07b_CONTRADICTORY_BOUNDS",
                severity: "CRITICAL",
                decl: tname.clone(),
                summary: format!(
                    "Contradictory numeric bounds on `{}` (requires {} {} and {} {}) -> vacuously true",
                    expr_s, op_lo, lo, op_hi, hi
                ),
                detail: expr_s.clone(),
            });
            break;
        }
    }

    // 3. Check trivial conclusions (`True`, `t = t`, `t ↔ t`, `t ≤ t`, or conclusion identical to a hypothesis)
    {
        let mut cargs = Vec::new();
        let ch = spine(env, concl, &mut cargs);
        let chn = if env.exprs[ch as usize].kind == E_CONST {
            env.name_str(env.exprs[ch as usize].a)
        } else {
            String::new()
        };
        if chn == "True" && cargs.is_empty() {
            findings.push(Finding {
                id: "F07a_TRIVIAL_TRUE_CONCLUSION",
                severity: "CRITICAL",
                decl: tname.clone(),
                summary: "Target theorem's conclusion is literal `True`".into(),
                detail: tname.clone(),
            });
        } else if ((chn == "Eq" && cargs.len() == 3 && dg.h1.he_alpha[cargs[1] as usize] == dg.h1.he_alpha[cargs[2] as usize])
            || (chn == "Iff" && cargs.len() == 2 && dg.h1.he_alpha[cargs[0] as usize] == dg.h1.he_alpha[cargs[1] as usize])
            || ((chn == "LE.le" || chn == "GE.ge")
                && cargs.len() == 4
                && dg.h1.he_alpha[cargs[2] as usize] == dg.h1.he_alpha[cargs[3] as usize]))
        {
            findings.push(Finding {
                id: "F07a_REFLEXIVE_CONCLUSION",
                severity: "CRITICAL",
                decl: tname.clone(),
                summary: "Target theorem's conclusion is syntactically reflexive (`t = t`, `t ↔ t`, or `t ≤ t`)".into(),
                detail: pp_expr(env, concl, 48, &bnames),
            });
        } else {
            let concl_pp = pp_expr(env, concl, 80, &bnames);
            if pos_hyps_pp.contains_key(&concl_pp) {
                findings.push(Finding {
                    id: "F07a_CONCLUSION_IN_PREMISES",
                    severity: "CRITICAL",
                    decl: tname.clone(),
                    summary: "Target theorem's conclusion is identical to one of its own hypotheses (`P → P`)".into(),
                    detail: concl_pp,
                });
            }
        }
    }

    // 4. F05c: Unparameterized hole (`*.answer` or `definition_names` entry) when explicit value parameters exist
    if !hole_decls.is_empty() {
        let mut concl_vars = FxSet::default();
        collect_outer_bvars(env, concl, nb, &mut concl_vars);
        let explicit_val_params: FxSet<usize> = (0..nb)
            .filter(|&i| binders[i].flag == 0 && !binders[i].is_prop && !binders[i].is_sort && concl_vars.contains(&i))
            .collect();
        if !explicit_val_params.is_empty() {
            // Walk `concl` for applications / occurrences of any hole decl
            let mut st: Vec<(u32, usize)> = vec![(concl, 0)];
            let mut visited: FxSet<(u32, usize)> = FxSet::default();
            let mut hole_calls: FxMap<usize, bool> = FxMap::default(); // hole_di -> any_call_uses_param
            while let Some((e, inner)) = st.pop() {
                let e = strip_mdata(env, e);
                if !visited.insert((e, inner)) {
                    continue;
                }
                let mut args = Vec::new();
                let h = spine(env, e, &mut args);
                if let Some((_, di)) = const_head_name(env, h, names_str) {
                    if hole_decls.contains(&di) {
                        let mut arg_vars = FxSet::default();
                        for &a in &args {
                            collect_outer_bvars(env, a, nb + inner, &mut arg_vars);
                        }
                        let uses_param = explicit_val_params.iter().any(|&p| arg_vars.contains(&p));
                        let ent = hole_calls.entry(di).or_insert(false);
                        if uses_param {
                            *ent = true;
                        }
                    }
                }
                let x = env.exprs[e as usize];
                match x.kind {
                    E_APP => {
                        st.push((x.a, inner));
                        st.push((x.b, inner));
                    }
                    E_LAM | E_PI => {
                        st.push((x.a, inner));
                        st.push((x.b, inner + 1));
                    }
                    E_LET => {
                        st.push((x.a, inner));
                        st.push((x.b, inner));
                        st.push((x.c, inner + 1));
                    }
                    E_PROJ => st.push((x.b, inner)),
                    _ => {}
                }
            }
            for (hdi, uses_param) in hole_calls {
                if !uses_param {
                    let pnames: Vec<String> = explicit_val_params.iter().map(|&i| binders[i].name.clone()).collect();
                    findings.push(Finding {
                        id: "F05c_UNPARAMETERIZED_HOLE",
                        severity: "HIGH",
                        decl: tname.clone(),
                        summary: format!(
                            "Hole definition `{}` is not applied to quantified parameter(s) [{}] — forces a constant answer across all inputs",
                            names_str[hdi],
                            pnames.join(", ")
                        ),
                        detail: pp_expr(env, concl, 48, &bnames),
                    });
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------------
// JSON Serialization Helpers
// ---------------------------------------------------------------------------------------------------

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_str_arr(v: &[String]) -> String {
    let inner: Vec<String> = v.iter().map(|s| json_str(s)).collect();
    format!("[{}]", inner.join(", "))
}

fn severity_rank(s: &str) -> u8 {
    match s {
        "CRITICAL" => 4,
        "HIGH" => 3,
        "WARN" => 2,
        "INFO" => 1,
        _ => 0,
    }
}

// ---------------------------------------------------------------------------------------------------
// CLI & Commands
// ---------------------------------------------------------------------------------------------------

struct AuditOpts {
    threads: usize,
    verbose: bool,
    solution_mode: bool,
    config: Option<String>,
    targets: Option<String>,
    base: Option<String>,
    base_index: Option<String>,
    reading_set: Option<String>,
    json_out: Option<String>,
    tsv_out: Option<String>,
    fail_on: Option<String>,
    export_path: String,
}

fn is_high_risk_canonical_concept(short: &str) -> bool {
    matches!(
        short,
        "RiemannHypothesis"
            | "GeneralizedRiemannHypothesis"
            | "FermatLastTheorem"
            | "Prime"
            | "Irreducible"
            | "Continuous"
            | "ContinuousOn"
            | "Differentiable"
            | "DifferentiableOn"
            | "Measurable"
            | "Integrable"
            | "IsCompact"
            | "IsOpen"
            | "IsClosed"
            | "Connected"
            | "IsConnected"
            | "Irrational"
            | "Transcendental"
            | "Squarefree"
            | "Coprime"
            | "Even"
            | "Odd"
            | "Injective"
            | "Surjective"
            | "Bijective"
            | "Group"
            | "CommGroup"
            | "Ring"
            | "CommRing"
            | "Field"
            | "TopologicalSpace"
            | "MetricSpace"
            | "NormedSpace"
            | "SimpleGraph"
            | "BddAbove"
            | "BddBelow"
            | "Nonempty"
            | "Finite"
            | "Infinite"
            | "Tendsto"
            | "HasSum"
    )
}

fn is_proof_aux_name(nm: &str) -> bool {
    is_auto_boilerplate_name(nm)
        || nm.contains("._proof_")
        || nm.contains(".proof_")
        || nm.contains(".match_")
        || nm.contains("._simp_")
        || nm.contains(".eq_")
        || nm.contains("._unfold")
        || nm.contains("._sunfold")
        || nm.contains("._auxLemma")
        || nm.contains("._cstage")
        || nm.contains("._native")
        || nm.ends_with(".induct")
}

fn cmd_index_base(threads: usize, verbose: bool, out_path: &str, base_export: &str) -> R<()> {
    let t0 = Instant::now();
    let env = load(base_export, threads, verbose)?;
    let bl = BaseLookup::from_env(&env);
    bl.save_index(out_path)?;
    eprintln!(
        "expaudit: indexed {} base declarations ({} distinctive short names) -> {} in {:.2} s",
        bl.by_name.len(),
        bl.short_defs.len(),
        out_path,
        t0.elapsed().as_secs_f64()
    );
    std::mem::forget(env);
    Ok(())
}

fn cmd_audit(o: &AuditOpts) -> R<i32> {
    let t0 = Instant::now();
    let (env_res, base_res) = std::thread::scope(|s| {
        let hb = s.spawn(|| -> R<BaseLookup> {
            if let Some(idx_path) = &o.base_index {
                BaseLookup::load_index(idx_path)
            } else if let Some(b_path) = &o.base {
                let b = load(b_path, (o.threads / 2).max(1), o.verbose)?;
                let bl = BaseLookup::from_env(&b);
                std::mem::forget(b);
                Ok(bl)
            } else {
                Ok(BaseLookup::heuristic())
            }
        });
        let e = load(&o.export_path, o.threads, o.verbose);
        (e, hb.join().unwrap())
    });
    let env = env_res?;
    let base = base_res?;
    let dg = compute_digests(&env);

    // Map full declaration names
    let mut names_str: Vec<String> = Vec::with_capacity(env.decls.len());
    let mut name_to_idx: FxMap<String, u32> = FxMap::default();
    name_to_idx.reserve(env.decls.len());
    for (j, d) in env.decls.iter().enumerate() {
        let s = env.name_str(d.name);
        name_to_idx.insert(s.clone(), j as u32);
        names_str.push(s);
    }

    let bcls = classify_decls(&env, &dg, &names_str, &base);

    // Read config / targets
    let mut cfg = match &o.config {
        Some(p) => read_comp_config(p)?,
        None => CompConfig::default(),
    };
    if let Some(ts) = &o.targets {
        cfg.theorem_names = parse_targets_spec(ts)?;
    } else if !cfg.has_config && cfg.theorem_names.is_empty() {
        // Default when neither --config nor --targets is passed: all project theorems in export!
        for (j, d) in env.decls.iter().enumerate() {
            if bcls[j] == 0 && d.kind == D_THM && !is_auto_boilerplate_name(&names_str[j]) {
                cfg.theorem_names.push(names_str[j].clone());
            }
        }
    }

    let mut findings: Vec<Finding> = Vec::new();

    if cfg.theorem_names.is_empty() {
        findings.push(Finding {
            id: "F01_EMPTY_TARGETS",
            severity: "CRITICAL",
            decl: "<config>".into(),
            summary: "No target theorems specified in challenge configuration".into(),
            detail: "theorem_names is empty".into(),
        });
    }

    // Check permitted_axioms
    if cfg.has_config {
        let std_ax = ["propext", "Quot.sound", "Classical.choice"];
        for ax in &cfg.permitted_axioms {
            if !std_ax.contains(&ax.as_str()) {
                findings.push(Finding {
                    id: "F02_NONSTANDARD_PERMITTED_AXIOM",
                    severity: "CRITICAL",
                    decl: ax.clone(),
                    summary: format!("Challenge configuration permits non-standard axiom `{}`", ax),
                    detail: format!("permitted_axioms = {:?}", cfg.permitted_axioms),
                });
            }
        }
    }

    let mut missing_targets: Vec<String> = Vec::new();
    let mut target_indices: Vec<u32> = Vec::new();
    let mut is_target = vec![false; env.decls.len()];
    for t in &cfg.theorem_names {
        match name_to_idx.get(t) {
            None => {
                missing_targets.push(t.clone());
                findings.push(Finding {
                    id: "F01_MISSING_TARGET",
                    severity: "CRITICAL",
                    decl: t.clone(),
                    summary: format!("Target theorem `{}` is missing from challenge export", t),
                    detail: t.clone(),
                });
            }
            Some(&di) => {
                is_target[di as usize] = true;
                target_indices.push(di);
                if env.decls[di as usize].kind != D_THM {
                    findings.push(Finding {
                        id: "F01_TARGET_NOT_THEOREM",
                        severity: "CRITICAL",
                        decl: t.clone(),
                        summary: format!(
                            "Target `{}` is declared as `{}` rather than `theorem`",
                            t,
                            kind_name(env.decls[di as usize].kind)
                        ),
                        detail: t.clone(),
                    });
                }
            }
        }
    }

    let mut hole_set: FxSet<usize> = FxSet::default();
    let mut seed_decls = target_indices.clone();
    for dn in &cfg.definition_names {
        match name_to_idx.get(dn) {
            None => {
                findings.push(Finding {
                    id: "F05_MISSING_DEFINITION_HOLE",
                    severity: "HIGH",
                    decl: dn.clone(),
                    summary: format!("`definition_names` entry `{}` is missing from challenge export", dn),
                    detail: dn.clone(),
                });
            }
            Some(&di) => {
                hole_set.insert(di as usize);
                seed_decls.push(di);
                findings.push(Finding {
                    id: "F05a_DEFINITION_HOLE",
                    severity: "INFO",
                    decl: dn.clone(),
                    summary: format!("`{}` is listed in `definition_names` (solutions may supply any body)", dn),
                    detail: pp_expr(&env, env.decls[di as usize].ty, 48, &[]),
                });
                let d = &env.decls[di as usize];
                if d.kind == D_DEFN && !expr_mentions_sorry(&env, d.val) {
                    findings.push(Finding {
                        id: "F05b_UNSORRIED_HOLE",
                        severity: "HIGH",
                        decl: dn.clone(),
                        summary: format!(
                            "`definition_names` entry `{}` has a concrete body without `sorry` (rejected by Lean >= 4.37 comparator)",
                            dn
                        ),
                        detail: pp_expr(&env, d.val, 48, &[]),
                    });
                }
            }
        }
    }

    // Compute statement closure
    let (in_sc, deps) = stmt_closure(&env, &seed_decls);
    let mut sc_roots: Vec<u32> = Vec::new();
    for (j, d) in env.decls.iter().enumerate() {
        if !in_sc[j] {
            continue;
        }
        sc_roots.push(d.ty);
        if matches!(d.kind, D_DEFN | D_OPAQUE) {
            sc_roots.push(d.val);
        }
    }
    let sc_dag = dag_size_roots(&env, &sc_roots);

    // Precompute which custom inductives have at least one instance/value in the export
    let mut has_instance_for_induct: FxSet<usize> = FxSet::default();
    for (j, d) in env.decls.iter().enumerate() {
        if matches!(d.kind, D_DEFN | D_THM | D_AXIOM | D_OPAQUE) && !is_target[j] {
            let mut cur = strip_mdata(&env, d.ty);
            while env.exprs[cur as usize].kind == E_PI {
                cur = strip_mdata(&env, env.exprs[cur as usize].b);
            }
            let mut a = Vec::new();
            let h = spine(&env, cur, &mut a);
            if let Some((_, cdi)) = const_head_name(&env, h, &names_str) {
                if env.decls[cdi].kind == D_INDUCT {
                    has_instance_for_induct.insert(cdi);
                }
            }
        }
    }

    // Also record `sorryAx`-bodied custom defs in `stmt_closure` as holes for F05c
    let mut all_hole_decls = hole_set.clone();
    let mut sc_total = 0usize;
    let mut sc_base = 0usize;
    let mut sc_base_mod = 0usize;
    let mut sc_custom_total = 0usize;
    let mut sc_custom_user = 0usize;
    let mut sc_custom_auto = 0usize;

    for (j, d) in env.decls.iter().enumerate() {
        if !in_sc[j] {
            continue;
        }
        sc_total += 1;
        match bcls[j] {
            1 => {
                sc_base += 1;
                continue;
            }
            2 => {
                sc_base_mod += 1;
                findings.push(Finding {
                    id: "F06a_BASE_MODIFIED",
                    severity: "CRITICAL",
                    decl: names_str[j].clone(),
                    summary: format!(
                        "Base library declaration `{}` was modified in the challenge export (differs from base digest!)",
                        names_str[j]
                    ),
                    detail: pp_expr(&env, d.ty, 48, &[]),
                });
            }
            _ => {
                sc_custom_total += 1;
                if is_target[j] {
                    // targets counted in sc_custom_total; track non-target user decls separately too
                    sc_custom_user += 1;
                } else if d.kind == D_REC || is_auto_boilerplate_name(&names_str[j]) {
                    sc_custom_auto += 1;
                } else {
                    sc_custom_user += 1;
                }
            }
        }

        // Lints on declarations in statement closure
        let nm = &names_str[j];
        if d.kind == D_AXIOM && !matches!(nm.as_str(), "propext" | "Quot.sound" | "Classical.choice" | "sorryAx") {
            let is_nd = nm.contains("._native.native_decide.") || nm == "Lean.ofReduceBool" || nm == "Lean.trustCompiler";
            findings.push(Finding {
                id: "F02_AXIOM_IN_STMT_CLOSURE",
                severity: "CRITICAL",
                decl: nm.clone(),
                summary: if is_nd {
                    format!("Unsound compiler-trust / `native_decide` axiom `{}` occurs in the statement closure", nm)
                } else {
                    format!("Non-standard axiom `{}` occurs in the statement closure", nm)
                },
                detail: pp_expr(&env, d.ty, 48, &[]),
            });
        }
        if d.kind == D_OPAQUE && bcls[j] == 0 {
            findings.push(Finding {
                id: "F04_OPAQUE_IN_STMT_CLOSURE",
                severity: "HIGH",
                decl: nm.clone(),
                summary: format!("`opaque` declaration `{}` in statement closure hides its definition from comparison", nm),
                detail: pp_expr(&env, d.ty, 48, &[]),
            });
        }
        if expr_mentions_sorry(&env, d.ty) {
            findings.push(Finding {
                id: "F03a_SORRY_IN_TYPE",
                severity: "CRITICAL",
                decl: nm.clone(),
                summary: format!("`sorryAx` occurs inside the TYPE signature of `{}`", nm),
                detail: pp_expr(&env, d.ty, 48, &[]),
            });
        }
        if d.kind == D_DEFN && !hole_set.contains(&j) && expr_mentions_sorry(&env, d.val) {
            all_hole_decls.insert(j);
            let last = nm.rsplit('.').next().unwrap_or(nm);
            if last == "answer" || nm.ends_with(".answer") {
                findings.push(Finding {
                    id: "F03c_UNLISTED_ANSWER_SLOT",
                    severity: "WARN",
                    decl: nm.clone(),
                    summary: format!("Answer-slot definition `{}` contains `sorryAx` and is not in `definition_names`", nm),
                    detail: pp_expr(&env, d.ty, 48, &[]),
                });
            } else {
                findings.push(Finding {
                    id: "F03b_SORRY_IN_CUSTOM_DEF",
                    severity: "CRITICAL",
                    decl: nm.clone(),
                    summary: format!("Custom definition `{}` in statement closure contains `sorryAx` in its body!", nm),
                    detail: pp_expr(&env, d.ty, 48, &[]),
                });
            }
        }
        // Short-name shadowing of base library concepts
        if bcls[j] == 0 && matches!(d.kind, D_DEFN | D_INDUCT) && !is_auto_boilerplate_name(nm) && !nm.starts_with("_private.") {
            let short = nm.rsplit('.').next().unwrap_or(nm);
            if !is_generic_short_name(short) {
                let sh = hbytes(SEED1, short.as_bytes());
                if let Some(base_ex) = base.short_defs.get(&sh) {
                    if base_ex != nm {
                        let high_risk = !nm.contains('.') || is_high_risk_canonical_concept(short);
                        findings.push(Finding {
                            id: if high_risk { "F06b_BASE_SHORTNAME_SHADOW" } else { "F06b_BASE_SHORTNAME_NOTE" },
                            severity: if high_risk { "HIGH" } else { "INFO" },
                            decl: nm.clone(),
                            summary: format!(
                                "Custom `{}` `{}` shares short name with base library `{}`{}",
                                kind_name(d.kind),
                                nm,
                                base_ex,
                                if high_risk { " — verify it is not redefining a standard mathematical concept" } else { " (namespaced project definition)" }
                            ),
                            detail: pp_expr(&env, d.ty, 48, &[]),
                        });
                    }
                }
            }
        }
    }

    // Also scan full proof closure from `seed_decls` (including `D_THM` proof bodies) for non-standard / `native_decide` axioms
    {
        let mut full_vis = vec![false; env.decls.len()];
        let mut q: Vec<u32> = Vec::new();
        for &sd in &seed_decls {
            if !full_vis[sd as usize] {
                full_vis[sd as usize] = true;
                q.push(sd);
            }
        }
        let mut st = Vec::new();
        let mut vis = Bits::new(env.exprs.len());
        while let Some(d_idx) = q.pop() {
            let decl = &env.decls[d_idx as usize];
            if decl.kind == D_AXIOM && !in_sc[d_idx as usize] {
                let nm = &names_str[d_idx as usize];
                if !matches!(nm.as_str(), "propext" | "Quot.sound" | "Classical.choice" | "sorryAx")
                    && !cfg.permitted_axioms.contains(nm)
                {
                    let is_nd = nm.contains("._native.native_decide.") || nm == "Lean.ofReduceBool" || nm == "Lean.trustCompiler";
                    findings.push(Finding {
                        id: "F02b_AXIOM_IN_PROOF_CLOSURE",
                        severity: "CRITICAL",
                        decl: nm.clone(),
                        summary: if is_nd {
                            format!("`native_decide` / compiler-trust axiom `{}` occurs in proof closure", nm)
                        } else {
                            format!("Undeclared custom axiom `{}` occurs in proof closure", nm)
                        },
                        detail: pp_expr(&env, decl.ty, 48, &[]),
                    });
                }
            }
            let mut push_dep = |nm: u32| -> R<()> {
                let r = env.canon[nm as usize];
                let di = env.decl_of[r as usize];
                if di != NONE && !full_vis[di as usize] {
                    full_vis[di as usize] = true;
                    q.push(di);
                }
                Ok(())
            };
            let _ = expr_consts(&env, decl.ty, &mut vis, &mut st, &mut push_dep);
            if matches!(decl.kind, D_DEFN | D_OPAQUE | D_THM) {
                let _ = expr_consts(&env, decl.val, &mut vis, &mut st, &mut push_dep);
            }
        }
    }

    // Per-target proof-support analysis & F11 (`--solution-mode`: "proved without the project" detector)
    let export_custom_theorems: usize = if o.solution_mode {
        (0..env.decls.len())
            .filter(|&j| bcls[j] == 0 && env.decls[j].kind == D_THM && !is_proof_aux_name(&names_str[j]))
            .count()
    } else {
        0
    };
    let mut proof_support_items: Vec<String> = Vec::new();
    if o.solution_mode {
        for &ti in &target_indices {
            let tidx = ti as usize;
            let other_custom_theorems = export_custom_theorems.saturating_sub(if env.decls[tidx].kind == D_THM && bcls[tidx] == 0 { 1 } else { 0 });
            let mut t_vis = vec![false; env.decls.len()];
            let mut q: Vec<u32> = vec![ti];
            t_vis[tidx] = true;
            let mut st = Vec::new();
            let mut vis = Bits::new(env.exprs.len());
            let mut has_sorry = false;
            let mut closure_cnt = 0usize;
            while let Some(d_idx) = q.pop() {
                closure_cnt += 1;
                let decl = &env.decls[d_idx as usize];
                if decl.kind == D_AXIOM && names_str[d_idx as usize] == "sorryAx" {
                    has_sorry = true;
                }
                let mut push_dep = |nm: u32| -> R<()> {
                    let r = env.canon[nm as usize];
                    let di = env.decl_of[r as usize];
                    if di != NONE && !t_vis[di as usize] {
                        t_vis[di as usize] = true;
                        q.push(di);
                    }
                    Ok(())
                };
                let _ = expr_consts(&env, decl.ty, &mut vis, &mut st, &mut push_dep);
                if matches!(decl.kind, D_DEFN | D_OPAQUE | D_THM) {
                    let _ = expr_consts(&env, decl.val, &mut vis, &mut st, &mut push_dep);
                }
            }
            let is_proved = env.decls[tidx].kind == D_THM && !has_sorry;
            let mut proj_lemmas: Vec<String> = Vec::new();
            let mut proj_defs_cnt = 0usize;
            for k in 0..env.decls.len() {
                if k != tidx && t_vis[k] && bcls[k] == 0 && !is_proof_aux_name(&names_str[k]) {
                    if env.decls[k].kind == D_THM {
                        proj_lemmas.push(names_str[k].clone());
                    } else if matches!(env.decls[k].kind, D_DEFN | D_INDUCT) {
                        proj_defs_cnt += 1;
                    }
                }
            }
            let val_dag = if env.decls[tidx].kind == D_THM { dag_size_roots(&env, &[env.decls[tidx].val]) } else { 0 };
            if is_proved && proj_lemmas.is_empty() && (other_custom_theorems > 0 || val_dag <= 250) {
                findings.push(Finding {
                    id: "F11_ZERO_PROJECT_PROOF_SUPPORT",
                    severity: if other_custom_theorems > 0 { "HIGH" } else { "WARN" },
                    decl: names_str[tidx].clone(),
                    summary: format!(
                        "Target theorem `{}` is proved using ZERO custom project lemmas (0/{} sibling/helper project theorems in export; proof DAG = {} nodes) — inspect for misformalized/trivialized target statement",
                        names_str[tidx], other_custom_theorems, val_dag
                    ),
                    detail: format!(
                        "proof_closure_decls={}, custom_proof_theorems=0, other_custom_theorems={}, proof_val_dag={}",
                        closure_cnt, other_custom_theorems, val_dag
                    ),
                });
            }
            let sample_lems: Vec<String> = proj_lemmas.iter().take(8).cloned().collect();
            proof_support_items.push(format!(
                "{{\"name\":{},\"is_proved\":{},\"proof_closure_decls\":{},\"custom_proof_theorems\":{},\"custom_proof_defs\":{},\"proof_val_dag\":{},\"sample_project_lemmas\":{}}}",
                json_str(&names_str[tidx]),
                if is_proved { "true" } else { "false" },
                closure_cnt,
                proj_lemmas.len(),
                proj_defs_cnt,
                val_dag,
                json_str_arr(&sample_lems)
            ));
        }
    }

    // Run telescope + expression hazard lints on targets and custom user definitions in statement closure
    let mut seen_keys: FxSet<(String, &'static str, u64)> = FxSet::default();
    for &ti in &target_indices {
        let j = ti as usize;
        if env.decls[j].kind == D_THM {
            audit_target_telescope(
                &env,
                &dg,
                &names_str,
                &bcls,
                &has_instance_for_induct,
                &all_hole_decls,
                j,
                &mut findings,
            );
        }
        let mut bn = Vec::new();
        let mut bt = Vec::new();
        let mut bp = Vec::new();
        let mut hp = Vec::new();
        scan_expr_hazards(
            &env,
            &dg,
            &names_str[j],
            env.decls[j].ty,
            &mut bn,
            &mut bt,
            &mut bp,
            0,
            &mut hp,
            false,
            false,
            &mut findings,
            &mut seen_keys,
        );
    }
    for (j, d) in env.decls.iter().enumerate() {
        if in_sc[j] && bcls[j] == 0 && d.kind == D_DEFN && !is_auto_boilerplate_name(&names_str[j]) && !all_hole_decls.contains(&j) {
            let mut def_arity = 0usize;
            let mut cur_ty = strip_mdata(&env, d.ty);
            while env.exprs[cur_ty as usize].kind == E_PI {
                def_arity += 1;
                cur_ty = strip_mdata(&env, env.exprs[cur_ty as usize].b);
            }
            let mut bn = Vec::new();
            let mut bt = Vec::new();
            let mut bp = Vec::new();
            let mut hp = Vec::new();
            scan_expr_hazards(
                &env,
                &dg,
                &names_str[j],
                d.val,
                &mut bn,
                &mut bt,
                &mut bp,
                def_arity,
                &mut hp,
                false,
                false,
                &mut findings,
                &mut seen_keys,
            );
        }
    }

    // Topological order of non-base declarations in statement closure
    let non_base_sc: Vec<bool> = (0..env.decls.len()).map(|j| in_sc[j] && bcls[j] != 1).collect();
    let topo = topo_sort_subset(&non_base_sc, &deps, &is_target);
    let custom_non_target_user = topo
        .iter()
        .filter(|&&j| !is_target[j] && env.decls[j].kind != D_REC && !is_auto_boilerplate_name(&names_str[j]) && env.decls[j].kind != D_CTOR)
        .count();

    // Build reading-set entries and optional `.lean` sheet
    let mut rs_json_items: Vec<String> = Vec::new();
    let mut rs_text = String::new();
    rs_text.push_str(&format!(
        "/-!\n# Minimal Statement Reading Set (generated by `fastverify` `expaudit`)\n\
         * Export: `{}`\n\
         * Base comparison mode: `{}`\n\
         * Statement closure: {} declarations ({} base, {} custom user-level, {} auto-generated boilerplate)\n\
         * Non-target custom definitions/inductives a human referee must inspect: **{}**\n-/\n\n",
        o.export_path, base.mode, sc_total, sc_base, sc_custom_user, sc_custom_auto, custom_non_target_user
    ));

    for &j in &topo {
        let d = &env.decls[j];
        let nm = &names_str[j];
        if d.kind == D_REC || d.kind == D_CTOR || is_auto_boilerplate_name(nm) {
            continue;
        }
        let role = if is_target[j] {
            "target_theorem"
        } else if hole_set.contains(&j) {
            "hole_definition"
        } else if bcls[j] == 2 {
            "base_modified"
        } else {
            match d.kind {
                D_DEFN => "custom_def",
                D_INDUCT => "custom_inductive",
                D_AXIOM => "custom_axiom",
                D_OPAQUE => "custom_opaque",
                D_THM => "helper_theorem_type",
                _ => "custom_other",
            }
        };
        let ty_s = pp_expr(&env, d.ty, 160, &[]);
        let body_s = match d.kind {
            D_DEFN | D_OPAQUE => Some(pp_expr(&env, d.val, 220, &[])),
            D_INDUCT => {
                let mut cs = Vec::new();
                for &c in &d.ctors {
                    let cn = env.name_str(c);
                    let cr = env.canon[c as usize];
                    let cdi = env.decl_of[cr as usize];
                    if cdi != NONE {
                        cs.push(format!("| {} : {}", cn, pp_expr(&env, env.decls[cdi as usize].ty, 100, &[])));
                    } else {
                        cs.push(format!("| {}", cn));
                    }
                }
                Some(cs.join("\n  "))
            }
            _ => None,
        };
        let ty_dag = dag_size_roots(&env, &[d.ty]);
        let val_dag = if matches!(d.kind, D_DEFN | D_OPAQUE) { dag_size_roots(&env, &[d.val]) } else { 0 };

        rs_text.push_str(&format!("-- [{}] (type DAG: {}, body DAG: {})\n", role, ty_dag, val_dag));
        match (d.kind, &body_s) {
            (D_INDUCT, Some(ctors_s)) => {
                rs_text.push_str(&format!("inductive {} : {} where\n  {}\n\n", nm, ty_s, ctors_s));
            }
            (D_DEFN, Some(b)) => {
                rs_text.push_str(&format!("def {} : {} :=\n  {}\n\n", nm, ty_s, b));
            }
            (D_OPAQUE, Some(b)) => {
                rs_text.push_str(&format!("opaque {} : {} := {}\n\n", nm, ty_s, b));
            }
            (D_THM, _) => {
                rs_text.push_str(&format!("theorem {} :\n  {} := sorry\n\n", nm, ty_s));
            }
            _ => {
                rs_text.push_str(&format!("{} {} : {}\n\n", kind_name(d.kind), nm, ty_s));
            }
        }

        rs_json_items.push(format!(
            "{{\"name\":{},\"kind\":{},\"role\":{},\"type_dag\":{},\"val_dag\":{},\"signature\":{},\"body\":{}}}",
            json_str(nm),
            json_str(kind_name(d.kind)),
            json_str(role),
            ty_dag,
            val_dag,
            json_str(&ty_s),
            match &body_s {
                Some(b) => json_str(b),
                None => "null".into(),
            }
        ));
    }

    if let Some(rs_path) = &o.reading_set {
        let mut f = File::create(rs_path).map_err(|e| Fail::Decline(format!("cannot write {}: {}", rs_path, e)))?;
        f.write_all(rs_text.as_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
    }

    // Sort findings deterministically: CRITICAL > HIGH > WARN > INFO
    findings.sort_by(|a, b| {
        severity_rank(b.severity)
            .cmp(&severity_rank(a.severity))
            .then_with(|| a.id.cmp(b.id))
            .then_with(|| a.decl.cmp(&b.decl))
    });

    let mut n_crit = 0usize;
    let mut n_high = 0usize;
    let mut n_warn = 0usize;
    let mut n_info = 0usize;
    for f in &findings {
        match f.severity {
            "CRITICAL" => n_crit += 1,
            "HIGH" => n_high += 1,
            "WARN" => n_warn += 1,
            _ => n_info += 1,
        }
    }

    let status = if n_crit > 0 {
        "CRITICAL"
    } else if n_high > 0 {
        "FLAGGED"
    } else if n_warn > 0 {
        "WARN"
    } else {
        "CLEAN"
    };

    if let Some(tsv_path) = &o.tsv_out {
        let mut w = std::io::BufWriter::new(
            File::create(tsv_path).map_err(|e| Fail::Decline(format!("cannot write {}: {}", tsv_path, e)))?,
        );
        writeln!(w, "severity\tid\tdecl\tsummary\tdetail").unwrap();
        for f in &findings {
            writeln!(
                w,
                "{}\t{}\t{}\t{}\t{}",
                f.severity,
                f.id,
                f.decl.replace('\t', " "),
                f.summary.replace('\t', " "),
                f.detail.replace('\t', " ")
            )
            .unwrap();
        }
    }

    let wall_s = t0.elapsed().as_secs_f64();
    let f_json: Vec<String> = findings
        .iter()
        .map(|f| {
            format!(
                "{{\"id\":{},\"severity\":{},\"source\":\"kernel_ast\",\"decl\":{},\"summary\":{},\"detail\":{}}}",
                json_str(f.id),
                json_str(f.severity),
                json_str(&f.decl),
                json_str(&f.summary),
                json_str(&f.detail)
            )
        })
        .collect();

    let exit_code = if let Some(thr) = &o.fail_on {
        let min_r = severity_rank(thr);
        if findings.iter().any(|f| severity_rank(f.severity) >= min_r) { 1 } else { 0 }
    } else {
        0
    };

    let js = format!(
        "{{\n  \"tool\": \"expaudit\",\n  \"version\": \"1.1\",\n  \"status\": {},\n  \"exit\": {},\n  \"wall_s\": {:.4},\n  \"challenge_export\": {},\n  \"comparator_config\": {},\n  \"base_mode\": {},\n  \"targets\": {{\n    \"theorem_names\": {},\n    \"definition_names\": {},\n    \"permitted_axioms\": {},\n    \"missing\": {}\n  }},\n  \"reading_set\": {{\n    \"statement_closure_decls\": {},\n    \"statement_closure_dag_nodes\": {},\n    \"base_decls\": {},\n    \"base_modified_decls\": {},\n    \"custom_total_decls\": {},\n    \"custom_user_decls\": {},\n    \"custom_non_target_user_decls\": {},\n    \"custom_auto_boilerplate_decls\": {},\n    \"pure_mathlib_statements\": {},\n    \"reading_set_file\": {},\n    \"declarations\": [\n      {}\n    ]\n  }},\n  \"proof_support\": {{\n    \"solution_mode\": {},\n    \"export_custom_theorems\": {},\n    \"targets\": [\n      {}\n    ]\n  }},\n  \"counts\": {{\"CRITICAL\": {}, \"HIGH\": {}, \"WARN\": {}, \"INFO\": {}}},\n  \"findings\": [\n    {}\n  ]\n}}\n",
        json_str(status),
        exit_code,
        wall_s,
        json_str(&o.export_path),
        match &o.config {
            Some(c) => json_str(c),
            None => "null".into(),
        },
        json_str(base.mode),
        json_str_arr(&cfg.theorem_names),
        json_str_arr(&cfg.definition_names),
        json_str_arr(&cfg.permitted_axioms),
        json_str_arr(&missing_targets),
        sc_total,
        sc_dag,
        sc_base,
        sc_base_mod,
        sc_custom_total,
        sc_custom_user,
        custom_non_target_user,
        sc_custom_auto,
        if custom_non_target_user == 0 && sc_base_mod == 0 { "true" } else { "false" },
        match &o.reading_set {
            Some(p) => json_str(p),
            None => "null".into(),
        },
        rs_json_items.join(",\n      "),
        if o.solution_mode { "true" } else { "false" },
        export_custom_theorems,
        proof_support_items.join(",\n      "),
        n_crit,
        n_high,
        n_warn,
        n_info,
        f_json.join(",\n    ")
    );

    if let Some(jp) = &o.json_out {
        let mut f = File::create(jp).map_err(|e| Fail::Decline(format!("cannot write {}: {}", jp, e)))?;
        f.write_all(js.as_bytes()).map_err(|e| Fail::Decline(e.to_string()))?;
    }
    print!("{}", js);

    let _ = AtomicUsize::new(0).load(Ordering::Relaxed);
    std::mem::forget(env);
    Ok(exit_code)
}

fn usage() -> ! {
    eprintln!(
        "usage:\n  expaudit index-base [-j N] [-v] -o OUT.baseidx BASE.export\n  \
         expaudit [audit] [-j N] [-v] [--solution-mode] [--config COMPARATOR.json] [--targets FILE|A,B]\n           \
         [--base BASE.export] [--base-index BASE.baseidx]\n           \
         [--reading-set OUT.lean] [--json OUT.json] [--tsv OUT.tsv]\n           \
         [--fail-on WARN|HIGH|CRITICAL] CHALLENGE_OR_SOLUTION.export"
    );
    std::process::exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        usage();
    }
    if args[0] == "--help" || args[0] == "-h" {
        usage();
    }
    if args[0] == "index-base" {
        let mut threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8);
        let mut verbose = false;
        let mut out_path: Option<String> = None;
        let mut files: Vec<String> = Vec::new();
        let mut i = 1usize;
        while i < args.len() {
            match args[i].as_str() {
                "-j" => {
                    i += 1;
                    threads = args.get(i).and_then(|s| s.parse().ok()).unwrap_or_else(|| usage());
                }
                "-v" => verbose = true,
                "-o" | "--out" => {
                    i += 1;
                    out_path = Some(args.get(i).cloned().unwrap_or_else(|| usage()));
                }
                s if s.starts_with('-') => usage(),
                s => files.push(s.to_string()),
            }
            i += 1;
        }
        if files.len() != 1 || out_path.is_none() {
            usage();
        }
        match cmd_index_base(threads.max(1), verbose, out_path.as_ref().unwrap(), &files[0]) {
            Ok(()) => std::process::exit(0),
            Err(Fail::Reject(m)) | Err(Fail::Decline(m)) => {
                eprintln!("expaudit: {}", m);
                std::process::exit(2);
            }
        }
    }

    let mut i = if args[0] == "audit" { 1usize } else { 0usize };
    let mut o = AuditOpts {
        threads: std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8),
        verbose: false,
        solution_mode: false,
        config: None,
        targets: None,
        base: None,
        base_index: None,
        reading_set: None,
        json_out: None,
        tsv_out: None,
        fail_on: None,
        export_path: String::new(),
    };
    let mut files: Vec<String> = Vec::new();
    while i < args.len() {
        let a = args[i].as_str();
        let mut next_val = || -> String {
            i += 1;
            args.get(i).cloned().unwrap_or_else(|| usage())
        };
        match a {
            "-j" | "--threads" => o.threads = next_val().parse().unwrap_or_else(|_| usage()),
            "-v" | "--verbose" => o.verbose = true,
            "--solution-mode" => o.solution_mode = true,
            "--config" => o.config = Some(next_val()),
            "--targets" => o.targets = Some(next_val()),
            "--base" => o.base = Some(next_val()),
            "--base-index" => o.base_index = Some(next_val()),
            "--reading-set" => o.reading_set = Some(next_val()),
            "--json" => o.json_out = Some(next_val()),
            "--tsv" => o.tsv_out = Some(next_val()),
            "--fail-on" => o.fail_on = Some(next_val()),
            _ if a.starts_with('-') => usage(),
            _ => files.push(a.to_string()),
        }
        i += 1;
    }
    if files.len() != 1 {
        usage();
    }
    o.threads = o.threads.max(1);
    o.export_path = files.remove(0);
    match cmd_audit(&o) {
        Ok(rc) => std::process::exit(rc),
        Err(Fail::Reject(m)) | Err(Fail::Decline(m)) => {
            eprintln!("expaudit: {}", m);
            std::process::exit(2);
        }
    }
}
