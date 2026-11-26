// expcompress — export-level (kernel-level) compression of a lean4export NDJSON export by SHARING.
//
//   expcompress EXPORT REDIRECTS_TSV TARGETS_FILE OUT_EXPORT [--stats FILE]
//
// REDIRECTS_TSV: lines "FROM<TAB>TO" (constant names).  Every reference (const node) to FROM is replaced by TO.
// The caller guarantees that FROM and TO are interchangeable (exphash: two theorems with the same statement - kernel
// hash incl. binder infos and level-parameter names - so by proof irrelevance every term stays well-typed; or two
// definitions with identical type and value), and that TO is declared before FROM in the export (no cycles).
// After redirecting, only what is reachable from TARGETS_FILE (whitespace-separated names: the export targets of the
// challenge, e.g. verify/challenge/export-targets.txt) is kept: names, levels, expressions and declarations are
// renumbered densely in their original order (the canonical numbering the trusted parser requires).
//
// This tool is UNTRUSTED: its output is only meaningful after the trusted check (fastverify check-sound.sh against the
// official challenge export) accepts it.  A wrong redirect can only make that check reject.
use serde_json::Value;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};

// ------------------------------------------------------------- JSON field scanner (same as exphash)
fn skip_ws(s: &[u8], mut i: usize) -> usize {
    while i < s.len() && (s[i] == b' ' || s[i] == b'\t' || s[i] == b'\r' || s[i] == b'\n') {
        i += 1;
    }
    i
}
fn skip_string(s: &[u8], mut i: usize) -> usize {
    i += 1;
    while i < s.len() {
        match s[i] {
            b'\\' => i += 2,
            b'"' => return i + 1,
            _ => i += 1,
        }
    }
    i
}
fn skip_value(s: &[u8], i: usize) -> usize {
    match s[i] {
        b'"' => skip_string(s, i),
        b'{' | b'[' => {
            let mut depth = 0i32;
            let mut j = i;
            while j < s.len() {
                match s[j] {
                    b'"' => {
                        j = skip_string(s, j);
                        continue;
                    }
                    b'{' | b'[' => depth += 1,
                    b'}' | b']' => {
                        depth -= 1;
                        if depth == 0 {
                            return j + 1;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            j
        }
        _ => {
            let mut j = i;
            while j < s.len() && s[j] != b',' && s[j] != b'}' && s[j] != b']' {
                j += 1;
            }
            j
        }
    }
}
fn fields<'a>(s: &'a [u8], i: usize, out: &mut Vec<(&'a [u8], &'a [u8])>) {
    out.clear();
    let mut i = skip_ws(s, i);
    if i >= s.len() || s[i] != b'{' {
        return;
    }
    i += 1;
    loop {
        i = skip_ws(s, i);
        if i >= s.len() || s[i] == b'}' {
            return;
        }
        if s[i] == b',' {
            i += 1;
            continue;
        }
        if s[i] != b'"' {
            return;
        }
        let ke = skip_string(s, i);
        let key = &s[i + 1..ke - 1];
        i = skip_ws(s, ke);
        if i >= s.len() || s[i] != b':' {
            return;
        }
        i = skip_ws(s, i + 1);
        let ve = skip_value(s, i);
        out.push((key, &s[i..ve]));
        i = ve;
    }
}
fn num(v: &[u8]) -> u64 {
    let mut x: u64 = 0;
    for &c in v {
        if c.is_ascii_digit() {
            x = x * 10 + (c - b'0') as u64;
        } else if c != b' ' {
            break;
        }
    }
    x
}
fn nums(v: &[u8]) -> Vec<u32> {
    let mut r = Vec::new();
    let mut cur: Option<u64> = None;
    for &c in v {
        if c.is_ascii_digit() {
            cur = Some(cur.unwrap_or(0) * 10 + (c - b'0') as u64);
        } else if let Some(x) = cur.take() {
            r.push(x as u32);
        }
    }
    if let Some(x) = cur {
        r.push(x as u32);
    }
    r
}
fn get<'a>(f: &[(&'a [u8], &'a [u8])], k: &[u8]) -> Option<&'a [u8]> {
    f.iter().find(|(a, _)| *a == k).map(|(_, v)| *v)
}
fn unquote(v: &[u8]) -> &[u8] {
    if v.len() >= 2 && v[0] == b'"' && v[v.len() - 1] == b'"' {
        &v[1..v.len() - 1]
    } else {
        v
    }
}

const K_BVAR: u8 = 1;
const K_SORT: u8 = 2;
const K_CONST: u8 = 3;
const K_APP: u8 = 4;
const K_BIND: u8 = 5; // lam / forallE
const K_LET: u8 = 7;
const K_LIT: u8 = 8;
const K_MDATA: u8 = 9;
const K_PROJ: u8 = 10;

#[derive(Default)]
struct Decl {
    defines: Vec<u32>,
    names: Vec<u32>,
    alls: Vec<u32>, // `all` lists (mutual block mates): kept alive with the declaration, not a dependency
    exprs: Vec<u32>,
}

fn collect_decl(v: &Value, top: bool, d: &mut Decl) {
    if let Some(o) = v.as_object() {
        for (k, x) in o {
            match k.as_str() {
                "name" => {
                    if let Some(n) = x.as_u64() {
                        d.names.push(n as u32);
                        let _ = top;
                        d.defines.push(n as u32);
                    }
                }
                "all" => {
                    if let Some(a) = x.as_array() {
                        for y in a {
                            if let Some(n) = y.as_u64() {
                                d.alls.push(n as u32);
                            }
                        }
                    }
                }
                "levelParams" | "induct" | "ctor" => {
                    if let Some(n) = x.as_u64() {
                        d.names.push(n as u32);
                    } else if let Some(a) = x.as_array() {
                        for y in a {
                            if let Some(n) = y.as_u64() {
                                d.names.push(n as u32);
                            }
                        }
                    }
                }
                "ctors" => {
                    if let Some(a) = x.as_array() {
                        for y in a {
                            if let Some(n) = y.as_u64() {
                                d.names.push(n as u32);
                            } else {
                                collect_decl(y, false, d);
                            }
                        }
                    }
                }
                "type" | "value" | "rhs" => {
                    if let Some(n) = x.as_u64() {
                        d.exprs.push(n as u32);
                    }
                }
                "types" | "recs" | "rules" => {
                    if let Some(a) = x.as_array() {
                        for y in a {
                            collect_decl(y, false, d);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Ctx {
    Name,
    Level,
    Expr,
    Decl,
}
#[derive(Clone, Copy, PartialEq)]
enum Cls {
    N,
    L,
    E,
    Lit,
    ConstName,
}
fn key_class(ctx: Ctx, key: &[u8], in_const: bool) -> Cls {
    match ctx {
        Ctx::Name => match key {
            b"in" | b"pre" => Cls::N,
            _ => Cls::Lit,
        },
        Ctx::Level => match key {
            b"il" | b"succ" | b"max" | b"imax" => Cls::L,
            b"param" => Cls::N,
            _ => Cls::Lit,
        },
        Ctx::Expr => match key {
            b"ie" | b"arg" | b"fn" | b"body" | b"type" | b"value" | b"struct" | b"expr" => Cls::E,
            b"sort" | b"us" => Cls::L,
            b"name" => {
                if in_const {
                    Cls::ConstName
                } else {
                    Cls::N
                }
            }
            b"typeName" => Cls::ConstName, // projections follow the redirect of their structure
            _ => Cls::Lit,
        },
        Ctx::Decl => match key {
            b"name" | b"all" | b"levelParams" | b"induct" | b"ctor" | b"ctors" => Cls::N,
            b"type" | b"value" | b"rhs" => Cls::E,
            _ => Cls::Lit,
        },
    }
}

struct Maps<'a> {
    nmap: &'a [u32],
    lmap: &'a [u32],
    emap: &'a [u32],
    redirect: &'a HashMap<u32, u32>,
}

/// copy `line` to `out`, replacing every index number according to its key's class
fn remap_line(line: &[u8], ctx: Ctx, m: &Maps, out: &mut Vec<u8>) -> Result<(), String> {
    // stack of (is_object, current key) ; arrays inherit the key of the enclosing object member
    let mut stack: Vec<(bool, Vec<u8>)> = Vec::with_capacity(8);
    let in_const = ctx == Ctx::Expr && line.windows(9).any(|w| w == b"{\"const\":");
    let mut i = 0;
    let s = line;
    let mut expect_key = false;
    while i < s.len() {
        let c = s[i];
        match c {
            b'{' => {
                stack.push((true, Vec::new()));
                expect_key = true;
                out.push(c);
                i += 1;
            }
            b'[' => {
                let k = stack.last().map(|x| x.1.clone()).unwrap_or_default();
                stack.push((false, k));
                out.push(c);
                i += 1;
            }
            b'}' | b']' => {
                stack.pop();
                out.push(c);
                i += 1;
            }
            b',' => {
                if let Some(t) = stack.last() {
                    expect_key = t.0;
                }
                out.push(c);
                i += 1;
            }
            b':' => {
                expect_key = false;
                out.push(c);
                i += 1;
            }
            b'"' => {
                let e = skip_string(s, i);
                if expect_key {
                    if let Some(t) = stack.last_mut() {
                        t.1 = s[i + 1..e - 1].to_vec();
                    }
                }
                out.extend_from_slice(&s[i..e]);
                i = e;
            }
            b'0'..=b'9' => {
                let mut j = i;
                while j < s.len() && s[j].is_ascii_digit() {
                    j += 1;
                }
                let x = num(&s[i..j]) as usize;
                let key: &[u8] = stack.last().map(|t| t.1.as_slice()).unwrap_or(b"");
                let y = match key_class(ctx, key, in_const) {
                    Cls::N => *m.nmap.get(x).ok_or("name index out of range")?,
                    Cls::L => *m.lmap.get(x).ok_or("level index out of range")?,
                    Cls::E => *m.emap.get(x).ok_or("expr index out of range")?,
                    Cls::ConstName => {
                        let r = *m.redirect.get(&(x as u32)).unwrap_or(&(x as u32)) as usize;
                        *m.nmap.get(r).ok_or("name index out of range")?
                    }
                    Cls::Lit => x as u32,
                };
                if y == u32::MAX {
                    return Err(format!("dead index referenced (key {:?})", String::from_utf8_lossy(key)));
                }
                out.extend_from_slice(y.to_string().as_bytes());
                i = j;
            }
            _ => {
                out.push(c);
                i += 1;
            }
        }
    }
    Ok(())
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    let stats_path = if let Some(p) = args.iter().position(|a| a == "--stats") {
        let f = args[p + 1].clone();
        args.remove(p);
        args.remove(p);
        Some(f)
    } else {
        None
    };
    let choose = if let Some(p) = args.iter().position(|a| a == "--choose") {
        args.remove(p);
        true
    } else {
        false
    };
    let write_redirects = if let Some(p) = args.iter().position(|a| a == "--write-redirects") {
        let f = args[p + 1].clone();
        args.remove(p);
        args.remove(p);
        Some(f)
    } else {
        None
    };
    if args.len() < 5 {
        eprintln!("usage: expcompress EXPORT (REDIRECTS_TSV | --choose CLASSES_TSV) TARGETS_FILE OUT_EXPORT [--stats FILE] [--write-redirects FILE]");
        std::process::exit(2);
    }
    let t0 = std::time::Instant::now();
    // ---------------------------------------------------------------- pass 1: structure
    let mut npre: Vec<u32> = vec![0];
    let mut ncomp: Vec<Box<str>> = vec!["".into()];
    let mut lkind: Vec<u8> = vec![0];
    let mut la: Vec<u32> = vec![0];
    let mut lb: Vec<u32> = vec![0];
    let mut ek: Vec<u8> = Vec::new();
    let mut e1: Vec<u32> = Vec::new();
    let mut e2: Vec<u32> = Vec::new();
    let mut e3: Vec<u32> = Vec::new();
    let mut e4: Vec<u32> = Vec::new();
    let mut lists: Vec<Vec<u32>> = Vec::new();
    let mut list_ix: HashMap<Vec<u32>, u32> = HashMap::new();
    let mut decls: Vec<Decl> = Vec::new();
    let mut name2decl: HashMap<u32, u32> = HashMap::new();
    {
        let f = File::open(&args[1]).expect("open export");
        let mut rd = BufReader::with_capacity(64 << 20, f);
        let mut line: Vec<u8> = Vec::with_capacity(1 << 20);
        let mut f1: Vec<(&[u8], &[u8])> = Vec::with_capacity(16);
        let mut f2: Vec<(&[u8], &[u8])> = Vec::with_capacity(16);
        let mut nl: u64 = 0;
        loop {
            line.clear();
            if rd.read_until(b'\n', &mut line).expect("read") == 0 {
                break;
            }
            nl += 1;
            let l: &[u8] = unsafe { std::slice::from_raw_parts(line.as_ptr(), line.len()) };
            fields(l, 0, &mut f1);
            if f1.is_empty() {
                continue;
            }
            let (k0, v0) = f1[0];
            if k0 == b"in" {
                let idx = num(v0) as usize;
                let (k1, v1) = f1[1];
                fields(v1, 0, &mut f2);
                let pre = get(&f2, b"pre").map(num).unwrap_or(0) as u32;
                let comp = if k1 == b"str" {
                    String::from_utf8_lossy(unquote(get(&f2, b"str").unwrap_or(b""))).into_owned()
                } else {
                    format!("{}", get(&f2, b"i").map(num).unwrap_or(0))
                };
                assert_eq!(idx, npre.len(), "sparse name index");
                npre.push(pre);
                ncomp.push(comp.into_boxed_str());
                continue;
            }
            if k0 == b"il" {
                let idx = num(v0) as usize;
                let (k1, v1) = f1[1];
                assert_eq!(idx, lkind.len(), "sparse level index");
                match k1 {
                    b"succ" => {
                        lkind.push(1);
                        la.push(num(v1) as u32);
                        lb.push(0);
                    }
                    b"max" | b"imax" => {
                        let xs = nums(v1);
                        lkind.push(2);
                        la.push(xs[0]);
                        lb.push(xs[1]);
                    }
                    _ => {
                        lkind.push(3); // param
                        la.push(num(v1) as u32);
                        lb.push(0);
                    }
                }
                continue;
            }
            let (ie_v, kf) = if k0 == b"ie" && f1.len() >= 2 {
                (Some(v0), f1[1])
            } else if f1.len() >= 2 && f1[f1.len() - 1].0 == b"ie" {
                (Some(f1[f1.len() - 1].1), f1[0])
            } else {
                (None, f1[0])
            };
            if let Some(iev) = ie_v {
                let idx = num(iev) as usize;
                assert_eq!(idx, ek.len(), "sparse expr index");
                let (kk, kv) = kf;
                let (k, a, b, c, d): (u8, u32, u32, u32, u32) = match kk {
                    b"bvar" => (K_BVAR, 0, 0, 0, 0),
                    b"sort" => (K_SORT, num(kv) as u32, 0, 0, 0),
                    b"const" => {
                        fields(kv, 0, &mut f2);
                        let nm = get(&f2, b"name").map(num).unwrap_or(0) as u32;
                        let us = get(&f2, b"us").map(nums).unwrap_or_default();
                        let li = match list_ix.get(&us) {
                            Some(&i) => i,
                            None => {
                                let i = lists.len() as u32;
                                lists.push(us.clone());
                                list_ix.insert(us, i);
                                i
                            }
                        };
                        (K_CONST, nm, li, 0, 0)
                    }
                    b"app" => {
                        fields(kv, 0, &mut f2);
                        (K_APP, get(&f2, b"fn").map(num).unwrap_or(0) as u32, get(&f2, b"arg").map(num).unwrap_or(0) as u32, 0, 0)
                    }
                    b"lam" | b"forallE" => {
                        fields(kv, 0, &mut f2);
                        (
                            K_BIND,
                            get(&f2, b"body").map(num).unwrap_or(0) as u32,
                            get(&f2, b"type").map(num).unwrap_or(0) as u32,
                            get(&f2, b"name").map(num).unwrap_or(0) as u32,
                            0,
                        )
                    }
                    b"letE" => {
                        fields(kv, 0, &mut f2);
                        (
                            K_LET,
                            get(&f2, b"body").map(num).unwrap_or(0) as u32,
                            get(&f2, b"type").map(num).unwrap_or(0) as u32,
                            get(&f2, b"value").map(num).unwrap_or(0) as u32,
                            get(&f2, b"name").map(num).unwrap_or(0) as u32,
                        )
                    }
                    b"natVal" | b"strVal" => (K_LIT, 0, 0, 0, 0),
                    b"mdata" => {
                        fields(kv, 0, &mut f2);
                        if get(&f2, b"data").is_some() {
                            eprintln!("expcompress: mdata with data is not supported (line {})", nl);
                            std::process::exit(2);
                        }
                        (K_MDATA, get(&f2, b"expr").map(num).unwrap_or(0) as u32, 0, 0, 0)
                    }
                    b"proj" => {
                        fields(kv, 0, &mut f2);
                        (
                            K_PROJ,
                            get(&f2, b"struct").map(num).unwrap_or(0) as u32,
                            get(&f2, b"typeName").map(num).unwrap_or(0) as u32,
                            0,
                            0,
                        )
                    }
                    _ => {
                        eprintln!("expcompress: unknown expression kind at line {}", nl);
                        std::process::exit(2);
                    }
                };
                ek.push(k);
                e1.push(a);
                e2.push(b);
                e3.push(c);
                e4.push(d);
                continue;
            }
            // declaration
            let v: Value = serde_json::from_slice(l).expect("decl json");
            let o = v.as_object().expect("object");
            let (dk, dv) = o.iter().next().expect("key");
            if dk == "meta" {
                continue;
            }
            let mut d = Decl::default();
            collect_decl(dv, true, &mut d);
            let di = decls.len() as u32;
            for &n in &d.defines {
                name2decl.insert(n, di);
            }
            decls.push(d);
        }
        eprintln!(
            "[{:.1}s] pass 1: {} names, {} levels, {} exprs, {} decls",
            t0.elapsed().as_secs_f64(),
            npre.len(),
            lkind.len(),
            ek.len(),
            decls.len()
        );
    }
    // decl names as strings
    let full = |mut i: usize| -> String {
        let mut parts: Vec<&str> = Vec::new();
        while i != 0 {
            parts.push(&ncomp[i]);
            i = npre[i] as usize;
        }
        parts.reverse();
        parts.join(".")
    };
    let mut byname: HashMap<String, u32> = HashMap::new();
    for &n in name2decl.keys() {
        byname.insert(full(n as usize), n);
    }
    // redirects
    let mut redirect: HashMap<u32, u32> = HashMap::new();
    let mut bad_redirects = 0u64;
    let mut choose_info = String::new();
    let mut deps_csr: Option<(Vec<u64>, Vec<u32>)> = None;
    if !choose {
        for l in std::fs::read_to_string(&args[2]).expect("redirects").lines() {
            let mut it = l.split('\t');
            let (a, b) = (it.next().unwrap_or(""), it.next().unwrap_or(""));
            match (byname.get(a), byname.get(b)) {
                (Some(&x), Some(&y)) if x != y => {
                    // TO must be declared before FROM (no cycles)
                    if name2decl[&y] < name2decl[&x] {
                        redirect.insert(x, y);
                    } else {
                        bad_redirects += 1;
                    }
                }
                _ => bad_redirects += 1,
            }
        }
    } else {
        // ---- --choose: pick one representative per class, cheapest first, acyclic by construction + SCC fallback
        // direct dependencies of every declaration (decl indices), CSR
        let nd = decls.len();
        let mut stamp: Vec<u32> = vec![u32::MAX; ek.len()];
        let mut doff: Vec<u64> = Vec::with_capacity(nd + 1);
        #[allow(unused_assignments)]
        let mut dtgt: Vec<u32> = Vec::new();
        let mut st: Vec<u32> = Vec::new();
        let mut tmp: Vec<u32> = Vec::new();
        for d in 0..nd {
            doff.push(dtgt.len() as u64);
            tmp.clear();
            for &n in &decls[d].names {
                if let Some(&t) = name2decl.get(&n) {
                    if t as usize != d {
                        tmp.push(t);
                    }
                }
            }
            st.clear();
            st.extend_from_slice(&decls[d].exprs);
            while let Some(e) = st.pop() {
                let e = e as usize;
                if stamp[e] == d as u32 {
                    continue;
                }
                stamp[e] = d as u32;
                match ek[e] {
                    K_CONST => {
                        if let Some(&t) = name2decl.get(&e1[e]) {
                            if t as usize != d {
                                tmp.push(t);
                            }
                        }
                    }
                    K_APP => {
                        st.push(e1[e]);
                        st.push(e2[e]);
                    }
                    K_BIND => {
                        st.push(e1[e]);
                        st.push(e2[e]);
                    }
                    K_LET => {
                        st.push(e1[e]);
                        st.push(e2[e]);
                        st.push(e3[e]);
                    }
                    K_MDATA => st.push(e1[e]),
                    K_PROJ => {
                        st.push(e1[e]);
                        if let Some(&t) = name2decl.get(&e2[e]) {
                            if t as usize != d {
                                tmp.push(t);
                            }
                        }
                    }
                    _ => {}
                }
            }
            tmp.sort_unstable();
            tmp.dedup();
            dtgt.extend_from_slice(&tmp);
        }
        doff.push(dtgt.len() as u64);
        drop(stamp);
        eprintln!("[{:.1}s] dependency graph: {} decls, {} edges", t0.elapsed().as_secs_f64(), nd, dtgt.len());
        // classes: name \t key \t redirectable \t cost
        struct M {
            d: u32,
            n: u32,
            red: bool,
            cost: u64,
        }
        let mut classes: HashMap<String, Vec<M>> = HashMap::new();
        // fixed redirects ("R<TAB>FROM<TAB>TO", e.g. whole inductive blocks: always to the earliest block)
        let mut fixed: Vec<(u32, u32)> = Vec::new();
        for l in std::fs::read_to_string(&args[2]).expect("classes").lines() {
            let p: Vec<&str> = l.split('\t').collect();
            if p.len() == 3 && p[0] == "R" {
                match (byname.get(p[1]), byname.get(p[2])) {
                    (Some(&x), Some(&y)) if name2decl[&y] < name2decl[&x] => fixed.push((x, y)),
                    _ => bad_redirects += 1,
                }
                continue;
            }
            if p.len() < 4 {
                continue;
            }
            if let Some(&n) = byname.get(p[0]) {
                let d = name2decl[&n];
                if decls[d as usize].defines.len() != 1 {
                    continue; // only single-constant declarations are chosen here
                }
                classes.entry(p[1].to_string()).or_default().push(M { d, n, red: p[2] == "1", cost: p[3].parse().unwrap_or(0) });
            } else {
                bad_redirects += 1;
            }
        }
        let mut cl: Vec<Vec<M>> = classes.into_values().filter(|v| v.len() >= 2 && v.iter().any(|m| m.red)).collect();
        for v in cl.iter_mut() {
            v.sort_by_key(|m| m.d);
        }
        // member -> class index (for the direct-reference test)
        let mut cls_of: HashMap<u32, u32> = HashMap::new();
        for (ci, v) in cl.iter().enumerate() {
            for m in v {
                cls_of.insert(m.d, ci as u32);
            }
        }
        let deps = |d: u32| -> &[u32] { &dtgt[doff[d as usize] as usize..doff[d as usize + 1] as usize] };
        let mut rep: Vec<usize> = vec![0; cl.len()]; // index into the class vector
        let mut fallback = vec![false; cl.len()];
        for (ci, v) in cl.iter().enumerate() {
            let mut best: Option<(u64, usize)> = None;
            for (k, m) in v.iter().enumerate() {
                if deps(m.d).iter().any(|t| cls_of.get(t) == Some(&(ci as u32))) {
                    continue; // directly uses another member: never a representative
                }
                let c = if m.red { m.cost } else { 0 };
                if best.map_or(true, |b| c < b.0) {
                    best = Some((c, k));
                }
            }
            rep[ci] = best.map(|b| b.1).unwrap_or(0);
        }
        let mut iter = 0;
        loop {
            iter += 1;
            // decl-level redirect for this choice
            let mut rd: HashMap<u32, u32> = HashMap::new();
            for &(x, y) in &fixed {
                rd.insert(name2decl[&x], name2decl[&y]);
            }
            for (ci, v) in cl.iter().enumerate() {
                let r = &v[rep[ci]];
                for (k, m) in v.iter().enumerate() {
                    if k != rep[ci] && m.red {
                        rd.insert(m.d, r.d);
                    }
                }
            }
            // Tarjan SCC (iterative) over non-redirected decls with redirected edges
            let mut index = vec![u32::MAX; nd];
            let mut low = vec![0u32; nd];
            let mut onst = vec![false; nd];
            let mut sstack: Vec<u32> = Vec::new();
            let mut cyc_nodes: Vec<u32> = Vec::new();
            let mut idx: u32 = 0;
            let tgt = |t: u32| -> u32 { *rd.get(&t).unwrap_or(&t) };
            for root in 0..nd as u32 {
                if index[root as usize] != u32::MAX || rd.contains_key(&root) {
                    continue;
                }
                let mut cs: Vec<(u32, usize)> = vec![(root, 0)];
                index[root as usize] = idx;
                low[root as usize] = idx;
                idx += 1;
                sstack.push(root);
                onst[root as usize] = true;
                while let Some(&mut (v, ref mut ei)) = cs.last_mut() {
                    let ds = deps(v);
                    if *ei < ds.len() {
                        let w = tgt(ds[*ei]);
                        *ei += 1;
                        if w == v {
                            cyc_nodes.push(v); // self loop
                            continue;
                        }
                        if index[w as usize] == u32::MAX {
                            index[w as usize] = idx;
                            low[w as usize] = idx;
                            idx += 1;
                            sstack.push(w);
                            onst[w as usize] = true;
                            cs.push((w, 0));
                        } else if onst[w as usize] {
                            low[v as usize] = low[v as usize].min(index[w as usize]);
                        }
                    } else {
                        cs.pop();
                        if let Some(&(u, _)) = cs.last() {
                            low[u as usize] = low[u as usize].min(low[v as usize]);
                        }
                        if low[v as usize] == index[v as usize] {
                            let mut comp: Vec<u32> = Vec::new();
                            loop {
                                let w = sstack.pop().unwrap();
                                onst[w as usize] = false;
                                comp.push(w);
                                if w == v {
                                    break;
                                }
                            }
                            if comp.len() > 1 {
                                cyc_nodes.extend_from_slice(&comp);
                            }
                        }
                    }
                }
            }
            if cyc_nodes.is_empty() {
                break;
            }
            let cyc: std::collections::HashSet<u32> = cyc_nodes.into_iter().collect();
            let mut changed = 0;
            for (ci, v) in cl.iter().enumerate() {
                if !fallback[ci] && cyc.contains(&v[rep[ci]].d) {
                    fallback[ci] = true;
                    rep[ci] = 0; // earliest member
                    changed += 1;
                }
            }
            eprintln!("choose: iteration {}: {} decls on cycles, {} classes fall back to the earliest member", iter, cyc.len(), changed);
            if changed == 0 {
                // cycles not caused by a chosen representative: drop the redirects of every class touching them
                for (ci, v) in cl.iter().enumerate() {
                    if v.iter().any(|m| cyc.contains(&m.d)) {
                        fallback[ci] = true;
                        rep[ci] = 0;
                    }
                }
                if iter > 50 {
                    eprintln!("expcompress: cannot make the redirects acyclic");
                    std::process::exit(2);
                }
            }
        }
        let nfb = fallback.iter().filter(|&&x| x).count();
        let mut nred = 0u64;
        for &(x, y) in &fixed {
            redirect.insert(x, y);
            nred += 1;
        }
        for (ci, v) in cl.iter().enumerate() {
            let r = &v[rep[ci]];
            for (k, m) in v.iter().enumerate() {
                if k != rep[ci] && m.red {
                    redirect.insert(m.n, r.n);
                    nred += 1;
                }
            }
        }
        choose_info = format!(", \"classes\": {}, \"fallback_classes\": {}, \"choose_iterations\": {}", cl.len(), nfb, iter);
        deps_csr = Some((std::mem::take(&mut doff), std::mem::take(&mut dtgt)));
        eprintln!("[{:.1}s] choose: {} classes, {} redirects, {} classes fell back to the earliest member, {} iterations", t0.elapsed().as_secs_f64(), cl.len(), nred, nfb, iter);
    }
    if let Some(p) = &write_redirects {
        let mut w = BufWriter::new(File::create(p).expect("write redirects"));
        for (a, b) in redirect.iter() {
            writeln!(w, "{}\t{}", full(*a as usize), full(*b as usize)).unwrap();
        }
    }
    // chains a->b->c: resolve to the final target
    let keys: Vec<u32> = redirect.keys().cloned().collect();
    for k in keys {
        let mut t = redirect[&k];
        let mut steps = 0;
        while let Some(&u) = redirect.get(&t) {
            t = u;
            steps += 1;
            if steps > 64 {
                break;
            }
        }
        redirect.insert(k, t);
    }
    eprintln!("redirects: {} applied, {} rejected (unknown name or wrong order)", redirect.len(), bad_redirects);
    // ---------------------------------------------------------------- reachability from the targets
    let mut live_n = vec![false; npre.len()];
    let mut live_l = vec![false; lkind.len()];
    let mut live_e = vec![false; ek.len()];
    let mut live_d = vec![false; decls.len()];
    let mut dstack: Vec<u32> = Vec::new();
    let mut missing_targets = Vec::new();
    for t in std::fs::read_to_string(&args[3]).expect("targets").split_whitespace() {
        match byname.get(t) {
            Some(n) => dstack.push(name2decl[n]),
            None => missing_targets.push(t.to_string()),
        }
    }
    if !missing_targets.is_empty() {
        eprintln!("expcompress: targets not in the export: {:?}", missing_targets);
    }
    fn mark_name(live_n: &mut [bool], npre: &[u32], mut n: u32) {
        while n != 0 && !live_n[n as usize] {
            live_n[n as usize] = true;
            n = npre[n as usize];
        }
    }
    let mut estack: Vec<u32> = Vec::new();
    let mut lstack: Vec<u32> = Vec::new();
    while let Some(d) = dstack.pop() {
        if live_d[d as usize] {
            continue;
        }
        live_d[d as usize] = true;
        let dd = &decls[d as usize];
        for &n in dd.names.iter().chain(dd.alls.iter()) {
            mark_name(&mut live_n, &npre, n);
            if let Some(&di) = name2decl.get(&n) {
                if !live_d[di as usize] {
                    dstack.push(di);
                }
            }
        }
        for &e in &dd.exprs {
            estack.push(e);
        }
        while let Some(e) = estack.pop() {
            let e = e as usize;
            if live_e[e] {
                continue;
            }
            live_e[e] = true;
            match ek[e] {
                K_SORT => lstack.push(e1[e]),
                K_CONST => {
                    let n = *redirect.get(&e1[e]).unwrap_or(&e1[e]);
                    mark_name(&mut live_n, &npre, n);
                    if let Some(&di) = name2decl.get(&n) {
                        if !live_d[di as usize] {
                            dstack.push(di);
                        }
                    }
                    for &l in &lists[e2[e] as usize] {
                        lstack.push(l);
                    }
                }
                K_APP => {
                    estack.push(e1[e]);
                    estack.push(e2[e]);
                }
                K_BIND => {
                    estack.push(e1[e]);
                    estack.push(e2[e]);
                    mark_name(&mut live_n, &npre, e3[e]);
                }
                K_LET => {
                    estack.push(e1[e]);
                    estack.push(e2[e]);
                    estack.push(e3[e]);
                    mark_name(&mut live_n, &npre, e4[e]);
                }
                K_MDATA => estack.push(e1[e]),
                K_PROJ => {
                    estack.push(e1[e]);
                    let tn = *redirect.get(&e2[e]).unwrap_or(&e2[e]);
                    mark_name(&mut live_n, &npre, tn);
                    if let Some(&di) = name2decl.get(&tn) {
                        if !live_d[di as usize] {
                            dstack.push(di);
                        }
                    }
                }
                _ => {}
            }
        }
        while let Some(l) = lstack.pop() {
            let l = l as usize;
            if l == 0 || live_l[l] {
                continue;
            }
            live_l[l] = true;
            match lkind[l] {
                1 => lstack.push(la[l]),
                2 => {
                    lstack.push(la[l]);
                    lstack.push(lb[l]);
                }
                _ => mark_name(&mut live_n, &npre, la[l]),
            }
        }
    }
    // dense renumbering
    let mk = |live: &[bool], implicit0: bool| -> Vec<u32> {
        let mut m = vec![u32::MAX; live.len()];
        let mut c: u32 = 0;
        for (i, &x) in live.iter().enumerate() {
            if i == 0 && implicit0 {
                m[0] = 0;
                c = 1;
                continue;
            }
            if x {
                m[i] = c;
                c += 1;
            }
        }
        m
    };
    let nmap = mk(&live_n, true);
    let lmap = mk(&live_l, true);
    let emap = mk(&live_e, false);
    let kept = |v: &[bool]| v.iter().filter(|&&x| x).count();
    eprintln!(
        "[{:.1}s] live: names {}/{}, levels {}/{}, exprs {}/{}, decls {}/{}",
        t0.elapsed().as_secs_f64(),
        kept(&live_n),
        npre.len() - 1,
        kept(&live_l),
        lkind.len() - 1,
        kept(&live_e),
        ek.len(),
        kept(&live_d),
        decls.len()
    );
    // ---------------------------------------------------------------- pass 2: emit
    // Output order: meta, all live names, all live levels, all live expressions (each group in its original order, so
    // every line only references lines above it), then the declarations - in --choose mode in a topological order of
    // the redirected dependency graph (a representative may come later in the input than its users), else in the
    // original order (which is topological because redirect targets are earlier).
    let maps = Maps { nmap: &nmap, lmap: &lmap, emap: &emap, redirect: &redirect };
    let nd = decls.len();
    let order: Vec<u32> = match &deps_csr {
        None => (0..nd as u32).collect(),
        Some((doff, dtgt)) => {
            let mut rdecl: HashMap<u32, u32> = HashMap::new();
            for (x, y) in redirect.iter() {
                rdecl.insert(name2decl[x], name2decl[y]);
            }
            let mut seen = vec![false; nd];
            let mut ord: Vec<u32> = Vec::with_capacity(nd);
            for r in 0..nd as u32 {
                if !live_d[r as usize] || seen[r as usize] {
                    continue;
                }
                let mut cs: Vec<(u32, u64)> = vec![(r, doff[r as usize])];
                seen[r as usize] = true;
                while let Some(&mut (v, ref mut ei)) = cs.last_mut() {
                    if *ei < doff[v as usize + 1] {
                        let t = dtgt[*ei as usize];
                        *ei += 1;
                        let w = *rdecl.get(&t).unwrap_or(&t);
                        if live_d[w as usize] && !seen[w as usize] {
                            seen[w as usize] = true;
                            cs.push((w, doff[w as usize]));
                        }
                    } else {
                        ord.push(v);
                        cs.pop();
                    }
                }
            }
            ord
        }
    };
    let mut w = BufWriter::with_capacity(64 << 20, File::create(&args[4]).expect("create out"));
    let mut line: Vec<u8> = Vec::with_capacity(1 << 20);
    let mut outl: Vec<u8> = Vec::with_capacity(1 << 20);
    let mut f1: Vec<(&[u8], &[u8])> = Vec::with_capacity(16);
    let (mut out_bytes, mut out_lines) = (0u64, 0u64);
    let mut decl_lines: Vec<Option<Vec<u8>>> = vec![None; nd];
    for phase in 0..2 {
        let f = File::open(&args[1]).expect("open export");
        let mut rd = BufReader::with_capacity(64 << 20, f);
        let mut di = 0usize;
        loop {
            line.clear();
            if rd.read_until(b'\n', &mut line).expect("read") == 0 {
                break;
            }
            let l: &[u8] = unsafe { std::slice::from_raw_parts(line.as_ptr(), line.len()) };
            fields(l, 0, &mut f1);
            if f1.is_empty() {
                continue;
            }
            let (k0, v0) = f1[0];
            let (ctx, live) = if k0 == b"in" {
                (Ctx::Name, live_n[num(v0) as usize])
            } else if k0 == b"il" {
                (Ctx::Level, live_l[num(v0) as usize])
            } else if k0 == b"ie" && f1.len() >= 2 {
                (Ctx::Expr, live_e[num(v0) as usize])
            } else if f1.len() >= 2 && f1[f1.len() - 1].0 == b"ie" {
                (Ctx::Expr, live_e[num(f1[f1.len() - 1].1) as usize])
            } else if k0 == b"meta" {
                if phase == 0 {
                    w.write_all(l).unwrap();
                    out_bytes += l.len() as u64;
                    out_lines += 1;
                }
                continue;
            } else {
                let x = live_d[di];
                di += 1;
                (Ctx::Decl, x)
            };
            if !live {
                continue;
            }
            let mine = match ctx {
                Ctx::Name | Ctx::Level => phase == 0,
                _ => phase == 1,
            };
            if !mine {
                continue;
            }
            outl.clear();
            if let Err(e) = remap_line(l, ctx, &maps, &mut outl) {
                eprintln!("expcompress: {} in line: {}", e, String::from_utf8_lossy(l));
                std::process::exit(2);
            }
            if ctx == Ctx::Decl {
                decl_lines[di - 1] = Some(outl.clone());
                continue;
            }
            w.write_all(&outl).unwrap();
            out_bytes += outl.len() as u64;
            out_lines += 1;
        }
    }
    for d in order {
        if let Some(l) = decl_lines[d as usize].take() {
            w.write_all(&l).unwrap();
            out_bytes += l.len() as u64;
            out_lines += 1;
        }
    }
    w.flush().unwrap();
    let msg = format!(
        "{{\"redirects\": {}, \"redirects_rejected\": {}, \"names\": [{}, {}], \"levels\": [{}, {}], \"exprs\": [{}, {}], \"decl_lines\": [{}, {}], \"out_bytes\": {}, \"out_lines\": {}, \"seconds\": {:.1}{}}}",
        redirect.len(),
        bad_redirects,
        kept(&live_n),
        npre.len() - 1,
        kept(&live_l),
        lkind.len() - 1,
        kept(&live_e),
        ek.len(),
        kept(&live_d),
        decls.len(),
        out_bytes,
        out_lines,
        t0.elapsed().as_secs_f64(),
        choose_info
    );
    eprintln!("{}", msg);
    if let Some(p) = stats_path {
        std::fs::write(p, msg + "\n").unwrap();
    }
}
