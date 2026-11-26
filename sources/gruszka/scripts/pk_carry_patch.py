# M8: applied after pk_counts_patch.py to Pestka's generated Rust (sources
# untouched). Usage: pk_carry_patch.py check/tc/mod.rs check/decl/mod.rs
#  - PK_NOCARRY=1: nothing kept across declarations (`carried` returns empty
#    maps); PK_NOCARRY=2: only the closed-term map kept.
#  - columns 9-14 of the PC J line: closed-type hits, closed-pair hits,
#    closed-fail hits, then the three misses (cachedType / known /
#    knownDifferent on shared terms).
#  - PK_TRACE=<declaration name>: "unfold C" (machine) and "lazyunfold C"
#    lines for that declaration.
import sys
tc, dc = sys.argv[1], sys.argv[2]
s = open(tc).read()
def sub(a, b):
    global s
    assert s.count(a) == 1, a
    s = s.replace(a, b)
sub("if crate::aver_generated::check::tc::shared(e) { { let __arg3 @ _ = crate::aver_generated::check::state::cacheGet(&st.closed, e); crate::aver_generated::check::tc::orCached",
    "if crate::aver_generated::check::tc::shared(e) { { let __arg3 @ _ = crate::aver_generated::check::state::cacheGet(&st.closed, e); if __arg3.is_some() { pkx_bump(0); } else { pkx_bump(3); } crate::aver_generated::check::tc::orCached")
sub("if crate::aver_generated::check::tc::sharedPair(t, s) { crate::aver_generated::check::state::closedPairGet(&st.closed, t, s) } else { false } }",
    "if crate::aver_generated::check::tc::sharedPair(t, s) { let r = crate::aver_generated::check::state::closedPairGet(&st.closed, t, s); if r { pkx_bump(1); } else { pkx_bump(4); } r } else { false } }")
sub("if crate::aver_generated::check::tc::sharedPair(t, s) { crate::aver_generated::check::state::closedFailGet(&st.closed, t, s) }",
    "if crate::aver_generated::check::tc::sharedPair(t, s) { let r = crate::aver_generated::check::state::closedFailGet(&st.closed, t, s); if r { pkx_bump(2); } else { pkx_bump(5); } r }")
sub("    pk_bump(0);\n    crate::cancel_checkpoint();\n    { let __t = &f; match __t.view() {",
    "    pk_bump(0);\n    if PKT.load(std::sync::atomic::Ordering::Relaxed) { if let Some(n) = crate::aver_generated::core::apps::constName(&f) { eprintln!(\"unfold {}\", crate::aver_generated::core::names::render(&n)); } }\n    crate::cancel_checkpoint();\n    { let __t = &f; match __t.view() {")
sub("    pk_bump(1);\n    crate::cancel_checkpoint();\n",
    "    pk_bump(1);\n    if PKT.load(std::sync::atomic::Ordering::Relaxed) { if let Some(n) = crate::aver_generated::core::apps::constName(&crate::aver_generated::core::apps::fnOf(e.clone())) { eprintln!(\"lazyunfold {}\", crate::aver_generated::core::names::render(&n)); } }\n    crate::cancel_checkpoint();\n")
s += '''
pub static PKX: [std::sync::atomic::AtomicU64; 6] = [const { std::sync::atomic::AtomicU64::new(0) }; 6];
#[inline(always)] pub fn pkx_bump(i: usize) { PKX[i].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }
pub fn pkx_take() -> [u64; 6] { let mut r = [0; 6]; for i in 0..6 { r[i] = PKX[i].swap(0, std::sync::atomic::Ordering::Relaxed); } r }
pub static PKT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
'''
open(tc, 'w').write(s)
s = open(dc).read()
sub('    eprintln!("PC\\tJ\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}", name, i1 - i0, c[0], c[1], c[2], c[3]);',
    '    let x = crate::aver_generated::check::tc::pkx_take();\n    eprintln!("PC\\tJ\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}", name, i1 - i0, c[0], c[1], c[2], c[3], x[0], x[1], x[2], x[3], x[4], x[5]);')
sub("    crate::aver_generated::check::tc::pk_take();\n    let i0 = pk_instr();\n    let r = jobChecks_inner",
    "    crate::aver_generated::check::tc::pk_take(); crate::aver_generated::check::tc::pkx_take();\n    let i0 = pk_instr();\n    let r = jobChecks_inner")
sub("    let name = crate::aver_generated::core::names::render(&j.head.name);\n",
    "    let name = crate::aver_generated::core::names::render(&j.head.name);\n    crate::aver_generated::check::tc::PKT.store(std::env::var(\"PK_TRACE\").map(|t| t == name.to_string()).unwrap_or(false), std::sync::atomic::Ordering::Relaxed);\n")
sig = 'pub fn carried(mut st @ _: crate::aver_generated::check::state::St) -> Facts {\n    crate::cancel_checkpoint();\n'
sub(sig, sig + '''    if std::env::var_os("PK_NOCARRY").is_some() {
        let nc2 = std::env::var("PK_NOCARRY").map(|v| v == "2").unwrap_or(false);
        let e = || crate::aver_generated::core::cache::empty();
        let closed = if nc2 { crate::aver_generated::check::decl::bounded(st.closed, st.limits.closed.clone()) } else { e() };
        return Box::new(crate::aver_generated::check::decl::Facts__Fields { closed, unfolds: e(), types: e(), vars: e(), lctx: crate::aver_generated::check::decl::localsKept(st.lctx, true), next: st.next, topLevel: st.topLevel, inferCache: e(), checkCache: e(), whnfCache: e(), coreCache: e(), eqOk: e(), eqFail: e(), eqNo: e(), rules: Default::default() });
    }
''')
open(dc, 'w').write(s)
