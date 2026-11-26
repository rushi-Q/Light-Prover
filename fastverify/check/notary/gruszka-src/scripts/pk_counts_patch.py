# M5/M2: per-declaration counters in Pestka's generated Rust (sources untouched):
# 0 unfoldOn (machine delta), 1 unfoldStep (lazy step, stepCache miss),
# 2 inferCached miss, 3 eqBoolTrue (comparison past quick)
import sys, re
tc, dc = sys.argv[1], sys.argv[2]
s = open(tc).read()
def ins_after_sig(s, sig, code):
    i = s.index(sig); j = s.index('{\n', i) + 2
    return s[:j] + code + s[j:]
s = ins_after_sig(s, 'pub fn unfoldOn(', '    pk_bump(0);\n')
s = ins_after_sig(s, 'pub fn unfoldStep(', '    pk_bump(1);\n')
s = ins_after_sig(s, 'pub fn __lent_inferCached(', '    if hit.is_none() { pk_bump(2); }\n')
a = '            __MutualTco17::EqBoolTrue(mut st @ _, mut t @ _, mut s @ _) => {\n'
assert s.count(a) == 1
s = s.replace(a, a + '                pk_bump(3);\n')
s += '''
pub static PKC: [std::sync::atomic::AtomicU64; 4] = [const { std::sync::atomic::AtomicU64::new(0) }; 4];
#[inline(always)] pub fn pk_bump(i: usize) { PKC[i].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }
pub fn pk_take() -> [u64; 4] { let mut r = [0; 4]; for i in 0..4 { r[i] = PKC[i].swap(0, std::sync::atomic::Ordering::Relaxed); } r }
'''
open(tc, 'w').write(s)
d = open(dc).read()
old1="pub fn jobChecks(mut j @ _: Job, mut st0 @ _: crate::aver_generated::check::state::St) -> Result<Facts, crate::aver_generated::check::state::Fail> {"
old2="pub fn prepared(mut env @ _: crate::aver_generated::check::state::Env, d @ _: &crate::aver_generated::core::decls::Decl) -> Result<Addition, crate::aver_generated::check::state::Fail> {"
assert d.count(old1)==1 and d.count(old2)==1
d=d.replace(old1, old1.replace("pub fn jobChecks(","pub fn jobChecks_inner("))
d=d.replace(old2, old2.replace("pub fn prepared(","pub fn prepared_inner("))
d+='''
#[repr(C)] struct RU4 { f: [u64; 31], instructions: u64, cycles: u64, rest: [u64; 20] }
unsafe extern "C" { fn proc_pid_rusage(pid: i32, flavor: i32, buf: *mut RU4) -> i32; fn getpid() -> i32; }
fn pk_instr() -> u64 { unsafe { let mut r: RU4 = std::mem::zeroed(); proc_pid_rusage(getpid(), 4, &mut r); r.instructions } }
pub fn jobChecks(j: Job, st0: crate::aver_generated::check::state::St) -> Result<Facts, crate::aver_generated::check::state::Fail> {
    let name = crate::aver_generated::core::names::render(&j.head.name);
    crate::aver_generated::check::tc::pk_take();
    let i0 = pk_instr();
    let r = jobChecks_inner(j, st0);
    let i1 = pk_instr(); let c = crate::aver_generated::check::tc::pk_take();
    eprintln!("PC\\tJ\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}", name, i1 - i0, c[0], c[1], c[2], c[3]);
    r
}
pub fn prepared(env: crate::aver_generated::check::state::Env, d: &crate::aver_generated::core::decls::Decl) -> Result<Addition, crate::aver_generated::check::state::Fail> {
    crate::aver_generated::check::tc::pk_take();
    let i0 = pk_instr();
    let r = prepared_inner(env, d);
    let i1 = pk_instr(); let c = crate::aver_generated::check::tc::pk_take();
    eprintln!("PC\\tB\\t{}\\t{}\\t{}\\t{}\\t{}\\t{}", crate::aver_generated::core::names::render(&crate::aver_generated::core::decls::nameOf(d)), i1 - i0, c[0], c[1], c[2], c[3]);
    r
}
'''
open(dc,'w').write(d)
