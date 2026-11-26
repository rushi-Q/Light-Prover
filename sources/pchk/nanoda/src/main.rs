use nanoda_lib::util::Config;

// C07: large allocations (the export dag's tables and entry vectors, ~GBs, accessed randomly) are
// marked MADV_HUGEPAGE so that, with THP in `madvise` mode, they are backed by 2 MB pages (far fewer
// TLB misses). Pure memory-management hint: allocation contents and program logic are unchanged.
mod huge_alloc {
    use std::alloc::{GlobalAlloc, Layout, System};
    pub struct HugeAlloc;
    const HUGE_MIN: usize = 4 << 20;
    const PAGE_2M: usize = 2 << 20;
    const MADV_HUGEPAGE: i32 = 14;
    extern "C" {
        fn madvise(addr: *mut core::ffi::c_void, len: usize, advice: i32) -> i32;
    }
    #[inline]
    unsafe fn advise(p: *mut u8, len: usize) {
        let start = (p as usize + PAGE_2M - 1) & !(PAGE_2M - 1);
        let end = (p as usize + len) & !(PAGE_2M - 1);
        if end > start {
            let _ = madvise(start as *mut core::ffi::c_void, end - start, MADV_HUGEPAGE);
        }
    }
    unsafe impl GlobalAlloc for HugeAlloc {
        #[inline]
        unsafe fn alloc(&self, l: Layout) -> *mut u8 {
            let p = System.alloc(l);
            if !p.is_null() && l.size() >= HUGE_MIN { advise(p, l.size()) }
            p
        }
        #[inline]
        unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
            let p = System.alloc_zeroed(l);
            if !p.is_null() && l.size() >= HUGE_MIN { advise(p, l.size()) }
            p
        }
        #[inline]
        unsafe fn dealloc(&self, p: *mut u8, l: Layout) { System.dealloc(p, l) }
        #[inline]
        unsafe fn realloc(&self, p: *mut u8, l: Layout, new_size: usize) -> *mut u8 {
            let q = System.realloc(p, l, new_size);
            if !q.is_null() && new_size >= HUGE_MIN { advise(q, new_size) }
            q
        }
    }
}

#[global_allocator]
static GLOBAL: huge_alloc::HugeAlloc = huge_alloc::HugeAlloc;
use std::error::Error;
use std::path::Path;

fn main() -> Result<(), MainError> {
    let mut args = std::env::args();
    let _ = args.next();
    let out = match args.next().as_ref() {
        None => Err(Box::from("This program expects a path to a configuration file.".to_string())),
        Some(p) if p == "-h" || p == "--help" => return Ok(println!("{}", HELP_LONG)),
        Some(p) => use_config(&Path::new(p)),
    }
    .map_err(|e| MainError(e))?;

    if let Some(msg) = out {
        println!("{}", msg);
    }
    Ok(())
}

// Returns an optional success message.
fn use_config(config_path: &Path) -> Result<Option<String>, Box<dyn Error>> {
    let cfg = Config::try_from(config_path)?;
    // Make sure the target pretty printer destination is accessible before doing any real work.
    let mut pp_destination = cfg.get_pp_destination()?;
    let t0 = std::time::Instant::now();
    let (export_file, skipped_axioms) = cfg.to_export_file()?;
    let t1 = std::time::Instant::now();
    eprintln!("[timing] parse {:.3} s", (t1 - t0).as_secs_f64());
    // Check the environment
    export_file.check_all_declars();
    eprintln!("[timing] check {:.3} s", t1.elapsed().as_secs_f64());
    // Pretty print as necessary
    let pp_errs = export_file.pp_selected_declars(pp_destination.as_mut());
    if export_file.config.print_success_message {
        if pp_errs.is_empty() {
            if skipped_axioms.is_empty() {
                Ok(Some(format!("Checked {} declarations with no errors", export_file.declars.len())))
            } else {
                Ok(Some(format!("Checked {} declarations with no errors, skipping exported but unpermitted axioms {:?}",
                export_file.declars.len(), skipped_axioms)))
            }
        } else {
            Ok(Some(format!(
                "Checked {} declarations with no typechecker errors, {} pretty printer errors: {:#?}",
                export_file.declars.len(),
                pp_errs.len(),
                pp_errs
            )))
        }
    } else if skipped_axioms.is_empty() {
        Ok(None)
    } else {
        Ok(Some(format!("Skipped exported but unpermitted axioms {:?}", skipped_axioms)))
    }
}

struct MainError(Box<dyn Error>);

impl std::fmt::Debug for MainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}\n\n{}", self.0, HELP_SHORT) }
}

const HELP_SHORT: &str = "run with `-h` or `--help` for help";
const HELP_LONG: &str = concat!(
    "nanoda_bin",
    " ",
    env!("CARGO_PKG_VERSION"),
    "\n\n",
    env!("CARGO_PKG_DESCRIPTION"),
    "\n\n",
    "get more help at ",
    env!("CARGO_PKG_REPOSITORY"),
    "\n\n",
    include_str!("../README.md")
);
