/*
 * lowmem_arena.c — Unboxed mmap arenas for ccmp-lowmem.
 *
 * Uses lazy anonymous mmaps (MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE) so only touched 4 KB
 * pages consume physical RSS, zero realloc/memcpy spikes occur, and munmap() returns 100% of
 * physical pages to the OS kernel immediately before the next stage runs.
 *
 * Every index is explicitly bounds-checked; any overflow returns an error sentinel so the Lean
 * caller falls back or declines cleanly (fail-closed).
 */
#define _GNU_SOURCE
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>

static void *lm_mmap(size_t bytes) {
    if (bytes == 0) bytes = 4096;
    void *p = mmap(NULL, bytes, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    return (p == MAP_FAILED) ? NULL : p;
}

static void lm_munmap(void **pp, size_t *cap_bytes) {
    if (*pp) {
        munmap(*pp, *cap_bytes);
        *pp = NULL;
        *cap_bytes = 0;
    }
}

/* ---- Pass 1: Constant-dependency DAG over expressions ---- */
#define PCACHE_BITS 21
#define PCACHE_SIZE (1u << PCACHE_BITS)
#define PCACHE_MASK (PCACHE_SIZE - 1u)
#define MAX_CNODE_IDX 0x7FFFFFFEu
#define INVALID_U32   0xFFFFFFFFu

static uint32_t *g_expr_cnode = NULL;   size_t g_expr_cnode_bytes = 0; uint64_t g_max_exprs = 0; uint64_t g_num_exprs = 0;
static uint32_t *g_pair_l = NULL;       size_t g_pair_l_bytes = 0;
static uint32_t *g_pair_r = NULL;       size_t g_pair_r_bytes = 0;
static uint32_t *g_pair_seen = NULL;    size_t g_pair_seen_bytes = 0;  uint64_t g_max_pairs = 0; uint64_t g_num_pairs = 0;
static uint64_t *g_pcache_key = NULL;   size_t g_pcache_key_bytes = 0;
static uint32_t *g_pcache_val = NULL;   size_t g_pcache_val_bytes = 0;
static uint32_t *g_dfs_stack = NULL;    size_t g_dfs_stack_bytes = 0;  uint64_t g_dfs_cap = 0;

/* Per-name and per-declaration CSR graph for checkAxioms */
static uint32_t *g_name_seen = NULL;      size_t g_name_seen_bytes = 0;
static uint32_t *g_decl_of_name = NULL;   size_t g_decl_of_name_bytes = 0; uint64_t g_max_names = 0;
static uint32_t *g_decl_name_idx = NULL;  size_t g_decl_name_idx_bytes = 0;
static uint8_t  *g_decl_kind = NULL;      size_t g_decl_kind_bytes = 0;
static uint64_t *g_decl_edge_off = NULL;  size_t g_decl_edge_off_bytes = 0; uint64_t g_max_decls = 0; uint64_t g_num_decls = 0;
static uint32_t *g_edge_dst = NULL;       size_t g_edge_dst_bytes = 0;      uint64_t g_max_edges = 0; uint64_t g_num_edges = 0;

static uint32_t g_visit_gen = 1;
static int g_cur_decl_ok = 1;

/* Canonical name indices. The official reader (LeanExport/Parse.lean) maps every name
 * INDEX to a Name and keys declarations by NAME: a second index of an existing Name is an alias (accepted; both indices
 * denote the same constant), and a Name declared twice is 'Duplicate declaration' (an error). The Lean side registers every
 * name record, in file order, with the index of the FIRST record of the same Name (fv_lm_name_canon: g_canon[i] = i for a
 * new Name, else the first index). Every name index entering the arena - constant references (const, proj typeName),
 * declaration names, declaration name lists (ctors, all, induct, rule ctors), decl-kind lookups, BFS roots and legal
 * axioms - goes through canon_of() first, so the declaration table, the edges and every lookup are keyed by Name exactly
 * like the official reader: aliases resolve to one constant, and a Name declared under two indices hits the duplicate check
 * of fv_lm_decl_begin (-> pass 1 declines -> the official reader decides: 'Duplicate declaration'). */
#define NO_CANON 0xFFFFFFFFFFFFFFFFull
static uint32_t *g_canon = NULL;          size_t g_canon_bytes = 0;         uint64_t g_num_canon = 0;

static inline uint64_t canon_of(uint64_t name_idx) {
    if (!g_canon || name_idx >= g_num_canon) return NO_CANON;
    return (uint64_t)g_canon[name_idx];
}

/* Pass 2: selective expression bitmap */
static uint64_t *g_bmap = NULL;           size_t g_bmap_bytes = 0;          uint64_t g_bmap_nbits = 0;

static void free_pass1_exprs_internal(void) {
    lm_munmap((void **)&g_expr_cnode, &g_expr_cnode_bytes);
    lm_munmap((void **)&g_pair_l, &g_pair_l_bytes);
    lm_munmap((void **)&g_pair_r, &g_pair_r_bytes);
    lm_munmap((void **)&g_pair_seen, &g_pair_seen_bytes);
    lm_munmap((void **)&g_pcache_key, &g_pcache_key_bytes);
    lm_munmap((void **)&g_pcache_val, &g_pcache_val_bytes);
    lm_munmap((void **)&g_dfs_stack, &g_dfs_stack_bytes);
    lm_munmap((void **)&g_name_seen, &g_name_seen_bytes);
}

static void free_all_internal(void) {
    free_pass1_exprs_internal();
    lm_munmap((void **)&g_decl_of_name, &g_decl_of_name_bytes);
    lm_munmap((void **)&g_decl_name_idx, &g_decl_name_idx_bytes);
    lm_munmap((void **)&g_decl_kind, &g_decl_kind_bytes);
    lm_munmap((void **)&g_decl_edge_off, &g_decl_edge_off_bytes);
    lm_munmap((void **)&g_edge_dst, &g_edge_dst_bytes);
    lm_munmap((void **)&g_bmap, &g_bmap_bytes);
    lm_munmap((void **)&g_canon, &g_canon_bytes);
    g_num_canon = 0;
}

LEAN_EXPORT lean_obj_res fv_lm_reset_all(void) {
    free_all_internal();
    return lean_io_result_mk_ok(lean_box(0));
}

/* The Lean 4.36 / 4.37 compilers erase the IO world token at `@[extern]` calls
 * (the generated LowMemParse.c declares e.g. `lean_object* fv_lm_name_canon(uint64_t, uint64_t);`), so no function here
 * takes the `lean_obj_arg w` parameter any more: the C definitions now match the generated declarations exactly. */

/* Sizes upper-bounded lazily from file length (MAP_NORESERVE commits 0 bytes upfront). */
LEAN_EXPORT lean_obj_res fv_lm_init(uint64_t file_bytes) {
    free_all_internal();
    uint64_t bound_lines = file_bytes / 12 + 65536;
    if (bound_lines > MAX_CNODE_IDX) bound_lines = MAX_CNODE_IDX;

    g_max_exprs = bound_lines;
    g_max_pairs = bound_lines;
    g_max_names = bound_lines;
    g_max_decls = file_bytes / 24 + 65536;
    if (g_max_decls > MAX_CNODE_IDX) g_max_decls = MAX_CNODE_IDX;
    g_max_edges = bound_lines * 2;
    if (g_max_edges < (1ull << 24)) g_max_edges = (1ull << 24);
    g_dfs_cap = 1ull << 25; /* 33M entries */

    g_expr_cnode_bytes = (size_t)g_max_exprs * sizeof(uint32_t);
    g_pair_l_bytes     = (size_t)g_max_pairs * sizeof(uint32_t);
    g_pair_r_bytes     = (size_t)g_max_pairs * sizeof(uint32_t);
    g_pair_seen_bytes  = (size_t)g_max_pairs * sizeof(uint32_t);
    g_pcache_key_bytes = (size_t)PCACHE_SIZE * sizeof(uint64_t);
    g_pcache_val_bytes = (size_t)PCACHE_SIZE * sizeof(uint32_t);
    g_dfs_stack_bytes  = (size_t)g_dfs_cap * sizeof(uint32_t);
    g_name_seen_bytes  = (size_t)g_max_names * sizeof(uint32_t);
    g_decl_of_name_bytes  = (size_t)g_max_names * sizeof(uint32_t);
    g_decl_name_idx_bytes = (size_t)g_max_decls * sizeof(uint32_t);
    g_decl_kind_bytes     = (size_t)g_max_decls * sizeof(uint8_t);
    g_decl_edge_off_bytes = (size_t)(g_max_decls + 2) * sizeof(uint64_t);
    g_edge_dst_bytes      = (size_t)g_max_edges * sizeof(uint32_t);
    g_canon_bytes         = (size_t)g_max_names * sizeof(uint32_t);

    g_expr_cnode    = (uint32_t *)lm_mmap(g_expr_cnode_bytes);
    g_pair_l        = (uint32_t *)lm_mmap(g_pair_l_bytes);
    g_pair_r        = (uint32_t *)lm_mmap(g_pair_r_bytes);
    g_pair_seen     = (uint32_t *)lm_mmap(g_pair_seen_bytes);
    g_pcache_key    = (uint64_t *)lm_mmap(g_pcache_key_bytes);
    g_pcache_val    = (uint32_t *)lm_mmap(g_pcache_val_bytes);
    g_dfs_stack     = (uint32_t *)lm_mmap(g_dfs_stack_bytes);
    g_name_seen     = (uint32_t *)lm_mmap(g_name_seen_bytes);
    g_decl_of_name  = (uint32_t *)lm_mmap(g_decl_of_name_bytes);
    g_decl_name_idx = (uint32_t *)lm_mmap(g_decl_name_idx_bytes);
    g_decl_kind     = (uint8_t  *)lm_mmap(g_decl_kind_bytes);
    g_decl_edge_off = (uint64_t *)lm_mmap(g_decl_edge_off_bytes);
    g_edge_dst      = (uint32_t *)lm_mmap(g_edge_dst_bytes);
    g_canon         = (uint32_t *)lm_mmap(g_canon_bytes);

    if (!g_expr_cnode || !g_pair_l || !g_pair_r || !g_pair_seen || !g_pcache_key || !g_pcache_val ||
        !g_dfs_stack || !g_name_seen || !g_decl_of_name || !g_decl_name_idx || !g_decl_kind ||
        !g_decl_edge_off || !g_edge_dst || !g_canon) {
        free_all_internal();
        return lean_io_result_mk_ok(lean_box_uint32(0));
    }
    /* Note: g_decl_of_name uses 0 = not declared, d + 1 = declared at index d, so zero-filled mmap needs NO memset! */
    g_num_exprs = 0;
    g_num_pairs = 0;
    g_num_decls = 0;
    g_num_edges = 0;
    g_visit_gen = 1;
    g_decl_edge_off[0] = 0;
    g_canon[0] = 0;      /* name index 0 = Name.anonymous (pre-bound, like the official reader's nameMap) */
    g_num_canon = 1;
    return lean_io_result_mk_ok(lean_box_uint32(1));
}

/* Register name record `idx` (must be the next index: dense, like pass 1's own check) whose Name was first
 * recorded at index `canon` (canon == idx for a new Name; else canon < idx must itself be canonical). 0 = refused. */
LEAN_EXPORT lean_obj_res fv_lm_name_canon(uint64_t idx, uint64_t canon) {
    if (!g_canon || idx != g_num_canon || idx >= g_max_names || idx >= MAX_CNODE_IDX || canon > idx)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    if (canon != idx && (uint64_t)g_canon[canon] != canon)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    g_canon[idx] = (uint32_t)canon;
    g_num_canon = idx + 1;
    return lean_io_result_mk_ok(lean_box_uint32(1));
}

static inline uint32_t cnode_const(uint64_t name_idx) {
    if (name_idx == 0 || name_idx >= MAX_CNODE_IDX) return INVALID_U32;
    return ((uint32_t)name_idx << 1);
}

static inline uint32_t cnode_merge(uint32_t a, uint32_t b) {
    if (a == INVALID_U32 || b == INVALID_U32) return INVALID_U32;
    if (a == 0) return b;
    if (b == 0 || a == b) return a;
    uint64_t key = ((uint64_t)a << 32) | (uint64_t)b;
    size_t h = (size_t)((key * 0x9E3779B97F4A7C15ULL) >> (64 - PCACHE_BITS)) & PCACHE_MASK;
    if (g_pcache_key[h] == key) {
        return (g_pcache_val[h] << 1) | 1u;
    }
    if (g_num_pairs >= g_max_pairs || g_num_pairs >= MAX_CNODE_IDX) return INVALID_U32;
    uint32_t pidx = (uint32_t)(g_num_pairs++);
    g_pair_l[pidx] = a;
    g_pair_r[pidx] = b;
    g_pcache_key[h] = key;
    g_pcache_val[h] = pidx;
    return (pidx << 1) | 1u;
}

static inline uint32_t push_cnode(uint64_t expected_idx, uint32_t cn) {
    if (expected_idx != g_num_exprs || g_num_exprs >= g_max_exprs || cn == INVALID_U32) return 0;
    g_expr_cnode[g_num_exprs++] = cn;
    return 1;
}

LEAN_EXPORT lean_obj_res fv_lm_num_exprs(void) {
    return lean_io_result_mk_ok(lean_box_uint64(g_num_exprs));
}

/* Push leaf expr with 0 constants (bvar, sort, natVal, strVal) */
LEAN_EXPORT lean_obj_res fv_lm_expr_empty(uint64_t idx) {
    return lean_io_result_mk_ok(lean_box_uint32(push_cnode(idx, 0)));
}

/* Push const expr referencing name_idx */
LEAN_EXPORT lean_obj_res fv_lm_expr_const(uint64_t idx, uint64_t name_idx) {
    if (name_idx >= g_max_names) return lean_io_result_mk_ok(lean_box_uint32(0));
    name_idx = canon_of(name_idx);   /* by Name (index 0 stays 0 and declines below) */
    if (name_idx == NO_CANON) return lean_io_result_mk_ok(lean_box_uint32(0));
    /* name index 0 (= Name.anonymous) is a constant like any other for the official getUsedConstants;
     * the cnode encoding (name_idx << 1) cannot represent it, so decline (pass 1 fails -> official reader + official
     * checkAxioms when <= 512 MiB, else no verdict). cnode_const(0) returns INVALID_U32 -> push_cnode returns 0. */
    uint32_t cn = cnode_const(name_idx);
    return lean_io_result_mk_ok(lean_box_uint32(push_cnode(idx, cn)));
}

/* Push unary expr (mdata) copying child's cnode */
LEAN_EXPORT lean_obj_res fv_lm_expr_unary(uint64_t idx, uint64_t c1) {
    if (c1 >= g_num_exprs) return lean_io_result_mk_ok(lean_box_uint32(0));
    return lean_io_result_mk_ok(lean_box_uint32(push_cnode(idx, g_expr_cnode[c1])));
}

/* Push proj expr referencing struct_name_idx AND child expr c1 (FoldConsts.lean line 41!) */
LEAN_EXPORT lean_obj_res fv_lm_expr_proj(uint64_t idx, uint64_t type_name_idx, uint64_t struct_eidx) {
    if (type_name_idx >= g_max_names || struct_eidx >= g_num_exprs)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    type_name_idx = canon_of(type_name_idx);   /* by Name */
    if (type_name_idx == NO_CANON) return lean_io_result_mk_ok(lean_box_uint32(0));
    uint32_t cn_ty = cnode_const(type_name_idx);   /* index 0 declines, see fv_lm_expr_const */
    uint32_t cn = cnode_merge(cn_ty, g_expr_cnode[struct_eidx]);
    return lean_io_result_mk_ok(lean_box_uint32(push_cnode(idx, cn)));
}

/* Push binary expr (app, lam, forallE) combining c1 and c2 */
LEAN_EXPORT lean_obj_res fv_lm_expr_bin(uint64_t idx, uint64_t c1, uint64_t c2) {
    if (c1 >= g_num_exprs || c2 >= g_num_exprs) return lean_io_result_mk_ok(lean_box_uint32(0));
    uint32_t cn = cnode_merge(g_expr_cnode[c1], g_expr_cnode[c2]);
    return lean_io_result_mk_ok(lean_box_uint32(push_cnode(idx, cn)));
}

/* Push ternary expr (letE) combining c1, c2, c3 */
LEAN_EXPORT lean_obj_res fv_lm_expr_ter(uint64_t idx, uint64_t c1, uint64_t c2, uint64_t c3) {
    if (c1 >= g_num_exprs || c2 >= g_num_exprs || c3 >= g_num_exprs)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    uint32_t cn = cnode_merge(cnode_merge(g_expr_cnode[c1], g_expr_cnode[c2]), g_expr_cnode[c3]);
    return lean_io_result_mk_ok(lean_box_uint32(push_cnode(idx, cn)));
}

static void bump_gen(uint64_t cur_names) {
    g_visit_gen++;
    if (g_visit_gen == 0) {
        if (g_num_pairs > 0) memset(g_pair_seen, 0, (size_t)g_num_pairs * sizeof(uint32_t));
        if (cur_names > 0) memset(g_name_seen, 0, (size_t)cur_names * sizeof(uint32_t));
        g_visit_gen = 1;
    }
}

static inline void emit_used_name(uint32_t nidx) {
    if (nidx >= g_max_names) { g_cur_decl_ok = 0; return; }
    if (g_name_seen[nidx] == g_visit_gen) return;
    g_name_seen[nidx] = g_visit_gen;
    if (g_num_edges >= g_max_edges) { g_cur_decl_ok = 0; return; }
    g_edge_dst[g_num_edges++] = nidx;
}

static void emit_used_cnode(uint32_t root) {
    if (root == 0) return;
    if ((root & 1u) == 0) {
        emit_used_name(root >> 1);
        return;
    }
    uint64_t sp = 0;
    g_dfs_stack[sp++] = root;
    while (sp > 0) {
        uint32_t cur = g_dfs_stack[--sp];
        if (cur == 0) continue;
        if ((cur & 1u) == 0) {
            emit_used_name(cur >> 1);
        } else {
            uint32_t pidx = cur >> 1;
            if (g_pair_seen[pidx] == g_visit_gen) continue;
            g_pair_seen[pidx] = g_visit_gen;
            if (sp + 2 > g_dfs_cap) { g_cur_decl_ok = 0; return; }
            g_dfs_stack[sp++] = g_pair_r[pidx];
            g_dfs_stack[sp++] = g_pair_l[pidx];
        }
    }
}

/* Start recording a declaration (kind: 0=axiom, 1=def, 2=thm, 3=opaque, 4=quot, 5=induct, 6=ctor, 7=rec).
 * Returns 0 on duplicate constant name or overflow. the duplicate check is by NAME (canonical index), so a Name
 * declared under two aliased indices is a duplicate exactly like the official reader's 'Duplicate declaration'. */
LEAN_EXPORT lean_obj_res fv_lm_decl_begin(uint64_t name_idx, uint8_t kind, uint64_t cur_names) {
    if (name_idx >= g_max_names || g_num_decls >= g_max_decls)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    name_idx = canon_of(name_idx);
    if (name_idx == NO_CANON || name_idx >= g_max_names)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    if (g_decl_of_name[name_idx] != 0) /* duplicate declaration! */
        return lean_io_result_mk_ok(lean_box_uint32(0));
    uint32_t d = (uint32_t)g_num_decls;
    g_decl_of_name[name_idx] = d + 1u;
    g_decl_name_idx[d] = (uint32_t)name_idx;
    g_decl_kind[d] = kind;
    g_decl_edge_off[d] = g_num_edges;
    g_cur_decl_ok = 1;
    bump_gen(cur_names);
    return lean_io_result_mk_ok(lean_box_uint32(1));
}

LEAN_EXPORT lean_obj_res fv_lm_decl_add_name(uint64_t name_idx) {
    name_idx = canon_of(name_idx);   /* by Name */
    if (name_idx == NO_CANON || name_idx >= g_max_names) { g_cur_decl_ok = 0; return lean_io_result_mk_ok(lean_box(0)); }
    emit_used_name((uint32_t)name_idx);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res fv_lm_decl_add_expr(uint64_t eidx) {
    if (eidx >= g_num_exprs) { g_cur_decl_ok = 0; }
    else { emit_used_cnode(g_expr_cnode[eidx]); }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res fv_lm_decl_finish(void) {
    if (!g_cur_decl_ok) return lean_io_result_mk_ok(lean_box_uint32(0));
    g_num_decls++;
    g_decl_edge_off[g_num_decls] = g_num_edges;
    return lean_io_result_mk_ok(lean_box_uint32(1));
}

/* Free Pass-1 expression DAG mmaps immediately before checkAxioms & Pass 2! */
LEAN_EXPORT lean_obj_res fv_lm_free_expr_dag(void) {
    free_pass1_exprs_internal();
    return lean_io_result_mk_ok(lean_box(0));
}

/* Query declaration kind of name_idx: 0xFF if not declared, else 0..7 */
LEAN_EXPORT lean_obj_res fv_lm_get_decl_kind(uint64_t name_idx) {
    name_idx = canon_of(name_idx);   /* by Name */
    if (name_idx == NO_CANON || name_idx >= g_max_names || g_decl_of_name[name_idx] == 0)
        return lean_io_result_mk_ok(lean_box_uint32(0xFFu));
    uint32_t d = g_decl_of_name[name_idx] - 1u;
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)g_decl_kind[d]));
}

/* Exact Lake.Check.checkAxioms BFS over CSR graph.
 * Input: roots = ByteArray of packed little-endian uint32 root name_idxs;
 *        legals = ByteArray of packed little-endian uint32 legal axiom name_idxs.
 * Returns UInt64:
 *   0 = OK
 *   (1ULL << 32) | missing_name_idx = Constant not found in solution
 *   (2ULL << 32) | illegal_axiom_name_idx = Illegal axiom detected
 *   (3ULL << 32) = internal OOM
 */
LEAN_EXPORT lean_obj_res fv_lm_check_axioms_bfs(b_lean_obj_arg roots_ba, b_lean_obj_arg legals_ba) {
    size_t n_roots = lean_sarray_size(roots_ba) / 4;
    size_t n_legals = lean_sarray_size(legals_ba) / 4;
    const uint32_t *roots = (const uint32_t *)lean_sarray_cptr(roots_ba);
    const uint32_t *legals = (const uint32_t *)lean_sarray_cptr(legals_ba);

    size_t chk_bytes = (size_t)g_num_decls + 16;
    size_t stk_bytes = ((size_t)g_num_decls + 16) * sizeof(uint32_t);
    uint8_t *checked = (uint8_t *)lm_mmap(chk_bytes);
    uint32_t *stack  = (uint32_t *)lm_mmap(stk_bytes);
    if (!checked || !stack) {
        lm_munmap((void **)&checked, &chk_bytes);
        lm_munmap((void **)&stack, &stk_bytes);
        return lean_io_result_mk_ok(lean_box_uint64(3ULL << 32));
    }

    /* a decl is pushed at most ONCE (checked[] = 0 unseen, 2 queued, 1 done; marked when pushed), so the
     * stack never holds more than g_num_decls entries; the old code pushed once per EDGE to a not-yet-done decl, which
     * can exceed the (g_num_decls + 16)-entry mapping and write past it (into checked[] when the two mappings are
     * adjacent). The bound check below is defense in depth: overflow = internal error = no verdict. Visiting every
     * reachable decl exactly once and validating each of its edges is the official closure (Lake.Check.checkAxioms). */
    size_t cap = (size_t)g_num_decls + 16;
    size_t sp = 0;
    for (size_t i = 0; i < n_roots; i++) {
        uint64_t r_c = canon_of(roots[i]);   /* by Name */
        uint32_t r_nidx = (r_c == NO_CANON) ? INVALID_U32 : (uint32_t)r_c;
        if (r_nidx < g_max_names && g_decl_of_name[r_nidx] != 0) {
            uint32_t rd = g_decl_of_name[r_nidx] - 1u;
            if (checked[rd] != 0) continue;
            if (sp >= cap) { lm_munmap((void **)&checked, &chk_bytes); lm_munmap((void **)&stack, &stk_bytes);
                             return lean_io_result_mk_ok(lean_box_uint64(3ULL << 32)); }
            checked[rd] = 2;
            stack[sp++] = rd;
        }
    }

    uint64_t ret = 0;
    while (sp > 0) {
        uint32_t d = stack[--sp];
        if (checked[d] == 1) continue;
        uint64_t e0 = g_decl_edge_off[d];
        uint64_t e1 = g_decl_edge_off[d + 1];
        for (uint64_t e = e0; e < e1; e++) {
            uint32_t u_nidx = g_edge_dst[e];
            uint32_t ud1 = (u_nidx < g_max_names) ? g_decl_of_name[u_nidx] : 0;
            if (ud1 == 0) {
                ret = (1ULL << 32) | (uint64_t)u_nidx;
                goto done;
            }
            uint32_t ud = ud1 - 1u;
            if (g_decl_kind[ud] == 0) { /* axiomInfo */
                int is_legal = 0;
                for (size_t k = 0; k < n_legals; k++) {
                    if (canon_of(legals[k]) == (uint64_t)u_nidx) { is_legal = 1; break; }   /* by Name */
                }
                if (!is_legal) {
                    ret = (2ULL << 32) | (uint64_t)u_nidx;
                    goto done;
                }
            }
            if (checked[ud] == 0) {
                if (sp >= cap) { ret = 3ULL << 32; goto done; }
                checked[ud] = 2;
                stack[sp++] = ud;
            }
        }
        checked[d] = 1;
    }

done:
    lm_munmap((void **)&checked, &chk_bytes);
    lm_munmap((void **)&stack, &stk_bytes);
    return lean_io_result_mk_ok(lean_box_uint64(ret));
}

LEAN_EXPORT lean_obj_res fv_lm_free_graph(void) {
    lm_munmap((void **)&g_canon, &g_canon_bytes);
    g_num_canon = 0;
    lm_munmap((void **)&g_decl_of_name, &g_decl_of_name_bytes);
    lm_munmap((void **)&g_decl_name_idx, &g_decl_name_idx_bytes);
    lm_munmap((void **)&g_decl_kind, &g_decl_kind_bytes);
    lm_munmap((void **)&g_decl_edge_off, &g_decl_edge_off_bytes);
    lm_munmap((void **)&g_edge_dst, &g_edge_dst_bytes);
    return lean_io_result_mk_ok(lean_box(0));
}

/* ---- Pass 2: Selective expression bitmap & pread ---- */
LEAN_EXPORT lean_obj_res fv_lm_bmap_init(uint64_t nbits) {
    lm_munmap((void **)&g_bmap, &g_bmap_bytes);
    g_bmap_nbits = nbits;
    g_bmap_bytes = (size_t)(((nbits + 63) / 64 + 2) * sizeof(uint64_t));
    g_bmap = (uint64_t *)lm_mmap(g_bmap_bytes);
    return lean_io_result_mk_ok(lean_box_uint32(g_bmap ? 1 : 0));
}

LEAN_EXPORT lean_obj_res fv_lm_bmap_set(uint64_t idx) {
    if (g_bmap && idx < g_bmap_nbits) {
        g_bmap[idx >> 6] |= (1ULL << (idx & 63));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res fv_lm_bmap_get(uint64_t idx) {
    uint32_t v = (g_bmap && idx < g_bmap_nbits && ((g_bmap[idx >> 6] >> (idx & 63)) & 1ULL)) ? 1u : 0u;
    return lean_io_result_mk_ok(lean_box_uint32(v));
}

LEAN_EXPORT lean_obj_res fv_lm_bmap_any_range(uint64_t lo, uint64_t hi) {
    if (!g_bmap || lo >= hi || lo >= g_bmap_nbits)
        return lean_io_result_mk_ok(lean_box_uint32(0));
    if (hi > g_bmap_nbits) hi = g_bmap_nbits;
    uint64_t w0 = lo >> 6;
    uint64_t w1 = (hi - 1) >> 6;
    if (w0 == w1) {
        uint64_t mask = (~0ULL << (lo & 63));
        if ((hi & 63) != 0) mask &= ((1ULL << (hi & 63)) - 1ULL);
        return lean_io_result_mk_ok(lean_box_uint32((g_bmap[w0] & mask) ? 1u : 0u));
    }
    if (g_bmap[w0] & (~0ULL << (lo & 63)))
        return lean_io_result_mk_ok(lean_box_uint32(1u));
    for (uint64_t k = w0 + 1; k < w1; k++) {
        if (g_bmap[k] != 0) return lean_io_result_mk_ok(lean_box_uint32(1u));
    }
    uint64_t tail_mask = ((hi & 63) == 0) ? ~0ULL : ((1ULL << (hi & 63)) - 1ULL);
    return lean_io_result_mk_ok(lean_box_uint32((g_bmap[w1] & tail_mask) ? 1u : 0u));
}

LEAN_EXPORT lean_obj_res fv_lm_bmap_free(void) {
    lm_munmap((void **)&g_bmap, &g_bmap_bytes);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Read [offset, offset + len) from path into a ByteArray prefixed with '\n' at byte 0 (matching FastParse Chunk.buf). */
LEAN_EXPORT lean_obj_res fv_lm_pread_chunk(b_lean_obj_arg path_str, uint64_t offset, uint64_t len) {
    const char *path = lean_string_cstr(path_str);
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return lean_io_result_mk_error(lean_decode_io_error(errno, path_str));
    lean_object *ba = lean_alloc_sarray(1, (size_t)len + 1, (size_t)len + 1);
    uint8_t *dst = lean_sarray_cptr(ba);
    dst[0] = 10; /* '\n' prefix */
    size_t done = 0;
    while (done < (size_t)len) {
        ssize_t r = pread(fd, dst + 1 + done, (size_t)len - done, (off_t)(offset + done));
        if (r < 0) {
            if (errno == EINTR) continue;
            int e = errno;
            close(fd);
            lean_dec(ba);
            return lean_io_result_mk_error(lean_decode_io_error(e, path_str));
        }
        if (r == 0) {
            close(fd);
            lean_dec(ba);
            return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("short pread on export file")));
        }
        done += (size_t)r;
    }
    close(fd);
    return lean_io_result_mk_ok(ba);
}

LEAN_EXPORT lean_obj_res fv_lm_peak_rss_kb(void) {
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru) == 0) {
        return lean_io_result_mk_ok(lean_box_uint64((uint64_t)ru.ru_maxrss));
    }
    return lean_io_result_mk_ok(lean_box_uint64(0));
}
