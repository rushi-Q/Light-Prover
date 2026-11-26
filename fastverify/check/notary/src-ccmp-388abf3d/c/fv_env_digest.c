/*
 * fv_env_digest.c — Canonical Environment SHA-256 Digest
 *
 * Self-contained C99 implementation linked hermetically via official Lean 4.36 `leanc`.
 * Computes deterministic, order-independent, cryptographic SHA-256 Merkle DAG digests
 * of Lean 4.36 `Name`, `Level`, `Expr`, and `ConstantInfo` environments:
 *   - strict = 0 (`fv-env-sha256-v1`): 3-leg digest shared across ccmp, pleanchecker, gruszka
 *   - strict = 1 (`fv-env-strict-sha256-v1`): 2-leg digest across ccmp and pleanchecker
 *     (additionally binds `Expr.letE.nondep` and `Expr.mdata` wrappers)
 *
 * Iterative explicit stack (no recursion -> immune to C stack overflow on deep ASTs).
 * Per-worker thread context (zero lock contention; bounded memory).
 */
#include <lean/lean.h>

/* Hermetic libc declarations (leanc uses -nostdinc with bundled GLIBC_2.17 stub) */
extern void *malloc(size_t size);
extern void *calloc(size_t nmemb, size_t size);
extern void *realloc(void *ptr, size_t size);
extern void  free(void *ptr);
extern void  abort(void);
extern void *memcpy(void *dst, const void *src, size_t n);
extern void *memset(void *s, int c, size_t n);
extern int   memcmp(const void *s1, const void *s2, size_t n);
extern void  qsort(void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *));

/* Official Lean 4.36 exported getters from libLean.a */
extern uint8_t lean_expr_binder_info(lean_obj_arg e);
extern uint8_t lean_expr_is_have(lean_obj_arg e);

/* =========================================================================
 * FIPS 180-4 SHA-256
 * ========================================================================= */
typedef struct {
    uint32_t state[8];
    uint64_t bitlen;
    uint8_t  buf[64];
    size_t   buflen;
} sha256_ctx_t;

static const uint32_t SHA256_K[64] = {
    0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
    0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
    0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
    0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
    0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
    0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
    0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
    0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
    0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
    0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
    0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
    0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
    0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
    0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
    0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
    0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
};

static inline uint32_t rotr32(uint32_t x, unsigned n) {
    return (x >> n) | (x << (32u - n));
}

static void sha256_compress(sha256_ctx_t *ctx, const uint8_t block[64]) {
    uint32_t w[64];
    for (int i = 0; i < 16; ++i) {
        w[i] = ((uint32_t)block[4*i] << 24) | ((uint32_t)block[4*i + 1] << 16) |
               ((uint32_t)block[4*i + 2] << 8) | (uint32_t)block[4*i + 3];
    }
    for (int i = 16; i < 64; ++i) {
        uint32_t s0 = rotr32(w[i - 15], 7) ^ rotr32(w[i - 15], 18) ^ (w[i - 15] >> 3);
        uint32_t s1 = rotr32(w[i - 2], 17) ^ rotr32(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    uint32_t a = ctx->state[0], b = ctx->state[1], c = ctx->state[2], d = ctx->state[3];
    uint32_t e = ctx->state[4], f = ctx->state[5], g = ctx->state[6], h = ctx->state[7];
    for (int i = 0; i < 64; ++i) {
        uint32_t S1 = rotr32(e, 6) ^ rotr32(e, 11) ^ rotr32(e, 25);
        uint32_t ch = (e & f) ^ ((~e) & g);
        uint32_t t1 = h + S1 + ch + SHA256_K[i] + w[i];
        uint32_t S0 = rotr32(a, 2) ^ rotr32(a, 13) ^ rotr32(a, 22);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2 = S0 + maj;
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    ctx->state[0] += a; ctx->state[1] += b; ctx->state[2] += c; ctx->state[3] += d;
    ctx->state[4] += e; ctx->state[5] += f; ctx->state[6] += g; ctx->state[7] += h;
}

static void sha256_init(sha256_ctx_t *ctx) {
    ctx->state[0] = 0x6a09e667u; ctx->state[1] = 0xbb67ae85u;
    ctx->state[2] = 0x3c6ef372u; ctx->state[3] = 0xa54ff53au;
    ctx->state[4] = 0x510e527fu; ctx->state[5] = 0x9b05688cu;
    ctx->state[6] = 0x1f83d9abu; ctx->state[7] = 0x5be0cd19u;
    ctx->bitlen = 0;
    ctx->buflen = 0;
}

static void sha256_update(sha256_ctx_t *ctx, const uint8_t *data, size_t len) {
    ctx->bitlen += (uint64_t)len * 8u;
    size_t i = 0;
    if (ctx->buflen > 0) {
        size_t need = 64 - ctx->buflen;
        if (len < need) {
            memcpy(ctx->buf + ctx->buflen, data, len);
            ctx->buflen += len;
            return;
        }
        memcpy(ctx->buf + ctx->buflen, data, need);
        sha256_compress(ctx, ctx->buf);
        ctx->buflen = 0;
        i = need;
    }
    while (i + 64 <= len) {
        sha256_compress(ctx, data + i);
        i += 64;
    }
    if (i < len) {
        memcpy(ctx->buf, data + i, len - i);
        ctx->buflen = len - i;
    }
}

static void sha256_final(sha256_ctx_t *ctx, uint8_t out[32]) {
    uint64_t bits = ctx->bitlen;
    ctx->buf[ctx->buflen++] = 0x80u;
    if (ctx->buflen > 56) {
        memset(ctx->buf + ctx->buflen, 0, 64 - ctx->buflen);
        sha256_compress(ctx, ctx->buf);
        ctx->buflen = 0;
    }
    memset(ctx->buf + ctx->buflen, 0, 56 - ctx->buflen);
    for (int i = 0; i < 8; ++i) {
        ctx->buf[56 + i] = (uint8_t)(bits >> (56 - 8 * i));
    }
    sha256_compress(ctx, ctx->buf);
    for (int i = 0; i < 8; ++i) {
        out[4*i]     = (uint8_t)(ctx->state[i] >> 24);
        out[4*i + 1] = (uint8_t)(ctx->state[i] >> 16);
        out[4*i + 2] = (uint8_t)(ctx->state[i] >> 8);
        out[4*i + 3] = (uint8_t)(ctx->state[i]);
    }
}

static inline void sha_u8(sha256_ctx_t *c, uint8_t v) { sha256_update(c, &v, 1); }

static inline void sha_u32_le(sha256_ctx_t *c, uint32_t v) {
    uint8_t b[4] = { (uint8_t)v, (uint8_t)(v >> 8), (uint8_t)(v >> 16), (uint8_t)(v >> 24) };
    sha256_update(c, b, 4);
}

static inline void sha_u64_le(sha256_ctx_t *c, uint64_t v) {
    uint8_t b[8] = {
        (uint8_t)v, (uint8_t)(v >> 8), (uint8_t)(v >> 16), (uint8_t)(v >> 24),
        (uint8_t)(v >> 32), (uint8_t)(v >> 40), (uint8_t)(v >> 48), (uint8_t)(v >> 56)
    };
    sha256_update(c, b, 8);
}

static inline void sha_bytes(sha256_ctx_t *c, const uint8_t *p, size_t n) {
    sha_u32_le(c, (uint32_t)n);
    if (n > 0) sha256_update(c, p, n);
}

static void sha_lean_nat(sha256_ctx_t *c, b_lean_obj_arg n) {
    if (lean_is_scalar(n)) {
        uint64_t v = (uint64_t)lean_unbox(n);
        uint8_t b[8];
        size_t len = 0;
        while (v > 0) {
            b[len++] = (uint8_t)(v & 0xffu);
            v >>= 8;
        }
        sha_bytes(c, b, len);
        return;
    }
    /* Big Nat: extract 64 bits at a time via official lean_uint64_of_nat + lean_nat_shiftr */
    size_t cap = 64, len = 0;
    uint8_t *buf = (uint8_t *)malloc(cap);
    if (!buf) abort();
    lean_inc(n);
    lean_obj_arg cur = n;
    lean_obj_arg shift64 = lean_box(64);
    while (!(lean_is_scalar(cur) && lean_unbox(cur) == 0)) {
        uint64_t w = lean_uint64_of_nat(cur);
        if (len + 8 > cap) {
            cap *= 2;
            buf = (uint8_t *)realloc(buf, cap);
            if (!buf) abort();
        }
        for (int i = 0; i < 8; ++i) buf[len++] = (uint8_t)((w >> (8 * i)) & 0xffu);
        lean_obj_arg next = lean_nat_shiftr(cur, shift64);
        lean_dec(cur);
        cur = next;
    }
    lean_dec(cur);
    while (len > 0 && buf[len - 1] == 0) --len;
    sha_bytes(c, buf, len);
    free(buf);
}

/* =========================================================================
 * Per-Worker Cache + Exact Local Memo Table + Iterative Stack
 * ========================================================================= */
#define DM_BITS 16u
#define DM_SIZE (1u << DM_BITS)
#define DM_MASK (DM_SIZE - 1u)

typedef struct {
    uintptr_t ptr;
    uint8_t   h[32];
} dm_entry_t;

typedef struct {
    uintptr_t ptr;
    uint32_t  gen;
    uint8_t   h[32];
} loc_entry_t;

typedef struct {
    b_lean_obj_arg obj;
    uint8_t kind;   /* 0=name, 1=level, 2=expr */
    uint8_t done;   /* 0=push children, 1=combine */
} stack_frame_t;

typedef struct {
    uint8_t       strict;
    dm_entry_t   *dm;          /* bounded 65536-slot direct-mapped cache (~2.6 MB) */
    loc_entry_t  *loc;         /* per-constant exact memo table */
    size_t        loc_cap;
    size_t        loc_used;
    uint32_t      gen;
    stack_frame_t *stk;
    size_t        stk_len;
    size_t        stk_cap;
    uint8_t       h_anon[32];
    uint8_t       h_lzero[32];
} digest_ctx_t;

static inline size_t ptr_hash(uintptr_t p) {
    uint64_t x = (uint64_t)p;
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccduLL;
    x ^= x >> 33;
    x *= 0xc4ceb9fe1a85ec53uLL;
    x ^= x >> 33;
    return (size_t)x;
}

static void loc_grow(digest_ctx_t *ctx) {
    size_t ncap = ctx->loc_cap * 2;
    loc_entry_t *ntab = (loc_entry_t *)calloc(ncap, sizeof(loc_entry_t));
    if (!ntab) abort();
    size_t nmask = ncap - 1;
    uint32_t g = ctx->gen;
    for (size_t i = 0; i < ctx->loc_cap; ++i) {
        if (ctx->loc[i].gen == g) {
            size_t idx = ptr_hash(ctx->loc[i].ptr) & nmask;
            while (ntab[idx].gen == g) idx = (idx + 1) & nmask;
            ntab[idx] = ctx->loc[i];
        }
    }
    free(ctx->loc);
    ctx->loc = ntab;
    ctx->loc_cap = ncap;
}

static inline void loc_put(digest_ctx_t *ctx, uintptr_t key, size_t h, const uint8_t hval[32]) {
    if ((ctx->loc_used + 1) * 10 >= ctx->loc_cap * 7) {
        loc_grow(ctx);
    }
    size_t mask = ctx->loc_cap - 1;
    size_t idx = h & mask;
    uint32_t g = ctx->gen;
    while (ctx->loc[idx].gen == g) {
        if (ctx->loc[idx].ptr == key) {
            memcpy(ctx->loc[idx].h, hval, 32);
            return;
        }
        idx = (idx + 1) & mask;
    }
    ctx->loc[idx].ptr = key;
    ctx->loc[idx].gen = g;
    memcpy(ctx->loc[idx].h, hval, 32);
    ctx->loc_used++;
}

static inline int cache_get(digest_ctx_t *ctx, const void *p, uint8_t out[32]) {
    uintptr_t key = (uintptr_t)p;
    size_t h = ptr_hash(key);
    dm_entry_t *de = &ctx->dm[h & DM_MASK];
    if (de->ptr == key) {
        memcpy(out, de->h, 32);
        /* Promote into per-constant exact table so later dm evictions cannot lose this child */
        loc_put(ctx, key, h, out);
        return 1;
    }
    size_t mask = ctx->loc_cap - 1;
    size_t idx = h & mask;
    uint32_t g = ctx->gen;
    while (ctx->loc[idx].gen == g) {
        if (ctx->loc[idx].ptr == key) {
            memcpy(out, ctx->loc[idx].h, 32);
            de->ptr = key;
            memcpy(de->h, out, 32);
            return 1;
        }
        idx = (idx + 1) & mask;
    }
    return 0;
}

static inline void cache_put(digest_ctx_t *ctx, const void *p, const uint8_t hval[32]) {
    uintptr_t key = (uintptr_t)p;
    size_t h = ptr_hash(key);
    dm_entry_t *de = &ctx->dm[h & DM_MASK];
    de->ptr = key;
    memcpy(de->h, hval, 32);
    loc_put(ctx, key, h, hval);
}

static void ctx_reset_local(digest_ctx_t *ctx) {
    if (ctx->loc_cap > 65536) {
        free(ctx->loc);
        ctx->loc_cap = 4096;
        ctx->loc = (loc_entry_t *)calloc(ctx->loc_cap, sizeof(loc_entry_t));
        if (!ctx->loc) abort();
        ctx->gen = 1;
        ctx->loc_used = 0;
        return;
    }
    ctx->gen++;
    if (ctx->gen == 0) {
        memset(ctx->loc, 0, ctx->loc_cap * sizeof(loc_entry_t));
        ctx->gen = 1;
    }
    ctx->loc_used = 0;
}

static inline void stk_push(digest_ctx_t *ctx, b_lean_obj_arg obj, uint8_t kind, uint8_t done) {
    if (ctx->stk_len == ctx->stk_cap) {
        ctx->stk_cap *= 2;
        ctx->stk = (stack_frame_t *)realloc(ctx->stk, ctx->stk_cap * sizeof(stack_frame_t));
        if (!ctx->stk) abort();
    }
    ctx->stk[ctx->stk_len++] = (stack_frame_t){ obj, kind, done };
}

static inline uint8_t obj_tag_safe(b_lean_obj_arg o) {
    return lean_is_scalar(o) ? (uint8_t)lean_unbox(o) : lean_obj_tag(o);
}

/* =========================================================================
 * Iterative Merkle DAG Hashing: Name, Level, Expr
 * ========================================================================= */
static void hash_node_iter(digest_ctx_t *ctx, b_lean_obj_arg root, uint8_t root_kind, uint8_t out[32]) {
    uint8_t tmp[32];
    if (root_kind == 0 && obj_tag_safe(root) == 0) { memcpy(out, ctx->h_anon, 32); return; }
    if (root_kind == 1 && obj_tag_safe(root) == 0) { memcpy(out, ctx->h_lzero, 32); return; }
    if (!lean_is_scalar(root) && cache_get(ctx, root, out)) return;

    ctx->stk_len = 0;
    stk_push(ctx, root, root_kind, 0);

    while (ctx->stk_len > 0) {
        stack_frame_t fr = ctx->stk[--ctx->stk_len];
        b_lean_obj_arg o = fr.obj;

        if (fr.kind == 0) {
            /* Name */
            uint8_t tag = obj_tag_safe(o);
            if (tag == 0) continue;
            if (!fr.done) {
                if (cache_get(ctx, o, tmp)) continue;
                stk_push(ctx, o, 0, 1);
                b_lean_obj_arg pre = lean_ctor_get(o, 0);
                if (obj_tag_safe(pre) != 0 && !cache_get(ctx, pre, tmp)) {
                    stk_push(ctx, pre, 0, 0);
                }
            } else {
                uint8_t hpre[32];
                b_lean_obj_arg pre = lean_ctor_get(o, 0);
                if (obj_tag_safe(pre) == 0) memcpy(hpre, ctx->h_anon, 32);
                else if (!cache_get(ctx, pre, hpre)) abort();
                sha256_ctx_t s; sha256_init(&s);
                if (tag == 1) {
                    b_lean_obj_arg str = lean_ctor_get(o, 1);
                    sha_u8(&s, 0x02u);
                    sha256_update(&s, hpre, 32);
                    sha_bytes(&s, (const uint8_t *)lean_string_cstr(str), lean_string_size(str) - 1);
                } else {
                    b_lean_obj_arg num = lean_ctor_get(o, 1);
                    sha_u8(&s, 0x03u);
                    sha256_update(&s, hpre, 32);
                    sha_lean_nat(&s, num);
                }
                sha256_final(&s, tmp);
                cache_put(ctx, o, tmp);
            }
        } else if (fr.kind == 1) {
            /* Level */
            uint8_t tag = obj_tag_safe(o);
            if (tag == 0) continue;
            if (!fr.done) {
                if (cache_get(ctx, o, tmp)) continue;
                stk_push(ctx, o, 1, 1);
                if (tag == 1) {
                    b_lean_obj_arg u = lean_ctor_get(o, 0);
                    if (obj_tag_safe(u) != 0 && !cache_get(ctx, u, tmp)) stk_push(ctx, u, 1, 0);
                } else if (tag == 2 || tag == 3) {
                    b_lean_obj_arg u = lean_ctor_get(o, 0);
                    b_lean_obj_arg v = lean_ctor_get(o, 1);
                    if (obj_tag_safe(v) != 0 && !cache_get(ctx, v, tmp)) stk_push(ctx, v, 1, 0);
                    if (obj_tag_safe(u) != 0 && !cache_get(ctx, u, tmp)) stk_push(ctx, u, 1, 0);
                } else {
                    b_lean_obj_arg nm = lean_ctor_get(o, 0);
                    if (obj_tag_safe(nm) != 0 && !cache_get(ctx, nm, tmp)) stk_push(ctx, nm, 0, 0);
                }
            } else {
                sha256_ctx_t s; sha256_init(&s);
                uint8_t ha[32], hb[32];
                if (tag == 1) {
                    b_lean_obj_arg u = lean_ctor_get(o, 0);
                    if (obj_tag_safe(u) == 0) memcpy(ha, ctx->h_lzero, 32); else if (!cache_get(ctx, u, ha)) abort();
                    sha_u8(&s, 0x11u); sha256_update(&s, ha, 32);
                } else if (tag == 2 || tag == 3) {
                    b_lean_obj_arg u = lean_ctor_get(o, 0);
                    b_lean_obj_arg v = lean_ctor_get(o, 1);
                    if (obj_tag_safe(u) == 0) memcpy(ha, ctx->h_lzero, 32); else if (!cache_get(ctx, u, ha)) abort();
                    if (obj_tag_safe(v) == 0) memcpy(hb, ctx->h_lzero, 32); else if (!cache_get(ctx, v, hb)) abort();
                    sha_u8(&s, tag == 2 ? 0x12u : 0x13u);
                    sha256_update(&s, ha, 32); sha256_update(&s, hb, 32);
                } else {
                    b_lean_obj_arg nm = lean_ctor_get(o, 0);
                    if (obj_tag_safe(nm) == 0) memcpy(ha, ctx->h_anon, 32); else if (!cache_get(ctx, nm, ha)) abort();
                    sha_u8(&s, tag == 4 ? 0x14u : 0x15u);
                    sha256_update(&s, ha, 32);
                }
                sha256_final(&s, tmp);
                cache_put(ctx, o, tmp);
            }
        } else {
            /* Expr */
            uint8_t tag = lean_obj_tag(o);
            if (!fr.done) {
                if (cache_get(ctx, o, tmp)) continue;
                stk_push(ctx, o, 2, 1);
                switch (tag) {
                    case 0: /* bvar */
                    case 9: /* lit */
                        break;
                    case 1: /* fvar */
                    case 2: /* mvar */ {
                        b_lean_obj_arg nm = lean_ctor_get(o, 0);
                        if (obj_tag_safe(nm) != 0 && !cache_get(ctx, nm, tmp)) stk_push(ctx, nm, 0, 0);
                        break;
                    }
                    case 3: /* sort */ {
                        b_lean_obj_arg u = lean_ctor_get(o, 0);
                        if (obj_tag_safe(u) != 0 && !cache_get(ctx, u, tmp)) stk_push(ctx, u, 1, 0);
                        break;
                    }
                    case 4: /* const */ {
                        b_lean_obj_arg nm = lean_ctor_get(o, 0);
                        b_lean_obj_arg us = lean_ctor_get(o, 1);
                        while (!lean_is_scalar(us)) {
                            b_lean_obj_arg u = lean_ctor_get(us, 0);
                            if (obj_tag_safe(u) != 0 && !cache_get(ctx, u, tmp)) stk_push(ctx, u, 1, 0);
                            us = lean_ctor_get(us, 1);
                        }
                        if (obj_tag_safe(nm) != 0 && !cache_get(ctx, nm, tmp)) stk_push(ctx, nm, 0, 0);
                        break;
                    }
                    case 5: /* app */ {
                        b_lean_obj_arg f = lean_ctor_get(o, 0);
                        b_lean_obj_arg a = lean_ctor_get(o, 1);
                        if (!cache_get(ctx, a, tmp)) stk_push(ctx, a, 2, 0);
                        if (!cache_get(ctx, f, tmp)) stk_push(ctx, f, 2, 0);
                        break;
                    }
                    case 6: /* lam */
                    case 7: /* forallE */ {
                        b_lean_obj_arg nm = lean_ctor_get(o, 0);
                        b_lean_obj_arg ty = lean_ctor_get(o, 1);
                        b_lean_obj_arg bd = lean_ctor_get(o, 2);
                        if (!cache_get(ctx, bd, tmp)) stk_push(ctx, bd, 2, 0);
                        if (!cache_get(ctx, ty, tmp)) stk_push(ctx, ty, 2, 0);
                        if (obj_tag_safe(nm) != 0 && !cache_get(ctx, nm, tmp)) stk_push(ctx, nm, 0, 0);
                        break;
                    }
                    case 8: /* letE */ {
                        b_lean_obj_arg nm = lean_ctor_get(o, 0);
                        b_lean_obj_arg ty = lean_ctor_get(o, 1);
                        b_lean_obj_arg vl = lean_ctor_get(o, 2);
                        b_lean_obj_arg bd = lean_ctor_get(o, 3);
                        if (!cache_get(ctx, bd, tmp)) stk_push(ctx, bd, 2, 0);
                        if (!cache_get(ctx, vl, tmp)) stk_push(ctx, vl, 2, 0);
                        if (!cache_get(ctx, ty, tmp)) stk_push(ctx, ty, 2, 0);
                        if (obj_tag_safe(nm) != 0 && !cache_get(ctx, nm, tmp)) stk_push(ctx, nm, 0, 0);
                        break;
                    }
                    case 10: /* mdata */ {
                        b_lean_obj_arg sub = lean_ctor_get(o, 1);
                        if (!cache_get(ctx, sub, tmp)) stk_push(ctx, sub, 2, 0);
                        break;
                    }
                    case 11: /* proj */ {
                        b_lean_obj_arg tn = lean_ctor_get(o, 0);
                        b_lean_obj_arg st = lean_ctor_get(o, 2);
                        if (!cache_get(ctx, st, tmp)) stk_push(ctx, st, 2, 0);
                        if (obj_tag_safe(tn) != 0 && !cache_get(ctx, tn, tmp)) stk_push(ctx, tn, 0, 0);
                        break;
                    }
                    default:
                        abort();
                }
            } else {
                sha256_ctx_t s; sha256_init(&s);
                uint8_t h0[32], h1[32], h2[32], h3[32];
                switch (tag) {
                    case 0: /* bvar */
                        sha_u8(&s, 0x20u);
                        sha_lean_nat(&s, lean_ctor_get(o, 0));
                        sha256_final(&s, tmp);
                        break;
                    case 1: /* fvar */
                    case 2: /* mvar */ {
                        b_lean_obj_arg nm = lean_ctor_get(o, 0);
                        if (obj_tag_safe(nm) == 0) memcpy(h0, ctx->h_anon, 32); else if (!cache_get(ctx, nm, h0)) abort();
                        sha_u8(&s, tag == 1 ? 0x21u : 0x22u);
                        sha256_update(&s, h0, 32);
                        sha256_final(&s, tmp);
                        break;
                    }
                    case 3: /* sort */ {
                        b_lean_obj_arg u = lean_ctor_get(o, 0);
                        if (obj_tag_safe(u) == 0) memcpy(h0, ctx->h_lzero, 32); else if (!cache_get(ctx, u, h0)) abort();
                        sha_u8(&s, 0x23u);
                        sha256_update(&s, h0, 32);
                        sha256_final(&s, tmp);
                        break;
                    }
                    case 4: /* const */ {
                        b_lean_obj_arg nm = lean_ctor_get(o, 0);
                        b_lean_obj_arg us = lean_ctor_get(o, 1);
                        if (obj_tag_safe(nm) == 0) memcpy(h0, ctx->h_anon, 32); else if (!cache_get(ctx, nm, h0)) abort();
                        uint32_t cnt = 0;
                        b_lean_obj_arg it = us;
                        while (!lean_is_scalar(it)) { cnt++; it = lean_ctor_get(it, 1); }
                        sha_u8(&s, 0x24u);
                        sha256_update(&s, h0, 32);
                        sha_u32_le(&s, cnt);
                        it = us;
                        while (!lean_is_scalar(it)) {
                            b_lean_obj_arg u = lean_ctor_get(it, 0);
                            if (obj_tag_safe(u) == 0) memcpy(h1, ctx->h_lzero, 32); else if (!cache_get(ctx, u, h1)) abort();
                            sha256_update(&s, h1, 32);
                            it = lean_ctor_get(it, 1);
                        }
                        sha256_final(&s, tmp);
                        break;
                    }
                    case 5: /* app */ {
                        if (!cache_get(ctx, lean_ctor_get(o, 0), h0)) abort();
                        if (!cache_get(ctx, lean_ctor_get(o, 1), h1)) abort();
                        sha_u8(&s, 0x25u);
                        sha256_update(&s, h0, 32);
                        sha256_update(&s, h1, 32);
                        sha256_final(&s, tmp);
                        break;
                    }
                    case 6: /* lam */
                    case 7: /* forallE */ {
                        b_lean_obj_arg nm = lean_ctor_get(o, 0);
                        if (obj_tag_safe(nm) == 0) memcpy(h0, ctx->h_anon, 32); else if (!cache_get(ctx, nm, h0)) abort();
                        if (!cache_get(ctx, lean_ctor_get(o, 1), h1)) abort();
                        if (!cache_get(ctx, lean_ctor_get(o, 2), h2)) abort();
                        lean_inc(o);
                        uint8_t bi = lean_expr_binder_info(o);
                        sha_u8(&s, tag == 6 ? 0x26u : 0x27u);
                        sha_u8(&s, bi);
                        sha256_update(&s, h0, 32);
                        sha256_update(&s, h1, 32);
                        sha256_update(&s, h2, 32);
                        sha256_final(&s, tmp);
                        break;
                    }
                    case 8: /* letE */ {
                        b_lean_obj_arg nm = lean_ctor_get(o, 0);
                        if (obj_tag_safe(nm) == 0) memcpy(h0, ctx->h_anon, 32); else if (!cache_get(ctx, nm, h0)) abort();
                        if (!cache_get(ctx, lean_ctor_get(o, 1), h1)) abort();
                        if (!cache_get(ctx, lean_ctor_get(o, 2), h2)) abort();
                        if (!cache_get(ctx, lean_ctor_get(o, 3), h3)) abort();
                        if (!ctx->strict) {
                            sha_u8(&s, 0x28u);
                            sha256_update(&s, h0, 32);
                            sha256_update(&s, h1, 32);
                            sha256_update(&s, h2, 32);
                            sha256_update(&s, h3, 32);
                        } else {
                            lean_inc(o);
                            uint8_t nd = lean_expr_is_have(o) ? 1u : 0u;
                            sha_u8(&s, 0x2Bu);
                            sha256_update(&s, h0, 32);
                            sha256_update(&s, h1, 32);
                            sha256_update(&s, h2, 32);
                            sha256_update(&s, h3, 32);
                            sha_u8(&s, nd);
                        }
                        sha256_final(&s, tmp);
                        break;
                    }
                    case 9: /* lit */ {
                        b_lean_obj_arg lit = lean_ctor_get(o, 0);
                        uint8_t ltag = lean_obj_tag(lit);
                        if (ltag == 0) {
                            sha_u8(&s, 0x29u);
                            sha_lean_nat(&s, lean_ctor_get(lit, 0));
                        } else {
                            b_lean_obj_arg str = lean_ctor_get(lit, 0);
                            sha_u8(&s, 0x2Au);
                            sha_bytes(&s, (const uint8_t *)lean_string_cstr(str), lean_string_size(str) - 1);
                        }
                        sha256_final(&s, tmp);
                        break;
                    }
                    case 10: /* mdata */ {
                        if (!cache_get(ctx, lean_ctor_get(o, 1), h0)) abort();
                        if (!ctx->strict) {
                            memcpy(tmp, h0, 32);
                        } else {
                            sha_u8(&s, 0x2Cu);
                            sha256_update(&s, h0, 32);
                            sha256_final(&s, tmp);
                        }
                        break;
                    }
                    case 11: /* proj */ {
                        b_lean_obj_arg tn = lean_ctor_get(o, 0);
                        if (obj_tag_safe(tn) == 0) memcpy(h0, ctx->h_anon, 32); else if (!cache_get(ctx, tn, h0)) abort();
                        if (!cache_get(ctx, lean_ctor_get(o, 2), h1)) abort();
                        sha_u8(&s, 0x2Du);
                        sha256_update(&s, h0, 32);
                        sha_lean_nat(&s, lean_ctor_get(o, 1));
                        sha256_update(&s, h1, 32);
                        sha256_final(&s, tmp);
                        break;
                    }
                    default:
                        abort();
                }
                cache_put(ctx, o, tmp);
            }
        }
    }
    if (!cache_get(ctx, root, out)) abort();
}

static void hash_name_list(digest_ctx_t *ctx, sha256_ctx_t *s, b_lean_obj_arg xs) {
    uint32_t cnt = 0;
    b_lean_obj_arg it = xs;
    while (!lean_is_scalar(it)) { cnt++; it = lean_ctor_get(it, 1); }
    sha_u32_le(s, cnt);
    it = xs;
    uint8_t h[32];
    while (!lean_is_scalar(it)) {
        hash_node_iter(ctx, lean_ctor_get(it, 0), 0, h);
        sha256_update(s, h, 32);
        it = lean_ctor_get(it, 1);
    }
}

static void hash_const_head(digest_ctx_t *ctx, sha256_ctx_t *s,
                            b_lean_obj_arg name, b_lean_obj_arg lparams, b_lean_obj_arg ty,
                            uint8_t out_name_h[32]) {
    uint8_t ht[32];
    hash_node_iter(ctx, name, 0, out_name_h);
    sha256_update(s, out_name_h, 32);
    hash_name_list(ctx, s, lparams);
    hash_node_iter(ctx, ty, 2, ht);
    sha256_update(s, ht, 32);
}

static lean_obj_res mk_pair64(const uint8_t name_h[32], const uint8_t const_h[32]) {
    lean_obj_res ba = lean_alloc_sarray(1, 64, 64);
    uint8_t *dst = lean_sarray_cptr(ba);
    memcpy(dst, name_h, 32);
    memcpy(dst + 32, const_h, 32);
    return ba;
}

static lean_obj_res mk_bytes32(const uint8_t h[32]) {
    lean_obj_res ba = lean_alloc_sarray(1, 32, 32);
    memcpy(lean_sarray_cptr(ba), h, 32);
    return ba;
}

/* =========================================================================
 * External Object Lifecycle & FFI Exports
 * ========================================================================= */
static lean_external_class *g_digest_ctx_class = NULL;

static void digest_ctx_finalize(void *p) {
    digest_ctx_t *ctx = (digest_ctx_t *)p;
    if (!ctx) return;
    free(ctx->dm);
    free(ctx->loc);
    free(ctx->stk);
    free(ctx);
}

static void digest_ctx_foreach(void *p, b_lean_obj_arg f) {
    (void)p; (void)f;
}

static void ensure_ctx_class(void) {
    if (!g_digest_ctx_class) {
        g_digest_ctx_class = lean_register_external_class(digest_ctx_finalize, digest_ctx_foreach);
    }
}

/* NIST FIPS 180-4 SHA-256 self-test ("abc" -> ba7816bf...) */
LEAN_EXPORT lean_obj_res fv_sha256_selftest(lean_obj_arg w) {
    static const uint8_t expected[32] = {
        0xba,0x78,0x16,0xbf, 0x8f,0x01,0xcf,0xea, 0x41,0x41,0x40,0xde, 0x5d,0xae,0x22,0x23,
        0xb0,0x03,0x61,0xa3, 0x96,0x17,0x7a,0x9c, 0xb4,0x10,0xff,0x61, 0xf2,0x00,0x15,0xad
    };
    sha256_ctx_t s; sha256_init(&s);
    sha256_update(&s, (const uint8_t *)"abc", 3);
    uint8_t got[32]; sha256_final(&s, got);
    uint8_t ok = (memcmp(got, expected, 32) == 0) ? 1u : 0u;
    return lean_io_result_mk_ok(lean_box(ok));
}

LEAN_EXPORT lean_obj_res fv_digest_ctx_new(uint8_t strict, lean_obj_arg w) {
    ensure_ctx_class();
    digest_ctx_t *ctx = (digest_ctx_t *)calloc(1, sizeof(digest_ctx_t));
    if (!ctx) abort();
    ctx->strict = strict ? 1u : 0u;
    ctx->dm = (dm_entry_t *)calloc(DM_SIZE, sizeof(dm_entry_t));
    ctx->loc_cap = 4096;
    ctx->loc = (loc_entry_t *)calloc(ctx->loc_cap, sizeof(loc_entry_t));
    ctx->gen = 1;
    ctx->stk_cap = 1024;
    ctx->stk = (stack_frame_t *)malloc(ctx->stk_cap * sizeof(stack_frame_t));
    if (!ctx->dm || !ctx->loc || !ctx->stk) abort();

    sha256_ctx_t s;
    sha256_init(&s); sha_u8(&s, 0x01u); sha256_final(&s, ctx->h_anon);
    sha256_init(&s); sha_u8(&s, 0x10u); sha256_final(&s, ctx->h_lzero);

    lean_obj_res obj = lean_alloc_external(g_digest_ctx_class, ctx);
    return lean_io_result_mk_ok(obj);
}

static inline digest_ctx_t *get_ctx(b_lean_obj_arg o) {
    return (digest_ctx_t *)lean_get_external_data(o);
}

LEAN_EXPORT lean_obj_res fv_digest_hash_axiom(b_lean_obj_arg ctxo, b_lean_obj_arg name, b_lean_obj_arg lparams,
                                              b_lean_obj_arg ty, uint8_t is_unsafe, lean_obj_arg w) {
    digest_ctx_t *ctx = get_ctx(ctxo);
    ctx_reset_local(ctx);
    sha256_ctx_t s; sha256_init(&s);
    uint8_t nh[32], ch[32];
    sha_u8(&s, 0x40u);
    hash_const_head(ctx, &s, name, lparams, ty, nh);
    sha_u8(&s, is_unsafe ? 1u : 0u);
    sha256_final(&s, ch);
    return lean_io_result_mk_ok(mk_pair64(nh, ch));
}

LEAN_EXPORT lean_obj_res fv_digest_hash_defn(b_lean_obj_arg ctxo, b_lean_obj_arg name, b_lean_obj_arg lparams,
                                             b_lean_obj_arg ty, b_lean_obj_arg val,
                                             uint8_t hint_kind, uint32_t hint_height, uint8_t safety,
                                             b_lean_obj_arg all, lean_obj_arg w) {
    digest_ctx_t *ctx = get_ctx(ctxo);
    ctx_reset_local(ctx);
    sha256_ctx_t s; sha256_init(&s);
    uint8_t nh[32], vh[32], ch[32];
    sha_u8(&s, 0x41u);
    hash_const_head(ctx, &s, name, lparams, ty, nh);
    hash_node_iter(ctx, val, 2, vh);
    sha256_update(&s, vh, 32);
    sha_u8(&s, hint_kind);
    if (hint_kind == 2u) sha_u32_le(&s, hint_height);
    sha_u8(&s, safety);
    hash_name_list(ctx, &s, all);
    sha256_final(&s, ch);
    return lean_io_result_mk_ok(mk_pair64(nh, ch));
}

LEAN_EXPORT lean_obj_res fv_digest_hash_thm(b_lean_obj_arg ctxo, b_lean_obj_arg name, b_lean_obj_arg lparams,
                                            b_lean_obj_arg ty, b_lean_obj_arg val, b_lean_obj_arg all, lean_obj_arg w) {
    digest_ctx_t *ctx = get_ctx(ctxo);
    ctx_reset_local(ctx);
    sha256_ctx_t s; sha256_init(&s);
    uint8_t nh[32], vh[32], ch[32];
    sha_u8(&s, 0x42u);
    hash_const_head(ctx, &s, name, lparams, ty, nh);
    hash_node_iter(ctx, val, 2, vh);
    sha256_update(&s, vh, 32);
    hash_name_list(ctx, &s, all);
    sha256_final(&s, ch);
    return lean_io_result_mk_ok(mk_pair64(nh, ch));
}

LEAN_EXPORT lean_obj_res fv_digest_hash_opaque(b_lean_obj_arg ctxo, b_lean_obj_arg name, b_lean_obj_arg lparams,
                                               b_lean_obj_arg ty, b_lean_obj_arg val, uint8_t is_unsafe,
                                               b_lean_obj_arg all, lean_obj_arg w) {
    digest_ctx_t *ctx = get_ctx(ctxo);
    ctx_reset_local(ctx);
    sha256_ctx_t s; sha256_init(&s);
    uint8_t nh[32], vh[32], ch[32];
    sha_u8(&s, 0x43u);
    hash_const_head(ctx, &s, name, lparams, ty, nh);
    hash_node_iter(ctx, val, 2, vh);
    sha256_update(&s, vh, 32);
    sha_u8(&s, is_unsafe ? 1u : 0u);
    hash_name_list(ctx, &s, all);
    sha256_final(&s, ch);
    return lean_io_result_mk_ok(mk_pair64(nh, ch));
}

LEAN_EXPORT lean_obj_res fv_digest_hash_quot(b_lean_obj_arg ctxo, b_lean_obj_arg name, b_lean_obj_arg lparams,
                                             b_lean_obj_arg ty, uint8_t qkind, lean_obj_arg w) {
    digest_ctx_t *ctx = get_ctx(ctxo);
    ctx_reset_local(ctx);
    sha256_ctx_t s; sha256_init(&s);
    uint8_t nh[32], ch[32];
    sha_u8(&s, 0x44u);
    hash_const_head(ctx, &s, name, lparams, ty, nh);
    sha_u8(&s, qkind);
    sha256_final(&s, ch);
    return lean_io_result_mk_ok(mk_pair64(nh, ch));
}

LEAN_EXPORT lean_obj_res fv_digest_hash_induct(b_lean_obj_arg ctxo, b_lean_obj_arg name, b_lean_obj_arg lparams,
                                               b_lean_obj_arg ty, b_lean_obj_arg nparams, b_lean_obj_arg nindices,
                                               b_lean_obj_arg all, b_lean_obj_arg ctors, b_lean_obj_arg nnested,
                                               uint8_t is_rec, uint8_t is_unsafe, uint8_t is_refl, lean_obj_arg w) {
    digest_ctx_t *ctx = get_ctx(ctxo);
    ctx_reset_local(ctx);
    sha256_ctx_t s; sha256_init(&s);
    uint8_t nh[32], ch[32];
    sha_u8(&s, 0x45u);
    hash_const_head(ctx, &s, name, lparams, ty, nh);
    sha_lean_nat(&s, nparams);
    sha_lean_nat(&s, nindices);
    hash_name_list(ctx, &s, all);
    hash_name_list(ctx, &s, ctors);
    sha_lean_nat(&s, nnested);
    sha_u8(&s, is_rec ? 1u : 0u);
    sha_u8(&s, is_unsafe ? 1u : 0u);
    sha_u8(&s, is_refl ? 1u : 0u);
    sha256_final(&s, ch);
    return lean_io_result_mk_ok(mk_pair64(nh, ch));
}

LEAN_EXPORT lean_obj_res fv_digest_hash_ctor(b_lean_obj_arg ctxo, b_lean_obj_arg name, b_lean_obj_arg lparams,
                                             b_lean_obj_arg ty, b_lean_obj_arg induct, b_lean_obj_arg cidx,
                                             b_lean_obj_arg nparams, b_lean_obj_arg nfields, uint8_t is_unsafe,
                                             lean_obj_arg w) {
    digest_ctx_t *ctx = get_ctx(ctxo);
    ctx_reset_local(ctx);
    sha256_ctx_t s; sha256_init(&s);
    uint8_t nh[32], ih[32], ch[32];
    sha_u8(&s, 0x46u);
    hash_const_head(ctx, &s, name, lparams, ty, nh);
    hash_node_iter(ctx, induct, 0, ih);
    sha256_update(&s, ih, 32);
    sha_lean_nat(&s, cidx);
    sha_lean_nat(&s, nparams);
    sha_lean_nat(&s, nfields);
    sha_u8(&s, is_unsafe ? 1u : 0u);
    sha256_final(&s, ch);
    return lean_io_result_mk_ok(mk_pair64(nh, ch));
}

LEAN_EXPORT lean_obj_res fv_digest_hash_rec_rule(b_lean_obj_arg ctxo, b_lean_obj_arg ctor,
                                                 b_lean_obj_arg nfields, b_lean_obj_arg rhs, lean_obj_arg w) {
    digest_ctx_t *ctx = get_ctx(ctxo);
    ctx_reset_local(ctx);
    sha256_ctx_t s; sha256_init(&s);
    uint8_t cth[32], rh[32], out[32];
    sha_u8(&s, 0x48u);
    hash_node_iter(ctx, ctor, 0, cth);
    sha256_update(&s, cth, 32);
    sha_lean_nat(&s, nfields);
    hash_node_iter(ctx, rhs, 2, rh);
    sha256_update(&s, rh, 32);
    sha256_final(&s, out);
    return lean_io_result_mk_ok(mk_bytes32(out));
}

LEAN_EXPORT lean_obj_res fv_digest_hash_rec(b_lean_obj_arg ctxo, b_lean_obj_arg name, b_lean_obj_arg lparams,
                                            b_lean_obj_arg ty, b_lean_obj_arg all, b_lean_obj_arg nparams,
                                            b_lean_obj_arg nindices, b_lean_obj_arg nmotives, b_lean_obj_arg nminors,
                                            b_lean_obj_arg rule_hashes, uint8_t k_flag, uint8_t is_unsafe, lean_obj_arg w) {
    digest_ctx_t *ctx = get_ctx(ctxo);
    ctx_reset_local(ctx);
    sha256_ctx_t s; sha256_init(&s);
    uint8_t nh[32], ch[32];
    sha_u8(&s, 0x47u);
    hash_const_head(ctx, &s, name, lparams, ty, nh);
    hash_name_list(ctx, &s, all);
    sha_lean_nat(&s, nparams);
    sha_lean_nat(&s, nindices);
    sha_lean_nat(&s, nmotives);
    sha_lean_nat(&s, nminors);
    size_t nr = lean_array_size(rule_hashes);
    sha_u32_le(&s, (uint32_t)nr);
    for (size_t i = 0; i < nr; ++i) {
        b_lean_obj_arg rh = lean_array_get_core(rule_hashes, i);
        sha256_update(&s, lean_sarray_cptr(rh), 32);
    }
    sha_u8(&s, k_flag ? 1u : 0u);
    sha_u8(&s, is_unsafe ? 1u : 0u);
    sha256_final(&s, ch);
    return lean_io_result_mk_ok(mk_pair64(nh, ch));
}

static int cmp_pair64(const void *a, const void *b) {
    return memcmp(a, b, 64);
}

/* Finalize an Array of 64-byte ByteArrays into the canonical 64-hex-char env SHA-256 digest. */
LEAN_EXPORT lean_obj_res fv_digest_finalize_env(b_lean_obj_arg pairs_arr, uint8_t strict, lean_obj_arg w) {
    size_t n = lean_array_size(pairs_arr);
    uint8_t *flat = n > 0 ? (uint8_t *)malloc(n * 64u) : NULL;
    if (n > 0 && !flat) abort();
    for (size_t i = 0; i < n; ++i) {
        b_lean_obj_arg ba = lean_array_get_core(pairs_arr, i);
        memcpy(flat + i * 64u, lean_sarray_cptr(ba), 64u);
    }
    if (n > 1) {
        qsort(flat, n, 64u, cmp_pair64);
    }
    sha256_ctx_t s; sha256_init(&s);
    if (!strict) {
        static const uint8_t dom[] = "FV-ENV-SHA256-V1";
        sha256_update(&s, dom, sizeof(dom)); /* includes trailing NUL */
    } else {
        static const uint8_t dom[] = "FV-ENV-STRICT-SHA256-V1";
        sha256_update(&s, dom, sizeof(dom)); /* includes trailing NUL */
    }
    sha_u64_le(&s, (uint64_t)n);
    if (n > 0) sha256_update(&s, flat, n * 64u);
    uint8_t root[32];
    sha256_final(&s, root);
    free(flat);

    static const char hex[] = "0123456789abcdef";
    char out[65];
    for (int i = 0; i < 32; ++i) {
        out[2*i]     = hex[root[i] >> 4];
        out[2*i + 1] = hex[root[i] & 0xf];
    }
    out[64] = '\0';
    return lean_io_result_mk_ok(lean_mk_string(out));
}
