/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <cstdlib>
#include <new>
#include "runtime/debug.h"
#include "runtime/hash.h"
#include "runtime/object_ref.h"
#include "kernel/expr.h"
#include "kernel/expr_eq_fn.h"
#include "util/alloc.h"

namespace lean {
/*
Open-addressing caches for the kernel type checker (`type_checker::state`). They replace
`std::unordered_map<expr, expr, expr_hash, std::equal_to<expr>>` (`tc_expr_map`) and
`std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq>` (`tc_expr_pair_set`).

Keys are matched exactly as before: an entry matches iff its hash code (computed by the same
hash function as before and stored in the slot, just like libstdc++ caches it in the node) is
equal to the query's and the keys are `==` (`is_equal`, i.e. structural equality ignoring binder
info). Only lookup and insert-if-absent (the semantics of `std::unordered_map::insert`) are
supported; there is no erase and no iteration. Hence every sequence of queries gets exactly the
same answers as with the node-based containers, and the type checker takes exactly the same
decisions.

Representation: linear probing over a power-of-two slot array (maximal load factor 1/2),
allocated lazily on the first insertion. A lookup touches one contiguous slot (hash code, key and
value side by side) instead of a bucket array plus a chain of separately allocated nodes whose
bucket membership libstdc++ re-checks with an integer division per node, and destroying a cache
is one linear pass plus a single free instead of one free per entry.
*/
namespace tc_cache_detail {
inline void * alloc_slots(size_t bytes) {
#ifdef LEAN_MIMALLOC
    void * mem = mi_malloc(bytes);
#else
    void * mem = std::malloc(bytes);
#endif
    if (!mem) throw std::bad_alloc();
    return mem;
}
inline void free_slots(void * mem) {
#ifdef LEAN_MIMALLOC
    mi_free(mem);
#else
    std::free(mem);
#endif
}
inline unsigned log2_ceil(size_t n) { unsigned r = 0; while ((size_t(1) << r) < n) r++; return r; }
/* Fibonacci hashing of the 32-bit hash code: the high bits of the product select the home slot. */
inline size_t home(unsigned h, unsigned shift) {
    return static_cast<size_t>((static_cast<uint64>(h) * static_cast<uint64>(0x9E3779B97F4A7C15ull)) >> shift);
}
}

/* Two-object-slot open-addressing table. `Match` decides whether an occupied slot (whose hash code
   already equals the query's) matches the query. Both objects of an occupied slot are owned
   references. */
class tc_cache_table {
protected:
    struct slot {
        unsigned m_hash;
        unsigned m_used;
        object * m_fst;
        object * m_snd;
    };
    slot *   m_slots = nullptr;  // nullptr until the first insertion
    size_t   m_mask  = 0;        // capacity - 1
    size_t   m_size  = 0;
    unsigned m_shift = 0;        // 64 - log2(capacity)

    static constexpr size_t initial_capacity = 64;

    void init(size_t cap) {
        slot * s = static_cast<slot *>(tc_cache_detail::alloc_slots(cap * sizeof(slot)));
        for (size_t i = 0; i < cap; i++) s[i].m_used = 0;
        m_slots = s;
        m_mask  = cap - 1;
        m_shift = 64 - tc_cache_detail::log2_ceil(cap);
    }

    void grow() {
        slot * old     = m_slots;
        size_t old_cap = m_mask + 1;
        init(old_cap * 2);
        for (size_t i = 0; i < old_cap; i++) {
            if (old[i].m_used) {
                size_t j = tc_cache_detail::home(old[i].m_hash, m_shift);
                while (m_slots[j].m_used)
                    j = (j + 1) & m_mask;
                m_slots[j] = old[i];
            }
        }
        tc_cache_detail::free_slots(old);
    }

    /* Return the matching slot, or `nullptr`. */
    template<typename Match>
    slot const * find_slot(unsigned h, Match const & match) const {
        if (!m_slots) return nullptr;
        size_t i = tc_cache_detail::home(h, m_shift);
        while (true) {
            slot const & s = m_slots[i];
            if (!s.m_used) return nullptr;
            if (s.m_hash == h && match(s)) return &s;
            i = (i + 1) & m_mask;
        }
    }

    /* Insert `(fst, snd)` (borrowed; references are taken) unless a matching entry exists. */
    template<typename Match>
    void insert_if_absent(unsigned h, Match const & match, object * fst, object * snd) {
        if (!m_slots) {
            init(initial_capacity);
        } else if ((m_size + 1) * 2 > m_mask + 1) {
            if (find_slot(h, match)) return;
            grow();
        }
        size_t i = tc_cache_detail::home(h, m_shift);
        while (true) {
            slot & s = m_slots[i];
            if (!s.m_used) {
                inc(fst); inc(snd);
                s.m_hash = h;
                s.m_fst  = fst;
                s.m_snd  = snd;
                s.m_used = 1;
                m_size++;
                return;
            }
            if (s.m_hash == h && match(s)) return;
            i = (i + 1) & m_mask;
        }
    }

public:
    tc_cache_table() {}
    tc_cache_table(tc_cache_table const &) = delete;
    tc_cache_table & operator=(tc_cache_table const &) = delete;
    ~tc_cache_table() {
        if (!m_slots) return;
        for (size_t i = 0; i <= m_mask; i++) {
            if (m_slots[i].m_used) {
                dec(m_slots[i].m_fst);
                dec(m_slots[i].m_snd);
            }
        }
        tc_cache_detail::free_slots(m_slots);
    }
    size_t size() const { return m_size; }
};

/* Replacement for `std::unordered_map<expr, expr, expr_hash, std::equal_to<expr>>`. */
class tc_expr_map : public tc_cache_table {
    struct key_match {
        expr const & m_key;
        bool operator()(slot const & s) const { return is_equal(m_key, TO_REF(expr, s.m_fst)); }
    };
public:
    /* Return the value associated with `k` (borrowed), or `nullptr`. */
    object * find(expr const & k) const {
        slot const * s = find_slot(hash(k), key_match{k});
        return s ? s->m_snd : nullptr;
    }
    /* Associate `v` with `k` unless `k` is already present (like `std::unordered_map::insert`). */
    void insert(expr const & k, expr const & v) {
        insert_if_absent(hash(k), key_match{k}, k.raw(), v.raw());
    }
};

/* Cache of `environment::find` results of one `type_checker::state` (whose environment never
   changes), keyed by the identity of the queried name object. The name object is an owned
   reference, so its address cannot be reused by another object while the entry exists; hence a hit
   returns exactly what `environment::find` returned for the same (structurally equal) name.
   The value is the `constant_info` object (owned), or `box(0)` when the constant does not exist. */
class tc_const_cache : public tc_cache_table {
    struct ptr_match {
        object * m_key;
        bool operator()(slot const & s) const { return s.m_fst == m_key; }
    };
    static unsigned ptr_hash(object * o) {
        uint64 p = reinterpret_cast<uint64>(o);
        return static_cast<unsigned>((p >> 4) ^ (p >> 32));
    }
public:
    /* Return `true` and set `r` if `n` is cached. */
    bool find(name const & n, optional<constant_info> & r) const {
        object * k = n.raw();
        slot const * s = find_slot(ptr_hash(k), ptr_match{k});
        if (!s) return false;
        if (is_scalar(s->m_snd))
            r = optional<constant_info>();
        else
            r = optional<constant_info>(constant_info(s->m_snd, true));
        return true;
    }
    void insert(name const & n, optional<constant_info> const & r) {
        object * k = n.raw();
        insert_if_absent(ptr_hash(k), ptr_match{k}, k, r ? r->raw() : box(0));
    }
};

/* Replacement for `std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq>`. */
class tc_expr_pair_set : public tc_cache_table {
    struct pair_match {
        expr const & m_fst;
        expr const & m_snd;
        bool operator()(slot const & s) const {
            return is_equal(m_fst, TO_REF(expr, s.m_fst)) && is_equal(m_snd, TO_REF(expr, s.m_snd));
        }
    };
    /* Same hash code as `expr_pair_hash`. */
    static unsigned pair_hash(expr const & a, expr const & b) { return static_cast<unsigned>(lean::hash(hash(a), hash(b))); }
public:
    bool contains(expr const & a, expr const & b) const {
        return find_slot(pair_hash(a, b), pair_match{a, b}) != nullptr;
    }
    void insert(expr const & a, expr const & b) {
        insert_if_absent(pair_hash(a, b), pair_match{a, b}, a.raw(), b.raw());
    }
};
}
