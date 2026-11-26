/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <cstdlib>
#include <new>
#include <utility>
#include <type_traits>
#include "runtime/debug.h"
#include "runtime/int.h"
#include "util/alloc.h"

namespace lean {
/*
Small open-addressing hash map (linear probing, power-of-two capacity, maximal load factor 1/2)
for the per-traversal caches of `replace`, `for_each`, `expr_eq_fn` etc., which are keyed by raw
object pointers. Compared to `std::unordered_map`, it does not allocate a node per insertion, its
first `InlineCap` slots live inside the object itself, and it does no work at construction time.

It only supports `find` and `insert_if_absent` (no erase, no iteration), so its observable behavior
is exactly that of a map: the same sequence of queries yields the same answers as with
`std::unordered_map::find/insert`.

`KeyOps` must provide
  `static uint64 hash(Key const &)`, `static bool is_empty(Key const &)`, `static Key empty()`
where the empty key is never inserted. `Key` must be trivially copyable.
*/
template<typename Key, typename Value, typename KeyOps, unsigned InlineCap = 32>
class ptr_cache_map {
    static_assert(std::is_trivially_copyable<Key>::value, "ptr_cache_map key must be trivially copyable");
    static_assert(InlineCap >= 2 && (InlineCap & (InlineCap - 1)) == 0, "InlineCap must be a power of two");
    struct slot {
        Key m_key;
        alignas(Value) unsigned char m_value[sizeof(Value)];
        Value & value() { return *reinterpret_cast<Value *>(m_value); }
    };
    slot *   m_slots = nullptr; // nullptr until the first insertion
    size_t   m_mask  = 0;       // capacity - 1
    size_t   m_size  = 0;
    unsigned m_shift = 0;       // 64 - log2(capacity)
    alignas(slot) unsigned char m_inline[InlineCap * sizeof(slot)];

    static unsigned log2(size_t n) { unsigned r = 0; while ((size_t(1) << r) < n) r++; return r; }

    size_t index_of(Key const & k) const {
        // Fibonacci hashing: use the high bits of the product.
        return static_cast<size_t>((KeyOps::hash(k) * static_cast<uint64>(0x9E3779B97F4A7C15ull)) >> m_shift);
    }

    static slot * alloc_slots(size_t n) {
#ifdef LEAN_MIMALLOC
        void * mem = mi_malloc(n * sizeof(slot));
#else
        void * mem = std::malloc(n * sizeof(slot));
#endif
        if (!mem) throw std::bad_alloc();
        return static_cast<slot *>(mem);
    }

    static void free_slots(slot * s) {
#ifdef LEAN_MIMALLOC
        mi_free(s);
#else
        std::free(s);
#endif
    }

    void init(slot * slots, size_t cap) {
        m_slots = slots;
        m_mask  = cap - 1;
        m_shift = 64 - log2(cap);
        for (size_t i = 0; i < cap; i++)
            slots[i].m_key = KeyOps::empty();
    }

    void grow() {
        slot * old     = m_slots;
        size_t old_cap = m_mask + 1;
        // Grow faster while small: tables that outgrow the inline slots usually become much larger.
        size_t new_cap = old_cap < 4096 ? old_cap * 4 : old_cap * 2;
        init(alloc_slots(new_cap), new_cap);
        for (size_t i = 0; i < old_cap; i++) {
            if (!KeyOps::is_empty(old[i].m_key)) {
                size_t j = index_of(old[i].m_key);
                while (!KeyOps::is_empty(m_slots[j].m_key))
                    j = (j + 1) & m_mask;
                m_slots[j].m_key = old[i].m_key;
                new (m_slots[j].m_value) Value(std::move(old[i].value()));
                old[i].value().~Value();
            }
        }
        if (old != reinterpret_cast<slot *>(m_inline))
            free_slots(old);
    }

public:
    ptr_cache_map() {}
    ptr_cache_map(ptr_cache_map const &) = delete;
    ptr_cache_map & operator=(ptr_cache_map const &) = delete;
    ~ptr_cache_map() {
        if (!m_slots) return;
        if (!std::is_trivially_destructible<Value>::value) {
            for (size_t i = 0; i <= m_mask; i++) {
                if (!KeyOps::is_empty(m_slots[i].m_key))
                    m_slots[i].value().~Value();
            }
        }
        if (m_slots != reinterpret_cast<slot *>(m_inline))
            free_slots(m_slots);
    }

    /* Return a pointer to the value associated with `k`, or `nullptr`. */
    Value const * find(Key const & k) const {
        if (!m_slots) return nullptr;
        size_t i = index_of(k);
        while (true) {
            slot const & s = m_slots[i];
            if (KeyOps::is_empty(s.m_key)) return nullptr;
            if (s.m_key == k) return reinterpret_cast<Value const *>(s.m_value);
            i = (i + 1) & m_mask;
        }
    }

    /* Associate `v` with `k` unless `k` is already present (like `std::unordered_map::insert`).
       Return `true` iff the value was inserted. */
    template<typename V>
    bool insert_if_absent(Key const & k, V && v) {
        lean_assert(!KeyOps::is_empty(k));
        if (!m_slots) {
            init(reinterpret_cast<slot *>(m_inline), InlineCap);
        } else if ((m_size + 1) * 2 > m_mask + 1) {
            if (find(k)) return false;
            grow();
        }
        size_t i = index_of(k);
        while (true) {
            slot & s = m_slots[i];
            if (KeyOps::is_empty(s.m_key)) {
                s.m_key = k;
                new (s.m_value) Value(std::forward<V>(v));
                m_size++;
                return true;
            }
            if (s.m_key == k) return false;
            i = (i + 1) & m_mask;
        }
    }

    size_t size() const { return m_size; }
};

/* Set variant: `insert` returns `true` iff `k` was not present before. */
template<typename Key, typename KeyOps, unsigned InlineCap = 32>
class ptr_cache_set {
    struct unit {};
    ptr_cache_map<Key, unit, KeyOps, InlineCap> m_map;
public:
    bool contains(Key const & k) const { return m_map.find(k) != nullptr; }
    bool insert(Key const & k) { return m_map.insert_if_absent(k, unit()); }
    size_t size() const { return m_map.size(); }
};

/* Key operations for the common key types. */
struct ptr_key_ops {
    static uint64 hash(void * p) { return static_cast<uint64>(reinterpret_cast<size_t>(p)) >> 3; }
    static bool is_empty(void * p) { return p == nullptr; }
    static void * empty() { return nullptr; }
};

struct ptr_offset_key {
    void *   m_ptr;
    unsigned m_offset;
    bool operator==(ptr_offset_key const & o) const { return m_ptr == o.m_ptr && m_offset == o.m_offset; }
};

struct ptr_offset_key_ops {
    static uint64 hash(ptr_offset_key const & k) {
        return (static_cast<uint64>(reinterpret_cast<size_t>(k.m_ptr)) >> 3) ^ (static_cast<uint64>(k.m_offset) << 45);
    }
    static bool is_empty(ptr_offset_key const & k) { return k.m_ptr == nullptr; }
    static ptr_offset_key empty() { return ptr_offset_key{nullptr, 0}; }
};

struct ptr_pair_key {
    void * m_fst;
    void * m_snd;
    bool operator==(ptr_pair_key const & o) const { return m_fst == o.m_fst && m_snd == o.m_snd; }
};

struct ptr_pair_key_ops {
    static uint64 hash(ptr_pair_key const & k) {
        uint64 a = static_cast<uint64>(reinterpret_cast<size_t>(k.m_fst)) >> 3;
        uint64 b = static_cast<uint64>(reinterpret_cast<size_t>(k.m_snd)) >> 3;
        return a ^ (b * static_cast<uint64>(0xC2B2AE3D27D4EB4Full)) ^ (b >> 29);
    }
    static bool is_empty(ptr_pair_key const & k) { return k.m_fst == nullptr; }
    static ptr_pair_key empty() { return ptr_pair_key{nullptr, nullptr}; }
};
}
