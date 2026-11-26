/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <tuple>
#include "runtime/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"
#include "util/ptr_cache.h"

namespace lean {
/**
   \brief Apply <tt>f</tt> to the subexpressions of a given expression.

   f is invoked for each subexpression \c s of the input expression e.
   In a call <tt>f(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s. The replaces only visits children of \c e
   if f return none_expr.
*/
expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache = true);
inline expr replace(expr const & e, std::function<optional<expr>(expr const &)> const & f, bool use_cache = true) {
    return replace(e, [&](expr const & e, unsigned) { return f(e); }, use_cache);
}

struct replace_no_skip {
    bool operator()(expr const &, unsigned) const { return false; }
};

/* Implementation of `replace`, specialized to the function object types so that they can be inlined.
   `skip(e, offset)` is a cheap test that must imply that `f(e, offset)` returns `e` itself; such subterms
   are returned before consulting the cache (which cannot change the result, as the cached value would be `e`
   as well), and `f` is only called on subterms for which `skip` is false. */
template<typename F, typename S = replace_no_skip>
class replace_rec_fn {
    ptr_cache_map<ptr_offset_key, expr, ptr_offset_key_ops> m_cache;
    F const & m_f;
    S         m_skip;
    bool      m_use_cache;

    expr save_result(expr const & e, unsigned offset, expr r, bool shared) {
        if (shared)
            m_cache.insert_if_absent(ptr_offset_key{e.raw(), offset}, r);
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        if (m_skip(e, offset))
            return e;
        bool shared = false;
        if (m_use_cache && !is_likely_unshared(e)) {
            if (expr const * r = m_cache.find(ptr_offset_key{e.raw(), offset}))
                return *r;
            shared = true;
        }
        if (optional<expr> r = m_f(e, offset)) {
            return save_result(e, offset, std::move(*r), shared);
        } else {
            switch (e.kind()) {
            case expr_kind::Const: case expr_kind::Sort:
            case expr_kind::BVar:  case expr_kind::Lit:
            case expr_kind::MVar:  case expr_kind::FVar:
                return save_result(e, offset, e, shared);
            case expr_kind::MData: {
                expr new_e = apply(mdata_expr(e), offset);
                return save_result(e, offset, update_mdata(e, new_e), shared);
            }
            case expr_kind::Proj: {
                expr new_e = apply(proj_expr(e), offset);
                return save_result(e, offset, update_proj(e, new_e), shared);
            }
            case expr_kind::App: {
                expr new_f = apply(app_fn(e), offset);
                expr new_a = apply(app_arg(e), offset);
                return save_result(e, offset, update_app(e, new_f, new_a), shared);
            }
            case expr_kind::Pi: case expr_kind::Lambda: {
                expr new_d = apply(binding_domain(e), offset);
                expr new_b = apply(binding_body(e), offset+1);
                return save_result(e, offset, update_binding(e, new_d, new_b), shared);
            }
            case expr_kind::Let: {
                expr new_t = apply(let_type(e), offset);
                expr new_v = apply(let_value(e), offset);
                expr new_b = apply(let_body(e), offset+1);
                return save_result(e, offset, update_let(e, new_t, new_v, new_b), shared);
            }
            }
            lean_unreachable();
        }
    }
public:
    replace_rec_fn(F const & f, bool use_cache, S skip = S()):m_f(f), m_skip(skip), m_use_cache(use_cache) {}
    expr operator()(expr const & e) { return apply(e, 0); }
};

/* Same as `replace`, but `f` (taking `(expr const &, unsigned)`) is inlined instead of being called through
   `std::function`, and `skip` (see `replace_rec_fn`) is tested first on every subterm.
   Never inlined itself, so that the cache's inline storage cannot end up in the stack frame of a recursive caller. */
template<typename S, typename F>
__attribute__((noinline)) expr replace_inline(expr const & e, S const & skip, F const & f, bool use_cache = true) {
    return replace_rec_fn<F, S>(f, use_cache, skip)(e);
}
}
