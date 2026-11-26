// Build glue for native/*.cpp: no dependency on the GNU libstdc++ runtime library.
//
// The official Lean toolchain links executables with its bundled clang against LLVM libc++/libc++abi and never against
// GNU libstdc++, while lakefile.lean compiles the native code with the system C++ compiler (g++, i.e. libstdc++
// headers).  The header-only parts of libstdc++ are fine; this header removes or provides the few out-of-line pieces:
//  * explicit-instantiation declarations are disabled, so std::string & co. are instantiated in this translation unit;
//  * the std::__throw_* helpers, std::_Hash_bytes and std::__detail::_Prime_rehash_policy are defined below (weak);
//  * the code is compiled with -fno-exceptions -fno-rtti (no __cxa_throw / typeinfo objects from libsupc++);
//  * std::thread and std::condition_variable live in libstdc++.so: use NThread / NCondVar below instead.
// The remaining Itanium-ABI symbols (operator new/delete, __cxa_guard_*, __cxa_atexit, __dso_handle) are provided by
// libc++abi / glibc in the Lean link.  Check with `nm -uC .lake/build/native/fast_export.o`: only lean_*, libc,
// pthread, operator new/delete and __cxa_guard/atexit symbols may appear.
#pragma once

#include <bits/c++config.h>
#undef _GLIBCXX_EXTERN_TEMPLATE
#define _GLIBCXX_EXTERN_TEMPLATE 0
// safety net for the RULE below: glibc >= 2.38 selects the __isoc23_* strtol/scanf variants via this features.h macro
// (included by c++config.h); force the classic symbols, which every glibc (and the toolchain's link stubs) provides
#ifdef __GLIBC_USE_C2X_STRTOL
#undef __GLIBC_USE_C2X_STRTOL
#define __GLIBC_USE_C2X_STRTOL 0
#endif

#include <pthread.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <mutex>
#include <string>
#include <unordered_map>
#include <utility>

namespace lean4export_stdcxx_glue {
[[noreturn]] inline void fail(const char* what, const char* msg) {
    fprintf(stderr, "lean4export (native): fatal: %s%s%s\n", what, msg ? ": " : "", msg ? msg : "");
    fflush(stderr);
    abort();
}
}  // namespace lean4export_stdcxx_glue

#define LEAN4EXPORT_GLUE_WEAK __attribute__((weak))
namespace std {
LEAN4EXPORT_GLUE_WEAK void __throw_bad_exception() { lean4export_stdcxx_glue::fail("bad_exception", nullptr); }
LEAN4EXPORT_GLUE_WEAK void __throw_bad_alloc() { lean4export_stdcxx_glue::fail("out of memory (bad_alloc)", nullptr); }
LEAN4EXPORT_GLUE_WEAK void __throw_bad_array_new_length() { lean4export_stdcxx_glue::fail("bad_array_new_length", nullptr); }
LEAN4EXPORT_GLUE_WEAK void __throw_bad_cast() { lean4export_stdcxx_glue::fail("bad_cast", nullptr); }
LEAN4EXPORT_GLUE_WEAK void __throw_bad_typeid() { lean4export_stdcxx_glue::fail("bad_typeid", nullptr); }
LEAN4EXPORT_GLUE_WEAK void __throw_logic_error(const char* s) { lean4export_stdcxx_glue::fail("logic_error", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_domain_error(const char* s) { lean4export_stdcxx_glue::fail("domain_error", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_invalid_argument(const char* s) { lean4export_stdcxx_glue::fail("invalid_argument", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_length_error(const char* s) { lean4export_stdcxx_glue::fail("length_error", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_out_of_range(const char* s) { lean4export_stdcxx_glue::fail("out_of_range", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_out_of_range_fmt(const char* s, ...) { lean4export_stdcxx_glue::fail("out_of_range", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_runtime_error(const char* s) { lean4export_stdcxx_glue::fail("runtime_error", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_range_error(const char* s) { lean4export_stdcxx_glue::fail("range_error", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_overflow_error(const char* s) { lean4export_stdcxx_glue::fail("overflow_error", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_underflow_error(const char* s) { lean4export_stdcxx_glue::fail("underflow_error", s); }
LEAN4EXPORT_GLUE_WEAK void __throw_system_error(int e) { lean4export_stdcxx_glue::fail("system_error", strerror(e)); }
LEAN4EXPORT_GLUE_WEAK void __throw_bad_function_call() { lean4export_stdcxx_glue::fail("bad_function_call", nullptr); }

// std::hash<std::string> & co. (any good hash is fine: only this translation unit uses it)
LEAN4EXPORT_GLUE_WEAK size_t _Hash_bytes(const void* ptr, size_t len, size_t seed) {
    const unsigned char* p = (const unsigned char*)ptr;
    uint64_t h = 0xcbf29ce484222325ULL ^ (uint64_t)seed;
    for (size_t i = 0; i < len; i++) h = (h ^ p[i]) * 0x100000001b3ULL;
    h ^= h >> 33;
    h *= 0xff51afd7ed558ccdULL;
    h ^= h >> 33;
    return (size_t)h;
}
LEAN4EXPORT_GLUE_WEAK size_t _Fnv_hash_bytes(const void* ptr, size_t len, size_t seed) { return _Hash_bytes(ptr, len, seed); }

namespace __detail {
// bucket-count policy of std::unordered_map (same contract as libstdc++'s src/shared/hashtable-aux.cc)
LEAN4EXPORT_GLUE_WEAK size_t _Prime_rehash_policy::_M_next_bkt(size_t n) const {
    if (n == 0) return 1;  // first initialization with a zero hint: keep _M_next_resize = 0
    size_t b = n < 11 ? 11 : (n | 1);
    while (b % 3 == 0 || b % 5 == 0 || b % 7 == 0 || b % 11 == 0 || b % 13 == 0) b += 2;
    if (b < n) b = n;  // (overflow guard)
    _M_next_resize = (size_t)__builtin_floor((double)b * (double)_M_max_load_factor);
    return b;
}
LEAN4EXPORT_GLUE_WEAK pair<bool, size_t> _Prime_rehash_policy::_M_need_rehash(size_t n_bkt, size_t n_elt, size_t n_ins) const {
    if (n_elt + n_ins > _M_next_resize) {
        size_t want = n_elt + n_ins;
        if (_M_next_resize == 0 && want < 11) want = 11;
        double min_bkts = (double)want / (double)_M_max_load_factor;
        if (min_bkts >= (double)n_bkt) {
            size_t a = (size_t)__builtin_floor(min_bkts) + 1, b = n_bkt * 2;
            return {true, _M_next_bkt(a > b ? a : b)};
        }
        _M_next_resize = (size_t)__builtin_floor((double)n_bkt * (double)_M_max_load_factor);
        return {false, 0};
    }
    return {false, 0};
}
}  // namespace __detail
}  // namespace std
#undef LEAN4EXPORT_GLUE_WEAK

namespace lean4export_native {
// replacement for std::condition_variable (pthread condition variable used with std::unique_lock<std::mutex>)
struct NCondVar {
    pthread_cond_t c = PTHREAD_COND_INITIALIZER;
    NCondVar() = default;
    NCondVar(const NCondVar&) = delete;
    NCondVar& operator=(const NCondVar&) = delete;
    ~NCondVar() { pthread_cond_destroy(&c); }
    void wait(std::unique_lock<std::mutex>& l) { pthread_cond_wait(&c, l.mutex()->native_handle()); }
    template <class Pred>
    void wait(std::unique_lock<std::mutex>& l, Pred p) {
        while (!p()) wait(l);
    }
    void notify_one() { pthread_cond_signal(&c); }
    void notify_all() { pthread_cond_broadcast(&c); }
};
// replacement for std::thread (joinable pthread running a std::function; optional stack size)
struct NThread {
    pthread_t th{};
    bool running = false;
    std::function<void()>* fn = nullptr;
    NThread() = default;
    NThread(const NThread&) = delete;
    NThread& operator=(const NThread&) = delete;
    static void* tramp(void* a) {
        (*(std::function<void()>*)a)();
        return nullptr;
    }
    void start(std::function<void()> f, size_t stack = 0) {
        fn = new std::function<void()>(std::move(f));
        pthread_attr_t at;
        pthread_attr_init(&at);
        if (stack) pthread_attr_setstacksize(&at, stack);
        if (pthread_create(&th, &at, tramp, fn) != 0) lean4export_stdcxx_glue::fail("pthread_create failed", nullptr);
        pthread_attr_destroy(&at);
        running = true;
    }
    void join() {
        if (!running) return;
        pthread_join(th, nullptr);
        running = false;
        delete fn;
        fn = nullptr;
    }
    ~NThread() { join(); }
};
}  // namespace lean4export_native
