#define _GNU_SOURCE
#include <signal.h>
#include <execinfo.h>
#include <unistd.h>
#include <dlfcn.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
/* LD_PRELOAD shim: on SIGSEGV print a backtrace to stderr, then exit 139. Interposes sigaction so that the program's own
   SIGSEGV handler (Lean's stack-overflow detector) does not replace ours. Diagnostics only. */
static char altstack[1 << 16];
static void on_segv(int sig, siginfo_t *si, void *ctx) {
  void *buf[64]; int n = backtrace(buf, 64);
  char msg[128]; int len = snprintf(msg, sizeof msg, "\n[segv-shim] SIGSEGV at address %p, %d frames:\n", si->si_addr, n);
  write(2, msg, len); backtrace_symbols_fd(buf, n, 2); _exit(139);
}
static void install(void) {
  stack_t ss = { .ss_sp = altstack, .ss_size = sizeof altstack, .ss_flags = 0 }; sigaltstack(&ss, 0);
  struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_sigaction = on_segv; sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
  int (*real)(int, const struct sigaction *, struct sigaction *) = dlsym(RTLD_NEXT, "sigaction");
  real(SIGSEGV, &sa, 0);
}
__attribute__((constructor)) static void init(void) { install(); }
int sigaction(int signum, const struct sigaction *act, struct sigaction *old) {
  int (*real)(int, const struct sigaction *, struct sigaction *) = dlsym(RTLD_NEXT, "sigaction");
  if (signum == SIGSEGV && act) return 0;   /* keep our handler */
  return real(signum, act, old);
}
