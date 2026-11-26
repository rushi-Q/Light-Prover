#define _GNU_SOURCE
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <ucontext.h>
#include <unistd.h>
#include <link.h>
static void h(int sig, siginfo_t *si, void *ctx) {
  ucontext_t *uc = ctx;
  unsigned long ip = uc->uc_mcontext.gregs[REG_RIP];
  Dl_info info;
  char buf[256];
  int n = snprintf(buf, sizeof buf, "SIGILL at ip=%lx\n", ip);
  write(2, buf, n);
  FILE *f = fopen("/proc/self/maps", "r");
  char line[512];
  while (f && fgets(line, sizeof line, f)) {
    unsigned long a, b, off; char perm[8];
    if (sscanf(line, "%lx-%lx %7s %lx", &a, &b, perm, &off) == 4 && ip >= a && ip < b) {
      n = snprintf(buf, sizeof buf, "in map: %s  -> file offset %lx\n", line, ip - a + off);
      write(2, buf, n);
    }
  }
  unsigned char *p = (unsigned char*)ip;
  n = snprintf(buf, sizeof buf, "bytes: %02x %02x %02x %02x %02x %02x %02x %02x\n", p[0],p[1],p[2],p[3],p[4],p[5],p[6],p[7]);
  write(2, buf, n);
  _exit(132);
}
__attribute__((constructor)) static void init(void) {
  struct sigaction sa = {0};
  sa.sa_sigaction = h; sa.sa_flags = SA_SIGINFO;
  sigaction(SIGILL, &sa, 0);
}
