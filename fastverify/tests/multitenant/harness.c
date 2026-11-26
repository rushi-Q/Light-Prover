/* tests/multitenant/harness.c -- C-level policy probe of the fork-server child sandbox (fork/shim.c fv_child_setup2:
   setsid + Landlock + seccomp), as an attacker with NATIVE code inside an elaborating child would use it. Linked
   with the package's own shim.c; run inside the
   fvserve fork-server sandbox (batchverify.sandbox(..., mask=[STATE]), FVFORK_READ). Prints one 'ROW name ok|BAD detail'
   line per check (from the children's logs, which the runner collects). Parent P, victim sibling V, attackers a1..a5. */
#define _GNU_SOURCE
#include <lean/lean.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/syscall.h>
extern void lean_initialize_runtime_module(void);
extern lean_obj_res fv_child_setup2(b_lean_obj_arg outdir, b_lean_obj_arg srcfile, lean_obj_arg w);
static volatile sig_atomic_t got_usr1 = 0, self_sig = 0;
static void h(int s) { (void)s; got_usr1 = 1; }
static void hs(int s) { (void)s; self_sig = 1; }
static char base[4096], src[4096];
static int setup(const char *name) {
  char d[4096]; snprintf(d, sizeof d, "%s/%s", base, name); mkdir(d, 0755);
  lean_object *r = fv_child_setup2(lean_mk_string(d), lean_mk_string(src), lean_box(0));
  return (int)lean_unbox_uint32(lean_io_result_get_value(r));
}
#define ROW(name, ok, ...) do { printf("ROW %s %s ", name, (ok) ? "ok" : "BAD"); printf(__VA_ARGS__); printf("\n"); fflush(stdout); } while (0)
static void *thr(void *x) { return x; }
int main(int argc, char **argv) {
  if (argc < 3) return 2;
  lean_initialize_runtime_module();
  snprintf(base, sizeof base, "%s", argv[1]); snprintf(src, sizeof src, "%s", argv[2]);
  signal(SIGUSR1, h);
  pid_t P = getpid();
  pid_t V = fork();
  if (V == 0) { int rc = setup("victim"); printf("victim setup rc=%d\n", rc); fflush(stdout); for (int i = 0; i < 100; i++) usleep(100000); _exit(0); }
  usleep(500000);
  pid_t a = fork();
  if (a == 0) {   /* a1: direct actions on others + sanity of the own process */
    int rc = setup("a1"); ROW("setup", rc == 0, "rc=%d", rc);
    errno = 0; int r = kill(P, SIGUSR1); ROW("kill-parent", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = kill(-1, 0); ROW("kill-all", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = kill(V, 0); ROW("kill-sibling", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = kill(-P, 0); ROW("kill-parent-group", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    signal(SIGUSR2, hs); errno = 0; r = kill(0, SIGUSR2); usleep(10000);
    ROW("kill-own-group-sane", r == 0 && self_sig, "=%d errno=%d delivered=%d", r, errno, (int)self_sig);
    pthread_t t; r = pthread_create(&t, NULL, thr, NULL); if (r == 0) pthread_join(t, NULL);
    ROW("threads-sane", r == 0, "pthread_create=%d", r);
    ROW("own-session", getsid(0) == getpid() && getpgid(0) == getpid(), "sid=%d pgid=%d pid=%d", getsid(0), getpgid(0), getpid());
    char p[256]; snprintf(p, sizeof p, "/proc/%d/environ", P);
    errno = 0; int fd = open(p, O_RDONLY); ROW("parent-environ", fd < 0, "=%d errno=%d", fd, errno);
    snprintf(p, sizeof p, "/proc/%d/stat", V);
    errno = 0; fd = open(p, O_RDONLY); ROW("sibling-proc-stat", fd < 0, "=%d errno=%d", fd, errno);
    errno = 0; DIR *d = opendir("/proc"); ROW("proc-not-listable", d == NULL, "opendir=%p errno=%d", (void *)d, errno);
    errno = 0; fd = open("/proc/self/status", O_RDONLY); ROW("own-proc-readable", fd >= 0, "=%d errno=%d", fd, errno);
    snprintf(p, sizeof p, "%s/victim/log", base);
    errno = 0; fd = open(p, O_RDONLY); ROW("sibling-log", fd < 0, "=%d errno=%d", fd, errno);
    _exit(0);
  }
  waitpid(a, NULL, 0);
  a = fork();
  if (a == 0) {   /* a2: join the parent's group / start a new session, then kill(0) */
    int rc = setup("a2"); (void)rc;
    errno = 0; int r = setpgid(0, getpgid(P)); ROW("setpgid-parent-group", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = setpgid(0, V); ROW("setpgid-sibling-group", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = setsid(); ROW("setsid", r < 0, "=%d errno=%d", r, errno);
    kill(0, SIGUSR1);   /* own group only: must not reach the parent */
    _exit(0);
  }
  waitpid(a, NULL, 0);
  usleep(200000);
  printf("ROW parent-not-signalled %s got_usr1=%d\n", got_usr1 ? "BAD" : "ok", (int)got_usr1); fflush(stdout);
  a = fork();
  if (a == 0) {   /* a3: stop the sibling through any group trick */
    int rc = setup("a3"); (void)rc;
    if (setpgid(0, V) == 0) kill(0, SIGSTOP);   /* (never stop itself: only once inside the victim's group) */
    kill(-V, SIGSTOP); _exit(0);
  }
  usleep(700000);
  int st = 0;
  pid_t w = waitpid(V, &st, WUNTRACED | WNOHANG);
  kill(a, SIGKILL); waitpid(a, NULL, 0);   /* (a3 may have stopped itself together with the victim's group) */
  printf("ROW sibling-not-stopped %s\n", (w == V && WIFSTOPPED(st)) ? "BAD" : "ok"); fflush(stdout);
  if (w == V && WIFSTOPPED(st)) kill(V, SIGCONT);
  a = fork();
  if (a == 0) {   /* a4: limits / scheduling / io priority of others */
    int rc = setup("a4"); (void)rc;
    struct rlimit rl = {0, 0};
    errno = 0; long r = syscall(SYS_prlimit64, V, RLIMIT_NOFILE, &rl, NULL); ROW("prlimit-sibling", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    errno = 0; r = syscall(SYS_prlimit64, P, RLIMIT_NPROC, &rl, NULL); ROW("prlimit-parent", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    struct rlimit cur; errno = 0; r = getrlimit(RLIMIT_NOFILE, &cur); ROW("getrlimit-own-sane", r == 0, "=%ld errno=%d", r, errno);
    cpu_set_t cs; CPU_ZERO(&cs); CPU_SET(0, &cs);
    errno = 0; r = sched_setaffinity(V, sizeof cs, &cs); ROW("affinity-sibling", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    errno = 0; r = setpriority(PRIO_PROCESS, V, 19); ROW("setpriority-sibling", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    errno = 0; r = setpriority(PRIO_USER, 0, 19); ROW("setpriority-user", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    int nice0 = getpriority(PRIO_PROCESS, 0); int nice1 = nice0 < 19 ? nice0 + 1 : 19;   /* raising one's own niceness */
    errno = 0; r = setpriority(PRIO_PROCESS, 0, nice1); ROW("setpriority-own-sane", r == 0, "=%ld errno=%d (nice %d -> %d)", r, errno, nice0, nice1);
    struct sched_param sp = {0};
    errno = 0; r = sched_setscheduler(V, SCHED_IDLE, &sp); ROW("setscheduler-sibling", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    errno = 0; r = sched_setparam(V, &sp); ROW("setparam-sibling", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    errno = 0; r = syscall(SYS_ioprio_set, 1 /* IOPRIO_WHO_PROCESS */, V, (3 << 13)); ROW("ioprio-sibling", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    errno = 0; r = syscall(SYS_tkill, V, 0); ROW("tkill", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    errno = 0; r = syscall(SYS_tgkill, V, V, 0); ROW("tgkill-sibling", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    _exit(0);
  }
  waitpid(a, NULL, 0);
  a = fork();
  if (a == 0) {   /* a5: process creation */
    int rc = setup("a5"); (void)rc;
    errno = 0; long r = syscall(SYS_fork); if (r == 0) _exit(0); ROW("fork", r < 0 && errno == EPERM, "=%ld errno=%d", r, errno);
    char *av[] = {"/bin/true", NULL}; errno = 0; r = execv("/bin/true", av); ROW("exec", r < 0, "=%ld errno=%d", r, errno);
    _exit(0);
  }
  waitpid(a, NULL, 0);
  a = fork();
  if (a == 0) {   /* a6: metadata changes / watches on another tenant's files or the shared dir */
    int rc = setup("a6"); (void)rc;
    char p[4096]; snprintf(p, sizeof p, "%s/victim/log", base);
    char vd[4096]; snprintf(vd, sizeof vd, "%s/victim", base);
    errno = 0; int r = chmod(p, 0); ROW("chmod-sibling-file", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = chmod(vd, 0); ROW("chmod-sibling-dir", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = chmod(base, 0); ROW("chmod-batch-dir", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = fchmodat(AT_FDCWD, vd, 0, 0); ROW("fchmodat-sibling-dir", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = fchmod(1, 0); ROW("fchmod-own-fd", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = chown(vd, getuid(), getgid()); ROW("chown-sibling-dir", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = utimensat(AT_FDCWD, vd, NULL, 0); ROW("utimensat-sibling-dir", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = (int)syscall(SYS_setxattr, vd, "user.x", "1", 1, 0); ROW("setxattr-sibling-dir", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = (int)syscall(SYS_inotify_init1, 0); ROW("inotify", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    errno = 0; r = (int)syscall(SYS_fanotify_init, 0, 0); ROW("fanotify", r < 0 && errno == EPERM, "=%d errno=%d", r, errno);
    /* every denied syscall by number, on the sibling's dir / its own log fd */
    int lfd = 1;
    struct { const char *name; long nr; long a0, a1, a2, a3, a4, a5; int newer; } sc[] = {
#if defined(__x86_64__)
      { "sc-chmod", 90, (long)vd, 0, 0, 0, 0, 0, 0 }, { "sc-chown", 92, (long)vd, (long)getuid(), (long)getgid(), 0, 0, 0, 0 },
      { "sc-lchown", 94, (long)vd, (long)getuid(), (long)getgid(), 0, 0, 0, 0 }, { "sc-utime", 132, (long)vd, 0, 0, 0, 0, 0, 0 },
      { "sc-utimes", 235, (long)vd, 0, 0, 0, 0, 0, 0 }, { "sc-futimesat", 261, AT_FDCWD, (long)vd, 0, 0, 0, 0, 0 },
      { "sc-inotify_init", 253, 0, 0, 0, 0, 0, 0, 0 },
#endif
      { "sc-fchmod", SYS_fchmod, lfd, 0, 0, 0, 0, 0, 0 }, { "sc-fchmodat", SYS_fchmodat, AT_FDCWD, (long)vd, 0, 0, 0, 0, 0 },
      { "sc-fchmodat2", 452, AT_FDCWD, (long)vd, 0, 0, 0, 0, 0 },
      { "sc-fchown", SYS_fchown, lfd, (long)getuid(), (long)getgid(), 0, 0, 0, 0 },
      { "sc-fchownat", SYS_fchownat, AT_FDCWD, (long)vd, (long)getuid(), (long)getgid(), 0, 0, 0 },
      { "sc-utimensat", SYS_utimensat, AT_FDCWD, (long)vd, 0, 0, 0, 0, 0 },
      { "sc-utimensat-fd", SYS_utimensat, lfd, 0, 0, 0, 0, 0, 0 },
      { "sc-setxattr", SYS_setxattr, (long)vd, (long)"user.x", (long)"1", 1, 0, 0, 0 },
      { "sc-lsetxattr", SYS_lsetxattr, (long)vd, (long)"user.x", (long)"1", 1, 0, 0, 0 },
      { "sc-fsetxattr", SYS_fsetxattr, lfd, (long)"user.x", (long)"1", 1, 0, 0, 0 },
      { "sc-removexattr", SYS_removexattr, (long)vd, (long)"user.x", 0, 0, 0, 0, 0 },
      { "sc-lremovexattr", SYS_lremovexattr, (long)vd, (long)"user.x", 0, 0, 0, 0, 0 },
      { "sc-fremovexattr", SYS_fremovexattr, lfd, (long)"user.x", 0, 0, 0, 0, 0 },
      { "sc-inotify_init1", SYS_inotify_init1, 0, 0, 0, 0, 0, 0, 0 },
      { "sc-inotify_add_watch", SYS_inotify_add_watch, 0, (long)vd, 0xfff, 0, 0, 0, 0 },
      { "sc-fanotify_init", SYS_fanotify_init, 0, 0, 0, 0, 0, 0, 0 },
      { "sc-fanotify_mark", SYS_fanotify_mark, 0, 1, 0x3b, AT_FDCWD, (long)vd, 0, 0 },
      /* newer kernels (6.13+ / 6.17+): ENOSYS from the filter (or the kernel) is fine, success is not */
      { "sc-setxattrat", 463, AT_FDCWD, (long)vd, 0, (long)"user.x", 0, 0, 1 },
      { "sc-removexattrat", 466, AT_FDCWD, (long)vd, 0, (long)"user.x", 0, 0, 1 },
      { "sc-file_setattr", 469, AT_FDCWD, (long)vd, 0, 0, 0, 0, 1 },
    };
    for (size_t i = 0; i < sizeof sc / sizeof sc[0]; i++) {
      errno = 0; long rr = syscall(sc[i].nr, sc[i].a0, sc[i].a1, sc[i].a2, sc[i].a3, sc[i].a4, sc[i].a5);
      int ok = rr < 0 && (errno == EPERM || (sc[i].newer && errno == ENOSYS));
      ROW(sc[i].name, ok, "=%ld errno=%d", rr, errno);
    }
    _exit(0);
  }
  waitpid(a, NULL, 0);
  {
    struct stat sv, sb;
    char vd[4096]; snprintf(vd, sizeof vd, "%s/victim", base);
    int ok = stat(vd, &sv) == 0 && stat(base, &sb) == 0 && (sv.st_mode & 0700) == 0700 && (sb.st_mode & 0700) == 0700;
    printf("ROW modes-unchanged %s victim=%o batch=%o\n", ok ? "ok" : "BAD", (unsigned)(sv.st_mode & 07777), (unsigned)(sb.st_mode & 07777));
    fflush(stdout);
  }
  char lim[256]; snprintf(lim, sizeof lim, "/proc/%d/limits", V);
  FILE *f = fopen(lim, "r"); char ln[512]; int nofile0 = 0;
  while (f && fgets(ln, sizeof ln, f)) if (strstr(ln, "open files") && strstr(ln, " 0 ")) nofile0 = 1;
  if (f) fclose(f);
  printf("ROW sibling-limits-unchanged %s\n", nofile0 ? "BAD" : "ok"); fflush(stdout);
  kill(V, SIGKILL); waitpid(V, NULL, 0);
  return 0;
}
