/* fvfork shim: fork / reap / _exit / thread count / child sandboxing (Landlock + seccomp) / unbuffered stdin lines. */
#define _GNU_SOURCE
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <unistd.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <stddef.h>
#include <linux/types.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <linux/audit.h>
#include <linux/sched.h>

#ifndef __NR_landlock_create_ruleset
#define __NR_landlock_create_ruleset 444
#define __NR_landlock_add_rule 445
#define __NR_landlock_restrict_self 446
#endif
struct fv_ll_ruleset_attr { __u64 handled_access_fs; };
struct fv_ll_path_beneath_attr { __u64 allowed_access; __s32 parent_fd; } __attribute__((packed));
#define FV_LL_CREATE_RULESET_VERSION (1U << 0)
#define FV_LL_RULE_PATH_BENEATH 1
#define FS_EXECUTE (1ULL << 0)
#define FS_WRITE_FILE (1ULL << 1)
#define FS_READ_FILE (1ULL << 2)
#define FS_READ_DIR (1ULL << 3)
#define FS_REMOVE_DIR (1ULL << 4)
#define FS_REMOVE_FILE (1ULL << 5)
#define FS_MAKE_CHAR (1ULL << 6)
#define FS_MAKE_DIR (1ULL << 7)
#define FS_MAKE_REG (1ULL << 8)
#define FS_MAKE_SOCK (1ULL << 9)
#define FS_MAKE_FIFO (1ULL << 10)
#define FS_MAKE_BLOCK (1ULL << 11)
#define FS_MAKE_SYM (1ULL << 12)
#define FS_REFER (1ULL << 13)
#define FS_TRUNCATE (1ULL << 14)

LEAN_EXPORT lean_obj_res fv_fork(lean_obj_arg w) {
  fflush(stdout); fflush(stderr);
  /* no PR_SET_DUMPABLE 0 here - fvserve watches each child through /proc/PID/fd (limits, timeout
     kill), which a non-dumpable process refuses. A child cannot ptrace / process_vm_* / read /proc/PID/{mem,environ} of
     the parent or a sibling anyway: Landlock confines ptrace to the child's own domain (the parent is outside every
     domain, siblings are in disjoint ones), whatever kernel.yama.ptrace_scope says, and the child's seccomp filter
     denies ptrace / process_vm_readv / process_vm_writev / kcmp / pidfd_getfd outright. */
  pid_t p = fork();
  if (p < 0) return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)p));
}

LEAN_EXPORT lean_obj_res fv_reap(lean_obj_arg w) {
  int st = 0;
  pid_t p = waitpid(-1, &st, WNOHANG);
  uint64_t r = 0;
  if (p > 0) {
    kill(-p, SIGKILL);   /* nothing of the child's process group outlives it (the child cannot create processes) */
    uint32_t code = WIFEXITED(st) ? (uint32_t)WEXITSTATUS(st) : (WIFSIGNALED(st) ? 128u + (uint32_t)WTERMSIG(st) : 255u);
    r = ((uint64_t)(uint32_t)p << 32) | code;
  }
  return lean_io_result_mk_ok(lean_box_uint64(r));
}

LEAN_EXPORT lean_obj_res fv_exit(uint32_t code, lean_obj_arg w) {
  fflush(stdout); fflush(stderr);
  _exit((int)code);
}

LEAN_EXPORT lean_obj_res fv_nthreads(lean_obj_arg w) {
  uint32_t n = 0;
  DIR *d = opendir("/proc/self/task");
  if (d) { struct dirent *e; while ((e = readdir(d))) if (e->d_name[0] != '.') n++; closedir(d); }
  return lean_io_result_mk_ok(lean_box_uint32(n));
}

/* seccomp filter of a forked child (installed after Landlock, NO_NEW_PRIVS set,
   after setsid(): the child is the only member of its own session and process group). A child may not
   - create processes: execve/execveat/fork/vfork denied, clone only with CLONE_THREAD, clone3 -> ENOSYS (glibc then uses
     clone for threads);
   - act on any process but itself: kill only to its own pid, 0 (its own group = itself) or -pid; tgkill /
     rt_sigqueueinfo / rt_tgsigqueueinfo only with its own tgid; prlimit64 and sched_setaffinity only on pid 0 or itself;
     setpriority only PRIO_PROCESS on 0 or itself; tkill, pidfd_*, ptrace, process_vm_*, process_madvise,
     process_mrelease, kcmp, move_pages, migrate_pages, perf_event_open, ioprio_set, sched_setscheduler, sched_setparam,
     sched_setattr denied; no F_SETOWN/F_SETSIG/F_SETOWN_EX/FIOSETOWN/SIOCSPGRP (no SIGIO-routed signals);
   - change its session / process group (setsid, setpgid denied: it cannot join the parent's or a sibling's group);
   - leave its namespaces (unshare, setns), or use io_uring;
   - change file metadata or watch files (chmod/fchmod/fchmodat/fchmodat2, chown family, utime/utimes/futimesat/
     utimensat, set/remove xattr families, inotify_*, fanotify_*).
   Everything else is allowed (the elaboration itself is unchanged). Arguments are compared on their low 32 bits, which is
   what the kernel takes from them (pid_t / int). */
#if defined(__x86_64__)
#define FV_AUDIT_ARCH AUDIT_ARCH_X86_64
#elif defined(__aarch64__)
#define FV_AUDIT_ARCH AUDIT_ARCH_AARCH64
#endif
#define FV_ARG0 (offsetof(struct seccomp_data, args[0]))
#define FV_ARG1 (offsetof(struct seccomp_data, args[1]))
#define FV_ALLOW BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW)
#define FV_RET_ERR(e) BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | ((e) & SECCOMP_RET_DATA))
#define FV_DENY_NR(nr) BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (nr), 0, 1), FV_RET_ERR(EPERM)
/* nr allowed only if arg0 == own pid */
#define FV_NR_ARG0_SELF(nr) BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (nr), 0, 4), \
  BPF_STMT(BPF_LD | BPF_W | BPF_ABS, FV_ARG0), BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (uint32_t)me, 0, 1), \
  FV_ALLOW, FV_RET_ERR(EPERM)
/* nr allowed only if arg0 == own pid or 0 (= the caller) */
#define FV_NR_ARG0_SELF_OR_0(nr) BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (nr), 0, 5), \
  BPF_STMT(BPF_LD | BPF_W | BPF_ABS, FV_ARG0), BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (uint32_t)me, 1, 0), \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 0, 1), FV_ALLOW, FV_RET_ERR(EPERM)
static int fv_seccomp(void) {
#ifndef FV_AUDIT_ARCH
  return -1;
#else
  pid_t me = getpid();
  struct sock_filter f[] = {
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, arch)),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, FV_AUDIT_ARCH, 1, 0),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
#if defined(__x86_64__)
    BPF_JUMP(BPF_JMP | BPF_JGE | BPF_K, 0x40000000u, 0, 1), FV_RET_ERR(EPERM),   /* x32 syscall numbers */
#endif
    /* setxattrat (463), removexattrat (466), file_setattr (469) and every later syscall number:
       unknown to this filter -> ENOSYS (as on an older kernel; glibc then falls back to the older calls), so that a kernel
       upgrade cannot add an unfiltered metadata call (x86_64 numbers 512-547 are x32-only and invalid here anyway) */
    BPF_JUMP(BPF_JMP | BPF_JGE | BPF_K, 463, 0, 1), FV_RET_ERR(ENOSYS),
    FV_DENY_NR(__NR_execve), FV_DENY_NR(__NR_execveat),
#ifdef __NR_fork
    FV_DENY_NR(__NR_fork),
#endif
#ifdef __NR_vfork
    FV_DENY_NR(__NR_vfork),
#endif
    FV_DENY_NR(__NR_ptrace), FV_DENY_NR(__NR_process_vm_readv), FV_DENY_NR(__NR_process_vm_writev),
    FV_DENY_NR(__NR_kcmp), FV_DENY_NR(__NR_tkill), FV_DENY_NR(__NR_unshare), FV_DENY_NR(__NR_setns),
    FV_DENY_NR(__NR_setpgid), FV_DENY_NR(__NR_setsid), FV_DENY_NR(__NR_ioprio_set),
    FV_DENY_NR(__NR_sched_setscheduler), FV_DENY_NR(__NR_sched_setparam), FV_DENY_NR(__NR_sched_setattr),
    FV_DENY_NR(__NR_move_pages), FV_DENY_NR(__NR_migrate_pages), FV_DENY_NR(__NR_perf_event_open),
    FV_DENY_NR(424 /* pidfd_send_signal */), FV_DENY_NR(434 /* pidfd_open */), FV_DENY_NR(438 /* pidfd_getfd */),
    FV_DENY_NR(440 /* process_madvise */), FV_DENY_NR(448 /* process_mrelease */),
    FV_DENY_NR(425 /* io_uring_setup */), FV_DENY_NR(426 /* io_uring_enter */), FV_DENY_NR(427 /* io_uring_register */),
    /* Landlock does not cover metadata changes or watches - no chmod / chown / utime / xattr changes,
       no inotify / fanotify (a child could otherwise chmod 000 a shared or another tenant's directory, or watch names) */
    FV_DENY_NR(__NR_fchmod), FV_DENY_NR(__NR_fchmodat), FV_DENY_NR(452 /* fchmodat2 */),
    FV_DENY_NR(__NR_fchown), FV_DENY_NR(__NR_fchownat), FV_DENY_NR(__NR_utimensat),
    FV_DENY_NR(__NR_setxattr), FV_DENY_NR(__NR_lsetxattr), FV_DENY_NR(__NR_fsetxattr),
    FV_DENY_NR(__NR_removexattr), FV_DENY_NR(__NR_lremovexattr), FV_DENY_NR(__NR_fremovexattr),
    FV_DENY_NR(__NR_inotify_init1), FV_DENY_NR(__NR_inotify_add_watch), FV_DENY_NR(__NR_fanotify_init),
    FV_DENY_NR(__NR_fanotify_mark),
    /* no SysV / POSIX message-queue IPC (state that outlives the child in the shared
       IPC namespace of the fork server: a channel between sequential tenants) */
    FV_DENY_NR(__NR_shmget), FV_DENY_NR(__NR_shmat), FV_DENY_NR(__NR_shmctl), FV_DENY_NR(__NR_msgget),
    FV_DENY_NR(__NR_msgsnd), FV_DENY_NR(__NR_msgrcv), FV_DENY_NR(__NR_msgctl), FV_DENY_NR(__NR_semget),
    FV_DENY_NR(__NR_semop), FV_DENY_NR(__NR_semtimedop), FV_DENY_NR(__NR_semctl), FV_DENY_NR(__NR_mq_open),
    FV_DENY_NR(__NR_mq_unlink), FV_DENY_NR(__NR_mq_timedsend), FV_DENY_NR(__NR_mq_timedreceive),
    FV_DENY_NR(__NR_mq_notify), FV_DENY_NR(__NR_mq_getsetattr),
#ifdef __NR_chmod
    FV_DENY_NR(__NR_chmod),
#endif
#ifdef __NR_chown
    FV_DENY_NR(__NR_chown),
#endif
#ifdef __NR_lchown
    FV_DENY_NR(__NR_lchown),
#endif
#ifdef __NR_utime
    FV_DENY_NR(__NR_utime),
#endif
#ifdef __NR_utimes
    FV_DENY_NR(__NR_utimes),
#endif
#ifdef __NR_futimesat
    FV_DENY_NR(__NR_futimesat),
#endif
#ifdef __NR_inotify_init
    FV_DENY_NR(__NR_inotify_init),
#endif
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 435 /* clone3 */, 0, 1), FV_RET_ERR(ENOSYS),
    /* clone: threads only */
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_clone, 0, 4),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, FV_ARG0),
    BPF_JUMP(BPF_JMP | BPF_JSET | BPF_K, CLONE_THREAD, 0, 1),
    FV_ALLOW, FV_RET_ERR(EPERM),
    /* kill: own pid, 0 (own process group = this child alone after setsid) or -own pid */
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_kill, 0, 6),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, FV_ARG0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (uint32_t)me, 2, 0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, 0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (uint32_t)(-me), 0, 1),
    FV_ALLOW, FV_RET_ERR(EPERM),
    FV_NR_ARG0_SELF(__NR_tgkill), FV_NR_ARG0_SELF(__NR_rt_sigqueueinfo), FV_NR_ARG0_SELF(__NR_rt_tgsigqueueinfo),
    FV_NR_ARG0_SELF_OR_0(__NR_prlimit64), FV_NR_ARG0_SELF_OR_0(__NR_sched_setaffinity),
    /* setpriority(which, who, prio): only PRIO_PROCESS (0) on 0 or itself */
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_setpriority, 0, 7),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, FV_ARG0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 0, 4),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, FV_ARG1),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (uint32_t)me, 1, 0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 0, 1),
    FV_ALLOW, FV_RET_ERR(EPERM),
    /* fcntl: no F_SETOWN (8) / F_SETSIG (10) / F_SETOWN_EX (15) */
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_fcntl, 0, 6),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, FV_ARG1),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 8, 3, 0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 10, 2, 0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 15, 1, 0),
    FV_ALLOW, FV_RET_ERR(EPERM),
    /* ioctl: no FIOSETOWN (0x8901) / SIOCSPGRP (0x8902) */
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_ioctl, 0, 5),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, FV_ARG1),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0x8901, 2, 0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0x8902, 1, 0),
    FV_ALLOW, FV_RET_ERR(EPERM),
    FV_ALLOW,
  };
  struct sock_fprog prog = { (unsigned short)(sizeof f / sizeof f[0]), f };
  return prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog, 0, 0);
#endif
}

/* request line buffer of fv_next_line (the parent's stdin); wiped in every forked child (fv_child_setup2) */
static char g_buf[1 << 20];
static size_t g_len = 0;
static int g_eof = 0;

static int fv_ll_allow(int rs, const char *path, __u64 access) {
  struct fv_ll_path_beneath_attr pb;
  pb.allowed_access = access;
  pb.parent_fd = open(path, O_PATH | O_CLOEXEC);
  if (pb.parent_fd < 0) return -1;
  int r = (int)syscall(__NR_landlock_add_rule, rs, FV_LL_RULE_PATH_BENEATH, &pb, 0);
  close(pb.parent_fd);
  return r;
}

/* child: own session, stdout+stderr -> OUTDIR/log, stdin -> /dev/null, then Landlock: writes only
   beneath OUTDIR (and to /dev/null); READS only beneath OUTDIR, of its own source file SRC, the read-only roots in
   $FVFORK_READ (toolchain, packages, snapshot dir, binary dir: set by fvserve) and the system dirs; EXECUTE nowhere; then
   the seccomp filter above. Every failure -> a nonzero code (the child exits 97, fvserve falls back to the official lean). */
LEAN_EXPORT lean_obj_res fv_child_setup2(b_lean_obj_arg outdir, b_lean_obj_arg srcfile, lean_obj_arg w) {
  const char *dir = lean_string_cstr(outdir);
  const char *src = lean_string_cstr(srcfile);
  char path[4096];
  /* r2 (review M1): a session of its own (new session + process group = this child only; setsid/setpgid are then
     denied by the filter, so it can never join the parent's or a sibling's group); the copy of the parent's request buffer
     (earlier requests' ids / paths) is wiped */
  if (setsid() < 0) return lean_io_result_mk_ok(lean_box_uint32(10));
  memset(g_buf, 0, sizeof g_buf); g_len = 0;
  snprintf(path, sizeof path, "%s/log", dir);
  int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0644);
  if (fd < 0) return lean_io_result_mk_ok(lean_box_uint32(1));
  dup2(fd, 1); dup2(fd, 2); close(fd);
  int nul = open("/dev/null", O_RDONLY);
  if (nul < 0 || dup2(nul, 0) < 0) return lean_io_result_mk_ok(lean_box_uint32(15));   /* stdin must not stay the parent's */
  close(nul);
  setvbuf(stdout, NULL, _IOLBF, 0);
  long abi = syscall(__NR_landlock_create_ruleset, NULL, 0, FV_LL_CREATE_RULESET_VERSION);
  if (abi < 1) { fprintf(stderr, "fvfork: landlock unavailable (%ld)\n", abi); return lean_io_result_mk_ok(lean_box_uint32(2)); }
  __u64 handled = FS_EXECUTE | FS_READ_FILE | FS_READ_DIR | FS_WRITE_FILE | FS_REMOVE_DIR | FS_REMOVE_FILE | FS_MAKE_CHAR |
                  FS_MAKE_DIR | FS_MAKE_REG | FS_MAKE_SOCK | FS_MAKE_FIFO | FS_MAKE_BLOCK | FS_MAKE_SYM;
  if (abi >= 2) handled |= FS_REFER;
  if (abi >= 3) handled |= FS_TRUNCATE;
  struct fv_ll_ruleset_attr attr = { handled };
  int rs = (int)syscall(__NR_landlock_create_ruleset, &attr, sizeof attr, 0);
  if (rs < 0) return lean_io_result_mk_ok(lean_box_uint32(3));
  const __u64 RD = FS_READ_FILE | FS_READ_DIR;
  if (fv_ll_allow(rs, dir, handled & ~FS_EXECUTE) != 0) return lean_io_result_mk_ok(lean_box_uint32(4));
  if (fv_ll_allow(rs, src, FS_READ_FILE) != 0) return lean_io_result_mk_ok(lean_box_uint32(11));
  fv_ll_allow(rs, "/dev/null", FS_READ_FILE | FS_WRITE_FILE | (abi >= 3 ? FS_TRUNCATE : 0));
  /* no rule on /dev itself - a Landlock rule covers the whole subtree, across mounts, so it
     would also cover a state dir in /dev/shm; only the device nodes below are readable */
  static const char *sysdirs[] = { "/usr", "/lib", "/lib32", "/lib64", "/libx32", "/bin", "/sbin", "/etc", "/sys",
                                   "/proc/sys", NULL };
  for (int i = 0; sysdirs[i]; i++) fv_ll_allow(rs, sysdirs[i], RD);   /* absent ones are skipped */
  /* r2 (review M1/L5): of /proc only the child's OWN pid directory (/proc/self resolves to it) and a few global files:
     the parent's and the siblings' pids can neither be listed nor inspected */
  if (fv_ll_allow(rs, "/proc/self", RD) != 0) return lean_io_result_mk_ok(lean_box_uint32(14));
  static const char *procfiles[] = { "/proc/cpuinfo", "/proc/meminfo", "/proc/stat", "/proc/filesystems", "/proc/loadavg",
                                     "/proc/version", "/proc/uptime", "/dev/zero", "/dev/urandom", "/dev/random", "/dev/full",
                                     NULL };
  for (int i = 0; procfiles[i]; i++) fv_ll_allow(rs, procfiles[i], FS_READ_FILE);
  const char *ro = getenv("FVFORK_READ");
  if (!ro || !*ro) return lean_io_result_mk_ok(lean_box_uint32(12));
  char roots[8192];
  snprintf(roots, sizeof roots, "%s", ro);
  for (char *save = NULL, *t = strtok_r(roots, ":", &save); t; t = strtok_r(NULL, ":", &save))
    if (fv_ll_allow(rs, t, RD) != 0) return lean_io_result_mk_ok(lean_box_uint32(13));
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) return lean_io_result_mk_ok(lean_box_uint32(5));
  if (syscall(__NR_landlock_restrict_self, rs, 0) != 0) return lean_io_result_mk_ok(lean_box_uint32(6));
  close(rs);
  if (fv_seccomp() != 0) return lean_io_result_mk_ok(lean_box_uint32(7));
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

/* unbuffered line reader on fd 0: "" = no complete line within ms, "\x04" = EOF (buffer: see the top of the file) */
LEAN_EXPORT lean_obj_res fv_next_line(uint32_t ms, lean_obj_arg w) {
  for (int round = 0; round < 2; round++) {
    char *nl = memchr(g_buf, '\n', g_len);
    if (nl) {
      size_t n = (size_t)(nl - g_buf);
      lean_object *s = lean_mk_string_from_bytes(g_buf, n);
      memmove(g_buf, nl + 1, g_len - n - 1);
      memset(g_buf + g_len - n - 1, 0, n + 1);   /* r2 (review L5): no stale request bytes stay behind */
      g_len -= n + 1;
      return lean_io_result_mk_ok(s);
    }
    if (g_eof) return lean_io_result_mk_ok(lean_mk_string("\x04"));
    if (round == 1) break;
    struct pollfd p = { 0, POLLIN, 0 };
    int r = poll(&p, 1, (int)ms);
    if (r <= 0) break;
    ssize_t k = read(0, g_buf + g_len, sizeof g_buf - g_len);
    if (k <= 0) { g_eof = 1; continue; }
    g_len += (size_t)k;
  }
  return lean_io_result_mk_ok(lean_mk_string(""));
}

/* the lossy UTF-8 decode of the attempt file, as the release's own `lean` frontend does it. Up to 4.36 the runtime
   exports lean_decode_lossy_utf8 (Lean.Shell; used exactly as before); 4.37.0-rc1 removed it and its frontend uses
   String.fromUTF8Lossy (owned argument). Weak references: whichever this toolchain's libleanshared has is called. */
extern lean_obj_res lean_decode_lossy_utf8(b_lean_obj_arg a) __attribute__((weak));
extern lean_obj_res l_String_fromUTF8Lossy(lean_obj_arg a) __attribute__((weak));
LEAN_EXPORT lean_obj_res fv_decode_lossy_utf8(b_lean_obj_arg a) {
    if (lean_decode_lossy_utf8) return lean_decode_lossy_utf8(a);
    if (l_String_fromUTF8Lossy) { lean_inc(a); return l_String_fromUTF8Lossy(a); }
    return lean_mk_string_from_bytes((char const *)lean_sarray_cptr(a), lean_sarray_size(a));
}
