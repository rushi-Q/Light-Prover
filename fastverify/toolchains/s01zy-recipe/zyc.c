/* zyc SOCK REAL_LEAN ARGS...  -- minimal zygote client (R15 protocol, see lean r/r15 src/util/shell.cpp):
   sends cwd + argv (argv[0] = REAL_LEAN) + our stdout/stderr (SCM_RIGHTS) to the zygote at SOCK, waits for the
   child's exit status and exits with it. If the zygote cannot be reached, or goes away before replying, it execs
   REAL_LEAN ARGS... directly (same result, no shared import). ~1 ms instead of a Python wrapper. */
#define _GNU_SOURCE
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

static void plain(char ** argv) { execv(argv[2], argv + 2); perror("zyc: exec"); _exit(127); }

int main(int argc, char ** argv) {
    if (argc < 3) { fprintf(stderr, "usage: zyc SOCK REAL_LEAN ARGS...\n"); return 2; }
    int s = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
    struct sockaddr_un a; memset(&a, 0, sizeof a); a.sun_family = AF_UNIX;
    if (s < 0 || strlen(argv[1]) >= sizeof a.sun_path) plain(argv);
    strcpy(a.sun_path, argv[1]);
    if (connect(s, (struct sockaddr *)&a, sizeof a) != 0) { close(s); plain(argv); }
    char cwd[8192]; if (!getcwd(cwd, sizeof cwd)) { close(s); plain(argv); }
    size_t len = strlen(cwd) + 1; for (int i = 2; i < argc; i++) len += strlen(argv[i]) + 1;
    char * buf = malloc(len), * p = buf;
    p = stpcpy(p, cwd) + 1; for (int i = 2; i < argc; i++) p = stpcpy(p, argv[i]) + 1;
    uint32_t l32 = (uint32_t)len;
    struct iovec iov = { &l32, sizeof l32 };
    char cb[CMSG_SPACE(2 * sizeof(int))]; memset(cb, 0, sizeof cb);
    struct msghdr m; memset(&m, 0, sizeof m);
    m.msg_iov = &iov; m.msg_iovlen = 1; m.msg_control = cb; m.msg_controllen = sizeof cb;
    struct cmsghdr * c = CMSG_FIRSTHDR(&m);
    c->cmsg_level = SOL_SOCKET; c->cmsg_type = SCM_RIGHTS; c->cmsg_len = CMSG_LEN(2 * sizeof(int));
    int fds[2] = {1, 2}; memcpy(CMSG_DATA(c), fds, sizeof fds);
    if (sendmsg(s, &m, MSG_NOSIGNAL) != (ssize_t)sizeof l32) { close(s); plain(argv); }
    for (size_t off = 0; off < len;) {
        ssize_t w = send(s, buf + off, len - off, MSG_NOSIGNAL);
        if (w < 0 && errno == EINTR) continue;
        if (w <= 0) { close(s); plain(argv); }
        off += (size_t)w;
    }
    int32_t code; size_t got = 0;
    while (got < sizeof code) {
        ssize_t r = read(s, (char *)&code + got, sizeof code - got);
        if (r < 0 && errno == EINTR) continue;
        if (r <= 0) break;
        got += (size_t)r;
    }
    if (got < sizeof code) {  /* zygote gone before replying: its child died with it (PDEATHSIG); redo plainly */
        fprintf(stderr, "zyc: zygote connection lost, running plain lean\n"); close(s); plain(argv);
    }
    if (code == 211) { close(s); plain(argv); }  /* R15 df7789f19b: zygote child saw an import-memo MISS -> plain lean */
    return (code >= 0 && code < 256) ? code : 1;
}
