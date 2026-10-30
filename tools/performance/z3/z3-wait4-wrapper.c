/* Linux stdio Z3 accounting wrapper. Prepared for review; not yet compiled. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static volatile sig_atomic_t child_fd = -1;
static void forward(int sig) {
    int saved = errno;
    if (child_fd >= 0) (void)syscall(SYS_pidfd_send_signal, (int)child_fd, sig, NULL, 0);
    errno = saved;
}
static void json_string(FILE *f, const char *s) {
    const unsigned char *p = (const unsigned char *)s;
    fputc('"', f);
    while (*p) {
        unsigned char c = *p++;
        if (c == '"' || c == '\\') { fputc('\\', f); fputc(c, f); }
        else if (c < 32 || c >= 127) fprintf(f, "\\u%04x", c);
        else fputc(c, f);
    }
    fputc('"', f);
}
static long long micros(struct timeval v) {
    return (long long)v.tv_sec * 1000000LL + v.tv_usec;
}
static long long nanos(struct timespec v) {
    return (long long)v.tv_sec * 1000000000LL + v.tv_nsec;
}
static int atomic_file_done(FILE *f, const char *temp, const char *dest) {
    int bad = ferror(f);
    if (fclose(f) != 0) bad = 1;
    if (bad || rename(temp, dest) != 0) return -1;
    return 0;
}

static int child_start_ticks(pid_t pid, unsigned long long *ticks) {
    char path[64], buf[4096], *tail, *save = NULL, *token;
    snprintf(path, sizeof(path), "/proc/%ld/stat", (long)pid);
    FILE *f = fopen(path, "r");
    if (!f) return -1;
    if (!fgets(buf, sizeof(buf), f)) { fclose(f); return -1; }
    fclose(f); tail = strrchr(buf, ')');
    if (!tail) return -1;
    token = strtok_r(tail + 1, " ", &save);
    for (int i = 0; i < 19 && token; i++) token = strtok_r(NULL, " ", &save);
    if (!token || sscanf(token, "%llu", ticks) != 1) return -1;
    return 0;
}

int main(int argc, char **argv) {
    const char *real = getenv("FERRUM_Z3_REAL");
    const char *out = getenv("FERRUM_Z3_RECORD_DIR");
    char dir[PATH_MAX], start_tmp[PATH_MAX], start_path[PATH_MAX];
    char end_tmp[PATH_MAX], end_path[PATH_MAX], identity_tmp[PATH_MAX], identity_path[PATH_MAX], cwd[PATH_MAX];
    int gate[2]; unsigned long long ticks = 0;
    struct timespec start, end;
    struct sigaction sa, def;
    sigset_t blocked, oldmask;
    pid_t pid, got;
    struct rusage usage;
    int status = 0, version = 0, error = 0, fd = -1;
    FILE *f;
    if (!real || real[0] != '/' || !out || out[0] != '/' || !getcwd(cwd, sizeof(cwd))) return 125;
    if (snprintf(dir, sizeof(dir), "%s/z3-XXXXXX", out) >= (int)sizeof(dir) || !mkdtemp(dir)) return 125;
    if (snprintf(start_tmp, sizeof(start_tmp), "%s/start.tmp", dir) >= (int)sizeof(start_tmp) ||
        snprintf(start_path, sizeof(start_path), "%s/start.json", dir) >= (int)sizeof(start_path) ||
        snprintf(end_tmp, sizeof(end_tmp), "%s/end.tmp", dir) >= (int)sizeof(end_tmp) ||
        snprintf(end_path, sizeof(end_path), "%s/end.json", dir) >= (int)sizeof(end_path) ||
        snprintf(identity_tmp, sizeof(identity_tmp), "%s/identity.tmp", dir) >= (int)sizeof(identity_tmp) ||
        snprintf(identity_path, sizeof(identity_path), "%s/identity.json", dir) >= (int)sizeof(identity_path)) return 125;
    for (int i = 1; i < argc; i++) if (!strcmp(argv[i], "--version") || !strcmp(argv[i], "-version")) version = 1;
    if (clock_gettime(CLOCK_MONOTONIC, &start) != 0 || !(f = fopen(start_tmp, "wx"))) return 125;
    fprintf(f, "{\"wrapper_pid\":%ld,\"parent_pid\":%ld,\"start_monotonic_ns\":%lld,\"kind\":\"%s\",\"executable\":", (long)getpid(), (long)getppid(), nanos(start), version ? "version_probe" : "solver");
    json_string(f, real); fputs(",\"cwd\":", f); json_string(f, cwd); fputs(",\"argv\":[", f);
    for (int i = 0; i < argc; i++) { if (i) fputc(',', f); json_string(f, i == 0 ? real : argv[i]); }
    fputs("]}\n", f);
    if (atomic_file_done(f, start_tmp, start_path) != 0) return 125;

    sigemptyset(&blocked); sigaddset(&blocked, SIGTERM); sigaddset(&blocked, SIGINT);
    if (sigprocmask(SIG_BLOCK, &blocked, &oldmask) != 0) return 125;
    memset(&sa, 0, sizeof(sa)); sa.sa_handler = forward; sigemptyset(&sa.sa_mask);
    if (sigaction(SIGTERM, &sa, NULL) != 0 || sigaction(SIGINT, &sa, NULL) != 0) return 125;
    if (pipe2(gate, O_CLOEXEC) != 0) return 125;
    pid_t original_parent = getpid();
    pid = fork();
    if (pid == 0) {
        memset(&def, 0, sizeof(def)); def.sa_handler = SIG_DFL; sigemptyset(&def.sa_mask);
        if (sigaction(SIGTERM, &def, NULL) != 0 || sigaction(SIGINT, &def, NULL) != 0) _exit(126);
        /* Immediate child dies even if its wrapper is killed before it can forward. */
        if (prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 || getppid() != original_parent) _exit(126);
        if (sigprocmask(SIG_SETMASK, &oldmask, NULL) != 0) _exit(126);
        close(gate[1]);
        char permit;
        ssize_t n;
        do { n = read(gate[0], &permit, 1); } while (n < 0 && errno == EINTR);
        close(gate[0]);
        if (n != 1 || permit != 'G') _exit(126);
        argv[0] = (char *)real;
        execv(real, argv);
        _exit(errno == ENOENT ? 127 : 126);
    }
    close(gate[0]);
    if (pid < 0) { error = errno; close(gate[1]); }
    else {
        fd = (int)syscall(SYS_pidfd_open, pid, 0);
        if (fd < 0) { error = errno; (void)kill(pid, SIGKILL); }
        else child_fd = fd;
        if (!error && child_start_ticks(pid, &ticks) != 0) error = errno ? errno : EIO;
        if (!error) {
            f = fopen(identity_tmp, "wx");
            if (!f) error = errno;
            else {
                fprintf(f, "{\"wrapper_pid\":%ld,\"child_pid\":%ld,\"child_start_ticks\":%llu}\n", (long)getpid(), (long)pid, ticks);
                if (atomic_file_done(f, identity_tmp, identity_path) != 0) error = errno ? errno : EIO;
            }
        }
        if (!error && write(gate[1], "G", 1) != 1) error = errno ? errno : EIO;
        close(gate[1]);
        if (error) (void)kill(pid, SIGKILL);
        if (sigprocmask(SIG_SETMASK, &oldmask, NULL) != 0) { error = errno; (void)kill(pid, SIGKILL); }
        do { got = wait4(pid, &status, 0, &usage); } while (got < 0 && errno == EINTR);
        if (got < 0) error = errno;
        if (sigprocmask(SIG_BLOCK, &blocked, NULL) != 0) error = errno;
        child_fd = -1;
        if (fd >= 0) close(fd);
        if (sigprocmask(SIG_SETMASK, &oldmask, NULL) != 0) error = errno;
    }
    if (clock_gettime(CLOCK_MONOTONIC, &end) != 0) return 125;
    if (!(f = fopen(end_tmp, "wx"))) return 125;
    fprintf(f, "{\"wrapper_pid\":%ld,\"child_pid\":%ld,\"end_monotonic_ns\":%lld,\"wrapper_error_errno\":%d", (long)getpid(), (long)pid, nanos(end), error);
    if (!error) {
        fprintf(f, ",\"raw_wait_status\":%d,\"user_us\":%lld,\"system_us\":%lld,\"max_rss_kib\":%ld", status, micros(usage.ru_utime), micros(usage.ru_stime), usage.ru_maxrss);
        if (WIFEXITED(status)) fprintf(f, ",\"exit_code\":%d", WEXITSTATUS(status));
        if (WIFSIGNALED(status)) fprintf(f, ",\"signal\":%d,\"core_dumped\":%s", WTERMSIG(status), WCOREDUMP(status) ? "true" : "false");
    }
    fputs("}\n", f);
    if (atomic_file_done(f, end_tmp, end_path) != 0 || error) return 125;
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    if (WIFSIGNALED(status)) {
        int sig = WTERMSIG(status);
        memset(&def, 0, sizeof(def)); def.sa_handler = SIG_DFL; sigemptyset(&def.sa_mask);
        /* SIGKILL has a fixed disposition and cannot be passed to sigaction. */
        if (sig != SIGKILL && sigaction(sig, &def, NULL) != 0) return 125;
        sigset_t unblocked; sigemptyset(&unblocked); sigaddset(&unblocked, sig);
        if (sigprocmask(SIG_UNBLOCK, &unblocked, NULL) != 0 || kill(getpid(), sig) != 0) return 125;
        return 128 + sig;
    }
    return 125;
}
