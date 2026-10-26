#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
/* This host permits /proc/self/exe but not the equivalent numeric-PID path.
   Redirect only the current process's own executable lookup; all other
   readlink calls are passed unchanged to libc. No Lean kernel changes. */
ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
  char self[64];
  snprintf(self, sizeof(self), "/proc/%ld/exe", (long)getpid());
  if (strcmp(path, self) == 0) path = "/proc/self/exe";
  return real_readlink(path, buf, size);
}
