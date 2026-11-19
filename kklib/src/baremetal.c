/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------
  Support for bare-metal targets (KK_BAREMETAL), e.g. arm-none-eabi + newlib.
  Everything here is weak, so a board support package can replace it.
---------------------------------------------------------------------------*/
#include <errno.h>
#include <stdio.h>
#include <sys/stat.h>
#include <time.h>

/* 64-bit atomics. Cores like the Cortex-M0+/M33 have no 64-bit atomic
   instructions and newlib ships no libatomic. Koka runs single-threaded on
   these targets and its heap is never touched from interrupt handlers, so
   plain loads and stores are sufficient. */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wbuiltin-declaration-mismatch"
__attribute__((weak)) uint64_t __atomic_load_8(const volatile void* p, int order) {
  kk_unused(order); return *(const volatile uint64_t*)p;
}
__attribute__((weak)) void __atomic_store_8(volatile void* p, uint64_t v, int order) {
  kk_unused(order); *(volatile uint64_t*)p = v;
}
__attribute__((weak)) uint64_t __atomic_exchange_8(volatile void* p, uint64_t v, int order) {
  kk_unused(order); uint64_t old = *(volatile uint64_t*)p; *(volatile uint64_t*)p = v; return old;
}
__attribute__((weak)) uint64_t __atomic_fetch_add_8(volatile void* p, uint64_t v, int order) {
  kk_unused(order); uint64_t old = *(volatile uint64_t*)p; *(volatile uint64_t*)p = old + v; return old;
}
__attribute__((weak)) uint64_t __atomic_fetch_sub_8(volatile void* p, uint64_t v, int order) {
  kk_unused(order); uint64_t old = *(volatile uint64_t*)p; *(volatile uint64_t*)p = old - v; return old;
}
__attribute__((weak)) bool __atomic_compare_exchange_8(volatile void* p, void* expected, uint64_t desired,
                                                         bool weak, int success, int failure) {
  kk_unused(weak); kk_unused(success); kk_unused(failure);
  uint64_t cur = *(volatile uint64_t*)p;
  if (cur == *(uint64_t*)expected) { *(volatile uint64_t*)p = desired; return true; }
  *(uint64_t*)expected = cur;
  return false;
}
#pragma GCC diagnostic pop

/* POSIX calls that newlib declares but does not implement. They fail with
   ENOSYS; a board with a file system can provide real ones. */
__attribute__((weak)) int mkdir(const char* path, mode_t mode) {
  kk_unused(path); kk_unused(mode); errno = ENOSYS; return -1;
}
__attribute__((weak)) int creat(const char* path, mode_t mode) {
  kk_unused(path); kk_unused(mode); errno = ENOSYS; return -1;
}
__attribute__((weak)) int futimens(int fd, const struct timespec times[2]) {
  kk_unused(fd); kk_unused(times); errno = ENOSYS; return -1;
}
__attribute__((weak)) FILE* popen(const char* cmd, const char* mode) {
  kk_unused(cmd); kk_unused(mode); errno = ENOSYS; return NULL;
}
__attribute__((weak)) int pclose(FILE* f) {
  kk_unused(f); errno = ENOSYS; return -1;
}
