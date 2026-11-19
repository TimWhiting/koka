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
   instructions (32-bit atomics compile to LDREX/STREX and need nothing here)
   and newlib ships no libatomic. Koka runs on a single core on these targets,
   so the only possible interference is an interrupt handler: on M-profile
   cores each operation runs with interrupts masked (PRIMASK), which makes it
   atomic with respect to everything on that core. Running Koka on two cores
   at once would need a hardware spinlock here instead. */
#if defined(__ARM_ARCH_PROFILE) && (__ARM_ARCH_PROFILE == 'M')
static inline uint32_t kk_bm_irq_save(void) {
  uint32_t primask;
  __asm volatile ("mrs %0, primask\n\tcpsid i" : "=r"(primask) :: "memory");
  return primask;
}
static inline void kk_bm_irq_restore(uint32_t primask) {
  __asm volatile ("msr primask, %0" :: "r"(primask) : "memory");
}
#else
static inline uint32_t kk_bm_irq_save(void) { return 0; }
static inline void kk_bm_irq_restore(uint32_t primask) { kk_unused(primask); }
#endif

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wbuiltin-declaration-mismatch"
__attribute__((weak)) uint64_t __atomic_load_8(const volatile void* p, int order) {
  kk_unused(order);
  uint32_t m = kk_bm_irq_save(); uint64_t v = *(const volatile uint64_t*)p; kk_bm_irq_restore(m);
  return v;
}
__attribute__((weak)) void __atomic_store_8(volatile void* p, uint64_t v, int order) {
  kk_unused(order);
  uint32_t m = kk_bm_irq_save(); *(volatile uint64_t*)p = v; kk_bm_irq_restore(m);
}
__attribute__((weak)) uint64_t __atomic_exchange_8(volatile void* p, uint64_t v, int order) {
  kk_unused(order);
  uint32_t m = kk_bm_irq_save(); uint64_t old = *(volatile uint64_t*)p; *(volatile uint64_t*)p = v; kk_bm_irq_restore(m);
  return old;
}
__attribute__((weak)) uint64_t __atomic_fetch_add_8(volatile void* p, uint64_t v, int order) {
  kk_unused(order);
  uint32_t m = kk_bm_irq_save(); uint64_t old = *(volatile uint64_t*)p; *(volatile uint64_t*)p = old + v; kk_bm_irq_restore(m);
  return old;
}
__attribute__((weak)) uint64_t __atomic_fetch_sub_8(volatile void* p, uint64_t v, int order) {
  kk_unused(order);
  uint32_t m = kk_bm_irq_save(); uint64_t old = *(volatile uint64_t*)p; *(volatile uint64_t*)p = old - v; kk_bm_irq_restore(m);
  return old;
}
__attribute__((weak)) bool __atomic_compare_exchange_8(volatile void* p, void* expected, uint64_t desired,
                                                         bool weak, int success, int failure) {
  kk_unused(weak); kk_unused(success); kk_unused(failure);
  uint32_t m = kk_bm_irq_save();
  uint64_t cur = *(volatile uint64_t*)p;
  bool ok = (cur == *(uint64_t*)expected);
  if (ok) { *(volatile uint64_t*)p = desired; } else { *(uint64_t*)expected = cur; }
  kk_bm_irq_restore(m);
  return ok;
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
