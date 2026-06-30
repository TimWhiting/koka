/*---------------------------------------------------------------------------
  Thin macOS/BSD syscall shims for the Koka-native kqueue reactor
  (std/async/api/kq/evloop). Just kqueue/kevent + a monotonic clock — the reactor
  logic itself lives in Koka. No libuv.
---------------------------------------------------------------------------*/
#include <sys/types.h>
#include <sys/event.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

// Create a kqueue; returns its fd (or a negative errno on failure).
int32_t kk_kq_create( kk_context_t* ctx ) {
  kk_unused(ctx);
  return (int32_t)kqueue();
}

// Block up to `millis` ms (>=0) waiting for any registered event on the kqueue.
// Returns the number of ready events (0 on timeout). With no fds registered this
// is simply a sleep for up to `millis`.
int32_t kk_kq_wait( int32_t kq, int64_t millis, kk_context_t* ctx ) {
  kk_unused(ctx);
  if (millis < 0) millis = 0;
  struct timespec ts;
  ts.tv_sec  = (time_t)(millis / 1000);
  ts.tv_nsec = (long)((millis % 1000) * 1000000L);
  struct kevent evs[16];
  int n = kevent((int)kq, NULL, 0, evs, 16, &ts);
  return (int32_t)(n < 0 ? 0 : n);
}

// Monotonic clock in milliseconds.
int64_t kk_now_ms( kk_context_t* ctx ) {
  kk_unused(ctx);
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000 + (int64_t)(ts.tv_nsec / 1000000);
}
