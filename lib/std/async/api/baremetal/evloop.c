/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Tim Whiting

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Board hooks for the bare-metal event loop. All weak: a board support
// package overrides them (e.g. `time_us_64`, `__wfe`, and polling its DMA
// and USB stacks on a Raspberry Pi Pico).

__attribute__((weak)) int64_t kk_bm_now_us(void) {
  return kk_baremetal_nsecs() / 1000;
}

__attribute__((weak)) bool kk_bm_board_poll(kk_context_t* ctx) {
  kk_unused(ctx);
  return false;
}

__attribute__((weak)) void kk_bm_board_idle(int64_t until_us) {
  kk_unused(until_us);  // default: busy-wait (the loop simply comes around again)
}
