/*---------------------------------------------------------------------------
  Copyright 2020-2021, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

static kk_std_core_types__tuple2_ kk_timer_ticks_tuple(kk_context_t* ctx) {
  kk_duration_t d = kk_timer_ticks(ctx);
  // the conversion has about 15 digits of precision
  // we cannot do this more precisely as the api expects the fraction between 0.0 and 2.0 (for leap seconds).  
  double secs = (double)d.seconds;
  double frac = (double)d.attoseconds * 1e-18;
  return kk_std_core_types__new_dash__lp__comma__rp_( kk_double_box(secs,ctx), kk_double_box(frac,ctx), ctx );
}

static double kk_timer_dresolution(kk_context_t* ctx) {
  int64_t asecs = kk_timer_resolution(ctx);
  return (double)asecs * 1e-18;
}

typedef struct kk_timer_s {
  uv_timer_t timer_req;
  kk_std_time_duration__duration duration;
  kk_std_time_timer__timer timer;
  kk_function_t fun;
  kk_context_t* ctx;
  bool repeat;
} kk_timer_t;


static void kk_handle_timer(uv_timer_t* timer){
  kk_timer_t* t = timer->data;
  // TODO: Is this the right context? Evidence vector should be empty since this is top level callback?
  kk_context_t* ctx = t->ctx;
  // Returns false if the timer should be canceled
  kk_function_t f = kk_function_dup(t->fun, ctx);
  kk_std_time_timer__timer timer_dup = kk_std_time_timer__timer_dup(t->timer, ctx);
  bool res = kk_function_call(bool, (kk_function_t, kk_std_time_timer__timer, kk_context_t*), f, (f, timer_dup, ctx), ctx);

  if (t->repeat == false || res == false){
    kk_info_message("Timer stopping\n");
    int ret = uv_timer_stop(timer);
    if (ret != 0){
      kk_info_message("Timer stop ended with %s\n", uv_err_name(ret));
    }
    kk_function_drop(t->fun, ctx);
    kk_std_time_timer__timer_drop(t->timer, ctx);
    // kk_free(t, ctx); // Why does this not work. The timer should not be used any more?
  }
}

static kk_std_time_timer__timer kk_timer(kk_std_time_duration__duration timeout, kk_function_t fun, bool repeat_flag, kk_context_t* ctx){
  kk_timer_t* timer = kk_malloc(sizeof(kk_timer_t), ctx);

  kk_box_t b = { (uintptr_t)timer };
  kk_std_time_timer__timer result = kk_std_time_timer__new_Timer(b, ctx);

  kk_function_t f = kk_function_dup(fun, ctx);
  double secs = kk_std_num_ddouble_float64(timeout.secs, ctx);
  uint64_t ms = (uint64_t)(secs * 1000.0);
  kk_info_message("Timer scheduled for %d ms\n", ms);

  timer->repeat = repeat_flag;
  timer->duration = timeout;
  timer->timer_req.data = timer;
  timer->fun = f;
  timer->ctx = ctx;
  timer->timer = result;

  uv_timer_init(ctx->loop, &timer->timer_req);
  uv_timer_start(&timer->timer_req, &kk_handle_timer, ms, ms);

  return result;
}