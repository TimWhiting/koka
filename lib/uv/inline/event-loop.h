#define kk_function_as_ptr(f,ctx) ((void*)kk_datatype_as_ptr(f, ctx))
#define kk_function_from_ptr(p,ctx) (kk_datatype_from_ptr(p, ctx))
static kk_box_t kk_set_timeout(kk_function_t cb, int64_t time, kk_context_t* _ctx) {
  kk_uv_timer__timer t = kk_uv_timer_timer_init(_ctx);
  kk_uv_timer_timer_start(t, time, 0, cb, _ctx);
  return kk_uv_timer__timer_box(t, _ctx);
}

static kk_unit_t kk_clear_timeout(kk_box_t boxed_timer, kk_context_t* _ctx) {
  kk_uv_timer__timer timer = kk_uv_timer__timer_unbox(boxed_timer, KK_OWNED, _ctx);
  kk_uv_timer_timer_stop(timer, _ctx);
  return kk_Unit;
}