#include "std_os_event_dash_loop.h"

#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#include <emscripten/html5.h>

void one_iter() {
  // Can do a render loop to the screen here, etc. (this is the tick..)
  // puts("one iteration");
  return;
}
void kk_emscripten_loop_run(kk_context_t* _ctx){
  emscripten_set_main_loop(one_iter, 0, true);
}
#else

// UV allocator helpers, getting thread local context

static inline void* kk_malloc_ctx(size_t size) {
  return kk_malloc(size, kk_get_context());
}

static inline void* kk_realloc_ctx(void* p, size_t size) {
  return kk_realloc(p, size, kk_get_context());
}

static inline void* kk_calloc_ctx(size_t count, size_t size) {
  void* p = kk_malloc(count*size, kk_get_context());
  kk_memset(p, 0, count*size);
  return p;
}

static inline void kk_free_ctx(void* p) {
  kk_free(p, kk_get_context());
}

static inline void kk_uv_alloc_init(kk_context_t* _ctx){
  uv_replace_allocator(kk_malloc_ctx, kk_realloc_ctx, kk_calloc_ctx, kk_free_ctx);
}

static void kk_uv_loop_init(kk_context_t* _ctx) {
  uv_loop_t* loop = kk_malloc(sizeof(uv_loop_t), kk_get_context());
  uv_loop_init(loop);
  kk_context_t* ctx = loop->data = kk_get_context();
  ctx->loop = loop;
}

void kk_uv_loop_run(kk_context_t* _ctx){
  // Run the event loop after the initial startup of the program
  int ret = uv_run(uvloop(), UV_RUN_DEFAULT);
  if (ret != 0){
    kk_info_message("Event loop closed with status %s", uv_err_name(ret));
  }
}

static void kk_uv_loop_close(kk_context_t* _ctx) {
  uv_loop_close(uvloop());
  kk_free(uvloop(), _ctx);
}

static void kk_uv_handle_close_callback(uv_handle_t* handle){
  kk_context_t* _ctx = kk_get_context();
  kk_function_t callback = kk_function_from_ptr(handle->data, _ctx);
  kk_function_call(void, (kk_function_t, kk_context_t*), callback, (callback, _ctx), _ctx);  
  kk_free(handle, _ctx);
}

static void kk_uv_close(intptr_t handle, kk_function_t callback, kk_context_t* _ctx) {
  ((uv_handle_t*)handle)->data = kk_function_as_ptr(callback, _ctx);
  return uv_close((uv_handle_t*)handle, kk_uv_handle_close_callback);
}
#endif