#define kk_function_as_ptr(f,ctx) ((void*)kk_datatype_as_ptr(f, ctx))
#define kk_function_from_ptr(p,ctx) (kk_datatype_from_ptr(p, ctx))

#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#else
#include <uv.h>
#define uvloop() ((uv_loop_t*)(kk_context()->loop))
#define UV_OK 0

uv_buf_t* kk_bytes_list_to_uv_buffs(kk_std_core_types__list buffs, int* size, kk_context_t* _ctx);
uv_buf_t* kk_bytes_to_uv_buffs(kk_bytes_t bytes, kk_context_t* _ctx);

void kk_uv_unit_callback(uv_handle_t* hndl);
#endif