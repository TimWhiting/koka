#if defined(__wasi__)
#include <kklib.h>

kk_box_t getObjectField(kk_lib_web_wasm__jsObject obj, kk_string_t prop, kk_context_t* ctx){
  kk_ssize_t len;
  const uint8_t* s = kk_string_buf_borrow(prop, &len, ctx);
  Handle h = kk_js_get_prop(obj.h, s, ctx);
  return kk_lib_web_wasm__jsObject_box(kk_lib_web_wasm__new_JsObject(h, ctx), ctx);
}

kk_box_t getStaticField(kk_string_t prop, kk_context_t* ctx){
  kk_ssize_t len;
  const uint8_t* s = kk_string_buf_borrow(prop, &len, ctx);
  Handle obj = jsGlobalThis;
  Handle h = kk_js_get_prop(obj, s, ctx);
  return kk_lib_web_wasm__jsObject_box(kk_lib_web_wasm__new_JsObject(h, ctx), ctx);
}

void setObjectField(kk_lib_web_wasm__jsObject obj, kk_string_t prop, kk_box_t value, kk_context_t* ctx){
  kk_ssize_t len;
  const uint8_t* s = kk_string_buf_borrow(prop, &len, ctx);
  kk_js_set_prop(obj.h, s, kk_lib_web_wasm__jsObject_unbox(value, KK_BORROWED, ctx).h, ctx);
  return;
}

void setStaticField(kk_string_t prop, kk_box_t value, kk_context_t* ctx){
  kk_ssize_t len;
  const uint8_t* s = kk_string_buf_borrow(prop, &len, ctx);
  Handle obj = jsGlobalThis;
  kk_js_set_prop(obj, s, kk_lib_web_wasm__jsObject_unbox(value, KK_BORROWED, ctx).h, ctx);
  return;
}

#endif

