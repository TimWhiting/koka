#ifndef __EMSCRIPTEN__
void kk_uv_unit_callback(uv_handle_t* hndl) {
  kk_context_t* _ctx = kk_get_context();
  kk_function_t cb = kk_function_from_ptr(hndl->data, _ctx);
  kk_function_call(void, (kk_function_t, kk_context_t*),cb, (cb, _ctx), _ctx);
}

uv_buf_t* kk_bytes_list_to_uv_buffs(kk_std_core_types__list buffs, int* size, kk_context_t* _ctx){
  kk_std_core_types__list_dup(buffs, _ctx);
  kk_integer_t klist_len = kk_std_core_list_length(buffs, _ctx);
  int list_len = kk_integer_clamp32(klist_len, _ctx);
  uv_buf_t* uv_buffs = kk_malloc(sizeof(uv_buf_t) * list_len, _ctx);
  kk_std_core_types__list list = buffs;
  for (int i = 0; i < list_len; i++){
    struct kk_std_core_types_Cons* cons = kk_std_core_types__as_Cons(list, _ctx);
    kk_bytes_t bytes = kk_bytes_unbox(cons->head);
    kk_ssize_t len;
    const char* chars = kk_bytes_cbuf_borrow(bytes, &len, _ctx);
    uv_buffs[i].base = kk_malloc(len, _ctx);
    kk_memcpy(uv_buffs[i].base, chars, len);
    uv_buffs[i].len = len;
    list = cons->tail;
  }
  *size = list_len;
  return uv_buffs;
}

uv_buf_t* kk_bytes_to_uv_buffs(kk_bytes_t bytes, kk_context_t* _ctx){
  uv_buf_t* uv_buffs = kk_malloc(sizeof(uv_buf_t) * 1, _ctx);
  kk_ssize_t len;
  const char* chars = kk_bytes_cbuf_borrow(bytes, &len, _ctx);
  uv_buffs[0].base = kk_malloc(sizeof(char)*len, _ctx);
  kk_memcpy(uv_buffs[0].base, chars, len);
  uv_buffs[0].len = len;
  kk_bytes_drop(bytes, _ctx);
  return uv_buffs;
}
#endif