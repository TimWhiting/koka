#include <llhttp.h>
#define kk_function_as_ptr(f,ctx) ((void*)kk_datatype_as_ptr(f, ctx))
#define kk_function_from_ptr(p,ctx) (kk_datatype_from_ptr(p, ctx))

typedef struct {
  void* on_message_begin;
  void* on_url;
  void* on_status;
  void* on_method;
  void* on_version;
  void* on_header_field;
  void* on_header_value;
  void* on_chunk_extension_name;
  void* on_chunk_extension_value;
  void* on_headers_complete;
  void* on_body;
  void* on_message_complete;
  void* on_url_complete;
  void* on_status_complete;
  void* on_method_complete;
  void* on_version_complete;
  void* on_header_field_complete;
  void* on_header_value_complete;
  void* on_chunk_extension_name_complete;
  void* on_chunk_extension_value_complete;
  void* on_chunk_header;
  void* on_chunk_complete;
  void* on_reset;
} kk_llhttp_callbacks_t;

kk_llhttp_dash_capi__llhttp kk_llhttp_parser_init(kk_llhttp_dash_capi__llhttp_settings settings, int32_t type, kk_context_t* _ctx) {
  llhttp_t* parser = kk_malloc(sizeof(llhttp_t), _ctx);
  llhttp_settings_t* lsettings = (llhttp_settings_t*)settings.internal;
  kk_llhttp_callbacks_t* cbs = kk_zalloc(sizeof(kk_llhttp_callbacks_t), _ctx);
  llhttp_init(parser, type, lsettings);
  parser->data = cbs;
  return kk_llhttp_dash_capi__new_Llhttp((intptr_t)parser, _ctx);
}

int32_t kk_llhttp_execute(kk_llhttp_dash_capi__llhttp parser, kk_string_t string, kk_context_t* _ctx) {
  kk_ssize_t len;
  const char* data = kk_string_cbuf_borrow(string, &len, _ctx);
  llhttp_errno_t status = llhttp_execute((llhttp_t*)parser.internal, data, len);
  kk_string_drop(string, _ctx);
  return status;
}

int32_t kk_llhttp_bytes_execute(kk_llhttp_dash_capi__llhttp parser, kk_bytes_t bytes, kk_context_t* _ctx) {
  kk_ssize_t len;
  const uint8_t* data = kk_bytes_buf_borrow(bytes, &len, _ctx);
  llhttp_errno_t status = llhttp_execute((llhttp_t*)parser.internal, data, len);
  kk_bytes_drop(bytes, _ctx);
  return status;
}

int32_t kk_llhttp_finish(kk_llhttp_dash_capi__llhttp parser, kk_context_t* _ctx) {
  llhttp_t* p = (llhttp_t*)parser.internal;
  int status = llhttp_finish(p);
  kk_free(p->data, _ctx);
  kk_free(p, _ctx);
  return status;
}

#define define_set_callback(name) \
  void kk_llhttp_parser_set_##name(kk_llhttp_dash_capi__llhttp parser, kk_function_t callback, kk_context_t* _ctx) { \
    llhttp_t* lparser = (llhttp_t*)parser.internal; \
    kk_llhttp_callbacks_t* cbs = (kk_llhttp_callbacks_t*)lparser->data; \
    cbs->name = kk_function_as_ptr(callback, _ctx); \
  }

define_set_callback(on_message_begin)
define_set_callback(on_url)
define_set_callback(on_status)
define_set_callback(on_method)
define_set_callback(on_version)
define_set_callback(on_header_field)
define_set_callback(on_header_value)
define_set_callback(on_chunk_extension_name)
define_set_callback(on_chunk_extension_value)
define_set_callback(on_headers_complete)
define_set_callback(on_body)
define_set_callback(on_message_complete)
define_set_callback(on_url_complete)
define_set_callback(on_status_complete)
define_set_callback(on_method_complete)
define_set_callback(on_version_complete)
define_set_callback(on_header_field_complete)
define_set_callback(on_header_value_complete)
define_set_callback(on_chunk_extension_name_complete)
define_set_callback(on_chunk_extension_value_complete)
define_set_callback(on_chunk_header)
define_set_callback(on_chunk_complete)
define_set_callback(on_reset)


#define define_unit_callback(name) \
  int kk_llhttp_##name(llhttp_t* llhttp) { \
    kk_context_t* _ctx = kk_get_context(); \
    kk_llhttp_callbacks_t* cbs = (kk_llhttp_callbacks_t*)llhttp->data; \
    if (cbs->name != NULL) { \
      kk_function_t callback = kk_function_from_ptr(cbs->name, _ctx); \
      kk_function_dup(callback, _ctx); \
      return kk_function_call(int32_t, (kk_function_t, kk_context_t*), callback, (callback, _ctx), _ctx); \
    } else { \
      return 0; \
    } \
  }

#define define_data_callback(name) \
  int kk_llhttp_##name(llhttp_t* llhttp, const char *at, size_t length) { \
    kk_context_t* _ctx = kk_get_context(); \
    kk_llhttp_callbacks_t* cbs = (kk_llhttp_callbacks_t*)llhttp->data; \
    if (cbs->name != NULL) { \
      kk_function_t callback = kk_function_from_ptr(cbs->name, _ctx); \
      kk_function_dup(callback, _ctx); \
      return kk_function_call(int32_t, (kk_function_t, kk_string_t, kk_context_t*), callback, (callback, kk_string_alloc_from_utf8n(length, at, _ctx), _ctx), _ctx); \
    } else { \
      return 0; \
    } \
  }

/* Possible return values 0, -1, `HPE_PAUSED` */
define_unit_callback(on_message_begin)
/* Possible return values 0, -1, HPE_USER */
define_data_callback(on_url)
define_data_callback(on_status)
define_data_callback(on_method)
define_data_callback(on_version)
define_data_callback(on_header_field)
define_data_callback(on_header_value)
define_data_callback(on_chunk_extension_name)
define_data_callback(on_chunk_extension_value)
/* Possible return values:
 * 0  - Proceed normally
 * 1  - Assume that request/response has no body, and proceed to parsing the
 *      next message
 * 2  - Assume absence of body (as above) and make `llhttp_execute()` return
 *      `HPE_PAUSED_UPGRADE`
 * -1 - Error
 * `HPE_PAUSED`
 */
define_unit_callback(on_headers_complete)
/* Possible return values 0, -1, HPE_USER */
define_data_callback(on_body)
/* Possible return values 0, -1, `HPE_PAUSED` */
define_unit_callback(on_message_complete)
define_unit_callback(on_url_complete)
define_unit_callback(on_status_complete)
define_unit_callback(on_method_complete)
define_unit_callback(on_version_complete)
define_unit_callback(on_header_field_complete)
define_unit_callback(on_header_value_complete)
define_unit_callback(on_chunk_extension_name_complete)
define_unit_callback(on_chunk_extension_value_complete)
/* When on_chunk_header is called, the current chunk length is stored
 * in parser->content_length.
 * Possible return values 0, -1, `HPE_PAUSED`
 */
define_unit_callback(on_chunk_header)
define_unit_callback(on_chunk_complete)
define_unit_callback(on_reset)


kk_llhttp_dash_capi__llhttp_settings kk_llhttp_settings_default(kk_context_t* _ctx) {
  llhttp_settings_t* settings = kk_malloc(sizeof(llhttp_settings_t), _ctx);
  llhttp_settings_init(settings);
  settings->on_message_begin = kk_llhttp_on_message_begin;
  settings->on_url = kk_llhttp_on_url;
  settings->on_status = kk_llhttp_on_status;
  settings->on_method = kk_llhttp_on_method;
  settings->on_version = kk_llhttp_on_version;
  settings->on_header_field = kk_llhttp_on_header_field;
  settings->on_header_value = kk_llhttp_on_header_value;
  settings->on_chunk_extension_name = kk_llhttp_on_chunk_extension_name;
  settings->on_chunk_extension_value = kk_llhttp_on_chunk_extension_value;
  settings->on_headers_complete = kk_llhttp_on_headers_complete;
  settings->on_body = kk_llhttp_on_body;
  settings->on_message_complete = kk_llhttp_on_message_complete;
  settings->on_url_complete = kk_llhttp_on_url_complete;
  settings->on_status_complete = kk_llhttp_on_status_complete;
  settings->on_method_complete = kk_llhttp_on_method_complete;
  settings->on_version_complete = kk_llhttp_on_version_complete;
  settings->on_header_field_complete = kk_llhttp_on_header_field_complete;
  settings->on_header_value_complete = kk_llhttp_on_header_value_complete;
  settings->on_chunk_extension_name_complete = kk_llhttp_on_chunk_extension_name_complete;
  settings->on_chunk_extension_value_complete = kk_llhttp_on_chunk_extension_value_complete;
  settings->on_chunk_header = kk_llhttp_on_chunk_header;
  settings->on_chunk_complete = kk_llhttp_on_chunk_complete;
  settings->on_reset = kk_llhttp_on_reset;
  return kk_llhttp_dash_capi__new_Llhttp_settings((intptr_t)settings, _ctx);
}

