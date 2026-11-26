/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// #include <kklib.h>
// #include "evloop.h"

#include <uv.h>
#include <string.h>
#include <arpa/inet.h>

// free the handle once libuv has finished closing it
static void kk_uv_udp_free_cb(uv_handle_t* h) {
  kk_free(h, kk_get_context());
}

// build a sockaddr from host+port, trying IPv4 then IPv6
static int kk_uv_make_addr(const char* host, int port, struct sockaddr_storage* out) {
  memset(out, 0, sizeof(*out));
  if (uv_ip4_addr(host, port, (struct sockaddr_in*)out) == 0) return 0;
  return uv_ip6_addr(host, port, (struct sockaddr_in6*)out);
}

// Synchronous: create + bind a UDP socket; return Ok(opaque handle) or Error.
kk_std_core_exn__error kk_uv_udp_bind_sync(kk_uv_loop_t loop, kk_string_t host, int32_t port, kk_context_t* ctx) {
  uv_udp_t* h = (uv_udp_t*)kk_zalloc(sizeof(uv_udp_t), ctx);
  int err = uv_udp_init(kk_uv_loop(loop, ctx), h);
  if (err == 0) {
    struct sockaddr_storage addr;
    int aerr = UV_EINVAL;
    kk_with_string_as_qutf8_borrow(host, chost, ctx) {
      aerr = kk_uv_make_addr(chost, (int)port, &addr);
    }
    err = aerr;
    if (err == 0) {
      err = uv_udp_bind(h, (const struct sockaddr*)&addr, 0);
    }
  }
  kk_string_drop(host, ctx);
  if (err != 0) {
    uv_close((uv_handle_t*)h, kk_uv_udp_free_cb);
    return kk_error_from_uv_errno(err, ctx);
  }
  h->data = NULL;
  return kk_result_ok(kk_cptr_box((void*)h, ctx), ctx);
}

// Close and free a socket.
kk_unit_t kk_uv_udp_close(kk_box_t sock, kk_context_t* ctx) {
  uv_udp_t* h = (uv_udp_t*)kk_cptr_unbox_borrowed(sock, ctx);
  if (h != NULL) {
    uv_udp_recv_stop(h);
    if (h->data != NULL) {
      kk_function_drop(kk_datatype_from_ptr((kk_ptr_t)(h->data), ctx), ctx);
      h->data = NULL;
    }
    uv_close((uv_handle_t*)h, kk_uv_udp_free_cb);
  }
  kk_box_drop(sock, ctx);
  return kk_Unit;
}

// ----------------------------------------------------------------- send

typedef struct kk_udp_send_s {
  uv_udp_send_t req;     // first member: (uv_req_t*) casts must work
  kk_bytes_t    payload; // keep the payload alive until the send completes
  int           status;
} kk_udp_send_t;

static void kk_udp_send_result(kk_function_t cb, uv_req_t* _req, kk_context_t* ctx) {
  kk_udp_send_t* w = (kk_udp_send_t*)_req;
  kk_bytes_drop(w->payload, ctx);
  kk_std_core_exn__error res = (w->status < 0)
      ? kk_error_from_uv_errno(w->status, ctx)
      : kk_result_ok(kk_unit_box(kk_Unit), ctx);
  kk_function_call_error(cb, res, ctx);
}

static void kk_udp_send_cb(uv_udp_send_t* req, int status) {
  ((kk_udp_send_t*)req)->status = status;
  kk_uv_req_callback((uv_req_t*)req, &kk_udp_send_result);
}

kk_std_core_exn__error kk_uv_udp_send(kk_box_t sock, kk_string_t host, int32_t port, kk_bytes_t payload, kk_function_t cb, kk_context_t* ctx) {
  uv_udp_t* h = (uv_udp_t*)kk_cptr_unbox_borrowed(sock, ctx);
  kk_box_drop(sock, ctx);
  struct sockaddr_storage addr;
  int err = UV_EINVAL;
  kk_with_string_as_qutf8_borrow(host, chost, ctx) {
    err = kk_uv_make_addr(chost, (int)port, &addr);
  }
  kk_string_drop(host, ctx);
  if (h == NULL) err = UV_EINVAL;
  if (err != 0) { kk_bytes_drop(payload, ctx); kk_function_drop(cb, ctx); return kk_error_from_uv_errno(err, ctx); }
  kk_udp_send_t* w;
  err = kk_uv_req_create(sizeof(kk_udp_send_t), cb, (uv_req_t**)&w, ctx);
  if (err != 0) { kk_bytes_drop(payload, ctx); return kk_error_from_uv_errno(err, ctx); }
  w->payload = payload;
  w->status = 0;
  kk_ssize_t len = 0;
  const uint8_t* base = kk_bytes_buf_borrow(payload, &len, ctx);
  uv_buf_t bufs[1];
  bufs[0] = uv_buf_init((char*)base, (unsigned int)len);
  err = uv_udp_send((uv_udp_send_t*)w, h, bufs, 1, (const struct sockaddr*)&addr, &kk_udp_send_cb);
  if (err != 0) { kk_bytes_drop(payload, ctx); kk_uv_req_free((uv_req_t*)w, ctx); return kk_error_from_uv_errno(err, ctx); }
  return kk_result_uv_req_dispose0((uv_req_t*)w, ctx);
}

// ----------------------------------------------------------------- recv

static void kk_udp_alloc_cb(uv_handle_t* handle, size_t suggested, uv_buf_t* buf) {
  kk_context_t* ctx = kk_get_context();
  size_t n = (suggested > 0 ? suggested : 65536);
  char* base = (char*)kk_malloc((kk_ssize_t)n, ctx);
  *buf = uv_buf_init(base, (unsigned int)n);
}

// Build the (sender-ip, sender-port, payload) result for a received datagram.
static kk_std_core_exn__error kk_udp_datagram_result(ssize_t nread, const uv_buf_t* buf, const struct sockaddr* addr, kk_context_t* ctx) {
  if (nread < 0) return kk_error_from_uv_errno((int)nread, ctx);
  char ipbuf[64]; ipbuf[0] = 0; int port = 0;
  if (addr->sa_family == AF_INET6) {
    const struct sockaddr_in6* a6 = (const struct sockaddr_in6*)addr;
    uv_ip6_name(a6, ipbuf, sizeof(ipbuf)); port = (int)ntohs(a6->sin6_port);
  } else {
    const struct sockaddr_in* a4 = (const struct sockaddr_in*)addr;
    uv_ip4_name(a4, ipbuf, sizeof(ipbuf)); port = (int)ntohs(a4->sin_port);
  }
  kk_string_t ip   = kk_string_alloc_from_qutf8(ipbuf, ctx);
  kk_bytes_t  data = kk_bytes_alloc_dupn((kk_ssize_t)nread, (const uint8_t*)buf->base, ctx);
  kk_std_core_types__tuple3 tup = kk_std_core_types__new_Tuple3(
      kk_string_box(ip),
      kk_integer_box(kk_integer_from_int(port, ctx), ctx),
      kk_bytes_box(data), ctx);
  return kk_result_ok(kk_std_core_types__tuple3_box(tup, ctx), ctx);
}

// one-shot: deliver one datagram, then stop and clear the callback
static void kk_udp_recv_cb(uv_udp_t* h, ssize_t nread, const uv_buf_t* buf, const struct sockaddr* addr, unsigned flags) {
  kk_context_t* ctx = kk_get_context();
  if ((nread == 0 && addr == NULL) || h->data == NULL) {
    if (buf->base != NULL) kk_free(buf->base, ctx);
    return;
  }
  kk_function_t cb = kk_datatype_from_ptr((kk_ptr_t)(h->data), ctx);
  h->data = NULL;
  uv_udp_recv_stop(h);
  kk_std_core_exn__error res = kk_udp_datagram_result(nread, buf, addr, ctx);
  if (buf->base != NULL) kk_free(buf->base, ctx);
  kk_function_call_error(cb, res, ctx);
}

// streaming: deliver every datagram via the (retained) callback
static void kk_udp_recv_stream_cb(uv_udp_t* h, ssize_t nread, const uv_buf_t* buf, const struct sockaddr* addr, unsigned flags) {
  kk_context_t* ctx = kk_get_context();
  if ((nread == 0 && addr == NULL) || h->data == NULL) {
    if (buf->base != NULL) kk_free(buf->base, ctx);
    return;
  }
  kk_std_core_exn__error res = kk_udp_datagram_result(nread, buf, addr, ctx);
  if (buf->base != NULL) kk_free(buf->base, ctx);
  // call WITHOUT consuming the stored callback (dup, since the call drops one ref)
  kk_function_t cb = kk_datatype_from_ptr((kk_ptr_t)(h->data), ctx);
  kk_function_dup(cb, ctx);
  kk_function_call_error(cb, res, ctx);
}

static void kk_udp_recv_dispose(uv_handle_t* h, void* arg, kk_context_t* ctx) {
  uv_udp_recv_stop((uv_udp_t*)h);
  if (h->data != NULL) {
    kk_function_drop(kk_datatype_from_ptr((kk_ptr_t)(h->data), ctx), ctx);
    h->data = NULL;
  }
}

kk_std_core_exn__error kk_uv_udp_recv(kk_box_t sock, kk_function_t cb, kk_context_t* ctx) {
  uv_udp_t* h = (uv_udp_t*)kk_cptr_unbox_borrowed(sock, ctx);
  kk_box_drop(sock, ctx);
  if (h == NULL) { kk_function_drop(cb, ctx); return kk_error_from_uv_errno(UV_EINVAL, ctx); }
  if (h->data != NULL) {
    kk_function_drop(kk_datatype_from_ptr((kk_ptr_t)(h->data), ctx), ctx);
  }
  h->data = kk_datatype_as_ptr(cb, ctx);
  int err = uv_udp_recv_start(h, &kk_udp_alloc_cb, &kk_udp_recv_cb);
  if (err != 0) {
    kk_function_drop(kk_datatype_from_ptr((kk_ptr_t)(h->data), ctx), ctx);
    h->data = NULL;
    return kk_error_from_uv_errno(err, ctx);
  }
  return kk_result_uv_handle_dispose((uv_handle_t*)h, NULL, &kk_udp_recv_dispose, ctx);
}

// Start streaming receive: the callback is invoked for every datagram (it is
// retained across datagrams) until the socket is closed.
kk_std_core_exn__error kk_uv_udp_recv_start(kk_box_t sock, kk_function_t cb, kk_context_t* ctx) {
  uv_udp_t* h = (uv_udp_t*)kk_cptr_unbox_borrowed(sock, ctx);
  kk_box_drop(sock, ctx);
  if (h == NULL) { kk_function_drop(cb, ctx); return kk_error_from_uv_errno(UV_EINVAL, ctx); }
  if (h->data != NULL) {
    kk_function_drop(kk_datatype_from_ptr((kk_ptr_t)(h->data), ctx), ctx);
  }
  h->data = kk_datatype_as_ptr(cb, ctx);
  int err = uv_udp_recv_start(h, &kk_udp_alloc_cb, &kk_udp_recv_stream_cb);
  if (err != 0) {
    kk_function_drop(kk_datatype_from_ptr((kk_ptr_t)(h->data), ctx), ctx);
    h->data = NULL;
    return kk_error_from_uv_errno(err, ctx);
  }
  return kk_result_uv_handle_dispose((uv_handle_t*)h, NULL, &kk_udp_recv_dispose, ctx);
}
