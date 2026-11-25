/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting, Microsoft Research, Daan Leijen

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// for IDE
// #define __EMSCRIPTEN__
// #include <kklib.h>
// #include "evloop.h"
// #include <stdio.h>  // debug

#include <uv.h>
#ifndef _WIN32
#include <sys/select.h>   // the external-wait watcher thread (see below)
#endif

kk_std_core_exn__error kk_result_ok( kk_box_t val, kk_context_t* ctx ) {
  return kk_std_core_types__new_Ok(val,ctx);
}


// ---------------------------------------------------
// Handle/Request dispose
// ---------------------------------------------------

typedef void (kk_uv_dispose_fun_t)(void* p, void* arg, kk_context_t* ctx);

struct kk_uv_dispose_fun_closure_s {
  struct kk_function_s _base;
  void* p;
  void* arg;
  kk_uv_dispose_fun_t* dispose;
};

static kk_box_t kk_uv_dispose_fun(kk_function_t _fself, kk_context_t* ctx) {
  struct kk_uv_dispose_fun_closure_s* _self = kk_function_as(struct kk_uv_dispose_fun_closure_s*, _fself, ctx);
  void* p = _self->p;
  void* arg = _self->arg;
  kk_uv_dispose_fun_t* dispose = _self->dispose;
  kk_function_drop(_fself,ctx);
  dispose(p,arg,ctx);
  return kk_unit_box(kk_Unit);
}

kk_function_t kk_uv_dispose_fun_create(void* p, void* arg, kk_uv_dispose_fun_t* dispose, kk_context_t* ctx) {
  struct kk_uv_dispose_fun_closure_s* _self = kk_function_alloc_as(struct kk_uv_dispose_fun_closure_s, 1, ctx);
  _self->_base.fun = kk_kkfun_ptr_box(&kk_uv_dispose_fun, ctx);
  _self->p = p;
  _self->arg = arg;
  _self->dispose = dispose;
  return kk_datatype_from_base(&_self->_base, ctx);
}


kk_std_core_exn__error kk_result_uv_handle_dispose( uv_handle_t* handle, void* arg, kk_uv_handle_dispose_fun_t* dispose, kk_context_t* ctx ) {
  kk_function_t dispose_fun = kk_uv_dispose_fun_create((void*)handle,arg,(kk_uv_dispose_fun_t*)dispose,ctx);
  return kk_result_ok(kk_function_box(dispose_fun,ctx),ctx);
}

kk_std_core_exn__error kk_result_uv_handle_dispose0( uv_handle_t* handle, kk_context_t* ctx ) {
  return kk_result_uv_handle_dispose( handle, NULL, &kk_uv_handle_dispose, ctx);
}

kk_std_core_exn__error kk_result_uv_req_dispose( uv_req_t* req, void* arg, kk_uv_req_dispose_fun_t* dispose, kk_context_t* ctx ) {
  kk_function_t dispose_fun = kk_uv_dispose_fun_create((void*)req,arg,(kk_uv_dispose_fun_t*)dispose,ctx);
  return kk_result_ok(kk_function_box(dispose_fun,ctx),ctx);
}

kk_std_core_exn__error kk_result_uv_req_dispose0( uv_req_t* req, kk_context_t* ctx ) {
  return kk_result_uv_req_dispose( req, NULL, &kk_uv_req_dispose, ctx);
}


//---------------------------------------
// set allocator

#define KK_CUSTOM_INIT  kk_uv_alloc_init

static void* kk_malloc_ctx(size_t size) {
  return kk_malloc(size, kk_get_context());
}
static void* kk_realloc_ctx(void* p, size_t size) {
  return kk_realloc(p, size, kk_get_context());
}
static void* kk_calloc_ctx(size_t count, size_t size) {
  return kk_zalloc(count*size, kk_get_context());
}
static void kk_free_ctx(void* p) {
  kk_free(p, kk_get_context());
}
static void kk_uv_alloc_init(kk_context_t* _ctx){
  uv_replace_allocator(&kk_malloc_ctx, &kk_realloc_ctx, &kk_calloc_ctx, &kk_free_ctx);
}


//---------------------------------------
// utility
//---------------------------------------

kk_std_core_exn__error kk_error_from_uv_errno( int err, kk_context_t* ctx ) {
  if (err > 0) {
    return kk_error_from_errno(err,ctx);
  }
  else {
    const int syserr = -err; /* uv error codes are negative */
    const char* serr = uv_strerror(err);
    kk_string_t msg = kk_string_alloc_from_qutf8( serr, ctx );
    // kk_free(serr,ctx);
    return kk_std_core_types__new_Error( kk_std_core_exn__exception_box( kk_std_core_exn__new_Exception( msg,
                  kk_std_core_exn__new_ExnSystem(kk_reuse_null, 0, kk_integer_from_int(syserr,ctx), ctx), ctx), ctx), ctx );
  }
}


//---------------------------------------
// internal async call
//---------------------------------------

// typedef void (uv_arg_callback_t)(void* arg);

// typedef struct uv_closure_s {
//   uv_arg_callback_t* cb;
//   void*              arg;
// } uv_closure_t;

// static void uv_async_call_cb( uv_timer_t* t ) {
//   uv_closure_t* c = (uv_closure_t*)(t->data);
//   uv_arg_callback_t* cb = c->cb;
//   void* arg = c->arg;
//   kk_context_t* ctx = kk_get_context();
//   kk_free(c,ctx);
//   uv_close((uv_handle_t*)t,NULL);
//   kk_free(t,ctx);
//   cb(arg);
// }

// static void uv_async_call(uv_loop_t* loop, uv_arg_callback_t* cb, void* arg, uint64_t millisecs) {
//   kk_context_t* ctx = kk_get_context();
//   uv_timer_t* t   = kk_zalloc(sizeof(uv_timer_t),ctx);
//   uv_closure_t* c = kk_zalloc(sizeof(uv_closure_t),ctx);
//   c->cb = cb;
//   c->arg = arg;
//   uv_timer_init(loop,t);  
//   uv_timer_start(t,&uv_async_call_cb, millisecs, 0 );  
// }


//---------------------------------------
// handles
//---------------------------------------

kk_std_core_exn__error kk_result_uv_handle( uv_handle_t* h, kk_context_t* ctx ) {
  return kk_result_ok(kk_cptr_box(h,ctx),ctx);  // not freed, treat as an opaque value and free explicitly
}

long kk_uv_live_handles = 0;   // leak triage (read from the impeller shim stats)

int kk_uv_handle_create( size_t sz, kk_function_t cb, uv_handle_t** phandle, kk_context_t* ctx ) {
  kk_uv_live_handles++;
  uv_handle_t* h = *phandle = (uv_handle_t*)kk_zalloc(sz,ctx);
  if (h==NULL) {
    kk_function_drop(cb,ctx);
    return UV_ENOMEM;
  }
  else {
    h->data = kk_datatype_as_ptr(cb,ctx);
    return 0;
  }
}

void kk_uv_handle_free(uv_handle_t* h, kk_context_t* ctx) {
  kk_uv_live_handles--;
  if (h->data != NULL) {
    // drop the callback (just in case, should have been set NULL already in handle_close/callback)
    kk_datatype_drop( kk_datatype_from_ptr((kk_ptr_t)(h->data),ctx), ctx );
    h->data = NULL;
  }
  kk_free(h,ctx);
}

static void kk_uv_handle_close_cb(uv_handle_t* h) {
  kk_uv_handle_free(h,kk_get_context());
}

void kk_uv_handle_close(uv_handle_t* h) {
  if (h==NULL) return;
  if (h->data != NULL) {
    // drop the callback function right away
    // if a handle is disposed, uv might still schedule the callback; setting it to NULL prevents the callback still being called
    kk_context_t* ctx = kk_get_context();
    kk_function_drop( kk_datatype_from_ptr((kk_ptr_t)(h->data),ctx), ctx );
    h->data = NULL;
  }
  uv_close(h, &kk_uv_handle_close_cb);  // if uv_close is called, any in-progress request is called with UV_ECANCELED (<https://docs.libuv.org/en/v1.x/handle.html>)
}

void kk_uv_handle_dispose(uv_handle_t* handle, void* arg, kk_context_t* ctx) {
  kk_unused(arg);
  kk_unused(ctx);
  if (handle==NULL) return;
  kk_uv_handle_close((uv_handle_t*)handle);
}

void kk_uv_handle_callback(uv_handle_t* h) {
  if (h==NULL) return;
  if (h->data != NULL) {
    kk_context_t* ctx = kk_get_context();
    kk_function_t cb = kk_datatype_from_ptr((kk_ptr_t)(h->data),ctx); // the call drops the `cb`
    h->data = NULL;
    kk_function_call0(cb,ctx);
  }
  kk_uv_handle_close(h);
}


//---------------------------------------
// requests
//---------------------------------------

int kk_uv_req_create( size_t sz, kk_function_t cb, uv_req_t** preq, kk_context_t* ctx ) {
  uv_req_t* req = *preq = (uv_req_t*)kk_zalloc(sz,ctx);
  if (req==NULL) {
    kk_function_drop(cb,ctx);
    return UV_ENOMEM;
  }
  else {
    req->data = kk_datatype_as_ptr(cb,ctx);
    return 0;
  }
}

void kk_uv_req_free(uv_req_t* req, kk_context_t* ctx) {
  if (req == NULL) return;
  if (req->data != NULL) {
    // drop the callback (just in case, should have been set NULL already in req_close/callback)
    kk_datatype_drop( kk_datatype_from_ptr((kk_ptr_t)(req->data),ctx), ctx );
    req->data = NULL;
  }
  if (req->type == UV_FS) {
    uv_fs_req_cleanup((uv_fs_t*)req);
  }
  kk_free(req,ctx);
}

// static void kk_uv_req_close_cb(void* req) {
//   kk_uv_req_free((uv_req_t*)req,kk_get_context());
// }

void kk_uv_req_close(uv_req_t* req) {
  if (req==NULL) return;
  kk_context_t* ctx = kk_get_context();    
  if (req->data != NULL) {
    // drop the callback
    kk_datatype_drop( kk_datatype_from_ptr((kk_ptr_t)(req->data),ctx), ctx );
    req->data = NULL;
  }
  kk_uv_req_free(req,ctx);
  // uv_async_call(req->loop, (void*)req, &kk_uv_req_close_cb, 0);  // todo: can we call this right away?
}

// This is the Koka dispose functions called on cancelation
void kk_uv_req_dispose(uv_req_t* req, void* arg, kk_context_t* ctx) {
  kk_unused(arg);
  if (req==NULL) return;
  if (req->data != NULL) {
    // drop the callback so it will never be called
    kk_datatype_drop( kk_datatype_from_ptr((kk_ptr_t)(req->data),ctx), ctx );
    req->data = NULL;
  }
  uv_cancel(req);
  // if cancel succeeds, the request uv callback is called later with UV_ECANCELED (and closes the request)
  // if it fails, the uv callback will also be called (or has been called) (which closes/closed the request)
}

void kk_uv_req_callback(uv_req_t* req, kk_uv_req_call_fun_t* call ) {
  if (req==NULL) return;
  if (req->data != NULL) {
    kk_context_t* ctx = kk_get_context();
    kk_function_t cb = kk_datatype_from_ptr((kk_ptr_t)(req->data),ctx); // the call drops the `cb`
    req->data = NULL;    
    call(cb,req,ctx);  // call it
  }  
  kk_uv_req_close(req);
}

// -----------------------------------------------------
// Event Loop

kk_uv_loop_t kk_uv_loop_init(kk_context_t* ctx) {
  uv_loop_t* const uvloop = (uv_loop_t*)kk_zalloc(sizeof(uv_loop_t),ctx);
  if (uvloop != NULL) {
    uv_loop_init(uvloop);
  }
  return kk_cptr_raw_box(&kk_free_fun,uvloop,ctx);
}

uv_loop_t* kk_uv_loop(kk_uv_loop_t loop_borrowed, kk_context_t* ctx) {
  return (uv_loop_t*)kk_cptr_raw_unbox_borrowed(loop_borrowed, ctx);
}

static char* kk_uv_handle_type_str(uv_handle_t* handle) {
  switch (handle->type) {
    #define XX(code,lc) case UV_##code: return #lc;
    UV_HANDLE_TYPE_MAP(XX)
    #undef XX
    default: return "unknown";
  }
}

static void kk_uv_loop_walk_cb(uv_handle_t* handle, void* arg) {
  const char* closing_msg = uv_is_closing(handle) ? " [closing]" : "";
  const char* active_msg  = uv_is_active(handle) ? " [active]" : "";
  kk_warning_message(" - %s handle%s%s\n", kk_uv_handle_type_str(handle), active_msg, closing_msg);
}


static void kk_uv_loop_done(kk_uv_loop_t loop, kk_context_t* ctx) {
  uv_loop_t* const uvloop = kk_uv_loop(loop,ctx);
  int ret = uv_loop_close(uvloop);
  if (ret != 0) {
    if (ret == UV_EBUSY) {
      kk_warning_message("event loop closed with open child handles:\n");
      uv_walk(uvloop, kk_uv_loop_walk_cb, NULL);
    } else {
      kk_warning_message("event loop close returned error: %s\n", uv_strerror(ret));
    }
  }
  kk_box_drop(loop,ctx);
}

// -----------------------------------------------------
// External-wait integration (the libuv "embed" pattern). A host UI toolkit
// whose event wait must own the thread's sleep (GLFW/Cocoa: events only
// arrive on the main thread, inside ITS wait) installs an external waiter:
// the loop then alternates `uv_run(NOWAIT)` with the host's wait, passing
// `uv_backend_timeout` so uv timers still fire on time. A watcher thread
// select()s on the loop's backend fd and calls the host's `wake` when uv
// work becomes ready from elsewhere (uv_async sends from other threads,
// threadpool completions), so nothing is stranded while the host sleeps.
// Install from within a running callback: it uv_stop()s the current
// uv_run(DEFAULT), and the runner below switches over.

static _Thread_local uv_loop_t* kk_uv_running_loop = NULL;
static _Thread_local kk_uv_external_wait_fun* kk_uv_external_wait = NULL;

static uv_thread_t kk_uv_embed_thread;
static uv_sem_t    kk_uv_embed_sem;
static volatile int kk_uv_embed_stop = 0;
static uv_loop_t*  kk_uv_embed_loop = NULL;
static void (*kk_uv_embed_wake)(void) = NULL;   // read by the watcher thread

static void kk_uv_embed_runner(void* arg) {
  uv_loop_t* loop = (uv_loop_t*)arg;
  while (!kk_uv_embed_stop) {
    int fd = uv_backend_fd(loop);
    if (fd < 0) break;
    fd_set rfds; FD_ZERO(&rfds); FD_SET(fd, &rfds);
    struct timeval tv = { 0, 500000 };            // bounded stop-flag latency
    int r = select(fd + 1, &rfds, NULL, NULL, &tv);
    if (kk_uv_embed_stop) break;
    if (r > 0) {
      if (kk_uv_embed_wake != NULL) kk_uv_embed_wake();
      uv_sem_wait(&kk_uv_embed_sem);              // one wake per loop iteration
    }
  }
}

void kk_uv_loop_install_external_wait(kk_uv_external_wait_fun* wait, void (*wake)(void)) {
  kk_uv_external_wait = wait;
  kk_uv_embed_wake = wake;
  // the runner starts the watcher lazily on its first hybrid iteration (an
  // install may run BEFORE uv_run does -- strands start executing at fork);
  // if the loop is already running inside uv_run(DEFAULT), unwind it now
  if (kk_uv_running_loop != NULL) uv_stop(kk_uv_running_loop);
}

// the external signal: ONE pending single-shot uv_async a host can trigger.
// Used to park a strand until the host has input -- same single-shot callback
// shape as the timer above (the callback consumes the handle). A PROCESS
// global (not thread-local): uv_async_send is thread-safe, so a platform
// thread (GLFW main) can wake the render thread's parked pump.
static uv_async_t* kk_uv_external_signal = NULL;

static void kk_uv_external_signal_cb(uv_async_t* a) {
  if (kk_uv_external_signal == a) kk_uv_external_signal = NULL;
  kk_uv_handle_callback((uv_handle_t*)a);
}

static void kk_uv_external_signal_dispose(uv_handle_t* h, void* arg, kk_context_t* ctx) {
  kk_unused(arg); kk_unused(ctx);
  if ((uv_handle_t*)kk_uv_external_signal == h) kk_uv_external_signal = NULL;
  kk_uv_handle_close(h);
}

kk_std_core_exn__error kk_uv_external_signal_setup(kk_uv_loop_t loop, kk_function_t cb, kk_context_t* ctx) {
  uv_async_t* a;
  int err = kk_uv_handle_create(sizeof(uv_async_t), cb, (uv_handle_t**)&a, ctx);
  if (err!=0) return kk_error_from_uv_errno(err,ctx);
  err = uv_async_init(kk_uv_loop(loop,ctx), a, &kk_uv_external_signal_cb);
  if (err!=0) { kk_uv_handle_free((uv_handle_t*)a,ctx); return kk_error_from_uv_errno(err,ctx); }
  kk_uv_external_signal = a;
  return kk_result_uv_handle_dispose((uv_handle_t*)a, NULL, &kk_uv_external_signal_dispose, ctx);
}

void kk_uv_external_signal_trigger(void) {
  if (kk_uv_external_signal != NULL) uv_async_send(kk_uv_external_signal);
}

void kk_uv_loop_run(kk_uv_loop_t loop, kk_context_t* ctx) {
  uv_loop_t* const uvloop = kk_uv_loop(loop,ctx);
  int ret = UV_UNKNOWN_HANDLE;
  if (uvloop!=NULL) {
    kk_uv_running_loop = uvloop;
    for(;;) {
      if (kk_uv_external_wait == NULL) {
        ret = uv_run(uvloop,UV_RUN_DEFAULT);
        if (kk_uv_external_wait == NULL) break;  // finished normally
        // a callback installed an external waiter (and uv_stop'ed us): go hybrid
      }
      else {
        if (kk_uv_embed_loop != uvloop) {        // first hybrid iteration: start the watcher
          kk_uv_embed_loop = uvloop;
          kk_uv_embed_stop = 0;
          uv_sem_init(&kk_uv_embed_sem, 0);
          uv_thread_create(&kk_uv_embed_thread, &kk_uv_embed_runner, uvloop);
        }
        uv_run(uvloop, UV_RUN_NOWAIT);
        if (!uv_loop_alive(uvloop)) { ret = 0; break; }
        kk_uv_external_wait((int64_t)uv_backend_timeout(uvloop));
        uv_sem_post(&kk_uv_embed_sem);           // let the watcher re-arm
      }
    }
    kk_uv_running_loop = NULL;
    if (kk_uv_embed_loop == uvloop && kk_uv_embed_loop != NULL) {
      kk_uv_embed_stop = 1;
      uv_sem_post(&kk_uv_embed_sem);
      uv_thread_join(&kk_uv_embed_thread);
      uv_sem_destroy(&kk_uv_embed_sem);
      kk_uv_embed_loop = NULL;
      kk_uv_external_wait = NULL;
      kk_uv_embed_wake = NULL;
    }
  }
  if (ret!=0){
    kk_warning_message("event loop closed: %s\n", uv_strerror(ret));
  }
  kk_uv_loop_done(loop,ctx);
}

