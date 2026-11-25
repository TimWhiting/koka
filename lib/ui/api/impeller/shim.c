/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Koka fringe over the Impeller interop C API (impeller.h) plus the small
// window host (host.m). Impeller handles are thread-safe refcounted with
// Retain/Release -- the exact shape of a Perceus-owned `kk_cptr_raw` box:
// dropping the last Koka reference Releases the Impeller object. This file
// is textually included into the generated C of impeller.kk.

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <impeller.h>

// vendored single-header image decoder (public domain). The implementation is
// compiled EXACTLY once, here (this file is textually included into the one
// generated C of impeller.kk). Force 4-channel RGBA on load; native size only.
#define STB_IMAGE_IMPLEMENTATION
#define STBI_ONLY_PNG
#define STBI_ONLY_JPEG
#include "stb_image.h"

// host.m (libimpellerhost.dylib)
extern int   imp_host_init(int width, int height, const char* title);
extern int   imp_host_should_close(int win);
extern void  imp_host_poll(void);
extern void  imp_host_wait_events(double timeout_ms);
extern int   imp_host_take_events_dirty(void);
extern void  imp_host_wake(void);
extern double imp_host_refresh_ms(void);
extern void  imp_host_platform_loop(void);
extern void  imp_host_set_event_sink(void (*sink)(void));
extern int   imp_host_platform_split(void);
extern void  imp_host_mark_split(void);
extern int   imp_host_next_pointer(double* x, double* y);
extern int   imp_host_pointer_win(void);
extern unsigned int imp_host_next_char(void);
extern int   imp_host_char_win(void);
extern int   imp_host_next_key(void);
extern int   imp_host_key_win(void);
extern int   imp_host_cursor_win(void);
extern int   imp_host_scroll_win(void);
extern void* imp_host_context(void);
extern double imp_host_scale(int win);
extern double imp_host_width(int win);
extern double imp_host_height(int win);
extern double imp_host_cursor_x(int win);
extern void imp_host_inject_cursor(int win, double x, double y);
extern void imp_host_inject_pointer(int win, double kind, double x, double y);
extern void imp_host_inject_char(int win, unsigned int codepoint);
extern void imp_host_inject_key(int win, int key);
extern void imp_host_inject_scroll(int win, double dx, double dy);
extern void imp_host_drain_rings(void);
extern double imp_host_cursor_y(int win);
extern double imp_host_take_scroll_dy(int win);
extern double imp_host_take_scroll_dx(int win);
extern void  imp_host_present(int win, void* display_list);
extern void  imp_host_shutdown(void);
extern int   imp_host_open_window(int chrome, const char* title, double w, double h);
extern void  imp_host_close_window(int win);
extern void  imp_host_set_window_title(int win, const char* title);
extern void  imp_host_set_window_pos(int win, double x, double y);
extern int   imp_host_window_alive(int win);
extern long  imp_host_present_count(int win);
extern int   imp_host_window_close_requested(int win);
extern void  imp_host_main_window_origin(double* x, double* y);

// ---- Perceus-owned handles -------------------------------------------------

// KOKA_IMP_STATS=1: live-object counters (leak triage)
static long g_live_paint = 0, g_live_builder = 0, g_live_dl = 0, g_live_para = 0;
static long g_live_tex = 0;
static long g_live_pb = 0;   // rich-* incremental ParagraphBuilder objects
static long g_presents = 0;

static void kk_imp_paint_free(void* p, kk_block_t* b, kk_context_t* ctx) {
  kk_unused(b); kk_unused(ctx);
  g_live_paint--;
  ImpellerPaintRelease((ImpellerPaint)p);
}
static void kk_imp_dlb_free(void* p, kk_block_t* b, kk_context_t* ctx) {
  kk_unused(b); kk_unused(ctx);
  g_live_builder--;
  ImpellerDisplayListBuilderRelease((ImpellerDisplayListBuilder)p);
}
static void kk_imp_dl_free(void* p, kk_block_t* b, kk_context_t* ctx) {
  kk_unused(b); kk_unused(ctx);
  g_live_dl--;
  ImpellerDisplayListRelease((ImpellerDisplayList)p);
}
static void kk_imp_para_free(void* p, kk_block_t* b, kk_context_t* ctx) {
  kk_unused(b); kk_unused(ctx);
  g_live_para--;
  ImpellerParagraphRelease((ImpellerParagraph)p);
}
static void kk_imp_para_builder_free(void* p, kk_block_t* b, kk_context_t* ctx) {
  kk_unused(b); kk_unused(ctx);
  g_live_pb--;
  ImpellerParagraphBuilderRelease((ImpellerParagraphBuilder)p);
}
static void kk_imp_line_metrics_free(void* p, kk_block_t* b, kk_context_t* ctx) {
  kk_unused(b); kk_unused(ctx);
  ImpellerLineMetricsRelease((ImpellerLineMetrics)p);
}

// ---- window host ------------------------------------------------------------

static bool kk_imp_init(kk_string_t title, kk_integer_t w, kk_integer_t h, kk_context_t* ctx) {
  kk_ssize_t len;
  const char* ctitle = kk_string_cbuf_borrow(title, &len, ctx);
  int ok = imp_host_init((int)kk_integer_clamp32(w, ctx), (int)kk_integer_clamp32(h, ctx), ctitle);
  kk_string_drop(title, ctx);
  return (ok != 0);
}

static bool kk_imp_should_close(kk_integer_t win, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  return (imp_host_should_close(w) != 0);
}

static kk_unit_t kk_imp_poll(kk_context_t* ctx) {
  kk_unused(ctx);
  imp_host_poll();
  return kk_Unit;
}

static double g_kk_ptr_x = 0.0, g_kk_ptr_y = 0.0;

// 0 none, 1 press, 2 release; position via pointer-x/pointer-y
static kk_integer_t kk_imp_next_pointer(kk_context_t* ctx) {
  return kk_integer_from_int(imp_host_next_pointer(&g_kk_ptr_x, &g_kk_ptr_y), ctx);
}

static double kk_imp_pointer_x(kk_context_t* ctx) { kk_unused(ctx); return g_kk_ptr_x; }
static double kk_imp_pointer_y(kk_context_t* ctx) { kk_unused(ctx); return g_kk_ptr_y; }

// the window of the last DRAINED pointer/char/key event, and the window that
// last saw the cursor / the pending scroll delta
static kk_integer_t kk_imp_pointer_win(kk_context_t* ctx) {
  return kk_integer_from_int(imp_host_pointer_win(), ctx);
}
static kk_integer_t kk_imp_char_win(kk_context_t* ctx) {
  return kk_integer_from_int(imp_host_char_win(), ctx);
}
static kk_integer_t kk_imp_key_win(kk_context_t* ctx) {
  return kk_integer_from_int(imp_host_key_win(), ctx);
}
static kk_integer_t kk_imp_scroll_win(kk_context_t* ctx) {
  return kk_integer_from_int(imp_host_scroll_win(), ctx);
}
static kk_integer_t kk_imp_cursor_win(kk_context_t* ctx) {
  return kk_integer_from_int(imp_host_cursor_win(), ctx);
}

// next typed character as a string (empty when none)
static kk_string_t kk_imp_next_char(kk_context_t* ctx) {
  unsigned int c = imp_host_next_char();
  if (c == 0) return kk_string_empty();
  return kk_string_from_char((kk_char_t)c, ctx);
}

// 0 none, 1 backspace, 2 enter, 3 escape
static kk_integer_t kk_imp_next_key(kk_context_t* ctx) {
  return kk_integer_from_int(imp_host_next_key(), ctx);
}

static kk_unit_t kk_imp_shutdown(kk_context_t* ctx) {
  kk_unused(ctx);
  imp_host_shutdown();
  return kk_Unit;
}

// ---- titled windows: render->main command ring (host.m) --------------------
// create/destroy/retitle/reposition are all deferred to the main thread; these
// wrappers just enqueue (or read cached table state) and return immediately.

static kk_integer_t kk_imp_open_window(kk_integer_t chrome, kk_string_t title, double w, double h, kk_context_t* ctx) {
  kk_ssize_t len;
  const char* ctitle = kk_string_cbuf_borrow(title, &len, ctx);
  int id = imp_host_open_window(kk_integer_clamp32(chrome, ctx), ctitle, w, h);
  kk_string_drop(title, ctx);
  return kk_integer_from_int(id, ctx);
}

static kk_unit_t kk_imp_close_window(kk_integer_t win, kk_context_t* ctx) {
  imp_host_close_window(kk_integer_clamp32(win, ctx));
  return kk_Unit;
}

static kk_unit_t kk_imp_set_window_title(kk_integer_t win, kk_string_t title, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  kk_ssize_t len;
  const char* ctitle = kk_string_cbuf_borrow(title, &len, ctx);
  imp_host_set_window_title(w, ctitle);
  kk_string_drop(title, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_set_window_pos(kk_integer_t win, double x, double y, kk_context_t* ctx) {
  imp_host_set_window_pos(kk_integer_clamp32(win, ctx), x, y);
  return kk_Unit;
}

static bool kk_imp_window_alive(kk_integer_t win, kk_context_t* ctx) {
  return (imp_host_window_alive(kk_integer_clamp32(win, ctx)) != 0);
}

static bool kk_imp_window_close_requested(kk_integer_t win, kk_context_t* ctx) {
  return (imp_host_window_close_requested(kk_integer_clamp32(win, ctx)) != 0);
}

// frames actually presented to a window: a live-but-blank window reads 0
// (regression probe for the per-window pending-dl present path)
static kk_integer_t kk_imp_present_count(kk_integer_t win, kk_context_t* ctx) {
  return kk_integer_from_int64((int64_t)imp_host_present_count(kk_integer_clamp32(win, ctx)), ctx);
}

// screen coords of the main window; split into two externs (the Koka side
// pairs them into a tuple) -- same shape as pointer-x/pointer-y above
static double kk_imp_main_origin_x(kk_context_t* ctx) {
  kk_unused(ctx);
  double x, y; imp_host_main_window_origin(&x, &y); return x;
}
static double kk_imp_main_origin_y(kk_context_t* ctx) {
  kk_unused(ctx);
  double x, y; imp_host_main_window_origin(&x, &y); return y;
}

// ---- paints ------------------------------------------------------------------

static kk_box_t kk_imp_paint(double r, double g, double b, double a, kk_context_t* ctx) {
  g_live_paint++;
  ImpellerPaint paint = ImpellerPaintNew();
  ImpellerColor color = { (float)r, (float)g, (float)b, (float)a, kImpellerColorSpaceSRGB };
  ImpellerPaintSetColor(paint, &color);
  return kk_cptr_raw_box(&kk_imp_paint_free, (void*)paint, ctx);
}

// A paint whose colour source is a two-stop LINEAR GRADIENT between absolute
// points. The colour source is released immediately after being set: the paint
// retains it, so this hands ownership over rather than leaking one per frame.
// Colours arrive PACKED as 0xRRGGBBAA in an int32 rather than as eight
// doubles: Koka's C extern substitutes arguments by single-digit `#N`, so an
// extern with more than nine parameters silently emits `#1` followed by a
// literal `0` for the tenth. Packing keeps this at six. 8 bits per channel is
// what the display has anyway.
static ImpellerColor kk_imp_unpack_color(uint32_t c) {
  ImpellerColor out = { ((c >> 24) & 0xFF) / 255.0f, ((c >> 16) & 0xFF) / 255.0f,
                        ((c >> 8) & 0xFF) / 255.0f, (c & 0xFF) / 255.0f,
                        kImpellerColorSpaceSRGB };
  return out;
}

static kk_box_t kk_imp_paint_lgrad(double x0, double y0, double x1, double y1,
                                   int32_t c0, int32_t c1,
                                   kk_context_t* ctx) {
  g_live_paint++;
  ImpellerPaint paint = ImpellerPaintNew();
  ImpellerPoint start = { (float)x0, (float)y0 };
  ImpellerPoint end   = { (float)x1, (float)y1 };
  ImpellerColor colors[2] = { kk_imp_unpack_color((uint32_t)c0),
                              kk_imp_unpack_color((uint32_t)c1) };
  float stops[2] = { 0.0f, 1.0f };
  ImpellerColorSource src = ImpellerColorSourceCreateLinearGradientNew(
      &start, &end, 2, colors, stops, kImpellerTileModeClamp, NULL);
  if (src != NULL) {
    ImpellerPaintSetColorSource(paint, src);
    ImpellerColorSourceRelease(src);
  }
  return kk_cptr_raw_box(&kk_imp_paint_free, (void*)paint, ctx);
}

// The radial twin of the gradient paint above: centre, radius, inner and outer
// colour. Same packed-colour convention and the same release-after-set.
static kk_box_t kk_imp_paint_rgrad(double cx, double cy, double radius,
                                   int32_t c0, int32_t c1, kk_context_t* ctx) {
  g_live_paint++;
  ImpellerPaint paint = ImpellerPaintNew();
  ImpellerPoint center = { (float)cx, (float)cy };
  ImpellerColor colors[2] = { kk_imp_unpack_color((uint32_t)c0),
                              kk_imp_unpack_color((uint32_t)c1) };
  float stops[2] = { 0.0f, 1.0f };
  ImpellerColorSource src = ImpellerColorSourceCreateRadialGradientNew(
      &center, (float)radius, 2, colors, stops, kImpellerTileModeClamp, NULL);
  if (src != NULL) {
    ImpellerPaintSetColorSource(paint, src);
    ImpellerColorSourceRelease(src);
  }
  return kk_cptr_raw_box(&kk_imp_paint_free, (void*)paint, ctx);
}

// ---- images: decode (stb_image) + GPU texture upload --------------------------
// Textures are RAW ImpellerTexture handles passed to Koka as int (the pointer
// value). Lifetime is EXPLICIT: the backend's identity cache holds a handle per
// image owner and calls `texture-release` when the owner is pruned (unmounted).
// The Impeller context lives on the render thread (host.m's g_context) and the
// GPU upload MUST happen there -- these are only ever called from the render
// thread's paint walk.

// stbi_load reports the decoded size through these; read immediately after a
// successful `kk_imp_decode` on the SAME (render) thread (see the two-globals
// idiom used by main-window-origin above).
static int g_decoded_w = 0, g_decoded_h = 0;

// decode `path` to tightly-packed RGBA8888. Returns the pixel buffer pointer as
// an integer (0 on failure); the caller reads width/height via the accessors
// below and must hand the pointer to `kk_imp_texture_create` (which takes
// ownership of the buffer) -- or free it -- exactly once.
static kk_integer_t kk_imp_decode(kk_string_t path, kk_context_t* ctx) {
  kk_ssize_t len;
  const char* cpath = kk_string_cbuf_borrow(path, &len, ctx);
  int w = 0, h = 0, n = 0;
  stbi_uc* buf = stbi_load(cpath, &w, &h, &n, 4);   // 4 = force RGBA
  kk_string_drop(path, ctx);
  if (buf == NULL) { g_decoded_w = 0; g_decoded_h = 0; return kk_integer_from_int(0, ctx); }
  g_decoded_w = w; g_decoded_h = h;
  return kk_integer_from_int64((int64_t)(intptr_t)buf, ctx);
}

static kk_integer_t kk_imp_decoded_w(kk_context_t* ctx) { return kk_integer_from_int(g_decoded_w, ctx); }
static kk_integer_t kk_imp_decoded_h(kk_context_t* ctx) { return kk_integer_from_int(g_decoded_h, ctx); }

// decode encoded image bytes (a vector<int8>: a PNG/JPEG in memory, e.g. from a
// fetch or an embedded asset) to tightly-packed RGBA8888, exactly like
// kk_imp_decode but via stbi_load_from_memory. Returns the pixel buffer pointer
// as an int (0 on failure); the caller reads width/height via the accessors
// above and hands the pointer to kk_imp_upload_pixels (== kk_imp_texture_create)
// exactly once. The koka vector<int8> elements are value-boxed small ints
// (kk_int8_box); we copy them into a contiguous C buffer to feed stb.
static kk_integer_t kk_imp_decode_bytes(kk_vector_t bytes, kk_context_t* ctx) {
  kk_ssize_t len;
  kk_box_t* e = kk_vector_buf_borrow(bytes, &len, ctx);
  if (len <= 0) { kk_vector_drop(bytes, ctx); g_decoded_w = 0; g_decoded_h = 0; return kk_integer_from_int(0, ctx); }
  unsigned char* enc = (unsigned char*)malloc((size_t)len);
  if (enc == NULL) { kk_vector_drop(bytes, ctx); g_decoded_w = 0; g_decoded_h = 0; return kk_integer_from_int(0, ctx); }
  for (kk_ssize_t i = 0; i < len; i++) enc[i] = (unsigned char)(uint8_t)kk_int8_unbox(e[i], KK_BORROWED, ctx);
  kk_vector_drop(bytes, ctx);
  int w = 0, h = 0, n = 0;
  stbi_uc* buf = stbi_load_from_memory(enc, (int)len, &w, &h, &n, 4);   // 4 = force RGBA
  free(enc);
  if (buf == NULL) { g_decoded_w = 0; g_decoded_h = 0; return kk_integer_from_int(0, ctx); }
  g_decoded_w = w; g_decoded_h = h;
  return kk_integer_from_int64((int64_t)(intptr_t)buf, ctx);
}

// the mapping's release callback: Impeller owns the decoded buffer after a
// successful create and frees it here once the upload (possibly deferred to a
// background thread -- see impeller.h's ContentsNew doc) completes. Providing a
// release callback is the header's recommended, copy-avoiding path.
static void kk_imp_stbi_free_cb(void* user_data) {
  if (user_data != NULL) stbi_image_free(user_data);
}
// the plain-malloc twin (kk_imp_upload_rgba's buffer is malloc'd, not stbi's)
static void kk_imp_free_cb(void* user_data) {
  if (user_data != NULL) free(user_data);
}

// upload a tightly-packed RGBA buffer of size w*h as a GPU texture on the render
// thread (the Impeller context lives there). Takes ownership of `buf`: on
// success Impeller frees it via `freecb` once the upload completes, on failure
// we free it here with the SAME callback. Returns the texture handle (or NULL).
// Shared by kk_imp_texture_create (stb buffer) and kk_imp_upload_rgba (malloc).
static ImpellerTexture kk_imp_make_texture(uint8_t* buf, int w, int h, void (*freecb)(void*)) {
  ImpellerContext context = (ImpellerContext)imp_host_context();
  if (buf == NULL || context == NULL || w <= 0 || h <= 0) {
    if (buf != NULL) freecb(buf);
    return NULL;
  }
  ImpellerTextureDescriptor desc;
  desc.pixel_format = kImpellerPixelFormatRGBA8888;
  desc.size.width = (int64_t)w;
  desc.size.height = (int64_t)h;
  desc.mip_count = 1;
  ImpellerMapping mapping;
  mapping.data = (const uint8_t*)buf;
  mapping.length = (uint64_t)w * (uint64_t)h * 4u;
  mapping.on_release = freecb;
  ImpellerTexture tex = ImpellerTextureCreateWithContentsNew(context, &desc, &mapping, (void*)buf);
  if (tex == NULL) { freecb(buf); return NULL; }
  g_live_tex++;
  return tex;
}

// upload a decoded RGBA buffer (`bufi` = the pointer from kk_imp_decode /
// kk_imp_decode_bytes) as a w*h GPU texture on the render thread. Returns the
// texture handle as an int (0 on failure). Consumes the buffer (stbi-freed).
static kk_integer_t kk_imp_texture_create(kk_integer_t bufi, kk_integer_t wi, kk_integer_t hi, kk_context_t* ctx) {
  uint8_t* buf = (uint8_t*)(intptr_t)kk_integer_clamp64(bufi, ctx);
  int w = (int)kk_integer_clamp32(wi, ctx);
  int h = (int)kk_integer_clamp32(hi, ctx);
  ImpellerTexture tex = kk_imp_make_texture(buf, w, h, &kk_imp_stbi_free_cb);
  return kk_integer_from_int64((int64_t)(intptr_t)tex, ctx);
}

// upload an already-decoded RGBA vector<int8> (FromPixels: w*h*4 bytes, no
// decode) as a GPU texture on the render thread. Copies the koka bytes into a
// contiguous malloc buffer (Impeller frees it via kk_imp_free_cb). Returns the
// texture handle as an int (0 on failure).
static kk_integer_t kk_imp_upload_rgba(kk_vector_t rgba, kk_integer_t wi, kk_integer_t hi, kk_context_t* ctx) {
  int w = (int)kk_integer_clamp32(wi, ctx);
  int h = (int)kk_integer_clamp32(hi, ctx);
  kk_ssize_t len;
  kk_box_t* e = kk_vector_buf_borrow(rgba, &len, ctx);
  kk_ssize_t need = (kk_ssize_t)w * (kk_ssize_t)h * 4;
  if (w <= 0 || h <= 0 || len < need) { kk_vector_drop(rgba, ctx); return kk_integer_from_int(0, ctx); }
  uint8_t* buf = (uint8_t*)malloc((size_t)need);
  if (buf == NULL) { kk_vector_drop(rgba, ctx); return kk_integer_from_int(0, ctx); }
  for (kk_ssize_t i = 0; i < need; i++) buf[i] = (uint8_t)kk_int8_unbox(e[i], KK_BORROWED, ctx);
  kk_vector_drop(rgba, ctx);
  ImpellerTexture tex = kk_imp_make_texture(buf, w, h, &kk_imp_free_cb);
  return kk_integer_from_int64((int64_t)(intptr_t)tex, ctx);
}

// draw a source sub-rect of the texture into a destination rect (both in the
// builder's current logical space). Used by every image-fit mode. `r` is the
// 8-element vector [sx, sy, sw, sh, dx, dy, dw, dh] (see impeller.kk for why the
// coords are packed into a vector rather than passed as scalars).
static kk_unit_t kk_imp_draw_texture_rect(kk_box_t builder, kk_integer_t texi,
                                          kk_vector_t r, kk_context_t* ctx) {
  ImpellerTexture tex = (ImpellerTexture)(intptr_t)kk_integer_clamp64(texi, ctx);
  kk_ssize_t len;
  kk_box_t* e = kk_vector_buf_borrow(r, &len, ctx);
  if (tex != NULL && len >= 8) {
    double v[8];
    for (int i = 0; i < 8; i++) v[i] = kk_double_unbox(e[i], KK_BORROWED, ctx);
    ImpellerRect src = { (float)v[0], (float)v[1], (float)v[2], (float)v[3] };
    ImpellerRect dst = { (float)v[4], (float)v[5], (float)v[6], (float)v[7] };
    ImpellerDisplayListBuilderDrawTextureRect(
        (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx),
        tex, &src, &dst, kImpellerTextureSamplingLinear, NULL);
  }
  kk_box_drop(builder, ctx);
  kk_vector_drop(r, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_texture_release(kk_integer_t texi, kk_context_t* ctx) {
  ImpellerTexture tex = (ImpellerTexture)(intptr_t)kk_integer_clamp64(texi, ctx);
  if (tex != NULL) { ImpellerTextureRelease(tex); g_live_tex--; }
  return kk_Unit;
}

// currently-live GPU textures (successful texture-create minus texture-release
// with a non-zero handle) -- test probe for the image-retention leak guard
static kk_integer_t kk_imp_live_textures(kk_context_t* ctx) {
  return kk_integer_from_int((int)g_live_tex, ctx);
}

// ---- display-list building ----------------------------------------------------

static kk_box_t kk_imp_builder(kk_context_t* ctx) {
  g_live_builder++;
  ImpellerDisplayListBuilder b = ImpellerDisplayListBuilderNew(NULL);
  return kk_cptr_raw_box(&kk_imp_dlb_free, (void*)b, ctx);
}

static kk_unit_t kk_imp_draw_paint(kk_box_t builder, kk_box_t paint, kk_context_t* ctx) {
  ImpellerDisplayListBuilderDrawPaint(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx),
      (ImpellerPaint)kk_cptr_raw_unbox_borrowed(paint, ctx));
  kk_box_drop(builder, ctx);
  kk_box_drop(paint, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_draw_rect(kk_box_t builder, double x, double y, double w, double h,
                                  kk_box_t paint, kk_context_t* ctx) {
  ImpellerRect rect = { (float)x, (float)y, (float)w, (float)h };
  ImpellerDisplayListBuilderDrawRect(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx),
      &rect,
      (ImpellerPaint)kk_cptr_raw_unbox_borrowed(paint, ctx));
  kk_box_drop(builder, ctx);
  kk_box_drop(paint, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_draw_rrect(kk_box_t builder, double x, double y, double w, double h,
                                   double radius, kk_box_t paint, kk_context_t* ctx) {
  ImpellerRect rect = { (float)x, (float)y, (float)w, (float)h };
  ImpellerRoundingRadii radii;
  ImpellerPoint p = { (float)radius, (float)radius };
  radii.top_left = p; radii.top_right = p; radii.bottom_left = p; radii.bottom_right = p;
  ImpellerDisplayListBuilderDrawRoundedRect(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx),
      &rect, &radii,
      (ImpellerPaint)kk_cptr_raw_unbox_borrowed(paint, ctx));
  kk_box_drop(builder, ctx);
  kk_box_drop(paint, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_scale(kk_box_t builder, double sx, double sy, kk_context_t* ctx) {
  ImpellerDisplayListBuilderScale(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx), (float)sx, (float)sy);
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_translate(kk_box_t builder, double tx, double ty, kk_context_t* ctx) {
  ImpellerDisplayListBuilderTranslate(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx), (float)tx, (float)ty);
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

// draw a PRE-RECORDED display list into the builder (repaint boundaries)
static kk_unit_t kk_imp_draw_dl(kk_box_t builder, kk_box_t dl, double opacity, kk_context_t* ctx) {
  ImpellerDisplayListBuilderDrawDisplayList(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx),
      (ImpellerDisplayList)kk_cptr_raw_unbox_borrowed(dl, ctx),
      (float)opacity);
  kk_box_drop(builder, ctx);
  kk_box_drop(dl, ctx);
  return kk_Unit;
}

// KOKA_UI_REPAINT_RAINBOW=1: overlay each repaint boundary with a color that
// CHANGES on every re-record -- stable color = the subtree did not re-layout
// monotonically counts presents while the repaint rainbow is on (drives the
// rotating window-border color: a flash per present = the root re-recorded)
static kk_integer_t kk_imp_rainbow_seq(kk_context_t* ctx) {
  static int seq = 0;
  return kk_integer_from_int(seq++, ctx);
}

static bool kk_imp_debug_repaint(kk_context_t* ctx) {
  kk_unused(ctx);
  static int cached = -1;
  if (cached < 0) cached = (getenv("KOKA_UI_REPAINT_RAINBOW") != NULL) ? 1 : 0;
  return (cached != 0);
}

static kk_unit_t kk_imp_rotate(kk_box_t builder, double degrees, kk_context_t* ctx) {
  ImpellerDisplayListBuilderRotate(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx), (float)degrees);
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

// concat a full 4x4 (perspective/tilt) transform onto the save stack. `m` is
// our ROW-major `mat4.m` (16 float64, `m[r*4+c]`); ImpellerMatrix is
// COLUMN-major (see impeller.h's `ImpellerMatrix` doc comment) so this
// transposes on the way in. Header-derived, NOT yet pixel-verified -- the
// samples/ui/gallery card flip (task 6) is the visual check; if it mirrors,
// flip this AND web/backend.kk's css3d transpose together.
static kk_unit_t kk_imp_transform(kk_box_t builder, kk_vector_t m, kk_context_t* ctx) {
  kk_ssize_t len;
  kk_box_t* elems = kk_vector_buf_borrow(m, &len, ctx);
  ImpellerMatrix mat;
  for (int r = 0; r < 4; r++) {
    for (int c = 0; c < 4; c++) {
      double v = (len >= 16) ? kk_double_unbox(elems[r * 4 + c], KK_BORROWED, ctx) : ((r == c) ? 1.0 : 0.0);
      mat.m[c * 4 + r] = (float)v;
    }
  }
  ImpellerDisplayListBuilderTransform(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx), &mat);
  kk_box_drop(builder, ctx);
  kk_vector_drop(m, ctx);
  return kk_Unit;
}

// ---- event-driven input: hand the uv loop's idle sleep to GLFW ----
// (the libuv embed pattern; see std/async/api/uv/evloop.c). The waiter sleeps
// in glfwWaitEventsTimeout; when input arrived it triggers the external
// signal, which resumes the Koka pump strand awaiting it.
typedef void (kk_uv_external_wait_fun)(int64_t timeout_ms);
extern void kk_uv_loop_install_external_wait(kk_uv_external_wait_fun* wait, void (*wake)(void));
extern void kk_uv_external_signal_trigger(void);
extern kk_std_core_exn__error kk_uv_external_signal_setup(kk_box_t loop, kk_function_t cb, kk_context_t* ctx);

static void kk_imp_uv_wait(int64_t timeout_ms) {
  imp_host_wait_events((double)timeout_ms);
  if (imp_host_take_events_dirty()) kk_uv_external_signal_trigger();
}

static double kk_imp_refresh_ms(kk_context_t* ctx) {
  kk_unused(ctx);
  return imp_host_refresh_ms();
}

// the PLATFORM/RENDER split (see host.m): main parks in the GLFW event loop,
// waking the render thread's parked pump (the external signal) on input
static kk_unit_t kk_imp_platform_loop(kk_context_t* ctx) {
  kk_unused(ctx);
  imp_host_set_event_sink(&kk_uv_external_signal_trigger);
  imp_host_platform_loop();
  return kk_Unit;
}

static bool kk_imp_platform_split(kk_context_t* ctx) {
  kk_unused(ctx);
  return (imp_host_platform_split() != 0);
}

static kk_unit_t kk_imp_mark_split(kk_context_t* ctx) {
  kk_unused(ctx);
  imp_host_mark_split();
  return kk_Unit;
}

static kk_unit_t kk_imp_install_event_wait(kk_context_t* ctx) {
  kk_unused(ctx);
  kk_uv_loop_install_external_wait(&kk_imp_uv_wait, &imp_host_wake);
  return kk_Unit;
}

// save/restore the transform+clip stack, and intersect the clip with a rect --
// used to scroll: clip to the viewport, then paint the child at a y-offset.
static kk_unit_t kk_imp_save(kk_box_t builder, kk_context_t* ctx) {
  ImpellerDisplayListBuilderSave(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx));
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_restore(kk_box_t builder, kk_context_t* ctx) {
  ImpellerDisplayListBuilderRestore(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx));
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_clip_rect(kk_box_t builder, double x, double y, double w, double h,
                                  kk_context_t* ctx) {
  ImpellerRect rect = { (float)x, (float)y, (float)w, (float)h };
  ImpellerDisplayListBuilderClipRect(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx),
      &rect, kImpellerClipOperationIntersect);
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

// clip to a ROUNDED rect (uniform radius on all four corners) -- the native
// half of ui/widget's `clip`; the web half is `overflow:hidden` plus a
// matching `border-radius`. A zero radius goes through ClipRect, which is the
// cheaper path and what the scroll viewport already uses.
static kk_unit_t kk_imp_clip_rrect(kk_box_t builder, double x, double y, double w, double h,
                                   double r, kk_context_t* ctx) {
  ImpellerDisplayListBuilder b =
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx);
  ImpellerRect rect = { (float)x, (float)y, (float)w, (float)h };
  if (r > 0.0) {
    ImpellerPoint rad = { (float)r, (float)r };
    ImpellerRoundingRadii radii = { rad, rad, rad, rad };
    ImpellerDisplayListBuilderClipRoundedRect(b, &rect, &radii,
                                              kImpellerClipOperationIntersect);
  } else {
    ImpellerDisplayListBuilderClipRect(b, &rect, kImpellerClipOperationIntersect);
  }
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static double kk_imp_take_scroll_dy(kk_integer_t win, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  return imp_host_take_scroll_dy(w);
}

static double kk_imp_take_scroll_dx(kk_integer_t win, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  return imp_host_take_scroll_dx(w);
}

static double kk_imp_content_scale(kk_integer_t win, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  return imp_host_scale(w);
}

static double kk_imp_window_width(kk_integer_t win, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  return imp_host_width(w);
}
static double kk_imp_window_height(kk_integer_t win, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  return imp_host_height(w);
}
static double kk_imp_cursor_x(kk_integer_t win, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  return imp_host_cursor_x(w);
}

// synthetic input (ui/test-live): see imp_host_inject_* in host.m
static kk_unit_t kk_imp_inject_cursor(kk_integer_t win, double x, double y, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  imp_host_inject_cursor(w, x, y); return kk_Unit;
}
static kk_unit_t kk_imp_inject_pointer(kk_integer_t win, double kind, double x, double y, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  imp_host_inject_pointer(w, kind, x, y); return kk_Unit;
}
static kk_unit_t kk_imp_inject_char(kk_integer_t win, kk_integer_t cp, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  imp_host_inject_char(w, (unsigned int)kk_integer_clamp32(cp, ctx)); return kk_Unit;
}
static kk_unit_t kk_imp_inject_key(kk_integer_t win, kk_integer_t key, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  imp_host_inject_key(w, kk_integer_clamp32(key, ctx)); return kk_Unit;
}
static kk_unit_t kk_imp_inject_scroll(kk_integer_t win, double dx, double dy, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  imp_host_inject_scroll(w, dx, dy); return kk_Unit;
}
static double kk_imp_cursor_y(kk_integer_t win, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  return imp_host_cursor_y(w);
}
static kk_unit_t kk_imp_drain_rings(kk_context_t* ctx) {
  kk_unused(ctx);
  imp_host_drain_rings(); return kk_Unit;
}

static kk_box_t kk_imp_build(kk_box_t builder, kk_context_t* ctx) {
  g_live_dl++;
  ImpellerDisplayList dl = ImpellerDisplayListBuilderCreateDisplayListNew(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx));
  kk_box_drop(builder, ctx);
  return kk_cptr_raw_box(&kk_imp_dl_free, (void*)dl, ctx);
}

static kk_unit_t kk_imp_present(kk_integer_t win, kk_box_t dl, kk_context_t* ctx) {
  int w = kk_integer_clamp32(win, ctx);
  imp_host_present(w, kk_cptr_raw_unbox_borrowed(dl, ctx));
  kk_box_drop(dl, ctx);
  g_presents++;
  if (getenv("KOKA_IMP_STATS") != NULL && g_presents % 300 == 0) {
    extern long kk_uv_live_handles;
    fprintf(stderr, "[imp] presents=%ld live: paint=%ld builder=%ld dl=%ld para=%ld pb=%ld tex=%ld uvhandles=%ld\n",
            g_presents, g_live_paint, g_live_builder, g_live_dl, g_live_para, g_live_pb, g_live_tex, kk_uv_live_handles);
  }
  return kk_Unit;
}

// ---- text ---------------------------------------------------------------------

static ImpellerTypographyContext kk_imp_typo(void) {
  static ImpellerTypographyContext tc = NULL;
  if (tc == NULL) tc = ImpellerTypographyContextNew();
  return tc;
}

// SHAPED-PARAGRAPH CACHE: shaping is the expensive part of text, and paint
// re-draws the same strings frame after frame. Keyed by (text,size,rgba,
// width); one slot per hash bucket (collision = replace), so it is bounded
// and self-evicting. Single-threaded (only the render thread shapes).
#define KK_PARA_CACHE_SIZE 4096
typedef struct { char* key; ImpellerParagraph para; } kk_para_slot;
static kk_para_slot g_para_cache[KK_PARA_CACHE_SIZE];

static unsigned kk_para_hash(const char* s) {
  unsigned h = 2166136261u;
  while (*s) { h ^= (unsigned char)*s++; h *= 16777619u; }
  return h;
}

// layout `text` at `size` in `rgba`, wrapped to `width`: an immutable paragraph
static kk_box_t kk_imp_paragraph_uncached(kk_string_t text, double size,
                                 double r, double g, double b, double a,
                                 double width, kk_context_t* ctx) {
  ImpellerParagraphStyle style = ImpellerParagraphStyleNew();
  ImpellerPaint fg = ImpellerPaintNew();
  ImpellerColor color = { (float)r, (float)g, (float)b, (float)a, kImpellerColorSpaceSRGB };
  ImpellerPaintSetColor(fg, &color);
  ImpellerParagraphStyleSetForeground(style, fg);
  ImpellerParagraphStyleSetFontSize(style, (float)size);

  ImpellerParagraphBuilder pb = ImpellerParagraphBuilderNew(kk_imp_typo());
  ImpellerParagraphBuilderPushStyle(pb, style);
  kk_ssize_t len;
  const char* cbuf = kk_string_cbuf_borrow(text, &len, ctx);
  ImpellerParagraphBuilderAddText(pb, (const uint8_t*)cbuf, (uint32_t)len);
  ImpellerParagraph para = ImpellerParagraphBuilderBuildParagraphNew(pb, (float)width);
  kk_string_drop(text, ctx);

  ImpellerParagraphBuilderRelease(pb);
  ImpellerPaintRelease(fg);
  ImpellerParagraphStyleRelease(style);
  g_live_para++;
  return kk_cptr_raw_box(&kk_imp_para_free, (void*)para, ctx);
}

static kk_box_t kk_imp_paragraph(kk_string_t text, double size,
                                 double r, double g, double b, double a,
                                 double width, kk_context_t* ctx) {
  kk_ssize_t len;
  const char* cbuf = kk_string_cbuf_borrow(text, &len, ctx);
  char* key = NULL;
  (void)asprintf(&key, "%s\x01%.3f|%.4f,%.4f,%.4f,%.4f|%.2f", cbuf, size, r, g, b, a, width);
  if (key == NULL) return kk_imp_paragraph_uncached(text, size, r, g, b, a, width, ctx);
  kk_para_slot* slot = &g_para_cache[kk_para_hash(key) % KK_PARA_CACHE_SIZE];
  if (slot->key != NULL && strcmp(slot->key, key) == 0) {
    free(key);
    kk_string_drop(text, ctx);
    ImpellerParagraphRetain(slot->para);       // one ref for the returned box
    g_live_para++;
    return kk_cptr_raw_box(&kk_imp_para_free, (void*)slot->para, ctx);
  }
  kk_box_t boxed = kk_imp_paragraph_uncached(text, size, r, g, b, a, width, ctx);
  ImpellerParagraph para = (ImpellerParagraph)kk_cptr_raw_unbox_borrowed(boxed, ctx);
  if (slot->key != NULL) { free(slot->key); ImpellerParagraphRelease(slot->para); }
  slot->key = key;
  slot->para = para;
  ImpellerParagraphRetain(para);               // the cache's own ref
  return boxed;
}

static double kk_imp_para_height(kk_box_t para, kk_context_t* ctx) {
  double h = (double)ImpellerParagraphGetHeight(
      (ImpellerParagraph)kk_cptr_raw_unbox_borrowed(para, ctx));
  kk_box_drop(para, ctx);
  return h;
}

static double kk_imp_para_width(kk_box_t para, kk_context_t* ctx) {
  double w = (double)ImpellerParagraphGetLongestLineWidth(
      (ImpellerParagraph)kk_cptr_raw_unbox_borrowed(para, ctx));
  kk_box_drop(para, ctx);
  return w;
}

static kk_unit_t kk_imp_draw_paragraph(kk_box_t builder, kk_box_t para,
                                       double x, double y, kk_context_t* ctx) {
  ImpellerPoint point = { (float)x, (float)y };
  ImpellerDisplayListBuilderDrawParagraph(
      (ImpellerDisplayListBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx),
      (ImpellerParagraph)kk_cptr_raw_unbox_borrowed(para, ctx),
      &point);
  kk_box_drop(builder, ctx);
  kk_box_drop(para, ctx);
  return kk_Unit;
}

// ---- rich text: incremental multi-run paragraph builder ------------------
// mirrors kk_imp_paragraph_uncached's shape (style, add text, build) but
// split across separate calls so a `rich` widget's spans can each push
// their own style before/after the base run's text. NOT cached (see the
// task notes -- hashing an arbitrary span list isn't worth it yet).

static kk_box_t kk_imp_rich_begin(kk_context_t* ctx) {
  ImpellerParagraphBuilder pb = ImpellerParagraphBuilderNew(kk_imp_typo());
  // ImpellerParagraphBuilderNew is nullable per the SDK header (allocation
  // failure); NULL flows harmlessly through every kk_imp_rich_* call below
  // (each is guarded) and `kk_imp_para_builder_free`'s Release is already a
  // documented no-op on NULL.
  if (pb != NULL) g_live_pb++;
  return kk_cptr_raw_box(&kk_imp_para_builder_free, (void*)pb, ctx);
}

static kk_unit_t kk_imp_rich_push_style(kk_box_t builder, double size,
                                        double r, double g, double b, double a,
                                        kk_context_t* ctx) {
  ImpellerParagraphBuilder pb =
      (ImpellerParagraphBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx);
  if (pb != NULL) {
    ImpellerParagraphStyle style = ImpellerParagraphStyleNew();
    ImpellerColor c = { (float)r, (float)g, (float)b, (float)a, kImpellerColorSpaceSRGB };
    ImpellerPaint fg = ImpellerPaintNew();
    ImpellerPaintSetColor(fg, &c);
    ImpellerParagraphStyleSetForeground(style, fg);
    ImpellerParagraphStyleSetFontSize(style, (float)size);
    ImpellerParagraphBuilderPushStyle(pb, style);
    ImpellerPaintRelease(fg);
    ImpellerParagraphStyleRelease(style);
  }
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_rich_add_text(kk_box_t builder, kk_string_t text, kk_context_t* ctx) {
  ImpellerParagraphBuilder pb =
      (ImpellerParagraphBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx);
  if (pb != NULL) {
    kk_ssize_t len;
    const char* cbuf = kk_string_cbuf_borrow(text, &len, ctx);
    ImpellerParagraphBuilderAddText(pb, (const uint8_t*)cbuf, (uint32_t)len);
  }
  kk_string_drop(text, ctx);
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static kk_unit_t kk_imp_rich_pop_style(kk_box_t builder, kk_context_t* ctx) {
  ImpellerParagraphBuilder pb =
      (ImpellerParagraphBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx);
  if (pb != NULL) ImpellerParagraphBuilderPopStyle(pb);
  kk_box_drop(builder, ctx);
  return kk_Unit;
}

static kk_box_t kk_imp_rich_build(kk_box_t builder, double width, kk_context_t* ctx) {
  ImpellerParagraphBuilder pb =
      (ImpellerParagraphBuilder)kk_cptr_raw_unbox_borrowed(builder, ctx);
  ImpellerParagraph para = (pb == NULL) ? NULL
      : ImpellerParagraphBuilderBuildParagraphNew(pb, (float)width);
  kk_box_drop(builder, ctx);
  // ImpellerParagraphBuilderBuildParagraphNew is nullable too; NULL flows
  // harmlessly through height/width/line-count/line-metrics/glyph-bounds-at
  // (each already NULL-checks or the SDK no-ops on NULL) same as above.
  if (para != NULL) g_live_para++;
  return kk_cptr_raw_box(&kk_imp_para_free, (void*)para, ctx);
}

// ---- rich text: glyph-info-based span rect resolution ---------------------
//
// A `text-span` is indexed by CODEPOINT offset into `content` (ui/widget's
// convention), but Impeller's glyph-info/line-metrics API is indexed by
// UTF-16 CODE UNIT. `kk_imp_cp_to_u16` walks `content`'s UTF-8 decoding up
// to `cp_index` codepoints and sums the UTF-16 units each one takes (1 for
// BMP, 2 -- a surrogate pair -- above it), giving the code-unit index the
// glyph-info calls need.
static size_t kk_imp_cp_to_u16(const uint8_t* buf, kk_ssize_t len, kk_ssize_t cp_index) {
  size_t u16 = 0;
  const uint8_t* p = buf;
  const uint8_t* end = buf + len;
  for (kk_ssize_t i = 0; i < cp_index && p < end; i++) {
    kk_ssize_t n;
    kk_char_t c = kk_utf8_read(p, &n);
    if (n <= 0) break;   // malformed byte sequence -- don't count a phantom unit
    u16 += ((uint32_t)c > 0xFFFFU) ? 2 : 1;
    p += n;
  }
  return u16;
}

static kk_integer_t kk_imp_cp_to_u16_raw(kk_string_t content, kk_integer_t cp,
                                         kk_context_t* ctx) {
  kk_ssize_t len;
  const char* cbuf = kk_string_cbuf_borrow(content, &len, ctx);
  size_t u16 = kk_imp_cp_to_u16((const uint8_t*)cbuf, len, kk_integer_clamp32(cp, ctx));
  kk_string_drop(content, ctx);
  return kk_integer_from_int((int)u16, ctx);
}

// paragraph line metrics: a boxed handle (like `paragraph`/`rich-builder`)
// so Koka can query per-line UTF-16 code-unit ranges without re-fetching the
// whole ImpellerLineMetrics object on every call.
static kk_box_t kk_imp_para_line_metrics(kk_box_t para, kk_context_t* ctx) {
  ImpellerLineMetrics lm = ImpellerParagraphGetLineMetrics(
      (ImpellerParagraph)kk_cptr_raw_unbox_borrowed(para, ctx));
  kk_box_drop(para, ctx);
  if (lm == NULL) return kk_cptr_raw_box(&kk_imp_line_metrics_free, NULL, ctx);
  ImpellerLineMetricsRetain(lm);
  return kk_cptr_raw_box(&kk_imp_line_metrics_free, (void*)lm, ctx);
}

static kk_integer_t kk_imp_line_count(kk_box_t para, kk_context_t* ctx) {
  uint32_t n = ImpellerParagraphGetLineCount(
      (ImpellerParagraph)kk_cptr_raw_unbox_borrowed(para, ctx));
  kk_box_drop(para, ctx);
  return kk_integer_from_int((int)n, ctx);
}

static kk_integer_t kk_imp_line_start_u16(kk_box_t lm, kk_integer_t line, kk_context_t* ctx) {
  void* p = kk_cptr_raw_unbox_borrowed(lm, ctx);
  size_t idx = (p == NULL) ? 0
      : ImpellerLineMetricsGetCodeUnitStartIndex((ImpellerLineMetrics)p,
                                                  (size_t)kk_integer_clamp32(line, ctx));
  kk_box_drop(lm, ctx);
  return kk_integer_from_int((int)idx, ctx);
}

static kk_integer_t kk_imp_line_end_u16(kk_box_t lm, kk_integer_t line, kk_context_t* ctx) {
  void* p = kk_cptr_raw_unbox_borrowed(lm, ctx);
  // ExcludingWhitespace (not the plain CodeUnitEndIndex, which includes
  // trailing whitespace the line wrapped on): a span's hit-rect should
  // bound its own glyphs, not the wrap's trailing space.
  size_t idx = (p == NULL) ? 0
      : ImpellerLineMetricsGetCodeUnitEndIndexExcludingWhitespace((ImpellerLineMetrics)p,
                                                (size_t)kk_integer_clamp32(line, ctx));
  kk_box_drop(lm, ctx);
  return kk_integer_from_int((int)idx, ctx);
}

// last resolved glyph bounds -- single-threaded render-thread scratch state,
// the same "stash then separate getters" idiom `kk_imp_decode`'s
// `decoded-w`/`decoded-h` already uses; safe as long as no other
// glyph-bounds-at call is interleaved before the getters run (true of every
// call site: `impeller.kk`'s wrapper reads all four fields back-to-back).
static double g_glyph_x = 0.0, g_glyph_y = 0.0, g_glyph_w = 0.0, g_glyph_h = 0.0;

static bool kk_imp_glyph_bounds_at(kk_box_t para, kk_integer_t code_unit_index, kk_context_t* ctx) {
  ImpellerParagraph p = (ImpellerParagraph)kk_cptr_raw_unbox_borrowed(para, ctx);
  ImpellerGlyphInfo gi = ImpellerParagraphCreateGlyphInfoAtCodeUnitIndexNew(
      p, (size_t)kk_integer_clamp32(code_unit_index, ctx));
  kk_box_drop(para, ctx);
  if (gi == NULL) return false;
  ImpellerRect bounds;
  ImpellerGlyphInfoGetGraphemeClusterBounds(gi, &bounds);
  // EMPIRICALLY (not per the header comment): this SDK build's
  // GetGraphemeClusterBounds fills `bounds.x` with the glyph's VERTICAL
  // (line) position and `bounds.y` with its HORIZONTAL (within-line)
  // position -- verified against a real multi-line paragraph (x constant
  // within a line and jumping by line-height across lines; y increasing
  // monotonically by each glyph's own width within a line). Swapped here so
  // the (x,y,w,h) this module exposes matches every OTHER rect in ui/widget
  // (x = horizontal, y = vertical, top-left origin).
  g_glyph_x = (double)bounds.y;
  g_glyph_y = (double)bounds.x;
  g_glyph_w = (double)bounds.width;
  g_glyph_h = (double)bounds.height;
  ImpellerGlyphInfoRelease(gi);
  return true;
}

static double kk_imp_glyph_bounds_x(kk_context_t* ctx) { kk_unused(ctx); return g_glyph_x; }
static double kk_imp_glyph_bounds_y(kk_context_t* ctx) { kk_unused(ctx); return g_glyph_y; }
static double kk_imp_glyph_bounds_w(kk_context_t* ctx) { kk_unused(ctx); return g_glyph_w; }
static double kk_imp_glyph_bounds_h(kk_context_t* ctx) { kk_unused(ctx); return g_glyph_h; }
