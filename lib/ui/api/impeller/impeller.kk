/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Koka bindings for the Impeller interop C API (Flutter's rendering engine
// as a standalone 2D library) plus a small GLFW/Metal window host. Impeller
// handles are refcounted (Retain/Release), which maps one-to-one onto
// Perceus ownership: every handle here is a Perceus-owned box whose final
// drop Releases the Impeller object -- "release is a drop", exactly like
// the DOM externref slots in web-ui.
module ui/api/impeller/impeller

import std/num/float64
import std/num/int32
import ui/widget
import ui/transform   // mat4 (row-major 4x4) for `transform`

extern import
  c file "shim.c"

// an immutable paint (color, for now)
pub value struct paint(obj : any)

// a display-list builder (single-use: `build` consumes it)
pub value struct builder(obj : any)

// an immutable, replayable display list
pub value struct display-list(obj : any)

// an immutable, laid-out paragraph
pub value struct paragraph(obj : any)

// ----------------------------------------------------------------
// window host

extern init-raw(title : string, width : int, height : int) : ioc bool
  c "kk_imp_init"

pub fun init(title : string, width : int, height : int) : <ioc,exn> ()
  if !init-raw(title, width, height)
    then throw("impeller: could not initialize the window host (Metal/GLFW)")

extern should-close-raw( win : int ) : ioc bool
  c "kk_imp_should_close"
pub fun should-close( win : int = 0 ) : ioc bool
  should-close-raw(win)

// wait for events (up to one frame interval)
pub extern poll-events() : ioc ()
  c "kk_imp_poll"

// hand the libuv loop's idle sleep to GLFW (the embed pattern; see
// std/async/api/uv/evloop.c): input wakes the loop instantly, idle burns no
// CPU, uv timers still fire on time. Call once, after the window exists.
pub extern install-event-wait() : ioc ()
  c "kk_imp_install_event_wait"

// park until the host waiter reports input (single-shot uv_async; the waiter
// triggers it after processing GLFW events that touched our callbacks)
pub extern input-signal-setup( evloop : any, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  c "kk_uv_external_signal_setup"

// draw a pre-recorded display list into the builder (repaint boundaries)
extern draw-dl-raw( b : any, dl : any, opacity : float64 ) : ioc ()
  c "kk_imp_draw_dl"
pub fun draw-display-list( b : builder, dl : display-list, opacity : float64 = 1.0 ) : ioc ()
  draw-dl-raw(b.obj, dl.obj, opacity)

// KOKA_UI_REPAINT_RAINBOW=1: tint repaint boundaries, new color per re-record
pub extern debug-repaint() : ioc bool
  c "kk_imp_debug_repaint"

// present counter under the repaint rainbow (border color rotation)
pub extern rainbow-seq() : ioc int
  c "kk_imp_rainbow_seq"

// synthetic input injection (ui/test-live middleman): same rings, same wake
// as real GLFW events -- the pump cannot tell the difference
extern inject-cursor-raw( win : int, x : float64, y : float64 ) : ioc ()
  c "kk_imp_inject_cursor"
pub fun inject-cursor( x : float64, y : float64, win : int = 0 ) : ioc ()
  inject-cursor-raw(win, x, y)

extern inject-pointer-raw( win : int, kind : float64, x : float64, y : float64 ) : ioc ()
  c "kk_imp_inject_pointer"
pub fun inject-pointer( kind : float64, x : float64, y : float64, win : int = 0 ) : ioc ()
  inject-pointer-raw(win, kind, x, y)

extern inject-char-raw( win : int, cp : int ) : ioc ()
  c "kk_imp_inject_char"
pub fun inject-char( cp : int, win : int = 0 ) : ioc ()
  inject-char-raw(win, cp)

extern inject-key-raw( win : int, key : int ) : ioc ()
  c "kk_imp_inject_key"
pub fun inject-key( key : int, win : int = 0 ) : ioc ()
  inject-key-raw(win, key)

extern inject-scroll-raw( win : int, dx : float64, dy : float64 ) : ioc ()
  c "kk_imp_inject_scroll"
pub fun inject-scroll( dx : float64, dy : float64, win : int = 0 ) : ioc ()
  inject-scroll-raw(win, dx, dy)

// discard every pending event in all four host rings (pointer, char, key,
// scroll) without processing them -- ui/test-live calls this between
// scenarios so a tail burst that outraces the scenario's own settle cannot
// be drained LATE, against the next scenario's freshly-reset fields
pub extern drain-rings() : ioc ()
  c "kk_imp_drain_rings"

// the display's refresh interval in ms (120Hz ProMotion -> ~8.3)
pub extern refresh-ms() : ioc float64
  c "kk_imp_refresh_ms"

// the platform/render split: `platform-loop` parks the MAIN thread in the GLFW
// event wait for the app's lifetime (callbacks wake the render thread --
// including from inside the Cocoa modal resize loop); `mark-split` arms the
// split before the render thread spawns; `platform-split` queries it.
pub extern platform-loop() : ioc ()
  c "kk_imp_platform_loop"
pub extern mark-split() : ioc ()
  c "kk_imp_mark_split"
pub extern platform-split() : ioc bool
  c "kk_imp_platform_split"

// dequeue a pending pointer event: 0 none, 1 press, 2 release; the
// position is `pointer-x`/`pointer-y`
pub extern next-pointer() : ioc int
  c "kk_imp_next_pointer"

pub extern pointer-x() : ioc float64
  c "kk_imp_pointer_x"

pub extern pointer-y() : ioc float64
  c "kk_imp_pointer_y"

// the window of the last DRAINED pointer event (next-pointer)
pub extern pointer-win() : ioc int
  c "kk_imp_pointer_win"

// dequeue a typed character (empty string when none)
pub extern next-char() : ioc string
  c "kk_imp_next_char"

// the window of the last DRAINED char event (next-char)
pub extern char-win() : ioc int
  c "kk_imp_char_win"

// dequeue a special key: 0 none, 1 backspace, 2 enter, 3 escape
pub extern next-key() : ioc int
  c "kk_imp_next_key"

// the window of the last DRAINED key event (next-key)
pub extern key-win() : ioc int
  c "kk_imp_key_win"

// the window the pending (undrained) scroll delta is tagged for
pub extern scroll-win() : ioc int
  c "kk_imp_scroll_win"

// the window that last saw the cursor (move, click, or synthetic inject)
pub extern cursor-win() : ioc int
  c "kk_imp_cursor_win"

pub extern shutdown() : ioc ()
  c "kk_imp_shutdown"

// ----------------------------------------------------------------
// titled windows: render->main command ring (host.m). Create/destroy/
// retitle/reposition are all deferred to the main thread; these calls just
// enqueue (or read cached table state) and return immediately.

// allocate a table slot and enqueue creation on the main thread; returns the
// slot id right away -- window-alive reports false until the main thread
// drains the create command
extern open-window-raw( chrome : int, title : string, w : float64, h : float64 ) : ioc int
  c "kk_imp_open_window"
pub fun open-window( chrome : int, title : string, w : float64, h : float64 ) : ioc int
  open-window-raw(chrome, title, w, h)

pub extern close-window( win : int ) : ioc ()
  c "kk_imp_close_window"

extern set-window-title-raw( win : int, title : string ) : ioc ()
  c "kk_imp_set_window_title"
pub fun set-window-title( win : int, title : string ) : ioc ()
  set-window-title-raw(win, title)

pub extern set-window-pos( win : int, x : float64, y : float64 ) : ioc ()
  c "kk_imp_set_window_pos"

// created AND not close-requested
pub extern window-alive( win : int ) : ioc bool
  c "kk_imp_window_alive"

// frames actually presented to `win` (0 for a blank window -- test probe)
pub extern present-count( win : int ) : ioc int
  c "kk_imp_present_count"

// sticky until close-window: the user hit the close button
pub extern window-close-requested( win : int ) : ioc bool
  c "kk_imp_window_close_requested"

extern main-origin-x-raw() : ioc float64
  c "kk_imp_main_origin_x"
extern main-origin-y-raw() : ioc float64
  c "kk_imp_main_origin_y"

// screen coords of the main window (slot 0), for Panel placement
pub fun main-window-origin() : ioc (float64, float64)
  (main-origin-x-raw(), main-origin-y-raw())

// ----------------------------------------------------------------
// painting

extern paint-raw(r : float64, g : float64, b : float64, a : float64) : ioc any
  c "kk_imp_paint"

// a solid paint of the given color
// Colours are PACKED into one int32 each. Koka substitutes C extern arguments
// by single-digit `#N`, so an extern with more than NINE parameters silently
// emits `#1` followed by a literal `0` for the tenth -- the eight loose colour
// components this needs would have produced `kk_imp_paint_lgrad(sx,...,sx0,
// sx1,sx2)`, which happens to fail to compile here but is a miscompilation,
// not a diagnostic.
extern paint-lgrad-raw( sx : float64, sy : float64, ex : float64, ey : float64,
                        c0 : int32, c1 : int32 ) : ioc any
  c "kk_imp_paint_lgrad"

fun pack8( c : color ) : int32
  fun ch( v : float64 ) : int
    val u = if v < 0.0 then 0.0 elif v > 1.0 then 1.0 else v
    (u * 255.0).int
  (ch(c.r) * 16777216 + ch(c.g) * 65536 + ch(c.b) * 256 + ch(c.a)).int32

// a paint filled with a two-stop linear gradient between ABSOLUTE points
pub fun linear-paint( x0 : float64, y0 : float64, x1 : float64, y1 : float64,
                      c0 : color, c1 : color ) : ioc paint
  Paint(paint-lgrad-raw(x0, y0, x1, y1, c0.pack8, c1.pack8))

extern paint-rgrad-raw( cx : float64, cy : float64, rad : float64,
                        c0 : int32, c1 : int32 ) : ioc any
  c "kk_imp_paint_rgrad"

// a paint filled with a two-stop radial gradient at an ABSOLUTE centre/radius
pub fun radial-paint( cx : float64, cy : float64, rad : float64,
                      c0 : color, c1 : color ) : ioc paint
  Paint(paint-rgrad-raw(cx, cy, rad, c0.pack8, c1.pack8))

pub fun solid(c : color) : ioc paint
  Paint(paint-raw(c.r, c.g, c.b, c.a))

extern builder-raw() : ioc any
  c "kk_imp_builder"

pub fun builder() : ioc builder
  Builder(builder-raw())

extern draw-paint-raw(b : any, p : any) : ioc ()
  c "kk_imp_draw_paint"

// flood the surface with `p` (the background)
pub fun draw-background(b : builder, p : paint) : ioc ()
  draw-paint-raw(b.obj, p.obj)

extern draw-rect-raw(b : any, x : float64, y : float64, w : float64, h : float64, p : any) : ioc ()
  c "kk_imp_draw_rect"

pub fun draw-rect(b : builder, x : float64, y : float64, w : float64, h : float64, p : paint) : ioc ()
  draw-rect-raw(b.obj, x, y, w, h, p.obj)

extern draw-rrect-raw(b : any, x : float64, y : float64, w : float64, h : float64, radius : float64, p : any) : ioc ()
  c "kk_imp_draw_rrect"

pub fun draw-rounded-rect(b : builder, x : float64, y : float64, w : float64, h : float64, radius : float64, p : paint) : ioc ()
  draw-rrect-raw(b.obj, x, y, w, h, radius, p.obj)

extern scale-raw(b : any, sx : float64, sy : float64) : ioc ()
  c "kk_imp_scale"

// scale subsequent drawing (used for retina rendering)
pub fun scale(b : builder, sx : float64, sy : float64) : ioc ()
  scale-raw(b.obj, sx, sy)

// transform+clip save stack, and clip to a rectangle -- a scroll region clips
// to its viewport then paints its child translated by the scroll offset
extern save-raw(b : any) : ioc ()
  c "kk_imp_save"
extern restore-raw(b : any) : ioc ()
  c "kk_imp_restore"
extern clip-rect-raw(b : any, x : float64, y : float64, w : float64, h : float64) : ioc ()
  c "kk_imp_clip_rect"

extern clip-rrect-raw(b : any, x : float64, y : float64, w : float64, h : float64, r : float64) : ioc ()
  c "kk_imp_clip_rrect"

extern translate-raw(b : any, tx : float64, ty : float64) : ioc ()
  c "kk_imp_translate"
extern rotate-raw(b : any, degrees : float64) : ioc ()
  c "kk_imp_rotate"
extern transform-raw(b : any, m : vector<float64>) : ioc ()
  c "kk_imp_transform"

pub fun save(b : builder) : ioc ()
  save-raw(b.obj)
pub fun restore(b : builder) : ioc ()
  restore-raw(b.obj)
// translate / rotate subsequent drawing (rotation is about the CURRENT origin:
// translate to the pivot, rotate, translate back)
pub fun translate(b : builder, tx : float64, ty : float64) : ioc ()
  translate-raw(b.obj, tx, ty)
pub fun rotate(b : builder, degrees : float64) : ioc ()
  rotate-raw(b.obj, degrees)
// concat a full 4x4 (perspective/tilt) transform onto the save stack (see
// `ui/transform`'s `mat4`, ROW-major); the shim transposes to Impeller's
// column-major `ImpellerMatrix`
pub fun transform(b : builder, mtx : mat4) : ioc ()
  transform-raw(b.obj, mtx.m)
pub fun clip-rect(b : builder, x : float64, y : float64, w : float64, h : float64) : ioc ()
  clip-rect-raw(b.obj, x, y, w, h)

// clip to a rounded rect (uniform radius); r <= 0 falls through to clip-rect
pub fun clip-rrect(b : builder, x : float64, y : float64, w : float64, h : float64, r : float64) : ioc ()
  clip-rrect-raw(b.obj, x, y, w, h, r)

// drain the accumulated mouse-wheel / trackpad delta (logical points) since the
// last call; applied to the scroll region under the cursor
extern take-scroll-dy-raw( win : int ) : ioc float64
  c "kk_imp_take_scroll_dy"
pub fun take-scroll-dy( win : int = 0 ) : ioc float64
  take-scroll-dy-raw(win)

// horizontal wheel/trackpad delta since the last call (for horizontal regions)
extern take-scroll-dx-raw( win : int ) : ioc float64
  c "kk_imp_take_scroll_dx"
pub fun take-scroll-dx( win : int = 0 ) : ioc float64
  take-scroll-dx-raw(win)

// the backing scale factor of the window (2.0 on retina)
extern content-scale-raw( win : int ) : ioc float64
  c "kk_imp_content_scale"
pub fun content-scale( win : int = 0 ) : ioc float64
  content-scale-raw(win)

// the current window size in logical points (updates when the user resizes)
extern window-width-raw( win : int ) : ioc float64
  c "kk_imp_window_width"
pub fun window-width( win : int = 0 ) : ioc float64
  window-width-raw(win)

extern window-height-raw( win : int ) : ioc float64
  c "kk_imp_window_height"
pub fun window-height( win : int = 0 ) : ioc float64
  window-height-raw(win)

// the LIVE cursor position in logical points (for hover; unlike pointer-x/y it
// updates continuously, not just on press/release)
extern cursor-x-raw( win : int ) : ioc float64
  c "kk_imp_cursor_x"
pub fun cursor-x( win : int = 0 ) : ioc float64
  cursor-x-raw(win)

extern cursor-y-raw( win : int ) : ioc float64
  c "kk_imp_cursor_y"
pub fun cursor-y( win : int = 0 ) : ioc float64
  cursor-y-raw(win)

extern build-raw(b : any) : ioc any
  c "kk_imp_build"

pub fun build(b : builder) : ioc display-list
  Display-list(build-raw(b.obj))

extern present-raw(win : int, dl : any) : ioc ()
  c "kk_imp_present"

// draw a display list onto the next frame and present it
pub fun present(dl : display-list, win : int = 0) : ioc ()
  present-raw(win, dl.obj)

// ----------------------------------------------------------------
// text

extern paragraph-raw(text : string, size : float64, r : float64, g : float64, b : float64, a : float64, width : float64) : ioc any
  c "kk_imp_paragraph"

// lay out `text` at `size` in `color`, wrapped to `width`
pub fun paragraph(text : string, size : float64, color : color, width : float64 = 10000.0) : ioc paragraph
  Paragraph(paragraph-raw(text, size, color.r, color.g, color.b, color.a, width))

extern para-height-raw(p : any) : ioc float64
  c "kk_imp_para_height"

// the laid-out height of a paragraph
pub fun height(p : paragraph) : ioc float64
  para-height-raw(p.obj)

extern para-width-raw(p : any) : ioc float64
  c "kk_imp_para_width"

// the longest laid-out line width of a paragraph
pub fun width(p : paragraph) : ioc float64
  para-width-raw(p.obj)

extern draw-paragraph-raw(b : any, p : any, x : float64, y : float64) : ioc ()
  c "kk_imp_draw_paragraph"

pub fun draw-paragraph(b : builder, p : paragraph, x : float64, y : float64) : ioc ()
  draw-paragraph-raw(b.obj, p.obj, x, y)

// ----------------------------------------------------------------
// rich text: an INCREMENTAL paragraph builder (Impeller's own mechanism for
// mixing styles within one flowing paragraph -- PushStyle/AddText/PopStyle,
// called repeatedly, then one Build). Mirrors `paragraph`'s single-run shape
// but split across separate calls so a `rich` widget's spans can each open
// their own style, nested inside the base run's.

pub value struct rich-builder(obj : any)

extern rich-begin-raw() : ioc any
  c "kk_imp_rich_begin"
pub fun rich-begin() : ioc rich-builder
  Rich-builder(rich-begin-raw())

extern rich-push-style-raw(b : any, size : float64, r : float64, g : float64, b2 : float64, a : float64) : ioc ()
  c "kk_imp_rich_push_style"
// param named `rb` (not `b`) -- `b` would shadow `color`'s own `.b` (blue)
// field accessor below
pub fun push-style(rb : rich-builder, size : float64, color : color) : ioc ()
  rich-push-style-raw(rb.obj, size, color.r, color.g, color.b, color.a)

extern rich-add-text-raw(b : any, text : string) : ioc ()
  c "kk_imp_rich_add_text"
pub fun add-text(rb : rich-builder, text : string) : ioc ()
  rich-add-text-raw(rb.obj, text)

extern rich-pop-style-raw(b : any) : ioc ()
  c "kk_imp_rich_pop_style"
pub fun pop-style(rb : rich-builder) : ioc ()
  rich-pop-style-raw(rb.obj)

extern rich-build-raw(b : any, width : float64) : ioc any
  c "kk_imp_rich_build"
// `build` (unqualified) already names `builder`'s display-list build above --
// this is `rich-builder`'s own (a paragraph, not a display list). Param
// named `rb` throughout this rich-builder API (not `b`) for consistency
// with `push-style` (where `b` would shadow `color`'s own `.b` accessor).
pub fun rich-build(rb : rich-builder, width : float64 = 10000.0) : ioc paragraph
  Paragraph(rich-build-raw(rb.obj, width))

// ----------------------------------------------------------------
// rich text: glyph-info-based span rect resolution. `measure-rich`'s real
// (non-test) handler builds the same multi-run paragraph `rich`'s paint case
// does, then resolves each span's rect(s) by walking Impeller's glyph info /
// line metrics -- CODEPOINT offsets in (ui/widget's `text-span` convention)
// are converted to the UTF-16 code-unit indices Impeller's glyph API wants.

// convert a CODEPOINT offset into `content` to the UTF-16 code-unit index
// Impeller's glyph-info calls index by (`content` re-decoded fresh each
// call -- span counts are small, not worth caching a decode table for).
extern cp-to-u16-raw(content : string, cp : int) : ioc int
  c "kk_imp_cp_to_u16_raw"
pub fun cp-to-u16(content : string, cp : int) : ioc int
  cp-to-u16-raw(content, cp)

// a paragraph's line metrics: one boxed handle so per-line queries don't
// re-fetch the whole ImpellerLineMetrics object each time.
pub value struct line-metrics(obj : any)

extern line-metrics-raw(p : any) : ioc any
  c "kk_imp_para_line_metrics"
pub fun line-metrics(p : paragraph) : ioc line-metrics
  Line-metrics(line-metrics-raw(p.obj))

extern line-count-raw(p : any) : ioc int
  c "kk_imp_line_count"
pub fun line-count(p : paragraph) : ioc int
  line-count-raw(p.obj)

extern line-start-raw(lm : any, line : int) : ioc int
  c "kk_imp_line_start_u16"
// the UTF-16 code-unit index the line starts at (inclusive)
pub fun line-start(lm : line-metrics, line : int) : ioc int
  line-start-raw(lm.obj, line)

extern line-end-raw(lm : any, line : int) : ioc int
  c "kk_imp_line_end_u16"
// the UTF-16 code-unit index the line ends at (exclusive)
pub fun line-end(lm : line-metrics, line : int) : ioc int
  line-end-raw(lm.obj, line)

extern glyph-bounds-at-raw(p : any, code-unit-index : int) : ioc bool
  c "kk_imp_glyph_bounds_at"
extern glyph-bounds-x-raw() : ioc float64
  c "kk_imp_glyph_bounds_x"
extern glyph-bounds-y-raw() : ioc float64
  c "kk_imp_glyph_bounds_y"
extern glyph-bounds-w-raw() : ioc float64
  c "kk_imp_glyph_bounds_w"
extern glyph-bounds-h-raw() : ioc float64
  c "kk_imp_glyph_bounds_h"

// the grapheme-cluster bounds (x,y,w,h, relative to the PARAGRAPH's own
// origin) of the glyph at `code-unit-index` (UTF-16), or `Nothing` past the
// end of the text.
pub fun glyph-bounds-at(p : paragraph, code-unit-index : int) : ioc maybe<(float64,float64,float64,float64)>
  if glyph-bounds-at-raw(p.obj, code-unit-index) then
    Just((glyph-bounds-x-raw(), glyph-bounds-y-raw(), glyph-bounds-w-raw(), glyph-bounds-h-raw()))
  else Nothing

// ----------------------------------------------------------------
// images: decode (stb_image) + GPU texture upload. A texture is a RAW Impeller
// handle carried as an `int` (the pointer value) with EXPLICIT lifetime -- the
// backend's identity cache creates one per image owner and `texture-release`s
// it when the owner unmounts. Decode is a plain file read; the upload MUST run
// on the render thread (that is where the Impeller context lives).

extern decode-ptr-raw( path : string ) : ioc int
  c "kk_imp_decode"
extern decoded-w-raw() : ioc int
  c "kk_imp_decoded_w"
extern decoded-h-raw() : ioc int
  c "kk_imp_decoded_h"

// decode `path` to native-size RGBA. `Just((buf, w, h))` on success (`buf` is an
// opaque pointer held C-side, to be consumed EXACTLY once by `upload-pixels`),
// `Nothing` on failure (missing file / unsupported format).
pub fun decode-image( path : string ) : ioc maybe<(int, int, int)>
  val p = decode-ptr-raw(path)
  if p == 0 then Nothing
  else Just((p, decoded-w-raw(), decoded-h-raw()))

// async-image primitives (task #53): the decode (off render thread) and the
// upload (ON the render thread) are SPLIT so `future-boundary`'s `run` can run
// the decode in `compute` and hand the pixel buffer back for a render-thread
// upload. `decode-path`/`decode-bytes` return `(bufptr, w, h)` WITHOUT uploading
// (the buffer is consumed later by `upload-pixels`); `upload-rgba` is the
// no-decode FromPixels path (already-RGBA bytes straight to a texture).

// `decode-path` is `decode-image` under the split's name (a plain file read +
// stbi decode; safe to run on a worker thread -- no GPU/Impeller context needed).
pub fun decode-path( path : string ) : ioc maybe<(int, int, int)>
  decode-image(path)

extern decode-bytes-ptr-raw( bytes : vector<int8> ) : ioc int
  c "kk_imp_decode_bytes"

// decode in-memory encoded bytes (PNG/JPEG) to native-size RGBA, like
// `decode-path` but via `stbi_load_from_memory`. Same buffer-ownership contract.
pub fun decode-bytes( bytes : vector<int8> ) : ioc maybe<(int, int, int)>
  val p = decode-bytes-ptr-raw(bytes)
  if p == 0 then Nothing
  else Just((p, decoded-w-raw(), decoded-h-raw()))

// upload a decoded buffer (from `decode-path`/`decode-bytes`) as a GPU texture
// (render thread ONLY). Consumes `buf`. Returns the texture handle, or 0 on fail.
pub extern upload-pixels( buf : int, w : int, h : int ) : ioc int
  c "kk_imp_texture_create"

// upload an already-decoded RGBA vector (FromPixels -- no decode step) as a GPU
// texture (render thread ONLY). Returns the texture handle, or 0 on failure.
pub extern upload-rgba( rgba : vector<int8>, w : int, h : int ) : ioc int
  c "kk_imp_upload_rgba"

// upload a decoded buffer as a GPU texture (render thread). Consumes `buf`.
// Returns the texture handle, or 0 on failure. (Retained name for the Sync
// paint path in backend.kk; `upload-pixels` is the async-split alias.)
pub extern texture-create( buf : int, w : int, h : int ) : ioc int
  c "kk_imp_texture_create"

// the 8 rect coords go through a vector (the `transform` idiom): Koka's
// auto-generated wrapper for a `c "name"` extern caps at 9 args, and builder +
// texture + 8 floats is 10 -- the vector collapses them to one arg
extern draw-texture-rect-raw( b : any, tex : int, r : vector<float64> ) : ioc ()
  c "kk_imp_draw_texture_rect"

// draw a source sub-rect of `tex` into a destination rect (builder space).
// `r` = [sx, sy, sw, sh, dx, dy, dw, dh]
pub fun draw-texture-rect( b : builder, tex : int,
                           sx : float64, sy : float64, sw : float64, sh : float64,
                           dx : float64, dy : float64, dw : float64, dh : float64 ) : ioc ()
  draw-texture-rect-raw(b.obj, tex, [sx, sy, sw, sh, dx, dy, dw, dh].vector)

// release a texture handle (GPU memory freed); safe on 0
pub extern texture-release( tex : int ) : ioc ()
  c "kk_imp_texture_release"

// currently-live GPU textures (successful texture-create minus texture-release
// with a non-zero handle) -- test probe for the image-retention leak guard
pub extern live-textures() : ioc int
  c "kk_imp_live_textures"
