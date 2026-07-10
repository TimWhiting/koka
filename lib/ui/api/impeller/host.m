/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Window/present host for the Koka Impeller sample: the only Objective-C in
// the project (GLFW window + CAMetalLayer + surface present). Everything
// else -- display lists, paints, text -- is called directly from the Koka
// fringe (shim.c) through the plain-C impeller.h. Plain C ABI throughout;
// compiled into libimpellerhost.dylib by build.kk.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <stdint.h>

#define GLFW_INCLUDE_NONE
#include "GLFW/glfw3.h"
#define GLFW_EXPOSE_NATIVE_COCOA
#import "GLFW/glfw3native.h"

#include "impeller.h"

#import <AppKit/AppKit.h>
#import <Metal/Metal.h>
#import <QuartzCore/QuartzCore.h>

// ---- the window TABLE -------------------------------------------------------
// Slot 0 is the main/titled window, filled by imp_host_init; slots 1.. are
// reserved for future panel windows (none are created yet -- this task only
// re-homes the existing single-window state into slot 0, behavior-preserving).
// GLFW callbacks discover their slot via glfwGetWindowUserPointer (set to the
// slot index at creation time) instead of assuming the one global window.
#define IMP_MAX_WINDOWS 16
typedef struct {
  GLFWwindow*   window;
  CAMetalLayer* layer;
  double        scale;              // backing scale factor (retina)
  volatile double win_w, win_h;      // cached logical size (render-thread read)
  double        cursor_x, cursor_y; int cursor_seen;
  int           chrome;              // 0 titled/main, 1 panel
  volatile int  alive;
  volatile int  close_requested;    // sticky: user hit the close button (win != 0 only)
  volatile int  pending;            // slot claimed by open-window, CREATE not yet drained
  void*         pending_dl;         // split mode: this window's published display list (g_present_mutex)
  volatile long presented;          // frames actually presented to THIS window (test probe)
} imp_win;
static imp_win g_wins[IMP_MAX_WINDOWS];   // slot 0 = main

// ---- render->main COMMAND RING ---------------------------------------------
// Window create/destroy/retitle/reposition may ONLY happen on the main thread
// (Cocoa/GLFW window calls off-main are undefined behavior). The render
// thread (or any caller) enqueues a command here and wakes main via
// glfwPostEmptyEvent(); main drains the ring at its two designated drain
// sites (see imp_host_drain_commands).
typedef struct { int op; int win; int chrome; char title[128]; double x, y, w, h; } imp_cmd;
#define IMP_OP_CREATE     1
#define IMP_OP_DESTROY    2
#define IMP_OP_SET_TITLE  3
#define IMP_OP_SET_POS    4
#define IMP_CMD_RING_SIZE 64
static imp_cmd g_cmds[IMP_CMD_RING_SIZE];
static int g_cmd_head = 0, g_cmd_count = 0;
static pthread_mutex_t g_cmd_mutex = PTHREAD_MUTEX_INITIALIZER;

// cached screen position of the main window (slot 0), stamped by its GLFW
// window-pos callback -- the render thread never calls GLFW getters
static volatile double g_main_x = 0.0, g_main_y = 0.0;

// clamp a caller-supplied window id into the table (id 0 = main): a stray id
// must never index out of bounds
static int imp_win_id(int win) {
  return (win < 0 || win >= IMP_MAX_WINDOWS) ? 0 : win;
}

static ImpellerContext g_context = NULL;

// pending input events (window coordinates / codepoints), small ring
// buffers polled from Koka -- no callback ever crosses into Koka code.
// pointer kinds: 1 = left press, 2 = release, 3 = right press (context menu)
#define IMP_MAX_EVENTS 128
static double g_pointer[IMP_MAX_EVENTS][4];   // kind, x, y, win
static int g_pointer_head = 0, g_pointer_count = 0;
static int g_last_pointer_win = 0;            // win of the last DRAINED pointer entry
typedef struct { unsigned int v; int win; } imp_char_ev;
static imp_char_ev g_chars[IMP_MAX_EVENTS];   // unicode codepoints + source window
static int g_char_head = 0, g_char_count = 0;
static int g_last_char_win = 0;
typedef struct { int v; int win; } imp_key_ev;
static imp_key_ev g_keys[IMP_MAX_EVENTS];     // GLFW key codes (specials only) + source window
static int g_key_head = 0, g_key_count = 0;
static int g_last_key_win = 0;

static long g_frame_limit = -1;  // KOKA_IMP_FRAMES: auto-close for testing
static long g_frames = 0;

// accumulated mouse-wheel / trackpad scroll delta (logical points), drained
// each poll by the Koka backend and applied to the scroll region under the
// cursor. GLFW reports "lines"; we scale to a point-ish step. Kept GLOBAL
// (not per-window): scroll targets whichever window is under the cursor, one
// wheel at a time, so a single accumulator + a window TAG is sufficient.
static double g_scroll_dy = 0.0;
static double g_scroll_dx = 0.0;   // trackpad horizontal delta (for horizontal scroll regions)
static int g_scroll_win = 0;       // the window the pending scroll delta belongs to

// the window that last saw the cursor (move, click, or synthetic inject),
// stamped by the cursor-position callback / inject-cursor / inject-pointer
static int g_cursor_win = 0;

// set by every input callback (and drawable resizes / close requests): the
// event-driven pump wakes only when this is set (see imp_host_wait_events)
static volatile int g_events_dirty = 0;

// PLATFORM/RENDER THREAD SPLIT (see imp_host_platform_loop): when active, the
// MAIN thread owns GLFW/Cocoa only (window + event wait; it survives the modal
// resize loop) and the RENDER thread runs the whole app. Events cross via the
// ring buffers (mutexed below); window metrics are CACHED by main-thread
// callbacks so the render thread never calls GLFW itself.
static pthread_mutex_t g_ev_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t g_present_mutex = PTHREAD_MUTEX_INITIALIZER;  // guards the per-window pending_dl slots + teardown
static volatile int g_shutting_down = 0;
// Under the split the render thread never touches Metal/CoreAnimation (off-
// main presents raced CA fences/transactions and crashed): it PUBLISHES its
// display list here (a per-window pending slot) and wakes main
// (glfwPostEmptyEvent); the PLATFORM thread presents each window's freshest
// pending frame -- including from the size callbacks during a live resize.
static void imp_flush_present(void);   // fwd: called from the resize callback
static volatile int g_platform_split = 0;
static void (*g_event_sink)(void) = NULL;              // wakes the render thread

// mark input/layout state dirty AND wake the render thread immediately. Called
// from the GLFW callbacks -- which also fire INSIDE the Cocoa modal resize
// loop, where our own glfwWaitEvents call never returns; waking from the
// callback is what makes live-resize re-rendering work.
static void imp_mark_dirty(void) {
  g_events_dirty = 1;
  if (g_event_sink != NULL) g_event_sink();
}

// recover the window-table slot a GLFW callback fired for (stashed at window
// creation time via glfwSetWindowUserPointer)
static int imp_win_slot(GLFWwindow* window) {
  return (int)(intptr_t)glfwGetWindowUserPointer(window);
}

static void imp_cursor_pos_callback(GLFWwindow* window, double x, double y) {
  int win = imp_win_slot(window);
  g_wins[win].cursor_x = x; g_wins[win].cursor_y = y; g_wins[win].cursor_seen = 1;
  g_cursor_win = win;
  imp_mark_dirty();
}

static void imp_mouse_callback(GLFWwindow* window, int button, int action, int mods) {
  if (action != GLFW_PRESS && action != GLFW_RELEASE) return;
  int win = imp_win_slot(window);
  pthread_mutex_lock(&g_ev_mutex);
  if (g_pointer_count >= IMP_MAX_EVENTS) { pthread_mutex_unlock(&g_ev_mutex); return; }
  // use the event-time cursor position (see g_wins[win].cursor_x); fall back to
  // the live position only if no move has been seen yet (then the mouse is
  // stationary)
  double x, y;
  if (g_wins[win].cursor_seen) { x = g_wins[win].cursor_x; y = g_wins[win].cursor_y; }
  else glfwGetCursorPos(window, &x, &y);
  int slot = (g_pointer_head + g_pointer_count) % IMP_MAX_EVENTS;
  // right-button press is its own kind (3) so the backend can raise a context
  // menu; left press is 1, any release is 2.
  double k = (action == GLFW_RELEASE) ? 2.0
             : (button == GLFW_MOUSE_BUTTON_RIGHT ? 3.0 : 1.0);
  g_pointer[slot][0] = k;
  g_pointer[slot][1] = x;
  g_pointer[slot][2] = y;
  g_pointer[slot][3] = (double)win;
  g_pointer_count++;
  pthread_mutex_unlock(&g_ev_mutex);
  imp_mark_dirty();
}

static void imp_scroll_callback(GLFWwindow* window, double xoffset, double yoffset) {
  int win = imp_win_slot(window);
  pthread_mutex_lock(&g_ev_mutex);
  // positive yoffset = wheel up / two-finger down; 40 pts per notch feels
  // OS-like without a physics model. Sign: scrolling up reveals earlier content
  // (decreases the offset), handled by the backend. xoffset is the trackpad
  // horizontal delta, drained for horizontal scroll regions.
  g_scroll_dy += yoffset * 40.0;
  g_scroll_dx += xoffset * 40.0;
  g_scroll_win = win;
  pthread_mutex_unlock(&g_ev_mutex);
  imp_mark_dirty();
}

static void imp_char_callback(GLFWwindow* window, unsigned int codepoint) {
  int win = imp_win_slot(window);
  pthread_mutex_lock(&g_ev_mutex);
  if (g_char_count < IMP_MAX_EVENTS) {
    int slot = (g_char_head + g_char_count) % IMP_MAX_EVENTS;
    g_chars[slot].v = codepoint;
    g_chars[slot].win = win;
    g_char_count++;
  }
  pthread_mutex_unlock(&g_ev_mutex);
  imp_mark_dirty();
}

static void imp_key_callback(GLFWwindow* window, int key, int scancode, int action, int mods) {
  if (action != GLFW_PRESS && action != GLFW_REPEAT) return;
  if (key != GLFW_KEY_BACKSPACE && key != GLFW_KEY_ENTER && key != GLFW_KEY_ESCAPE) return;
  int win = imp_win_slot(window);
  pthread_mutex_lock(&g_ev_mutex);
  if (g_key_count < IMP_MAX_EVENTS) {
    int slot = (g_key_head + g_key_count) % IMP_MAX_EVENTS;
    g_keys[slot].v = key;
    g_keys[slot].win = win;
    g_key_count++;
  }
  pthread_mutex_unlock(&g_ev_mutex);
  imp_mark_dirty();
}

// --- SYNTHETIC input injection (ui/test-live middleman driver) -------------
// Pushes into the SAME ring buffers the GLFW callbacks fill and wakes the
// pump the same way (imp_mark_dirty) -- downstream code cannot tell a
// synthetic event from a real one. Callable from any thread (mutexed).

void imp_host_inject_cursor(int win, double x, double y) {
  int w = imp_win_id(win);
  g_wins[w].cursor_x = x; g_wins[w].cursor_y = y; g_wins[w].cursor_seen = 1;
  g_cursor_win = w;
  imp_mark_dirty();
}

void imp_host_inject_pointer(int win, double kind, double x, double y) {
  int w = imp_win_id(win);
  pthread_mutex_lock(&g_ev_mutex);
  if (g_pointer_count < IMP_MAX_EVENTS) {
    int slot = (g_pointer_head + g_pointer_count) % IMP_MAX_EVENTS;
    g_pointer[slot][0] = kind;   // 1 = left press, 2 = release, 3 = right press
    g_pointer[slot][1] = x;
    g_pointer[slot][2] = y;
    g_pointer[slot][3] = (double)w;
    g_pointer_count++;
  }
  pthread_mutex_unlock(&g_ev_mutex);
  g_wins[w].cursor_x = x; g_wins[w].cursor_y = y; g_wins[w].cursor_seen = 1;   // event-time position
  g_cursor_win = w;
  imp_mark_dirty();
}

void imp_host_inject_char(int win, unsigned int codepoint) {
  int w = imp_win_id(win);
  pthread_mutex_lock(&g_ev_mutex);
  if (g_char_count < IMP_MAX_EVENTS) {
    int slot = (g_char_head + g_char_count) % IMP_MAX_EVENTS;
    g_chars[slot].v = codepoint;
    g_chars[slot].win = w;
    g_char_count++;
  }
  pthread_mutex_unlock(&g_ev_mutex);
  imp_mark_dirty();
}

// key: GLFW codes, same set the callback admits (259 backspace, 257 enter,
// 256 escape)
void imp_host_inject_key(int win, int key) {
  int w = imp_win_id(win);
  pthread_mutex_lock(&g_ev_mutex);
  if (g_key_count < IMP_MAX_EVENTS) {
    int slot = (g_key_head + g_key_count) % IMP_MAX_EVENTS;
    g_keys[slot].v = key;
    g_keys[slot].win = w;
    g_key_count++;
  }
  pthread_mutex_unlock(&g_ev_mutex);
  imp_mark_dirty();
}

void imp_host_inject_scroll(int win, double dx, double dy) {
  int w = imp_win_id(win);
  pthread_mutex_lock(&g_ev_mutex);
  g_scroll_dx += dx;
  g_scroll_dy += dy;
  g_scroll_win = w;
  pthread_mutex_unlock(&g_ev_mutex);
  imp_mark_dirty();
}

// Discard every pending synthetic/real event across all four rings (pointer,
// char, key, scroll) without processing them. ui/test-live calls this between
// scenarios (reset-app): a scenario's tail burst can still be sitting in a
// ring -- injected (mutexed, so already "delivered" from the injector's point
// of view) but not yet drained by the pump's next wake -- when the script
// moves on to reset + the next scenario's fresh click. Left alone, that
// residue is drained LATE, against the freshly-reset (same-keyed, since
// widget identity is deterministic across a reset render) field of the NEXT
// scenario, landing as a stray leading character. Draining here closes that
// window at its source (the rings), independent of however many state-ch
// transitions the residue would otherwise have produced.
void imp_host_drain_rings(void) {
  pthread_mutex_lock(&g_ev_mutex);
  g_pointer_head = 0; g_pointer_count = 0;
  g_char_head = 0;    g_char_count = 0;
  g_key_head = 0;     g_key_count = 0;
  g_scroll_dx = 0.0;  g_scroll_dy = 0.0;
  pthread_mutex_unlock(&g_ev_mutex);
}

static void imp_close_callback(GLFWwindow* window) {
  int win = imp_win_slot(window);
  if (win != 0) {
    // titled panel windows: the app decides (by no longer emitting the view),
    // so cancel the OS close and let Koka observe the sticky flag instead
    g_wins[win].close_requested = 1;
    glfwSetWindowShouldClose(window, GLFW_FALSE);
  }
  // window 0 keeps today's behavior: should-close(0) drives app shutdown
  imp_mark_dirty();   // wake the pump so should-close/close-requested is observed
}

static void imp_size_callback(GLFWwindow* window, int w, int h) {
  int win = imp_win_slot(window);
  g_wins[win].win_w = (double)w; g_wins[win].win_h = (double)h;   // cache for the render thread
  imp_mark_dirty();                            // re-layout at the new size (LIVE, mid-drag)
}

static void imp_fb_callback(GLFWwindow* window, int w, int h) {
  int win = imp_win_slot(window);
  if (g_wins[win].layer != NULL) g_wins[win].layer.drawableSize = CGSizeMake(w, h);   // main thread, in-callback
  imp_mark_dirty();
  if (win == 0) imp_flush_present();   // live resize: present the freshest pending frames mid-drag
}

// main window only: cache the screen position for main-window-origin (Panel
// placement) -- the render thread must never call glfwGetWindowPos itself
static void imp_window_pos_callback(GLFWwindow* window, int x, int y) {
  (void)window;
  g_main_x = (double)x; g_main_y = (double)y;
}

// install every input/lifecycle callback and stash the table slot in the
// GLFW user pointer -- shared by imp_host_init (slot 0) and command-driven
// titled-window creation (imp_host_drain_commands) so the two paths cannot
// drift out of sync.
static void imp_register_callbacks(GLFWwindow* window, int slot) {
  glfwSetWindowUserPointer(window, (void*)(intptr_t)slot);
  glfwSetMouseButtonCallback(window, imp_mouse_callback);
  glfwSetCursorPosCallback(window, imp_cursor_pos_callback);
  glfwSetScrollCallback(window, imp_scroll_callback);
  glfwSetCharCallback(window, imp_char_callback);
  glfwSetKeyCallback(window, imp_key_callback);
  glfwSetWindowCloseCallback(window, imp_close_callback);
  glfwSetWindowSizeCallback(window, imp_size_callback);
  glfwSetFramebufferSizeCallback(window, imp_fb_callback);
  if (slot == 0) glfwSetWindowPosCallback(window, imp_window_pos_callback);
}

// attach a CAMetalLayer to `window`'s content view and size the drawable --
// identical for the main window (imp_host_init) and titled windows opened
// later via the command ring (imp_host_drain_commands)
static void imp_attach_layer(imp_win* iw, GLFWwindow* window, double logical_w, double logical_h) {
  NSWindow* cocoa_window = glfwGetCocoaWindow(window);
  iw->layer = [CAMetalLayer layer];
  iw->layer.framebufferOnly = NO;
  iw->layer.pixelFormat = MTLPixelFormatBGRA8Unorm;
  iw->layer.device = MTLCreateSystemDefaultDevice();
  cocoa_window.contentView.layer = iw->layer;
  cocoa_window.contentView.wantsLayer = YES;

  // render at native (retina) resolution: the drawable is sized in physical
  // pixels, kept in sync with the (resizable) window by imp_host_poll, and the
  // Koka paint pass scales its logical-point display list by `g_wins[win].scale`.
  iw->scale = cocoa_window.backingScaleFactor;
  iw->layer.contentsScale = iw->scale;
  iw->layer.drawableSize = CGSizeMake(logical_w * iw->scale, logical_h * iw->scale);
}

int imp_host_init(int width, int height, const char* title) {
  imp_win* w0 = &g_wins[0];
  if (w0->window != NULL) return 1;   // idempotent (the platform thread inits first under the split)
  if (glfwInit() != GLFW_TRUE) return 0;
  if (glfwGetPlatform() != GLFW_PLATFORM_COCOA) return 0;
  glfwWindowHint(GLFW_CLIENT_API, GLFW_NO_API);
  glfwWindowHint(GLFW_RESIZABLE, GLFW_TRUE);
  w0->window = glfwCreateWindow(width, height, title, NULL, NULL);
  if (w0->window == NULL) return 0;
  imp_register_callbacks(w0->window, 0);
  w0->win_w = (double)width; w0->win_h = (double)height;
  w0->chrome = 0;   // main/titled
  w0->alive = 1;

  g_context = ImpellerContextCreateMetalNew(IMPELLER_VERSION);
  if (g_context == NULL) return 0;

  imp_attach_layer(w0, w0->window, (double)width, (double)height);

  const char* frames = getenv("KOKA_IMP_FRAMES");
  if (frames != NULL) g_frame_limit = atol(frames);
  { int wx, wy; glfwGetWindowPos(g_wins[0].window, &wx, &wy);   // stamp the origin NOW --
    g_main_x = (double)wx; g_main_y = (double)wy; }            // the pos callback only fires on moves
  return 1;
}

// ---- command-ring PRODUCER side (callable from any thread, e.g. the render
// thread) -- find a free slot / enqueue an op / wake main. -----------------

static void imp_cmd_push(const imp_cmd* cmd) {
  pthread_mutex_lock(&g_cmd_mutex);
  if (g_cmd_count < IMP_CMD_RING_SIZE) {
    int slot = (g_cmd_head + g_cmd_count) % IMP_CMD_RING_SIZE;
    g_cmds[slot] = *cmd;
    g_cmd_count++;
  }
  pthread_mutex_unlock(&g_cmd_mutex);
  glfwPostEmptyEvent();   // wake main out of glfwWaitEvents
}

// allocate a table slot and enqueue creation on the main thread; returns the
// slot id immediately (the window itself is not yet created -- window-alive
// reports false until the main thread drains IMP_OP_CREATE)
int imp_host_open_window(int chrome, const char* title, double w, double h) {
  int found = -1;
  pthread_mutex_lock(&g_cmd_mutex);
  for (int i = 1; i < IMP_MAX_WINDOWS; i++) {
    if (g_wins[i].alive == 0 && g_wins[i].window == NULL && g_wins[i].pending == 0) {
      found = i;
      g_wins[i].pending = 1;
      break;
    }
  }
  pthread_mutex_unlock(&g_cmd_mutex);
  if (found < 0) return -1;   // table full

  imp_cmd cmd;
  memset(&cmd, 0, sizeof(cmd));
  cmd.op = IMP_OP_CREATE;
  cmd.win = found;
  cmd.chrome = chrome;
  if (title != NULL) { strncpy(cmd.title, title, sizeof(cmd.title) - 1); }
  cmd.w = w; cmd.h = h;

  // enqueue and roll back the claimed slot if the ring itself is full --
  // otherwise the slot would be stranded forever (pending==1, no CREATE
  // ever issued, window-alive reports false permanently).
  pthread_mutex_lock(&g_cmd_mutex);
  int pushed = (g_cmd_count < IMP_CMD_RING_SIZE);
  if (pushed) {
    int slot = (g_cmd_head + g_cmd_count) % IMP_CMD_RING_SIZE;
    g_cmds[slot] = cmd;
    g_cmd_count++;
  } else {
    g_wins[found].pending = 0;
  }
  pthread_mutex_unlock(&g_cmd_mutex);
  glfwPostEmptyEvent();   // wake main out of glfwWaitEvents

  if (!pushed) {
    fprintf(stderr, "impeller host: command ring full, window request dropped\n");
    return -1;
  }
  return found;
}

// win 0 excluded on purpose: the main window's lifecycle belongs to
// init/shutdown (imp_host_init/imp_host_shutdown), not the command ring.
void imp_host_close_window(int win) {
  if (win <= 0 || win >= IMP_MAX_WINDOWS) return;
  imp_cmd cmd;
  memset(&cmd, 0, sizeof(cmd));
  cmd.op = IMP_OP_DESTROY;
  cmd.win = win;
  imp_cmd_push(&cmd);
}

// win 0 excluded on purpose: the main window's lifecycle belongs to
// init/shutdown, not the command ring.
void imp_host_set_window_title(int win, const char* title) {
  if (win <= 0 || win >= IMP_MAX_WINDOWS) return;
  imp_cmd cmd;
  memset(&cmd, 0, sizeof(cmd));
  cmd.op = IMP_OP_SET_TITLE;
  cmd.win = win;
  if (title != NULL) { strncpy(cmd.title, title, sizeof(cmd.title) - 1); }
  imp_cmd_push(&cmd);
}

// win 0 excluded on purpose: the main window's lifecycle belongs to
// init/shutdown, not the command ring.
void imp_host_set_window_pos(int win, double x, double y) {
  if (win <= 0 || win >= IMP_MAX_WINDOWS) return;
  imp_cmd cmd;
  memset(&cmd, 0, sizeof(cmd));
  cmd.op = IMP_OP_SET_POS;
  cmd.win = win;
  cmd.x = x; cmd.y = y;
  imp_cmd_push(&cmd);
}

// created AND not close-requested. Invalid/negative/overflow ids fail safe
// (return 0); window 0 keeps reporting its own alive state (g_wins[0].alive),
// which is set true by imp_host_init and never gated by the ring.
int imp_host_window_alive(int win) {
  if (win < 0 || win >= IMP_MAX_WINDOWS) return 0;
  return (g_wins[win].alive && !g_wins[win].close_requested) ? 1 : 0;
}

// sticky until close-window: the user hit the close button. Invalid ids
// fail safe (return 0) rather than aliasing onto window 0.
int imp_host_window_close_requested(int win) {
  if (win < 0 || win >= IMP_MAX_WINDOWS) return 0;
  return g_wins[win].close_requested ? 1 : 0;
}

void imp_host_main_window_origin(double* x, double* y) {
  *x = g_main_x; *y = g_main_y;
}

// ---- command-ring CONSUMER side: MAIN THREAD ONLY. Called from exactly two
// drain sites -- (a) the platform loop right after glfwWaitEvents returns,
// (b) imp_host_poll (embed / single-thread mode).
void imp_host_drain_commands(void) {
  for (;;) {
    imp_cmd cmd;
    pthread_mutex_lock(&g_cmd_mutex);
    if (g_cmd_count == 0) { pthread_mutex_unlock(&g_cmd_mutex); return; }
    cmd = g_cmds[g_cmd_head];
    g_cmd_head = (g_cmd_head + 1) % IMP_CMD_RING_SIZE;
    g_cmd_count--;
    pthread_mutex_unlock(&g_cmd_mutex);

    int w = imp_win_id(cmd.win);
    imp_win* iw = &g_wins[w];
    switch (cmd.op) {
      case IMP_OP_CREATE: {
        glfwWindowHint(GLFW_CLIENT_API, GLFW_NO_API);
        glfwWindowHint(GLFW_RESIZABLE, GLFW_TRUE);
        glfwWindowHint(GLFW_VISIBLE, GLFW_TRUE);
        // chrome 0 = titled window (decorated); chrome 1 = borderless panel:
        // no decorations and no focus steal on show (Task 6: Panel chrome).
        // NOT GLFW_FLOATING: a globally-floating window sits above OTHER
        // apps too -- the panel becomes a CHILD WINDOW of main below, which
        // keeps it above its parent only AND makes it follow parent drags
        // natively (the OS moves children with the parent, no render loop
        // round-trip).
        glfwWindowHint(GLFW_DECORATED, cmd.chrome == 0 ? GLFW_TRUE : GLFW_FALSE);
        glfwWindowHint(GLFW_FOCUS_ON_SHOW, cmd.chrome == 0 ? GLFW_TRUE : GLFW_FALSE);
        GLFWwindow* window = glfwCreateWindow((int)cmd.w, (int)cmd.h, cmd.title, NULL, NULL);
        if (window == NULL) {
          pthread_mutex_lock(&g_cmd_mutex);
          iw->pending = 0;
          pthread_mutex_unlock(&g_cmd_mutex);
          break;
        }
        if (cmd.chrome == 1) {
          // Cocoa-level panel tweaks beyond what GLFW hints cover.
          // NSWindowStyleMaskNonactivatingPanel is formally an NSPanel mask;
          // OR-ing it onto a plain NSWindow's styleMask worked cleanly in
          // testing (no assert, no appearance glitch) and reinforces
          // no-activate behavior beyond GLFW_FOCUS_ON_SHOW, so it is kept.
          // If this ever misbehaves on a future OS, drop just this one
          // setStyleMask line. The panel is attached as a CHILD of the main
          // window: above its parent (not other apps), and the OS drags it
          // along with the parent -- our render-driven set-window-pos then
          // only corrects for ANCHOR movement, not window movement.
          NSWindow* ns = glfwGetCocoaWindow(window);
          NSWindow* parent = (g_wins[0].window != NULL) ? glfwGetCocoaWindow(g_wins[0].window) : nil;
          if (ns != nil) {
            [ns setStyleMask:[ns styleMask] | NSWindowStyleMaskNonactivatingPanel];
            [ns setHidesOnDeactivate:NO];
            if (parent != nil) [parent addChildWindow:ns ordered:NSWindowAbove];
          }
        }
        // GLFW/layer setup stays outside the mutex -- only the bookkeeping
        // flags that imp_host_open_window's free-slot scan reads
        // (window/pending/alive) are mutex-protected below.
        imp_register_callbacks(window, w);
        iw->win_w = cmd.w; iw->win_h = cmd.h;
        iw->chrome = cmd.chrome;
        iw->close_requested = 0;
        imp_attach_layer(iw, window, cmd.w, cmd.h);
        pthread_mutex_lock(&g_cmd_mutex);
        iw->window = window;
        iw->pending = 0;
        iw->alive = 1;   // set last: this is what window-alive/imp_win_id consumers observe
        pthread_mutex_unlock(&g_cmd_mutex);
        break;
      }
      case IMP_OP_DESTROY: {
        // GLFW teardown stays outside the mutex -- only the bookkeeping
        // flags the open-window scan reads (window/pending/alive) are
        // mutex-protected below.
        if (iw->window != NULL && iw->chrome == 1) {
          // detach a panel from its parent BEFORE destroying it (a destroyed
          // child left attached crashes inside AppKit's child-window list)
          NSWindow* ns = glfwGetCocoaWindow(iw->window);
          if (ns != nil && [ns parentWindow] != nil) [[ns parentWindow] removeChildWindow:ns];
        }
        if (iw->window != NULL) glfwDestroyWindow(iw->window);
        iw->layer = NULL;
        pthread_mutex_lock(&g_present_mutex);
        if (iw->pending_dl != NULL) { ImpellerDisplayListRelease((ImpellerDisplayList)iw->pending_dl); iw->pending_dl = NULL; }
        pthread_mutex_unlock(&g_present_mutex);
        iw->presented = 0;
        pthread_mutex_lock(&g_cmd_mutex);
        iw->window = NULL;
        iw->alive = 0;
        iw->close_requested = 0;
        iw->pending = 0;
        pthread_mutex_unlock(&g_cmd_mutex);
        break;
      }
      case IMP_OP_SET_TITLE: {
        if (iw->window != NULL) glfwSetWindowTitle(iw->window, cmd.title);
        break;
      }
      case IMP_OP_SET_POS: {
        if (iw->window != NULL) glfwSetWindowPos(iw->window, (int)cmd.x, (int)cmd.y);
        break;
      }
      default: break;
    }
  }
}

// the display's refresh interval in ms; the frame clock paces to this and the
// drawable present syncs the rest. NSScreen.maximumFramesPerSecond is the
// accurate source on macOS (ProMotion -> 120; GLFW's video mode reports 60)
double imp_host_refresh_ms(void) {
  if (g_wins[0].window != NULL) {
    NSWindow* w = glfwGetCocoaWindow(g_wins[0].window);
    NSScreen* screen = (w != nil) ? w.screen : nil;
    if (screen == nil) screen = [NSScreen mainScreen];
    if (screen != nil) {
      NSInteger fps = screen.maximumFramesPerSecond;
      if (fps > 0) return 1000.0 / (double)fps;
    }
  }
  GLFWmonitor* mon = glfwGetPrimaryMonitor();
  if (mon != NULL) {
    const GLFWvidmode* mode = glfwGetVideoMode(mon);
    if (mode != NULL && mode->refreshRate > 0) return 1000.0 / (double)mode->refreshRate;
  }
  return 16.0;
}

int imp_host_should_close(int win) {
  int w = imp_win_id(win);
  if (g_shutting_down) return 1;
  if (g_wins[w].window == NULL) return 1;
  if (g_frame_limit >= 0 && g_frames >= g_frame_limit) return 1;
  return glfwWindowShouldClose(g_wins[w].window);
}

// current window size in logical points (the layout unit; retina scale is
// applied separately at paint time via imp_host_scale). Under the split the
// size is CACHED by main-thread callbacks (GLFW getters are main-thread-only).
double imp_host_width(int win) {
  int w = imp_win_id(win);
  if (g_platform_split) return g_wins[w].win_w;
  if (g_wins[w].window == NULL) return 0.0;
  int ww, h; glfwGetWindowSize(g_wins[w].window, &ww, &h); return (double)ww;
}
double imp_host_height(int win) {
  int w = imp_win_id(win);
  if (g_platform_split) return g_wins[w].win_h;
  if (g_wins[w].window == NULL) return 0.0;
  int ww, hh; glfwGetWindowSize(g_wins[w].window, &ww, &hh); return (double)hh;
}

// the LIVE cursor position in logical points -- CACHED by the cursor callback
// (the event-time position; GLFW's live getter is main-thread-only)
double imp_host_cursor_x(int win) {
  int w = imp_win_id(win);
  if (g_platform_split || g_wins[w].cursor_seen) return g_wins[w].cursor_seen ? g_wins[w].cursor_x : -1.0;
  if (g_wins[w].window == NULL) return -1.0;
  double x, y; glfwGetCursorPos(g_wins[w].window, &x, &y); return x;
}
double imp_host_cursor_y(int win) {
  int w = imp_win_id(win);
  if (g_platform_split || g_wins[w].cursor_seen) return g_wins[w].cursor_seen ? g_wins[w].cursor_y : -1.0;
  if (g_wins[w].window == NULL) return -1.0;
  double x, y; glfwGetCursorPos(g_wins[w].window, &x, &y); return y;
}

// the window that last saw the cursor (move, click, or synthetic inject)
int imp_host_cursor_win(void) {
  return g_cursor_win;
}

// the window the pending (undrained) scroll delta is tagged for
int imp_host_scroll_win(void) {
  return g_scroll_win;
}

// drain the accumulated wheel delta (logical points) since the last call --
// scroll is a GLOBAL accumulator tagged with the window it targets (the
// window under the cursor when the wheel moved); only that window drains it.
double imp_host_take_scroll_dy(int win) {
  int w = imp_win_id(win);
  pthread_mutex_lock(&g_ev_mutex);
  double dy = 0.0;
  if (g_scroll_win == w) { dy = g_scroll_dy; g_scroll_dy = 0.0; }
  pthread_mutex_unlock(&g_ev_mutex);
  return dy;
}
double imp_host_take_scroll_dx(int win) {
  int w = imp_win_id(win);
  pthread_mutex_lock(&g_ev_mutex);
  double dx = 0.0;
  if (g_scroll_win == w) { dx = g_scroll_dx; g_scroll_dx = 0.0; }
  pthread_mutex_unlock(&g_ev_mutex);
  return dx;
}

// non-blocking: cadence comes from the caller (the app's uv timer strand)
// keep the Metal drawable sized to the (resizable) window's framebuffer, so
// resizing re-flows instead of stretching the old drawable; a change also
// marks events dirty (the pump re-renders at the new size). Window 0 only for
// now -- the main loop below only pumps the one window that exists today.
static void imp_host_upkeep(void) {
  imp_win* w0 = &g_wins[0];
  if (w0->window != NULL && w0->layer != NULL) {
    int fbw, fbh; glfwGetFramebufferSize(w0->window, &fbw, &fbh);
    static int last_fbw = 0, last_fbh = 0;
    if (fbw != last_fbw || fbh != last_fbh) {
      last_fbw = fbw; last_fbh = fbh;
      w0->layer.drawableSize = CGSizeMake(fbw, fbh);
      g_events_dirty = 1;
    }
  }
}

void imp_host_poll(void) {
  g_frames++;
  @autoreleasepool {          // custom main loop: drain per iteration
    glfwPollEvents();
    imp_host_upkeep();
  }
  imp_host_drain_commands();   // embed (single-thread) drain site
}

// EVENT-DRIVEN wait (the uv external waiter): sleep in GLFW until an event or
// `timeout_ms` (the time to the next uv timer; <0 = none pending). Under a
// KOKA_IMP_FRAMES test run the wait is capped so frames keep ticking and the
// auto-close fires.
void imp_host_wait_events(double timeout_ms) {
  g_frames++;
  double t = timeout_ms;
  if (g_frame_limit >= 0 && (t < 0.0 || t > 16.0)) t = 16.0;
  @autoreleasepool {          // custom main loop: drain per iteration
    if (t == 0.0) glfwPollEvents();
    else if (t < 0.0) glfwWaitEvents();
    else glfwWaitEventsTimeout(t / 1000.0);
    imp_host_upkeep();
  }
  // reaching the test frame limit must WAKE the (input-parked) pump so it
  // observes should-close
  if (g_frame_limit >= 0 && g_frames >= g_frame_limit) g_events_dirty = 1;
}

// consume the events-dirty flag (the waiter signals the pump when set)
int imp_host_take_events_dirty(void) {
  int d = g_events_dirty;
  g_events_dirty = 0;
  return d;
}

// wake a sleeping imp_host_wait_events from another thread (GLFW documents
// glfwPostEmptyEvent as thread-safe)
void imp_host_wake(void) {
  if (g_wins[0].window != NULL) glfwPostEmptyEvent();
}

// ---- the PLATFORM/RENDER split ----------------------------------------------
// The MAIN thread parks here for the app's lifetime: wait for events, keep the
// drawable sized, and wake the render thread (the registered sink) whenever the
// callbacks marked events dirty. Crucially this loop keeps working INSIDE the
// Cocoa modal resize loop -- the size callback fires, the sink wakes the render
// thread, and the render thread re-lays-out and presents WHILE the user drags.

void imp_host_set_event_sink(void (*sink)(void)) {
  g_event_sink = sink;
}

int imp_host_platform_split(void) {
  return g_platform_split;
}

// arm the split BEFORE the render thread spawns (so its pump never installs
// the single-thread embed waiter)
void imp_host_mark_split(void) {
  g_platform_split = 1;
}

void imp_host_platform_loop(void) {
  g_platform_split = 1;
  while (!imp_host_should_close(0)) {
    @autoreleasepool {
      if (g_frame_limit >= 0) glfwWaitEventsTimeout(0.016);  // test mode: keep frames ticking
      else glfwWaitEvents();
      imp_host_drain_commands();   // platform-loop drain site (right after the wait returns)
      g_frames++;
      imp_host_upkeep();
      imp_flush_present();   // present the render thread's latest frame
    }
    if (g_frame_limit >= 0 && g_frames >= g_frame_limit) g_events_dirty = 1;
    if (g_events_dirty) {
      g_events_dirty = 0;
      if (g_event_sink != NULL) g_event_sink();
    }
  }
  // window closed (or frame limit): make sure the render thread observes it
  if (g_event_sink != NULL) g_event_sink();
}

// next pointer event: returns 0 when empty, else the kind (1 press, 2 release)
int imp_host_next_pointer(double* x, double* y) {
  pthread_mutex_lock(&g_ev_mutex);
  if (g_pointer_count == 0) { pthread_mutex_unlock(&g_ev_mutex); return 0; }
  int kind = (int)g_pointer[g_pointer_head][0];
  *x = g_pointer[g_pointer_head][1];
  *y = g_pointer[g_pointer_head][2];
  g_last_pointer_win = (int)g_pointer[g_pointer_head][3];
  g_pointer_head = (g_pointer_head + 1) % IMP_MAX_EVENTS;
  g_pointer_count--;
  pthread_mutex_unlock(&g_ev_mutex);
  return kind;
}

// the window of the last DRAINED pointer event (imp_host_next_pointer)
int imp_host_pointer_win(void) {
  return g_last_pointer_win;
}

// next typed character (0 when empty)
unsigned int imp_host_next_char(void) {
  pthread_mutex_lock(&g_ev_mutex);
  if (g_char_count == 0) { pthread_mutex_unlock(&g_ev_mutex); return 0; }
  unsigned int c = g_chars[g_char_head].v;
  g_last_char_win = g_chars[g_char_head].win;
  g_char_head = (g_char_head + 1) % IMP_MAX_EVENTS;
  g_char_count--;
  pthread_mutex_unlock(&g_ev_mutex);
  return c;
}

// the window of the last DRAINED char event
int imp_host_char_win(void) {
  return g_last_char_win;
}

// next special key: 0 none, 1 backspace, 2 enter, 3 escape
int imp_host_next_key(void) {
  pthread_mutex_lock(&g_ev_mutex);
  if (g_key_count == 0) { pthread_mutex_unlock(&g_ev_mutex); return 0; }
  int k = g_keys[g_key_head].v;
  g_last_key_win = g_keys[g_key_head].win;
  g_key_head = (g_key_head + 1) % IMP_MAX_EVENTS;
  g_key_count--;
  pthread_mutex_unlock(&g_ev_mutex);
  return (k == GLFW_KEY_BACKSPACE ? 1 : k == GLFW_KEY_ENTER ? 2 : 3);
}

// the window of the last DRAINED key event
int imp_host_key_win(void) {
  return g_last_key_win;
}

void* imp_host_context(void) {
  return (void*)g_context;
}

// draw a display list onto the next drawable and present it
double imp_host_scale(int win) {
  int w = imp_win_id(win);
  return g_wins[w].scale;
}

// draw + present on the CURRENT thread (main-only under the split)
static void imp_do_present(int win, ImpellerDisplayList dl) {
  // the app runs a CUSTOM main loop, so nothing drains the thread's
  // autorelease pool for us: without a per-present pool the autoreleased
  // drawable (an IOSurface-backed object) leaks EVERY FRAME
  @autoreleasepool {
    id<CAMetalDrawable> drawable = [g_wins[win].layer nextDrawable];
    if (drawable != nil) {
      ImpellerSurface surface = ImpellerSurfaceCreateWrappedMetalDrawableNew(
          g_context, (__bridge void*)drawable);
      if (surface != NULL) {
        ImpellerSurfaceDrawDisplayList(surface, dl);
        ImpellerSurfacePresent(surface);
        ImpellerSurfaceRelease(surface);
        g_wins[win].presented++;
      }
    }
  }
}

void imp_host_present(int win, void* display_list) {
  int w = imp_win_id(win);
  if (display_list == NULL) return;
  if (g_shutting_down || g_wins[w].window == NULL || g_context == NULL) return;
  if (g_platform_split) {
    // render thread: PUBLISH the display list into THIS window's slot; main
    // presents it. (A single shared slot here once routed every secondary
    // window's frames into window 0 -- blank secondaries, ghost visuals.)
    ImpellerDisplayListRetain((ImpellerDisplayList)display_list);
    pthread_mutex_lock(&g_present_mutex);
    if (g_wins[w].pending_dl != NULL) ImpellerDisplayListRelease((ImpellerDisplayList)g_wins[w].pending_dl);
    g_wins[w].pending_dl = display_list;
    pthread_mutex_unlock(&g_present_mutex);
    glfwPostEmptyEvent();
  }
  else {
    imp_do_present(w, (ImpellerDisplayList)display_list);
  }
}

// frames actually presented to a window (test probe: a blank window is 0)
long imp_host_present_count(int win) {
  return g_wins[imp_win_id(win)].presented;
}

// MAIN: present each window's latest published display list, if any
// (platform-loop wake + the size callbacks during a live resize).
static void imp_flush_present(void) {
  for (int i = 0; i < IMP_MAX_WINDOWS; i++) {
    pthread_mutex_lock(&g_present_mutex);
    ImpellerDisplayList dl = (ImpellerDisplayList)g_wins[i].pending_dl;
    g_wins[i].pending_dl = NULL;
    pthread_mutex_unlock(&g_present_mutex);
    if (dl == NULL) continue;
    if (!g_shutting_down && g_wins[i].window != NULL && g_context != NULL) imp_do_present(i, dl);
    ImpellerDisplayListRelease(dl);
  }
}

void imp_host_shutdown(void) {
  // stop new publishes, drop the pending frame, THEN tear down (main thread)
  g_shutting_down = 1;
  pthread_mutex_lock(&g_present_mutex);
  for (int i = 0; i < IMP_MAX_WINDOWS; i++) {
    if (g_wins[i].pending_dl != NULL) { ImpellerDisplayListRelease((ImpellerDisplayList)g_wins[i].pending_dl); g_wins[i].pending_dl = NULL; }
  }
  if (g_context != NULL) { ImpellerContextRelease(g_context); g_context = NULL; }
  if (g_wins[0].window != NULL) { glfwDestroyWindow(g_wins[0].window); g_wins[0].window = NULL; }
  glfwTerminate();
  pthread_mutex_unlock(&g_present_mutex);
}
