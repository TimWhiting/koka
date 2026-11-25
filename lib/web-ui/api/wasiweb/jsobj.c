/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Tim Whiting

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// #include <kklib.h>  -- already included (this file is textually pasted into
// `jsobj.kk`'s own generated .c via `extern import c file`, same convention
// as evloop.c/dom.c).

// Module-local externref table + free-list: the Perceus-owned replacement
// for a JS-side handle `Map` (the old `dom.js` had one; this rewrite's
// `index.html` has none, see its comments). Every live JS object referenced
// from Koka (a DOM element, for now -- but the table itself is not
// DOM-specific) gets a slot in `kk_js_table`; the slot number (never the
// externref itself, which cannot be stored inside a `kk_box_t` directly --
// wasm externrefs are opaque host references, not bit patterns) is what a
// Koka `element` value actually holds (see dom.kk), wrapped in a
// `kk_cptr_raw_box` (kklib/include/kklib/box.h) whose free function is
// `kk_js_obj_free_fun` below.
//
// This is the whole point of Core Task 2: Perceus's ordinary refcounting on
// that box *is* the JS object's lifetime. When the last reference to a
// Koka-level `element` (or any other value wrapping one of these boxes)
// drops, kklib calls the free function, which nulls the table slot
// (releasing wasm's strong reference to the externref, so the browser's own
// JS GC can reclaim the DOM element once nothing else references it) and
// returns the slot to the free-list for reuse. No JS-side Map, no WeakRef,
// no finalizer registry -- see ../readme.md for the full story and the
// slot-recycling proof (`live-slots` export below + index.html's verify
// hook).
//
// Table declaration/grow/get/set syntax and the null-ref/is-null builtins
// were validated in a standalone scratch compile *before* writing this file
// (Step 1 of the brief) -- see ../readme.md ("Step 1: scratch compile") and
// .superpowers/sdd/core-task-2-report.md for the exact transcript. Summary:
// clang 23 (wasi-sdk 34.0-rc.1) compiles `static __externref_t t[0];` +
// `__builtin_wasm_table_grow/get/set` + `__builtin_wasm_ref_null_extern` +
// `__builtin_wasm_ref_is_null_extern` cleanly under `--target=wasm32-wasip1`
// with *no* extra `-mreference-types` flag (reference types are
// unconditionally available on this target in this clang), and node >= 24
// instantiates + runs the resulting module with no extra `WebAssembly`
// feature flags either.

// `nodebug`: clang's DWARF emission for a global variable normally generates
// a data-symbol relocation for its location expression, but `kk_js_table`
// is a wasm *table* symbol, not a data symbol -- wasm-ld rejects that
// relocation ("invalid data relocation: kk_js_table") whenever this
// translation unit is compiled with `-g` (koka's default C build always
// passes `-g`, see src/Compile/Options.hs). `nodebug` suppresses debug-info
// generation for just this one variable, which sidesteps the mismatch
// entirely; nothing else in this file needs it (ordinary C globals/functions
// don't hit this). Confirmed necessary+sufficient in the Step-1 scratch
// compile -- see ../readme.md.
__attribute__((nodebug)) static __externref_t kk_js_table[0];
static kk_ssize_t     kk_js_table_capacity;  // = 0

static int32_t*  kk_js_freelist;
static kk_ssize_t kk_js_freelist_count;
static kk_ssize_t kk_js_freelist_capacity;

// Slot 0 is reserved invalid -- never allocated -- precisely so a "not
// found"/absent JS object (a null externref, e.g. from
// `get-element-by-id` when the id doesn't exist) can be represented as slot
// 0 without ever touching the table. See `kk_wasiweb_dom_get_element_by_id`
// in dom.c, which checks `__builtin_wasm_ref_is_null_extern` and returns 0
// directly instead of calling `kk_js_obj_alloc`.
static int32_t kk_js_next_slot = 1;

static int32_t kk_js_allocated_count;  // total allocations, ever
static int32_t kk_js_freed_count;      // total frees, ever; live == allocated - freed

static void kk_js_table_ensure(int32_t slot, kk_context_t* ctx) {
  if (slot >= kk_js_table_capacity) {
    int32_t grow_by = (int32_t)((slot + 1) - kk_js_table_capacity);
    int32_t prev = __builtin_wasm_table_grow(kk_js_table, __builtin_wasm_ref_null_extern(), grow_by);
    if (prev < 0) {
      // growth failed (host refused/OOM): fail loudly rather than letting the
      // subsequent table.set trap with no context.
      kk_fatal_error(ENOMEM, "koka js-obj: externref table growth failed");
    }
    kk_js_table_capacity = slot + 1;
  }
  kk_unused(ctx);
}

static void kk_js_freelist_push(int32_t slot, kk_context_t* ctx) {
  if (kk_js_freelist_count == kk_js_freelist_capacity) {
    kk_ssize_t newcap = (kk_js_freelist_capacity == 0 ? 8 : kk_js_freelist_capacity * 2);
    kk_js_freelist = (int32_t*)kk_realloc(kk_js_freelist, newcap * sizeof(int32_t), ctx);
    kk_js_freelist_capacity = newcap;
  }
  kk_js_freelist[kk_js_freelist_count++] = slot;
}

static bool kk_js_freelist_pop(int32_t* out) {
  if (kk_js_freelist_count == 0) return false;
  *out = kk_js_freelist[--kk_js_freelist_count];
  return true;
}

// Allocates a fresh slot for `ref` and stores it into the table -- callers
// must already have checked `ref` is not a null externref (see dom.c; slot 0
// is reserved for that case and this function is never asked to allocate
// it). Pops the free-list first; only grows the (monotonically-sized) table
// when the free-list is empty and a brand new slot number is needed.
int32_t kk_js_obj_alloc(__externref_t ref, kk_context_t* ctx) {
  int32_t slot;
  if (!kk_js_freelist_pop(&slot)) {
    slot = kk_js_next_slot++;
  }
  kk_js_table_ensure(slot, ctx);
  __builtin_wasm_table_set(kk_js_table, slot, ref);
  kk_js_allocated_count++;
  return slot;
}

// Returns the externref stored at `slot`, or a null externref for slot 0 (or
// any slot never allocated / already freed and not yet reused).
__externref_t kk_js_obj_get(int32_t slot) {
  if (slot <= 0 || slot >= kk_js_table_capacity) return __builtin_wasm_ref_null_extern();
  return __builtin_wasm_table_get(kk_js_table, slot);
}

// The `kk_cptr_raw` free function (kklib/include/kklib/box.h): kklib calls
// this exactly once, when the last reference to the box created by
// `kk_js_obj_box` below drops. `p` carries the slot number smuggled through
// the `void*` field (never dereferenced as a pointer). THIS is where Perceus
// ownership meets the JS side: nulling the table slot drops wasm's own
// strong reference to the externref, letting the browser's JS GC reclaim the
// underlying object once nothing else references it -- no explicit "close"
// or "dispose" call from Koka is needed, unlike the old handle-Map design.
// Non-static: layered destructors elsewhere (e.g. dom.c's subscription
// free function, which must first tell the host to removeEventListener)
// release their slot through this after their own idempotent fringe call.
// This is the ONLY way a slot returns to the free-list.
void kk_js_obj_release_slot(int32_t slot, kk_context_t* ctx) {
  if (slot > 0 && slot < kk_js_table_capacity) {
    __builtin_wasm_table_set(kk_js_table, slot, __builtin_wasm_ref_null_extern());
  }
  kk_js_freelist_push(slot, ctx);
  kk_js_freed_count++;
}

static void kk_js_obj_free_fun(void* p, kk_block_t* block, kk_context_t* ctx) {
  kk_unused(block);
  kk_js_obj_release_slot((int32_t)(intptr_t)p, ctx);
}

// Wraps `slot` in a Perceus-refcounted box (a plain `kk_cptr_raw_box`, no new
// kklib API -- see the global constraint in the task brief): a Koka
// `element` (dom.kk) holds exactly one of these as its `any` field. Dropping
// the box (ordinary Perceus refcounting, e.g. when an `element` value goes
// out of scope with no other references) is what frees the slot -- see
// `kk_js_obj_free_fun` above.
kk_box_t kk_js_obj_box(int32_t slot, kk_context_t* ctx) {
  return kk_cptr_raw_box(&kk_js_obj_free_fun, (void*)(intptr_t)slot, ctx);
}

// Borrowed (does not consume a reference, mirrors `kk_string_buf_borrow`) --
// callers (dom.c) still own the box and must drop it themselves afterward.
int32_t kk_js_obj_slot_borrow(kk_box_t box, kk_context_t* ctx) {
  void* p = kk_cptr_raw_unbox_borrowed(box, ctx);
  return (int32_t)(intptr_t)p;
}

// Debug/verify export (see ../readme.md, "Slot-recycling proof", and
// index.html's verify hook): `allocated - freed` == the number of
// currently-live slots. Exported directly as a wasm core-module export --
// read straight from JS after the demo's synthetic clicks run, no
// Koka-level wrapper needed for this one (it exists purely to let the page
// assert that Perceus actually drove a table.set(null) for a
// scope-local element, proving drop -> release really fired).
__attribute__((export_name("koka:dom/live-slots")))
int32_t kk_js_live_slots(void) {
  return kk_js_allocated_count - kk_js_freed_count;
}

// ---- release-debugging exports (see ../readme.md, "Debugging release") ----
// Together these let the HOST enumerate every live slot and describe what it
// still references (index.html's `kokaDebug.slots()`): `slot-high-water` is
// the walk bound, `slot-ref` hands the externref at a slot back to JS (null
// if free). Purely observational -- nothing here changes ownership.

__attribute__((export_name("koka:dom/slot-high-water")))
int32_t kk_js_slot_high_water(void) {
  return kk_js_next_slot;
}

__attribute__((export_name("koka:dom/slot-ref")))
__externref_t kk_js_slot_ref(int32_t slot) {
  return kk_js_obj_get(slot);
}

// lifetime counters, for rate/churn debugging (live == allocated - freed)
__attribute__((export_name("koka:dom/slots-allocated")))
int32_t kk_js_slots_allocated(void) { return kk_js_allocated_count; }

__attribute__((export_name("koka:dom/slots-freed")))
int32_t kk_js_slots_freed(void) { return kk_js_freed_count; }
