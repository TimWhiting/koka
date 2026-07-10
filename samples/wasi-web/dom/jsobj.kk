/*---------------------------------------------------------------------------
  Copyright 2026, Microsoft Research, Daan Leijen, Tim Whiting

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// `kk_js_obj` -- a module-local externref table (see jsobj.c) giving Koka a
// Perceus-owned handle onto arbitrary JS/host objects (DOM elements, for
// now). Sample-scoped for now (demo-local, not `lib/std`); promotion to
// `lib/std` is a later decision, noted in ../readme.md.
//
// This module has no imports/exports of its own -- `dom.kk` is the only
// consumer, calling `box` to wrap a table slot right after allocating it
// (in `dom.c`, which forward-declares jsobj.c's non-static C functions the
// same way `dom.c` forward-declares `evloop.c`'s `kk_wasiweb_loop_ref`, see
// that file's comments). No Koka-level `alloc`/`get` wrapper is needed here:
// only C code (dom.c) ever calls those, since only C code can hold a raw
// `__externref_t` value.
module jsobj

extern import
  c file "jsobj.c"

// Wraps a table slot (allocated by C code, e.g. dom.c's
// `kk_wasiweb_dom_get_element_by_id`) into a Perceus-refcounted `any`.
// Dropping the last reference to the returned value is what releases the
// underlying JS object -- see jsobj.c's `kk_js_obj_free_fun`.
pub extern box(slot : int32) : any
  c "kk_js_obj_box"
