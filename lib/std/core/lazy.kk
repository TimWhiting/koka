/*---------------------------------------------------------------------------
  Copyright 2012-2024, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Internal functions to support lazy types
//
module std/core/lazy

import std/core/types

// note: all of the following definitions will be made hidden (prefix with `@`)
// in the future and are only exposed for now for experimentation

// internal: marker for lazy values that get matched to evaluate to whnf
pub fip extern whnf-target(target : a) : ()
  inline "/**/"

// internal: explicitly force update-in-place for lazy values
pub fip extern whnf-update(target : a, x : a) : a
  inline "#1"

// internal: evaluate atomically (or return `false` if already evaluated)
pub inline fip extern atomic-enter(^target : a, lazy-tag: int32 ) : bool
  c "kk_lazy_atomic_enter"

// internal: release an atomically evaluated value
pub inline fip extern atomic-leave(target : a) : ()
  c "kk_lazy_atomic_leave"


// internal: test if a lazy value is in whnf
pub inline fip extern datatype-is-whnf(^x:a, lazy-tag:int32) : bool
  c "kk_datatype_is_whnf"

// internal: test if a heap allocated lazy value is in whnf
pub inline fip extern datatype-ptr-is-whnf(^x:a, lazy-tag:int32) : bool
  c "kk_datatype_ptr_is_whnf"


// internal: test if a heap allocated data type is unique
pub inline fip extern datatype-ptr-is-unique(^x:a) : bool
  c "kk_datatype_ptr_is_unique"

// internal: test if a heap allocated data type is thread-shared
pub inline fip extern datatype-ptr-is-thread-shared(^x : a) : bool
  c "kk_datatype_ptr_is_thread_shared"

val internal = 42
