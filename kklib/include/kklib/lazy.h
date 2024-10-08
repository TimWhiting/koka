#pragma once
#ifndef KK_LAZY_H
#define KK_LAZY_H
/*---------------------------------------------------------------------------
  Copyright 2024, Microsoft Research, Daan Leijen, Anton Lorenzen

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// returns `false` if updated and unblocked (we still need eval in such case due to indirections)
// returns `true` if blocked and now can be evaluated
kk_decl_export bool kk_lazy_atomic_thread_enter(kk_block_t* lazy /* borrow */, int32_t indirect_tag, kk_context_t* ctx);
kk_decl_export void kk_lazy_atomic_thread_leave(kk_block_t* lazy, kk_context_t* ctx);


static inline bool kk_lazy_atomic_enter(kk_datatype_ptr_t lazy /* borrow */, int32_t indirect_tag, kk_context_t* ctx) {
  kk_block_t* b = kk_datatype_as_ptr(lazy,ctx);
  if kk_likely(!kk_block_is_thread_shared(b) && kk_block_field_idx(b) != KK_FIELD_IDX_LAZY_BLOCKED) {
    kk_block_field_idx_set(b,KK_FIELD_IDX_LAZY_BLOCKED);
    return true;
  }
  else {
    return kk_lazy_atomic_thread_enter(b,indirect_tag,ctx);
  }
}

static inline void kk_lazy_atomic_leave(kk_datatype_t lazy, kk_context_t* ctx) {
  kk_block_t* b = kk_datatype_as_ptr(lazy,ctx);
  if kk_likely(!kk_block_is_thread_shared(b)) {
    kk_assert(kk_block_field_idx(b) == KK_FIELD_IDX_LAZY_BLOCKED);
    kk_block_field_idx_set(b,0);
    kk_block_drop(b,ctx);
  }
  else {
    kk_lazy_atomic_thread_leave(b,ctx);
  }
}

static inline bool kk_datatype_is_whnf( kk_datatype_t lazy, int32_t indirect_tag, kk_context_t* ctx ) {
  return (kk_datatype_is_singleton(lazy) || kk_datatype_ptr_tag(lazy,ctx) < (kk_tag_t)indirect_tag);
}

static inline bool kk_datatype_ptr_is_whnf( kk_datatype_t lazy, int32_t indirect_tag, kk_context_t* ctx ) {
  kk_assert(kk_datatype_is_ptr(lazy));
  return (kk_datatype_ptr_tag(lazy,ctx) < (kk_tag_t)indirect_tag);
}



#endif // KK_LAZY_H
