module std/core/cextern

import std/num/int32
import std/core/types
import std/core/int

extern import
  c header-file "inline/cextern.h"

// A managed koka pointer to C memory
// Owned values can be freely passed around, captured in lambdas, escape their scope, etc.
pub alias owned-c<t> = extern-owned<t>

// A borrowed koka pointer to C memory during a scope s
// Borrowed values are only guaranteed valid during their scope, should not escape the scope
// For example an `owned-c<array<t>>` should only allow borrowed references to the middle of an array during a scope where the owned pointer will not be dropped
pub alias borrowed-c<s::S,t> = extern-borrowed<t>

// A raw pointer to C memory
pub type c-pointer<t>

// An opaque type to designate c-array types in Koka
pub type c-array<t>

// A type alias for a null pointer of type `t`
pub alias c-null<t> = c-pointer<t>

// The null pointer in C
pub inline extern cnull(): c-null<t>
  c inline "(intptr_t)0"

// A null callback pointer
pub val null-cb = 0.intptr_t

// Needs to be extern otherwise, the compiler will optimize out the function and not keep the reference alive
// Ensure that a reference is > 1 until after this point
pub extern owned/keepalive(^s: owned-c<a>): <> ()
  ""

// Release a reference (decref an owned reference)
pub fun owned/release(s: owned-c<a>): <> ()
  ()

// Retain a reference (incref an owned reference)
pub extern owned/retain(s: owned-c<a>): <> ()
  ""

pub inline extern int/ptr<t>(i: intptr_t): c-pointer<t>
  c inline "(intptr_t)#1"

pub inline extern carray/intptr<t>(c: c-array<t>): intptr_t
  c inline "#1"

pub inline extern carray/ptr<t>(c: c-array<t>): c-pointer<t>
  c inline "#1"

pub inline extern intptr/carray<t>(c: intptr_t): c-array<t>
  c inline "#1"

pub inline extern ptr/carray<t>(c: c-pointer<t>): c-array<t>
  c inline "#1"

// Allow casting between different types of pointers
pub inline extern unsafe/cptr-cast<s>(c: c-pointer<t>): c-pointer<s>
  c inline "#1"

// Allocate `n*size-of` bytes of memory using kk_malloc and return a pointer to the allocated memory
inline extern int/malloc<t>(n: int32, size-of: int32): c-pointer<t>
  c inline "(kk_addr_t)kk_malloc(#1*#2, kk_context())"

// Allocate `n*size-of` bytes of memory using C's malloc and return a pointer to the allocated memory
inline extern int/malloc-c<t>(n: int32, size-of: int32): c-pointer<t>
  c inline "(kk_addr_t)malloc(#1*#2)"

// Allocate a single element of type `t` using `kk_malloc` and return a managed pointer
// Type `t` should:
// - Be an opaque type in Koka corresponding to a C type (e.g. `pub type cstruct` with no members)
// - Have a `size-of` function that returns the size of the structure in bytes
pub inline fun single/malloc<t>(?size-of: (c-null<t>) -> int32): owned-c<t>
  int/malloc(1.int32, size-of(cnull())).c-own-extern

// Allocate `n` elements of type `t` using `kk_malloc` and return a managed pointer to the array
// Type `t` should:
// - Be an opaque type in Koka corresponding to a C type (e.g. `pub type cstruct` with no members)
// - Have a `size-of` function that returns the size of the structure in bytes
pub inline fun array/malloc<t>(n: int32, ?size-of: (c-null<t>) -> int32): owned-c<c-array<t>>
  int/malloc(n, size-of(cnull())).c-own-extern

// Allocate a single element of type `t` using C's `malloc` and return a managed pointer
// Type `t` should:
// - Be an opaque type in Koka corresponding to a C type (e.g. `pub type cstruct` with no members)
// - Have a `size-of` function that returns the size of the structure in bytes
pub inline fun single/malloc-c<t>(?size-of: (c-null<t>) -> int32): owned-c<t>
  int/malloc-c(1.int32, size-of(cnull())).c-own-free-calloc-extern

// Allocate `n` elements of type `t` using C's `malloc` and return a managed pointer to the array
// Type `t` should:
// - Be an opaque type in Koka corresponding to a C type (e.g. `pub type cstruct` with no members)
// - Have a `size-of` function that returns the size of the structure in bytes
pub inline fun array/malloc-c<t>(n: int32, ?size-of: (c-null<t>) -> int32): owned-c<c-array<t>>
  int/malloc-c(n, size-of(cnull())).c-own-free-calloc-extern

// !!!WARNING!!! UNSAFE API
// Allocate `n` elements of type `t` using `kk_malloc` and return a managed pointer to the array
// Type `t` should:
// - Be an opaque type in Koka corresponding to a C type (e.g. `pub type cstruct` with no members)
// - Have a `size-of` function that returns the size of the structure in bytes
//
// NOTES:
// Prefer using `array/malloc` or `single/malloc` instead of this function which return a managed pointer.
// Raw `c-pointer<t>` should be used in low-level generated koka ffi functions since the pointer is unknown to be managed or not.
// Conversion routines for `owned-c<t>` and `borrowed-c<s,t>` then should be used to get the raw pointers to be used in the ffi functions
// Higher level apis to c libraries should then provide an interface using `owned-c<t>` and `borrowed-c<s,t>` instead of `c-pointer<t>`
pub inline fun ptr/unsafe-malloc<t>(n: int32, ?size-of: (c-null<t>) -> int32): c-pointer<t>
  int/malloc(n, size-of(cnull()))

// !!!WARNING!!! UNSAFE API
// Allocate `n` elements of type `t` using C's `malloc` and return a managed pointer to the array
// Type `t` should:
// - Be an opaque type in Koka corresponding to a C type (e.g. `pub type cstruct` with no members)
// - Have a `size-of` function that returns the size of the structure in bytes
//
// NOTES:
// Prefer using `array/malloc-c` or `single/malloc-c` instead of this function which return a managed pointer.
// Raw `c-pointer<t>` should be used in low-level generated koka ffi functions since the pointer is unknown to be managed or not.
// Conversion routines for `owned-c<t>` and `borrowed-c<s,t>` then should be used to get the raw pointers to be used in the ffi functions
// Higher level apis to c libraries should then provide an interface using `owned-c<t>` and `borrowed-c<s,t>` instead of `c-pointer<t>`
pub inline fun ptr/unsafe-malloc-c<t>(n: int32, ?size-of: (c-null<t>) -> int32): c-pointer<t>
  int/malloc-c(n, size-of(cnull()))

// Transform a C ptr into a managed koka value, which will be freed by `kk_free` when koka's reference count reaches 0
inline extern c-own-extern(c: c-pointer<a>): owned-c<a>
  c inline "kk_cptr_raw_box(&kk_free_fun, (void *)#1, kk_context())"

// Transform a C ptr into a managed koka value, which will be freed by C's `free` when koka's reference count reaches 0
inline extern c-own-free-calloc-extern(c: c-pointer<a>): owned-c<a>
  c inline "kk_cptr_raw_box(&kk_free_calloc, (void *)#1, kk_context())"

// Transform a C ptr `c` into a koka value that holds the c reference without freeing it
// The pointer should be valid for the duration of the callback `f`.
inline extern c-borrow(c: c-pointer<t>, f: forall<s> borrowed-c<s,t> -> e a): e a
  c "kk_borrow_ptr"

// !!!WARNING!!!: Extremely unsafe API (needed for `c-borrow`), get approval to use anywhere else.
inline extern unsafe-cast<s>(b: c-pointer<t>): borrowed-c<s,t>
  c inline "#1"

// Transform an unmanaged C ptr into a managed koka reference to C memory
// Ensure the pointer is not going to be freed by C code, otherwise use `c-borrow` instead
// Also ensure the memory was allocated using `kk_malloc`
pub inline fun c-own<t>(t: c-pointer<t>): owned-c<t>
  t.c-own-extern

// Transform an unmanaged C ptr into a managed koka reference to C memory
// Ensure the pointer is not going to be freed by C code, otherwise use `c-borrow` instead
// Also ensure the memory was allocated using C's `malloc`
pub fun c-own-free-calloc<t>(t: c-pointer<t>): owned-c<t>
  t.c-own-free-calloc-extern

// Transform a koka `owned-c` managed pointer into a C ptr 
// Keeps the koka reference alive during the scope of the callback `f`
pub inline extern owned/with-ptr(^t: owned-c<t>, f: c-pointer<t> -> e a): e a
  c "kk_owned_with_ptr"

// Transform a koka `borrowed-c` managed pointer into a C ptr
// Keeps the koka reference alive during the scope of the callback `f`
pub inline extern borrowed/with-ptr(^t: borrowed-c<s,t>, f: c-pointer<t> -> e a): e a
  c "kk_borrowed_with_ptr"

// !!!WARNING!!! Extremely UNSAFE API
// Get the raw C pointer from a `borrowed-c` managed pointer to use immediately in an ffi function
// This doesn't return a typed pointer, and accepts any boxed type as input, so it is very dangerous
//   Use `borrowed/with-ptr` most of the time and
//       `borrow/use-ffi-ptr` if directly passing to an safe ffi call
pub inline extern unsafe-borrowed-ffi-ptr-extern<t>(c: borrowed-c<s,t>): c-pointer<t>
  c inline "(kk_addr_t)kk_cptr_unbox_borrowed(#1, kk_context())"

// !!!WARNING!!! UNSAFE API
// Get the raw C pointer from an `borrowed-c` managed pointer to use immediately in an ffi function
// Not safe to pass around Koka code
// However, since an immediate use is still within the scope of the `borrowed-c` it is safe
//   This is due borrowed pointers being guaranteed to be valid during their whole scope (the lambda enclosing the call to this method) 
//   A similar api for `owned-c` is not possible since converting an owned pointer to a raw pointer could allow the owned pointer to be freed if this was its last use
//   For owned pointers use `owned/with-ptr` instead
pub inline fun borrow/use-ffi-ptr<t>(c: borrowed-c<s,t>): c-pointer<t>
  c.unsafe-borrowed-ffi-ptr-extern

// Transform a koka `owned-c` managed pointer to an array into a C ptr pointing to the element at index `idx` of type `t` and size `size-of(cnull())`
// Keeps the koka reference alive during the scope of the callback `f`
// This is guaranteed due to be this being an external function (`f` is not inlineable), and `t` being borrowed
pub inline extern offset/with-ptr(^t: owned-c<c-array<t>>, idx: ssize_t, f: c-pointer<t> -> e a, size-of: int32): e a
  c "kk_owned_with_ptr_idx"

// Transform a koka `owned-c` managed pointer to an array into a C ptr pointing to the element at index `idx` of type `t` and size `size-of(cnull())`
// Keeps the koka reference alive during the scope of the callback `f`
pub inline fun c-array/with-ptr(t: owned-c<c-array<t>>, idx: ssize_t, f: forall<s> borrowed-c<s,t> -> e a, ?size-of: (c-null<t>) -> int32): e a
  offset/with-ptr(t, idx, fn(p) c-borrow(p, f), size-of(cnull()))

// Transform an assumed pointer to a C string into a Koka string
// Copies the memory
pub inline extern ptr/to-string(ptr: c-pointer<int8>): string
  c inline "kk_string_alloc_raw((const char *)#1, false, kk_context())"

// Transform an assumed pointer to a C string of length len into a Koka string
// Copies the memory
// Assume the array is non-null terminated and adds the terminating character
pub inline extern strlen-ptr/to-string(ptr: c-pointer<int8>, len: int64): string
  c inline "kk_string_alloc_raw_buff(#2, (char *)#1, false, kk_context())"

// Borrows the c pointer to a koka managed string for the duration of the callback `f`
inline extern ptr/with-c-string(^s: string, f: c-pointer<int8> -> e a): e a
  c "kk_with_c_string"

// Borrows the c pointer to a koka managed string for the duration of the callback `f`
pub inline fun cptr/with-c-string(^s: string, f: forall<s> borrowed-c<s,int8> -> e a): e a
  with-c-string(s, fn(p) c-borrow(p, f))
