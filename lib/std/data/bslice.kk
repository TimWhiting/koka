/*---------------------------------------------------------------------------
  Copyright 2024, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Byte slices
module std/data/bslice
import std/data/bytes

// A byte slice
pub struct bslice 
  bytes: bytes
  start: int
  len: int // The length of the slice
  total-len: int // Cached length of the backing byte array

// Create a byte slice from bytes
pub fun slice(b: bytes): bslice
  val len = b.length.int
  Bslice(b, 0, len, len)

// O(1). Advance the start position of a byte slice by `count` bytes
// up to the end of the byte array.
// A negative `count` advances the start position backwards up to index 0.
pub fun advance(b: bslice, n: int): bslice
  val Bslice(bts, start, len, tl) = b
  if n > 0 then
    if n > len then // If advancing past the current length, advance to the end
      Bslice(bts, start + len, 0, tl)
    else
      Bslice(bts, start + n, len - n, tl)
  elif n < 0 then
    if start + n < 0 then // If advancing past the beginning, advance to the beginning
      Bslice(bts, 0, len + start, tl)
    else 
      Bslice(bts, start + n, len - n, tl)
  else 
    Bslice(bts, start, len, tl)

// O(1). Extend a byte slice by `count` bytes up to the end of the byte slice.
// A negative `count` shrinks the slice up to the empty slice.
pub fun extend(b: bslice, n: int): bslice
  val Bslice(bts, start, len, tl) = b
  if n > 0 then
    if n > (tl - len) then // If extending past total end of bytes, extend to end of bytes
      Bslice(bts, start, tl - start, tl)
    else
      Bslice(bts, start, len + n, tl)
  elif n < 0 then
    if len + n < 0 then // If extending past start of slice, extend to start point
      Bslice(bts, start, 0, tl)
    else
      Bslice(bts, start, len + n, tl)
  else 
    Bslice(bts, start, len, tl)

// Truncates the slice to length 0
pub fun truncate(b: bslice): bslice 
  val Bslice(bts, start, _, tl) = b
  Bslice(bts, start, 0, tl)

// O(1). Return the byte slice from the start of the byte array up to the
// start of the `slice` argument.
pub fun before(slice: bslice): bslice
  val Bslice(bts, start, _, tl) = slice
  Bslice(bts, 0, start, tl)

// O(1). Return the byte slice from the end of the `slice` argument
// to the end of the byte array.
pub fun after(slice: bslice): bslice
  val Bslice(bts, start, len, tl) = slice
  val new-start = start + len
  Bslice(bts, new-start, tl - new-start, tl)

// Get's the byte at the offset `i`
pub fun @index( ^b : bslice, i : int ) : exn int8
  val Bslice(bts, start, len, _) = b
  if i < 0 || i >= len then throw("index out of bounds", ExnRange)
  bts.unsafe-index((start + i).ssize_t)