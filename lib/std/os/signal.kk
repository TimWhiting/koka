/*---------------------------------------------------------------------------
  Copyright 2023 Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

pub import std/os/uv
import std/num/int32

extern import
  c file "signal-inline.c"

value struct uvSignal {internal: intptr_t}

extern uvSignalInit(): io-noexn uvSignal
  c "kk_uv_signal_alloc" 
extern uvSignalStart(h: uvSignal, cb: (uvSignal) -> io-noexn (), signal: int32): io-noexn int32
  c "kk_uv_signal_start"
extern uvSignalStartOneShot(h: uvSignal, cb: () -> io-noexn (), signal: int32): io-noexn int32
  c "kk_uv_signal_start_oneshot"
extern uvSignalStop(h: uvSignal): io-noexn int32
  c "kk_uv_signal_stop"
pub extern signum(h: uvSignal): io-noexn int32
  c "kk_uv_signal_num"

pub val sSIGINT = ssSIGINT()
extern ssSIGINT(): int32
  c inline "SIGINT"

pub fun signal-start(signal: int32, cb: (uvSignal) -> io-noexn ()): io-noexn uvStatusCode
  uvSignalStart(uvSignalInit(), cb, signal).toStatusCode

pub fun signal-start-oneshot(signal: int32, cb: () -> io-noexn ()): io-noexn uvStatusCode
  uvSignalStartOneShot(uvSignalInit(), cb, signal).toStatusCode

pub fun signal-stop(h: uvSignal): io-noexn uvStatusCode
  uvSignalStop(h).toStatusCode