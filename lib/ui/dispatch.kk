/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The `dispatch` effect: request async work from within `update` without
// doing async work there -- the runtime (ui/app's loop, or ui/test's) runs
// the task interleaved at the loop boundary and its result comes back around
// as an ordinary message. Lives OUTSIDE ui/app so backend-free consumers
// (ui/test) can name update's type without pulling in a platform backend.
module ui/dispatch

import std/async
import ui/widget   // ioc

pub effect dispatch<a>
  fun spawn( task : () -> <async,ioc> a ) : ()

// Embed a child component's `update` (with its own msg type and its own
// spawned tasks) into a parent: child spawns are wrapped into parent
// messages, so components compose without sharing a msg type.
pub fun map-dispatch<a,b,c>( wrap : a -> b, action : () -> dispatch<a> c ) : dispatch<b> c
  with fun spawn(task)
    spawn( fn() wrap(task()) )
  action()
