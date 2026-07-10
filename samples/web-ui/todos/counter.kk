/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// A counter COMPONENT with its own closed msg type -- including an async
// "command": `AddSlowly` spawns a task (via the dispatch effect) that waits
// half a second and then comes back around as `Added(10)`. The component
// never does async work in its own update path (the style rule); the parent
// embeds this update with `map-dispatch(CounterMsg, ...)` (see main.kk) so
// the spawned task's result is wrapped into the parent's msg type.
module counter

import std/time/duration
import std/async
import web-ui/html
import web-ui/app
import web-ui/theme
import web-ui/ui

pub type msg
  Increment
  Decrement
  AddSlowly            // spawn: wait 500ms, then Added(10)
  Added( n : int )

pub struct model( count : int, pending : bool )

pub fun init() : model
  Model(0, False)

pub fun view( m : model ) : <keytree,theme> html<msg>
  page("Counter", [card([class_("counter")], [column([], [
    row([], [
      primary-button([id_("dec"), title_("decrement"), on-click(Decrement)], [text("−")]),
      span([id_("count"), class_("count"), accent-style("min-width:2em;text-align:center")],
           [text(m.count.show)]),
      primary-button([id_("inc"), title_("increment"), on-click(Increment)], [text("+")])
    ]),
    // disabled while the spawned task is in flight: the button greys out and
    // re-enables when `Added` comes back around as a message
    quiet-button([id_("slow"), disabled(m.pending), title_("adds 10 after a delay, via a spawned task"),
                  on-click(AddSlowly)],
                 [text(if m.pending then "Adding…" else "Add 10 (async)")])
  ])])])

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Increment -> m(count = m.count + 1)
    Decrement -> m(count = m.count - 1)
    AddSlowly ->
      if m.pending then m else
        spawn fn()
          wait(500.milli-seconds)
          Added(10)
        m(pending = True)
    Added(n) -> Model(m.count + n, False)
