// A counter COMPONENT with its own closed msg type -- including an async
// "command": `AddSlowly` spawns a task that waits half a second and returns
// as `Added(10)`. The parent embeds this update with `map-dispatch` (see
// main.kk) so the spawned task's result wraps into the parent's msg type.
module counter

import std/time/duration
import std/async
import ui/widget
import ui/style/default
import ui/app

pub type msg
  Increment
  Decrement
  AddSlowly
  Added( n : int )

pub struct model( count : int, pending : bool )

pub fun init() : model
  Model(0, False)

pub fun view( m : model, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  card(column([
    accented("counter", 18.0),
    row([
      primary-button("−", Decrement, size = 20.0),
      body(m.count.show, size = 34.0),
      primary-button("+", Increment, size = 20.0)
    ]),
    quiet-button(if m.pending then "adding…" else "+10 (async)", AddSlowly)
  ], gap = 12.0))

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
