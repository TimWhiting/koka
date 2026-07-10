/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The app runtime: an Elm-style loop with the machinery deleted.
//
//   app( init, view, update )
//
// - one message channel; every DOM handler is a message value routed into it
// - `update` is continuation-free (the `dispatch` effect's `fun spawn` is the
//   only doorway to async work, and the task runs OUTSIDE the UI path) — see
//   the design spec's style rule: view/update/diff never capture the model or
//   tree in a continuation, keeping them uniquely owned.
// - no Cmd: spawn's task IS the async action, its result is a message
// - no Sub: any strand can emit into the channel (see `every` below)
module web-ui/app

import std/async
import std/core/undiv
import std/time/duration
import std/async/interleave
import web-ui/html
import web-ui/vdom
import web-ui/dom

// Request async work from within `update` without doing async work there:
// the task runs interleaved at the loop boundary and its result comes back
// around as an ordinary message.
pub effect dispatch<a>
  fun spawn( task : () -> <async,ioc> a ) : ()

// Run an application: mount `view(init)` under the element with id
// `root-id`, then loop forever: receive a message, update, re-view, patch.
// Embed a child component's `update` (with its own msg type and its own
// spawned tasks) into a parent: child spawns are wrapped into parent
// messages, so components compose without sharing a msg type.
pub fun map-dispatch<a,b,c>( wrap : a -> b, action : () -> dispatch<a> c ) : dispatch<b> c
  with fun spawn(task)
    spawn( fn() wrap(task()) )
  action()

pub fun app<model,msg>( init : model,
                        view : model -> html<msg>,
                        update : (model, msg) -> dispatch<msg> model,
                        root-id : string = "app",
                        subs : list<(channel<msg>) -> <async,ioc> ()> = [] ) : <async,ioc> ()
  // `ioc` already includes div (the loop is deliberately never-returning) and
  // ndet; exn is discharged here so a user `main` is just `app(...)`.
  with handle/try fn(err)
    println("koka/app: uncaught exception: " ++ err.show)
  val ch = channel()
  val root = match get-element-by-id(root-id)
    Just(el) -> el
    Nothing  -> throw("app: no element with id '" ++ root-id ++ "'")
  val emit = fn(m) ch.emit-io(m)
  val tree0 = mount(view(init), root, emit)
  // ONE interleaving for the app's whole lifetime: the loop, every
  // subscription, and every spawned task are strands of it, forked
  // dynamically (`forking`). Spawning must never nest a fresh interleaving
  // around the running loop -- each nesting would push handler scopes that
  // can only unwind when the (never-returning) loop does, overflowing the
  // stack as spawns accumulate.
  forking fn(fork)
    subs.foreach fn(s)
      fork( fn() s(ch) )
    loop(ch, root, emit, init, tree0, view, update, fork)
  ()

fun loop<model,msg>( ch : channel<msg>, root : element, emit : msg -> ioc (),
                     model : model, tree : node<msg>,
                     view : model -> html<msg>,
                     update : (model, msg) -> dispatch<msg> model,
                     fork : (() -> <async,ioc,exn> ()) -> ioc () ) : <async,ioc,exn> ()
  val msg = ch.receive
  // collect spawned tasks; update itself stays continuation-free
  val tasks = ref([])
  val model2 =
    with fun spawn(task)
      tasks := Cons(task, !tasks)
    update(model, msg)
  val tree2 = patch(tree, view(model2), root, emit)
  // each task becomes a strand of the app's one interleaving; its result
  // re-enters as a message
  (!tasks).foreach fn(t)
    fork( fn() ch.emit-io(t()) )
  loop(ch, root, emit, model2, tree2, view, update, fork)

// A subscription is just a strand: emit `msg` every `secs` forever.
pub fun every<msg>( ch : channel<msg>, secs : duration, msg : msg ) : <async,ioc> ()
  wait(secs)
  ch.emit-io(msg)
  every(ch, secs, msg)
