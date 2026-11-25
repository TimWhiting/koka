// FBIP evaluation bench: does Perceus reuse actually fire on the vdom patch
// shapes at runtime? Run via run-bench.mjs (fake-DOM node host) with and
// without --fno-reuse; compare wall time and (with --fallocstats +
// MIMALLOC_SHOW_STATS=1) allocation counts. See ../readme.md.
module bench

import std/time/timer
import std/time/duration
import std/num/float64
import html
import vdom
import dom

val rows = 200
val iters = 500

fun row( i : int, sel : int ) : html<int>
  li([key(i.show), class_(if i == sel then "sel" else "row")],
     [text("item " ++ i.show)])

fun view( sel : int ) : html<int>
  ul([], list(1, rows).map(fn(i) row(i, sel)))

fun go( i : int, t : node<int>, root : element, emit : int -> ioc () ) : <ioc,exn> node<int>
  if i == 0 then t
  else go(i - 1, patch(t, view(i % rows), root, emit), root, emit)

pub fun main()
  match get-element-by-id("root")
    Nothing -> println("bench: no #root element (run under run-bench.mjs)")
    Just(root) ->
      val emit = fn(m : int) ()
      val tree = mount(view(0), root, emit)
      val (d, _t2) = elapsed
        go(iters, tree, root, emit)
      println("bench: " ++ rows.show ++ " rows x " ++ iters.show ++ " patches (1 class change each): "
              ++ (d.milli-seconds.float64).show ++ " ms")
