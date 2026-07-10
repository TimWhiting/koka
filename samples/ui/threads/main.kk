// Data-offload threading: a heavy PURE computation runs on a WORKER THREAD
// (native libuv threadpool) via `compute`, so the UI thread stays responsive.
// The FPS meter demos the DEMAND-DRIVEN frame clock: parked (no frames at
// all) until you start the bouncing-bar animation; then it reads the real
// frame rate -- which HOLDS during a native compute, and visibly stalls on
// web/wasi where `compute` degrades to a cooperative strand sharing the loop.
module main

import std/async
import std/async/thread
import std/os/env
import std/num/float64
import ui/widget
import ui/style/default
import ui/app

struct model( spinning : bool = False, computing : bool = False,
              result : maybe<int> = Nothing, n : int = 38 )

type msg
  ToggleSpin
  StartCompute( n : int )
  Computed( res : int )

// heavy, self-contained PURE work (recursion => `div`, which `pure` admits): the
// canonical CPU-bound task. Long enough at n=38 to watch the UI stay live.
fun fib( n : int ) : div int
  if n < 2 then n else fib(n - 1) + fib(n - 2)

// A live FPS meter: smooth 1000/dt over the anim-time deltas of the builds
// that actually happen -- it never requests frames itself, so it reads 0
// ("parked") until something animates. The cell is QUIET (a transition write
// per frame would render an echo frame and halve the native rate).
fun fps-meter( live : bool, key : key ) : <keytree,uistate,ioc> string
  val now = anim-time()
  val (cell, set-cell) = use-state-quiet((now, 0.0))   // (last build time, smoothed fps)
  if !live then
    set-cell(fn(_) (now, 0.0))
    "parked — no frames"
  else
    val dt = now - cell.fst
    if dt > 0.0 then
      val inst = 1000.0 / dt
      val smoothed = if cell.snd == 0.0 then inst else cell.snd * 0.9 + inst * 0.1
      set-cell(fn(_) (now, smoothed))
      smoothed.int.show ++ " fps"
    else
      cell.snd.int.show ++ " fps"

// the animation that CREATES frame demand: a bar bouncing between 20 and 240,
// flipping its target each time the tween settles (one transition per bounce)
fun bounce-bar( spinning : bool, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val (phase, set-phase) = use-state(True)
  val target = if !spinning then 0.0 elif phase then 240.0 else 20.0
  val w = animate(target, duration = 500.0, ease = ease-in-out)
  if spinning && w == target then
    set-phase(fn(p) !p)
  stack([ (0.0, 0.0, rect(240.0, 10.0, bg = Just(Fill(theme.palette/surface, 5.0)))),
          (0.0, 0.0, rect(w.max(4.0), 10.0, bg = Just(Fill(theme.accent, 5.0)))) ])

fun themed-view( m : model , key : key) : <keytree,uistate,ioc,theme> widget<msg>
  val status = if m.computing then "computing fib(" ++ m.n.show ++ ") on a worker…"
               else match m.result
                 Just(r) -> "fib(" ++ (m.n - 1).show ++ ") = " ++ r.show
                 Nothing -> "idle"
  // static-under-animation subtrees sit behind memo boundaries: while only the
  // clock drives frames (steady animation), they are reused by pointer and
  // skip rebuild + relayout; model messages force a full rebuild (dirty storm)
  // so the closure-captured `m`/`status` can never go stale
  fun header( key : key ) : <keytree,uistate,ioc,theme> widget<msg>
    column([
      body("The frame clock is demand-driven: parked until something animates."),
      body("Animate, then Compute: on native the work runs on a worker thread"),
      body("and the FPS holds; on the web the loop is shared and it stalls."),
    ])
  fun controls( key : key ) : <keytree,uistate,ioc,theme> widget<msg>
    row([ primary-button(if m.spinning then "Stop" else "Animate", ToggleSpin),
          primary-button(if m.computing then "Computing…" else "Compute fib(" ++ m.n.show ++ ")", StartCompute(m.n)) ])
  fun status-line( key : key ) : <keytree,uistate,ioc,theme> widget<msg>
    body(status)
  page("Koka × threads", [
    memo(header),
    card( column([
      accented(fps-meter(m.spinning, scope("fps")), 40.0),
      bounce-bar(m.spinning, scope("bar")),
      memo(controls),
      memo(status-line),
    ], gap = 16.0) ),
  ])

fun view( m : model , key : key) : <keytree,uistate,ioc> widget<msg>
  with val theme = dark
  themed-view(m, key)

fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    ToggleSpin -> m(spinning = !m.spinning)
    StartCompute(n) ->
      if m.computing then m else
        // offload fib(38) to a worker thread; its result returns as a message
        spawn fn()
          Computed( compute( fn() fib(n) ) )
        m(computing = True, result = Nothing)
    Computed(res) -> m(computing = False, n = m.n + 1, result = Just(res))

pub fun main()
  // --spin starts the animation immediately (for headless CPU measurement
  // against the flutter twin, whose AUTOSTART define does the same)
  val spin = get-args().any(fn(a) a == "--spin")
  app( Model(spinning = spin), view, update,
       App-config("Koka × threads", 480, 380), threads = Threaded )
