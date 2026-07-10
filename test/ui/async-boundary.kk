// Headless exercise of `future-boundary` (ui/async): an async `run` drives a
// boundary through placeholder -> ready / failed, a Retry re-runs a
// fail-then-succeed run (the generation mechanism), and `min-load` holds the
// placeholder past a fast resolve. Four independent boundaries (one per case),
// each scoped + given distinct placeholder/ready texts, share one app instance;
// the harness's async-pump strand (ui/test) runs the `run`s. Real `wait`s (not
// the fake frame clock) time the settles, so the assertions are wall-time
// based -- generous margins keep them robust.
module async-boundary

import std/core/unsafe
import std/async
import std/num/float64
import std/time/duration
import ui/widget
import ui/state
import ui/async
import ui/test

pub struct model()

pub type msg
  Noop

// the retry boundary's run reads this: attempt 1 throws, later attempts
// succeed. Reset at the start of each scenario so it is deterministic
// regardless of the other scenarios' (unasserted) runs of this same boundary.
val attempts : ref<global,int> = unsafe-total{ ref(0) }

// resolves after 30ms -> "hello"
fun fut-run() : <async,ioc> string
  wait(30.milli-seconds)
  "hello"

// throws after 10ms
fun err-run() : <async,ioc,exn> string
  wait(10.milli-seconds)
  throw("boom")

// fails the FIRST time, succeeds after (the generation/retry pin)
fun rty-run() : <async,ioc,exn> string
  attempts := !attempts + 1
  wait(5.milli-seconds)
  if !attempts <= 1 then throw("fail once") else "recovered"

// resolves in ~1ms; min-load holds the placeholder for 60ms
fun slow-run() : <async,ioc> string
  wait(1.milli-seconds)
  "done"

// resolves after 20ms -> "memo-hello" (used by the memo-wrapped scenario)
fun memo-fut-run() : <async,ioc> string
  wait(20.milli-seconds)
  "memo-hello"

// a scoped default-error-shaped failure builder (so the Retry control is
// addressable under `pfx ++ "-retry"`)
fun scoped-failed( pfx : string, e : exception, retry : () -> <uistate,ioc> (), ?key : key ) : <keytree,uistate,ioc> widget<msg>
  column([ text("failed: " ++ e.show, ?key = scope(pfx ++ "-msg")),
           act(box(text("Retry", ?key = scope(pfx ++ "-retry-lbl")), padding = 6.0), retry, ?key = scope(pfx ++ "-retry")) ])

// a future-boundary nested INSIDE a `memo` boundary -- the framework's own
// recommended pattern (e.g. an async image row inside a memoized
// lazy-column). No model message ever touches this subtree, so nothing else
// forces a dirty storm/rebuild: the async completion write is the ONLY thing
// that can dirty the memo. This pins Finding 1 (task-2-review.md).
fun memo-pane( key : key ) : <keytree,uistate,ioc> widget<msg>
  future-boundary( memo-fut-run,
                   fn(v) text(v, ?key = scope("memo-ready")),
                   placeholder = text("loading-memo", ?key = scope("memo-ph")),
                   ?key = scope("memo-fut") )

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  column([
    memo(memo-pane),
    future-boundary( fut-run,
                     fn(v) text(v, ?key = scope("fut-ready")),
                     placeholder = text("loading-fut", ?key = scope("fut-ph")),
                     ?key = scope("fut") ),
    future-boundary( err-run,
                     fn(v : string) text(v, ?key = scope("err-ready")),
                     placeholder = text("loading-err", ?key = scope("err-ph")),
                     failed = fn(e, retry) scoped-failed("err", e, retry),
                     ?key = scope("err") ),
    future-boundary( rty-run,
                     fn(v) text(v, ?key = scope("rty-ready")),
                     placeholder = text("loading-rty", ?key = scope("rty-ph")),
                     failed = fn(e, retry) scoped-failed("rty", e, retry),
                     ?key = scope("rty") ),
    future-boundary( slow-run,
                     fn(v) text(v, ?key = scope("slow-ready")),
                     placeholder = text("loading-slow", ?key = scope("slow-ph")),
                     min-load = 60.milli-seconds,
                     ?key = scope("slow") ),
  ])

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  m

// (a) placeholder before the run settles, ready content after.
pub fun future-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  attempts := 0
  check("placeholder present before settle", t.find("fut-ph").is-just)
  check-eq("placeholder text", t.texts("fut-ph"), ["loading-fut"])
  t.settle()
  check("still pending right after a fast settle (30ms not elapsed)", t.find("fut-ready").is-nothing)
  wait(120.milli-seconds)
  t.settle()
  check-eq("ready content after the run resolves", t.texts("fut-ready"), ["hello"])
  check("placeholder gone once ready", t.find("fut-ph").is-nothing)

// (b) a throwing run -> failed content + a Retry control.
pub fun error-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  attempts := 0
  wait(60.milli-seconds)
  t.settle()
  check-eq("failed content shows the thrown message", t.texts("err-msg"), ["failed: boom"])
  check("Retry control present", t.find("err-retry").is-just)
  check-eq("Retry label", t.texts("err-retry"), ["Retry"])

// (c) RETRY: fail first, then click Retry -> a fresh generation runs and
// succeeds. Pins the generation mechanism end to end.
pub fun retry-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  attempts := 0
  wait(40.milli-seconds)
  t.settle()
  check("failed on the first attempt", t.find("rty-retry").is-just)
  check-eq("first-attempt failure message", t.texts("rty-msg"), ["failed: fail once"])
  t.click("rty-retry")
  wait(40.milli-seconds)
  t.settle()
  check-eq("recovered after retry", t.texts("rty-ready"), ["recovered"])
  check("failure UI gone after a successful retry", t.find("rty-retry").is-nothing)

// (d) MIN-LOAD: a ~1ms run with min-load=60ms keeps the placeholder up well
// past the resolve, then goes ready once the floor elapses.
pub fun min-load-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  attempts := 0
  wait(20.milli-seconds)
  t.settle()
  check("placeholder still held by min-load at 20ms", t.find("slow-ph").is-just)
  check("not ready yet at 20ms (< 60ms min-load)", t.find("slow-ready").is-nothing)
  wait(80.milli-seconds)
  t.settle()
  check-eq("ready once min-load elapses", t.texts("slow-ready"), ["done"])
  check("placeholder gone once ready", t.find("slow-ph").is-nothing)

// (e) MEMO: the future-boundary lives inside a `memo` boundary that no model
// message ever dirties (see `memo-pane`). Placeholder first; once the run
// resolves, the async-store write must invalidate the memo boundary's read
// (Finding 1, task-2-review.md) or the memo keeps replaying the cached
// placeholder subtree forever -- this asserts the READY content actually
// appears.
pub fun memo-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  check("placeholder present before settle", t.find("memo-ph").is-just)
  check-eq("placeholder text", t.texts("memo-ph"), ["loading-memo"])
  t.settle()
  check("still pending right after a fast settle (20ms not elapsed)", t.find("memo-ready").is-nothing)
  wait(120.milli-seconds)
  t.settle()
  check-eq("ready content appears through the memo boundary", t.texts("memo-ready"), ["memo-hello"])
  check("placeholder gone once ready", t.find("memo-ph").is-nothing)

pub fun main()
  // "memo" runs FIRST: it needs to observe the placeholder before the run
  // settles, and every scenario in this list shares ONE app instance / one
  // continuously-running async-pump on real wall time, so running it after
  // the other (slower) scenarios would let its 20ms resolve happen long
  // before its own checks execute.
  test-scenarios("future-boundary", Model(), view, update,
                 [ ("memo",     memo-scenario),
                   ("future",   future-scenario),
                   ("error",    error-scenario),
                   ("retry",    retry-scenario),
                   ("min-load", min-load-scenario) ])
