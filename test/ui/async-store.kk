// Standalone check of the async-phase store (ui/reactive's `get-async`/
// `set-async`/`bump-async-gen`, foundation for the upcoming future-boundary
// async widget -- see .superpowers/sdd/task-1-brief.md). Not the
// test-scenarios harness -- a plain `with-uistate` program exercising the
// handler ops directly, with its own pass/fail counter.
module async-store

import std/core/unsafe
import std/num/int32
import ui/state

val passed : ref<global,int> = unsafe-total{ ref(0) }
val failed : ref<global,int> = unsafe-total{ ref(0) }

// process exit with a nonzero code on failure: `koka -e` does not propagate
// a child program's exit code, so the pass/fail line below is what the test
// suite actually greps -- this is just for direct/CI invocation.
extern exit-code( code : int32 ) : io ()
  c inline "exit((int)(#1))"
  js inline "process.exit(#1)"

fun check( name : string, cond : bool )
  if cond
    then passed := !passed + 1
    else
      failed := !failed + 1
      println("FAIL: " ++ name)

pub fun main()
  with-uistate
    // get on an id that was never set -> Nothing
    check("get-async on empty -> Nothing", get-async(1).is-nothing)

    // set then get round-trips the entry: erase a known int as the value,
    // unerase on read, and both the value and the generation match
    val e1 = Async-entry(7, RDone(erase(42)))
    set-async(2, e1)
    match get-async(2)
      Just(e) ->
        check("round-trip gen", e.gen == 7)
        match e.phase
          RDone(v) -> check("round-trip value", unerase(v) == 42)
          _ -> check("round-trip phase is RDone", False)
      Nothing -> check("round-trip: entry present", False)

    // bump-gen on an absent id -> generation 1, phase RPending
    val g1 = bump-async-gen(3)
    check("bump-gen on absent -> 1", g1 == 1)
    match get-async(3)
      Just(e) ->
        check("bump-gen(1) entry gen", e.gen == 1)
        check("bump-gen(1) entry phase RPending", e.phase.is-rpending)
      Nothing -> check("bump-gen(1): entry present", False)

    // bump again -> generation 2
    val g2 = bump-async-gen(3)
    check("bump-gen again -> 2", g2 == 2)
    match get-async(3)
      Just(e) -> check("bump-gen(2) entry gen", e.gen == 2)
      Nothing -> check("bump-gen(2): entry present", False)

    // set a Done entry, then bump-gen: generation advances AND the phase
    // resets to RPending (the stale-discard basis: a strand still applying
    // the OLD generation's result gets superseded)
    set-async(4, Async-entry(1, RDone(erase(99))))
    val g3 = bump-async-gen(4)
    check("bump-gen after Done -> advances", g3 == 2)
    match get-async(4)
      Just(e) ->
        check("bump-gen after Done: gen advanced", e.gen == 2)
        check("bump-gen after Done: phase reset to RPending", e.phase.is-rpending)
      Nothing -> check("bump-gen after Done: entry present", False)

    println("ASYNC-STORE: " ++ (!passed).show ++ "/" ++ (!passed + !failed).show ++ " passed")
    if !failed > 0 then
      println("ASYNC-STORE: FAILED (" ++ (!failed).show ++ " failures)")
      exit-code(1.int32)
