// The dependency-channel invariant for the KEYED ui/state stores (task #54).
//
// Every keyed store (cells / fields / scrolls / asyncs) shares one integer
// channel space, tagged by slot: `keyed-chan(id, slot) = id * slot-count +
// slot` (ui/reactive). Memoization rests entirely on that numbering being
// INJECTIVE: a memo boundary that read (store S, id X) must be woken by a
// write to (S, X) and by NOTHING else. Two ways it can break, both silent:
//
//   - COLLISION: two distinct (store, id) pairs map to one channel, so an
//     unrelated write wakes a boundary (a spurious rebuild -- wasteful but
//     invisible), or -- the dangerous direction -- the aliased pair makes a
//     boundary's real edge indistinguishable from a neighbour's. The old
//     hand-written `id*4+k` was exactly FULL at four stores: a fifth slot
//     would have aliased id+1's cell channel, which is why the multiplier is
//     now derived from `keyed-slots` rather than written by hand.
//   - A MISSING EDGE: a getter that forgets to `record`, or a setter that
//     forgets to `invalidate`, leaves a boundary frozen on stale state (the
//     async-image-under-a-memo bug that the async slot was added for).
//
// This is a PROPERTY test over the whole keyed cross-product rather than one
// case per store, so it keeps covering the invariant when a store is added:
// extend `stores` below with the new slot and the matrix grows itself.
// Adjacent ids are included on purpose -- id/id+1 is exactly where a
// too-small multiplier aliases first.
module state-channels

import std/core/unsafe
import std/num/int32
import ui/state

val passed : ref<global,int> = unsafe-total{ ref(0) }
val failed : ref<global,int> = unsafe-total{ ref(0) }

// `koka -e` does not propagate a child program's exit code, so the pass/fail
// line below is what the suite greps -- this is for direct/CI invocation.
extern exit-code( code : int32 ) : io ()
  c inline "exit((int)(#1))"
  js inline "process.exit(#1)"

fun check( name : string, cond : bool )
  if cond
    then passed := !passed + 1
    else
      failed := !failed + 1
      println("FAIL: " ++ name)

// one keyed store, as the pair of operations the invariant is about
struct store
  name  : string
  read  : ( id : int ) -> uistate ()
  write : ( id : int ) -> uistate ()

val stores : list<store> =
  [ Store("cell",   fn(id) get-cell(id).ignore,   fn(id) set-cell(id, erase(1))),
    Store("field",  fn(id) get-field(id).ignore,  fn(id) set-field(id, "x")),
    Store("scroll", fn(id) get-scroll(id).ignore, fn(id) set-scroll(id, Scroll-info(offset = 1.0))),
    Store("async",  fn(id) get-async(id).ignore,  fn(id) set-async(id, Async-entry(1, RPending))),
  ]

// the ids the matrix runs over: 0 (the root id, and the one an off-by-one
// multiplier collapses), a mid id, and an ADJACENT pair (7/8) -- a multiplier
// smaller than the slot count aliases neighbouring ids before anything else
val ids : list<int> = [0, 5, 7, 8]

// Run `body` as a memo boundary and report whether it came out dirty after
// `act`. `clear-storm` first: during a dirty STORM tracking is deliberately
// off (everything rebuilds anyway), so the edges under test are only live on
// a non-storm frame.
fun wakes( boundary : int, subscribe : () -> uistate (), act : () -> uistate () ) : <uistate,ioc> bool
  clear-storm()
  take-dirty-readers().ignore     // drop anything pending from an earlier case
  memo-begin(boundary)
  subscribe()
  memo-end()
  act()
  take-dirty-readers().any(fn(r) r == boundary)

pub fun main()
  with-uistate
    // a boundary id well clear of the ids under test: it is a READER key, a
    // different space from the channels, but keeping them disjoint makes a
    // failure unambiguous
    val boundary = 900

    stores.foreach fn(rs)
      ids.foreach fn(rid)
        // (1) the edge EXISTS: a write to the very pair that was read wakes
        // the boundary. This is the direction a forgotten `record` (getter)
        // or `invalidate` (setter) breaks -- the frozen-memo bug.
        check(rs.name ++ "@" ++ rid.show ++ " woken by its own write",
              wakes(boundary, { (rs.read)(rid) }, { (rs.write)(rid) }))

        // (2) the edge is EXACT: no OTHER (store, id) pair in the matrix
        // wakes it. This is the direction a channel collision breaks.
        stores.foreach fn(ws)
          ids.foreach fn(wid)
            if !(ws.name == rs.name && wid == rid) then
              check(rs.name ++ "@" ++ rid.show ++ " NOT woken by " ++ ws.name ++ "@" ++ wid.show,
                    !wakes(boundary, { (rs.read)(rid) }, { (ws.write)(wid) }))

    println("STATE-CHANNELS: " ++ (!passed).show ++ "/" ++ (!passed + !failed).show ++ " passed")
    if !failed > 0 then
      println("STATE-CHANNELS: FAILED (" ++ (!failed).show ++ " failures)")
      exit-code(1.int32)
