// .?key : child semantics probe: does the default-expr mint fire per CALL SITE,
// does the body see the unpacked int, and do nested components re-mint?
import ui/keytrie
import std/core/undiv

value struct child( key : int )

// the mint: named after the TYPE so `.?child : child` defaults to it per call site
fun child( ?key : int, ?kk-file-line : string ) : keytree child
  Child( kt-child(?key, Line(?kk-file-line)) )

fun leaf( tag : string, .?child : child ) : <keytree,console> ()
  println(tag ++ " id=" ++ (?child).key.show)

// a leaf in today's use-state style: takes the plain int + mints its OWN slot
fun leaf2( tag : string, ?key : int, ?kk-file-line : string ) : <keytree,console> ()
  println(tag ++ " id=" ++ kt-child(?key, Line(?kk-file-line)).show)

fun comp( tag : string, .?child : child ) : <keytree,console> ()
  // does the body expose the unpacked int (field `key`) so ?key : int resolves?
  leaf(tag ++ ".leafA")      // wants child -> passthrough (shares comp identity)
  leaf(tag ++ ".leafB")
  leaf2(tag ++ ".leaf2A")    // wants ?key : int -> the unpacked field?
  leaf2(tag ++ ".leaf2B")

fun main()
  with pretend-no-div
  with with-keytree
  val key = 0                 // the root id in scope as `key : int`
  comp("one")                 // call site 1
  comp("two")                 // call site 2 -> distinct subtree
  comp("one2")                // same comp, third site
