// Tim's scheme: ONE name ?key, role by TYPE. ?key:int = holds identity;
// .?key:child = component (call-site mint + unpack shadows key as the int).
import ui/keytrie
import std/core/undiv

value struct child( key : int )

// the mint: named `key`, returns child (the .? default resolves to this at call sites)
fun key( ?key : int, ?kk-file-line : string ) : keytree child
  Child( kt-child(?key, Line(?kk-file-line)) )

fun leaf( tag : string, ?key : int, ?kk-file-line : string ) : <keytree,console> ()
  println(tag ++ " id=" ++ kt-child(?key, Line(?kk-file-line)).show)

fun comp( tag : string, .?key : child ) : <keytree,console> ()
  leaf(tag ++ ".leafA")     // ?key:int -> the unpacked field
  leaf(tag ++ ".leafB")

fun comp2( tag : string, .?key : child ) : <keytree,console> ()
  comp(tag ++ ".compA")     // nested COMPONENT: does it re-mint?
  comp(tag ++ ".compB")
  leaf(tag ++ ".leaf")

fun main()
  with pretend-no-div
  with with-keytree
  val key = 0
  comp("one")
  comp("two")
  comp2("nest")
