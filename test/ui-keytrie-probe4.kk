import ui/keytrie
import std/core/undiv

value struct child( key : int )

fun key( ?key : int, ?kk-file-line : string ) : keytree child
  Child( kt-child(?key, Line(?kk-file-line)) )

fun leaf( tag : string, ?key : int, ?kk-file-line : string ) : <keytree,console> ()
  println(tag ++ " id=" ++ kt-child(?key, Line(?kk-file-line)).show)

fun comp( tag : string, .?key : child ) : <keytree,console> ()
  leaf(tag ++ ".A")
  leaf(tag ++ ".B")

fun variant-a()   // explicit arg: no resolution involved
  with pretend-no-div
  with with-keytree
  comp("expl", ?key = key(?key = 0, ?kk-file-line = "root"))

fun variant-b()   // resolution with ONLY the mint in scope (no int val named key)
  with pretend-no-div
  with with-keytree
  val root = 0
  comp("mint", ?key = key(?key = root, ?kk-file-line = "seed"))  // seed one level explicitly
  ()

fun main()
  variant-a()
  variant-b()
