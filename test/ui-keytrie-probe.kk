import ui/keytrie
import std/core/undiv
fun main()
  with pretend-no-div
  with with-keytree
  val a = kt-derive(0, Named("sidebar"))
  val b = kt-derive(a, Index(3))
  val a2 = kt-derive(0, Named("sidebar"))   // same segment -> same id
  val c = kt-derive(b, Line("f.kk:12"))
  println([a,b,a2,c].map(show).join(",") ++ " stable=" ++ (a == a2).show)
