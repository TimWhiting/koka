import std/data/map
import std/os/env
import std/num/int32

alias tree = map<int32,bool>

val compare_int = handler
  fun comp(a: int32, b: int32)
    a.compare(b)

fun make-tree(n : int32, t : tree) : <ecompare<int32>, div> tree
  if n <= zero then t else
    val m = n - 1.int32
    make-tree(m, insert(t, m, m % 10.int32 == zero))

fun main()
  with compare_int
  val n = get-args().head("").parse-int.default(4200000).int32
  val t = make-tree(n, Leaf)
  val v = t.fold(zero) fn(k,v,r:int32){ if v then r.inc else r }
  v.show.println
