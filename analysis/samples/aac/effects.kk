import std/core/undiv
pub import std/time
import std/num/ddouble

type tree
  Leaf
  Node(left: tree, right: tree, v: int)

effect iterator<i>
  ctl yield(v: i): ()

fun breadth-first(l: tree): iterator<int> ()
  match l
    Leaf -> ()
    Node(l, r, v) ->
      yield(v)
      breadth-first(l)
      breadth-first(r)

fun depth-first(l: tree): iterator<int> ()
  match l
    Leaf -> ()
    Node(l, r, v) ->
      depth-first(l)
      yield(v)
      depth-first(r)

fun count-tree(t: tree, iterate: (tree) -> <iterator<int>> ()): int
  var c := 0
  with handler
    fun yield(v: int) 
      c := c + v
  iterate(t)
  c

fun benchmark(name: string, f: () -> <console,ndet,utc|e> a, ?show: (a) -> string): <console,ndet,utc|e> a
  val start = now()
  val res = f()
  val end = now()
  println(name ++ " took " ++ (end - start).show)
  res.println
  res

fun make-tree(n: int): tree
  if n == 0 then
    Leaf
  else
    Node(make-tree((n - 1).pretend-decreasing), make-tree((n - 1).pretend-decreasing), n)

fun count-tree-breadth-first(t: tree): int
  val c = ref(0)
  fun count-tree-rec(t1: tree)
    match t1
      Leaf -> ()
      Node(l, r, v) ->
        c := !c + v
        count-tree-rec(l)
        count-tree-rec(r)
  count-tree-rec(t)
  !c

fun count-tree-depth-first(t: tree): int
  val c = ref(0)
  fun count-tree-rec(t1: tree)
    match t1
      Leaf -> ()
      Node(l, r, v) ->
        count-tree-rec(l)
        c := !c + v
        count-tree-rec(r)
  count-tree-rec(t)
  !c

fun optimized1(t: tree): int
  fun count-tree-rec(t1: tree): int
    match t1
      Leaf -> 0
      Node(l, r, v) ->
        count-tree-rec(l) + v + count-tree-rec(r)
  count-tree-rec(t)

// TODO: Better extra hand optimized (theoretical maximum)
fun optimized2(t: tree): int
  fun count-tree-rec(t1: tree, acc: int): int
    match t1
      Leaf -> acc
      Node(l, r, v) ->
        count-tree-rec(r, count-tree-rec(l, acc + v))
  count-tree-rec(t, 0)

fun main()
  val tree = make-tree(15)
  benchmark("Breadth-first")
    count-tree(tree, breadth-first)
  benchmark("Breadth-first Hand optimized")
    count-tree-breadth-first(tree) 
  benchmark("Depth-first")
    count-tree(tree, depth-first)
  benchmark("Depth-first Hand optimized")
    count-tree-depth-first(tree) 
  benchmark("Optimized1")
    optimized1(tree) 
  benchmark("Optimized2")
    optimized2(tree) 