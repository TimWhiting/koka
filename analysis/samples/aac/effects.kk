import std/core/undiv
pub import std/time
import std/num/ddouble

type tree
  Leaf
  Node(left: tree, right: tree, v: int)

effect iterator<i>
  ctl yield(v: i): ()

linear effect literator<i>
  fun lyield(v: i): ()

linear effect viterator<h,i>
  val sumv: ref<h,i>

fun breadth-first(^l: tree): iterator<int> ()
  match l
    Leaf -> ()
    Node(l, r, v) ->
      yield(v)
      breadth-first(l)
      breadth-first(r)

fun depth-first(^l: tree): iterator<int> ()
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

fun lbreadth-first(^l: tree): literator<int> ()
  match l
    Leaf -> ()
    Node(l, r, v) ->
      lyield(v)
      lbreadth-first(l)
      lbreadth-first(r)

fun ldepth-first(^l: tree): literator<int> ()
  match l
    Leaf -> ()
    Node(l, r, v) ->
      ldepth-first(l)
      lyield(v)
      ldepth-first(r)

fun lcount-tree(t: tree, iterate: (tree) -> <literator<int>> ()): int
  var c := 0
  with handler
    fun lyield(v: int) 
      c := c + v
  iterate(t)
  c

fun vcount-tree(t: tree, iterate: (tree) -> <viterator<h,int>> ()): int
  val c = ref(0)
  with handler
    val sumv = c
  iterate(t)
  !c

fun vbreadth-first(^l: tree): viterator<h,int> ()
  match l
    Leaf -> ()
    Node(l, r, v) ->
      val s:some<h> ref<h,int> = sumv
      s := !s + v
      vbreadth-first(l)
      vbreadth-first(r)

fun hcount-breadth(t: tree): int
  val c = ref(0)
  with handler
    val sumv = c
  fun internal(^l: tree)
    match l
      Leaf -> ()
      Node(l, r, v) ->
        c := !c + v
        internal(l)
        internal(r)
  internal(t)
  !c

fun hcount-depth(t: tree): int
  val c = ref(0)
  with handler
    val sumv = c
  fun internal(^l: tree)
    match l
      Leaf -> ()
      Node(l, r, v) ->
        c := !c + v
        internal(l)
        internal(r)
  internal(t)
  !c

fun vdepth-first(^l: tree): viterator<h,int> ()
  match l
    Leaf -> ()
    Node(l, r, v) ->
      vdepth-first(l)
      val s :some<h> ref<h,int> = sumv
      s := !s + v
      vdepth-first(r)

fun benchmark(name: string, f: () -> <console,ndet,utc|e> a): <console,ndet,utc|e> ()
  val start = now()
  for(5, fn(i) {f(); ()})
  val end = now()
  println(name ++ " took " ++ (end - start).show)

fun make-tree(n: int): tree
  if n == 0 then
    Leaf
  else
    Node(make-tree((n - 1).pretend-decreasing), make-tree((n - 1).pretend-decreasing), n)

fun count-tree-breadth-first-local(t: tree): int
  var c := 0
  fun count-tree-rec(t1: tree)
    match t1
      Leaf -> ()
      Node(l, r, v) ->
        c := c + v
        count-tree-rec(l)
        count-tree-rec(r)
  count-tree-rec(t)
  c


fun count-tree-depth-first-local(t: tree): int
  var c := 0
  fun count-tree-rec(t1: tree)
    match t1
      Leaf -> ()
      Node(l, r, v) ->
        count-tree-rec(l)
        c := c + v
        count-tree-rec(r)
  count-tree-rec(t)
  c

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
  val tree = make-tree(24)
  benchmark("Breadth-first")
    count-tree(tree, breadth-first)
  benchmark("Breadth-first Linear")
    lcount-tree(tree, lbreadth-first)
  benchmark("Breadth-first Val")
    vcount-tree(tree, vbreadth-first)
  benchmark("Breadth-first Hand insertion")
    hcount-breadth(tree)
  benchmark("Breadth-first optimized ref")
    count-tree-breadth-first(tree)
  benchmark("Breadth-first optimized local")
    count-tree-breadth-first-local(tree)
  benchmark("Depth-first")
    count-tree(tree, depth-first)
  benchmark("Depth-first Linear")
    lcount-tree(tree, ldepth-first)
  benchmark("Depth-first Val")
    vcount-tree(tree, vdepth-first)
  benchmark("Depth-first Hand insertion")
    hcount-depth(tree)
  benchmark("Depth-first optimized ref")
    count-tree-depth-first(tree) 
  benchmark("Depth-first optimized local")
    count-tree-depth-first-local(tree) 
  benchmark("Optimized1")
    optimized1(tree) 
  benchmark("Optimized2")
    optimized2(tree)
  optimized2(tree)