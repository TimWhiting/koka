module static-computation-graph
import std/num/float64

pub struct tensor
  shape: (int, int)
  data: vector<float64>

fun show(shape: (int, int)): string
  val (m, n) = shape
  "tensor(" ++ m.show ++ ", " ++ n.show ++ ")"

fun show(xs: list<float64>): string
  var s := "["
  foreach-indexed(xs) fn(i, x)
    s := s ++ x.show
    if (i != length(xs) - 1) then s := s ++ ", "
  s := s ++ "]"
  s

fun show(t: tensor): string
  t.shape.show ++ t.data.list.show

pub named effect compute<a>
  fun constE(x: tensor): a
  fun addE(x: a, y: a): a
  // fun mulE(x: a, y: a): a

inline extern unsafe-vector: forall<a> (n: ssize_t) -> total vector<a>
  c inline "kk_vector_alloc_uninit(#1,NULL,kk_context())"

inline extern unsafe-idx: forall<a> (v: vector<a>, i: ssize_t) -> <> a
  c inline "kk_vector_at_borrow(#1,#2)"

inline extern unsafe-assign: forall<a> (v: vector<a>, i: ssize_t, x : a) -> <> ()
  c "kk_vector_unsafe_assign"

fun foreach-indexedt(v: vector<a>, f: (a,ssize_t) -> e ()): e ()
  for(0, v.length.dec) fn(i)
    f(v.unsafe-idx(i.ssize_t), i.ssize_t)

fun vmap(v : vector<float64>, w: vector<float64>, f: (float64, float64) -> <> float64 ): <> vector<float64>
  val u = unsafe-vector(v.length.ssize_t)
  v.foreach-indexedt fn(x, i) {
    val y = w.unsafe-idx(i)
    unsafe-assign(u, i, f(x, y))
  }
  u

fun (+)(ts1: tensor, ts2: tensor): <> tensor
  assert("add: not match shape, " ++ show(ts1.shape) ++ " != " ++ show(ts2.shape), ts1.shape == ts2.shape)
  val dtype = ts1.shape
  val data = vmap(ts1.data, ts2.data, (+))
  Tensor(dtype, data)

fun (==)(s0: (int, int), s1: (int, int)): bool
  val (m0, n0) = s0
  val (m1, n1) = s1
  m0 == m1 && n0 == n1

fun addT(t1: tensor, t2: tensor): tensor
  t1 + t2

fun handle_graph(action)
  with h <- named handler
    fun constE(x) x
    fun addE(x, y) x.addT(y)
    return(x) x
  action(h)

fun main()
  with h <- handle_graph
  val x = h.constE(Tensor((2, 2), [1.0, 2.0, 3.0, 4.0].vector))
  val y = h.constE(Tensor((2, 2), [5.0, 6.0, 7.0, 8.0].vector))
  val z = h.addE(x, y)
  z.show.println
