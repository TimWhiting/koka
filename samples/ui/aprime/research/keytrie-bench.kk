// keytrie in ISOLATION: does uniqueness discipline on the handler's zipper
// state matter? The current with-keytree holds the zipper in a ref and reads
// it with `!zip` before every move -- the read dups, descend/ascend run at
// rc>=2, and every move REBUILDS its context chain with no fbip reuse. The
// U variant takes the zipper OUT with `swap` (rc=1 while moving) and puts it
// back, letting the zipper's rebuild-style moves reuse in place.
// Traffic mirrors a frame build: W sibling components under the root, each
// minting D nested slot identities (parent-to-child fast path + sibling
// re-roots, like real ?key derivation).
module keytrie-bench
import std/num/int64
import std/num/float64
import std/time/timer
import std/time/duration
import std/data/int-map
import ui/keytrie

val wide   = 100
val depth  = 5
val frames = 2000

fun chain( k : key, d : int ) : <keytree,div> int
  if d <= 0 then k.key-id
  else chain( kt-child(k, Slot("s", "f.kk:" ++ d.show)), d - 1 )

fun drive() : <keytree,div> int
  list(1, wide).foldl(0) fn(acc, i)
    acc + chain( kt-child(root-key, Named("c" ++ i.show)), depth )

// DEEP traffic: a component at depth P minting `wide` children -- after each
// child's chain the next mint re-roots to the deep parent. Full-root replay
// pays ascend(P+1+depth)+descend(P) per sibling; LCA pays ascend(1+depth).
val deepP = 12
fun drive-deep() : <keytree,div> int
  val parent = list(1, deepP).foldl(root-key) fn(k, l)
    kt-child(k, Named("p" ++ l.show))
  list(1, wide).foldl(0) fn(acc, i)
    acc + chain( kt-child(parent, Named("c" ++ i.show)), depth )

// U: the swap-discipline handler (same semantics as ui/keytrie's)
fun with-keytree-u( action : () -> <keytree,div,st<global>|e> a ) : <div,st<global>|e> a
  val zip  : ref<global, kzip> = ref(kzip/empty())
  val next : ref<global, int>  = ref(1)
  val paths : ref<global, list<(int, list<segment>)>> = ref([(0, [])])
  fun path-of( id : int ) : <read<global>> list<segment>
    match (!paths).lookup(fn(k) k == id)
      Just(p) -> p
      Nothing -> []
  fun walk-to( id : int ) : <div,st<global>> ()
    val z0 = zip.swap(kzip/empty())          // take OUT: rc=1
    var z := z0.to-root
    path-of(id).foreach fn(seg)
      val (z2, _) = z.descend(seg, fn() { val n = !next; next := n + 1; n })
      z := z2
    zip := z                                  // put back
  with handler
    fun kt-mark-dirty(_id) ()
    fun kt-subtree-dirty(_id) False
    fun kt-clean-dirty(_id) ()
    fun kt-open(_id) ()
    fun kt-close(_id) []
    fun kt-child-id( of, seg, _keep )
      if (!zip).focus.nid != of then walk-to(of)
      val z0 = zip.swap(kzip/empty())          // take OUT: rc=1 while descending
      val (z2, cid) = z0.descend(seg) fn()
        val n = !next
        next := n + 1
        paths := Cons( (n, path-of(of) ++ [seg]), !paths )
        n
      zip := z2                                 // put back
      cid
  action()

fun bench( label : string, drv : () -> <keytree,div> int,
           run : (() -> <keytree,div,st<global>,ndet,console> ()) -> <div,st<global>,ndet,console> () ) : <div,st<global>,ndet,console> ()
  val t0 = ticks()
  run fn()
    list(1, frames).foreach fn(_)
      drv().ignore
    println("  checksum: " ++ drv().show)   // ids must be FRAME-STABLE + variant-equal
  val ms = (ticks() - t0).milli-seconds
  println(label ++ ": " ++ ms.show ++ " ms  (" ++ (ms.float64 * 1000.0 / frames.float64).show ++ " us/frame)")

// V: swap discipline + paths as an int-map (Patricia) instead of assoc list
fun with-keytree-v( action : () -> <keytree,div,st<global>|e> a ) : <div,st<global>|e> a
  val zip  : ref<global, kzip> = ref(kzip/empty())
  val next : ref<global, int>  = ref(1)
  val paths : ref<global, int-map<list<segment>>> = ref(int-map/empty().set(0.int64, []))
  fun path-of( id : int ) : <read<global>> list<segment>
    (!paths).lookup(id.int64).default([])
  fun walk-to( id : int ) : <div,st<global>> ()
    val z0 = zip.swap(kzip/empty())
    var z := z0.to-root
    path-of(id).foreach fn(seg)
      val (z2, _) = z.descend(seg, fn() { val n = !next; next := n + 1; n })
      z := z2
    zip := z
  with handler
    fun kt-mark-dirty(_id) ()
    fun kt-subtree-dirty(_id) False
    fun kt-clean-dirty(_id) ()
    fun kt-open(_id) ()
    fun kt-close(_id) []
    fun kt-child-id( of, seg, _keep )
      if (!zip).focus.nid != of then walk-to(of)
      val z0 = zip.swap(kzip/empty())
      val (z2, cid) = z0.descend(seg) fn()
        val n = !next
        next := n + 1
        val pp = path-of(of) ++ [seg]        // BEFORE the swap (dummy map has no paths)
        val p0 = paths.swap(int-map/empty())
        paths := p0.set(n.int64, pp)
        n
      zip := z2
      cid
  action()

pub fun main()
  println("-- flat traffic (siblings under root; LCA == root, no gain possible):")
  bench("T lib (swap+i32map+LCA)   ", drive, fn(a) with-keytree(a))
  bench("U swap take-out (rc=1)    ", drive, fn(a) with-keytree-u(a))
  bench("V swap+intmap, ROOT rescan", drive, fn(a) with-keytree-v(a))
  println("-- deep traffic (parent at depth 12 minting siblings):")
  bench("T lib (LCA re-root)       ", drive-deep, fn(a) with-keytree(a))
  bench("V root-rescan             ", drive-deep, fn(a) with-keytree-v(a))
