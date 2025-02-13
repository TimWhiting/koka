// Bankers queue  (see "Purely Functional Data Structures" by Chris Okasaki, Sect. 6.3.2)
// - worst-case  O(n), persistent O(n)
// - amortized   O(1), persistent O(1)
module queue/bankers

import bench

lazy type stream<a>
  SNil
  SCons( head : a, tail : stream<a> )
  lazy SAppRev( pre : stream<a>, post : list<a> ) ->
    match pre
      SNil        -> sreverse(post)
      SCons(x,xx) -> SCons(x,SAppRev(xx,post))


fip fun sreverse-acc( xs : list<a>, acc : stream<a> ) : stream<a>
  match xs
    Cons(x,xx) -> sreverse-acc(xx, SCons(x,acc))
    Nil        -> acc

fip fun sreverse( xs : list<a> ) : stream<a>
  sreverse-acc(xs,SNil)


pub fbip fun list( s : stream<a> ) : div list<a>
  match s
    SCons(x,xx) -> Cons(x,xx.list)
    SNil -> Nil

fun stream(start : int, end : int)
  if (start>end) then SNil else SCons(start,stream(start+1,end))

pub fun test1()
  SAppRev(stream(1,3),[6,5,4]).list.println

/*
// The following should be generated.
// Note that `lazy/whnf-update(s,...)`` is always inserted at tail-position.
//
// If the argument is a singleton (`SNil`), larger, or unknown (`sreverse(post)`),
// an indirection is automatically inserted (`stream/Indirect`). Larger or unknown issue a warning.
//
// `lazy/whnf-update(s)` is compiled specially to only updates `s` if `s` is not unique.

noinline fun stream/lazy-eval( s : stream<a> ) : _ stream<a>
  lazy/whnf-target(s)      // just for the compiler to reference count and reuse correctly
  lazy match s             // lazy match so we can match on the lazy constructors (and no `stream/force` is inserted)
    SAppRev( pre, post )
      -> match stream/force(pre)
           SNil        -> lazy/whnf-update(s,sreverse(post))  // does this guarantee we never update an indirection with an indirection?
           SCons(x,xx) -> lazy/whnf-update(s,SCons(x,SAppRev(xx,post)))     // no recursive `stream/force` is inserted as we can statically see the `SCons`
    stream/Indirect(ind)   // generated
      -> ind               // we don't use `stream/force(ind)` as we guarantee `ind` is never an indirection itself (and always whnf)
    _ -> s

// evaluate one step and update
noinline fun stream/lazy-step( s : stream<a> ) : div stream<a>
  if lazy/datatype-ptr-is-unique(s) ||      // we never need to blackhole a unique lazy value (?)
     !lazy/enter(s,stream/lazy-tag)         // otherwise try to enter (maybe atomically and block waiting)
  then
    stream/lazy-eval(s)                     // we always eval (even if waiting) in order to resolve indirections
  else
    val v = stream/lazy-eval(s)             // if entered first, we need to call `lazy/leave` later
    lazy/leave(s)                           // unblock any others waiting for the value
    v

val stream/lazy-tag = 3   // always the indirection tag; anything >= 3 is considered a lazy constructor

// evaluate tail-recursively to whnf
noinline fun stream/lazy-whnf(s : stream<a> ) : div stream<a>
  val x = stream/lazy-step(s)
  if lazy/datatype-is-whnf(x,steam/lazy-tag) then x else stream/lazy-whnf(x)

// `stream/lazy-force` is inserted at any `match` on a `:stream<a>` type. (but not for a `lazy match`).
// it is a one-step unfolding of `lazy-whnf` for efficiency
inline fun stream/force( s : stream<a> ) : div stream<a>
  // `lazy/datatype-ptr-is-whnf` is fast as it just does `s->tag < stream/lazy-tag` (so we want to inline this)
  // (if a type can have singletons, it becomes `lazy/datatype-is-whnf(s)` == `is-value(s) || s->tag < stream/lazy-tag`)
  if lazy/datatype-is-whnf(s,stream/lazy-tag)
    then s
    else stream/lazy-whnf(s)
*/

struct bqueue<a>
  front : stream<a>
  front-len : int
  rear : list<a>
  rear-len : int

val bankers/empty = Bqueue( SNil, 0, Nil, 0 )

fun is-empty( ^q : bqueue<a> ) : bool
  q.front-len==0

fun size( ^q : bqueue<a> ) : int
  q.front-len + q.rear-len


fip(1) fun balance( Bqueue(front, front-len, rear, rear-len) : bqueue<a> ) : bqueue<a>
  if (front-len >= rear-len)
    then Bqueue(front, front-len, rear, rear-len)
    else Bqueue( SAppRev(front,rear), front-len + rear-len, Nil, 0)

fip(2) fun snoc( Bqueue(front,front-len,rear,rear-len) : bqueue<a>, x : a ) : bqueue<a>
  Bqueue(front, front-len, Cons(x,rear), rear-len+1).balance

fbip(2) fun uncons( Bqueue(front,front-len,rear,rear-len) : bqueue<a> ) : div maybe2<a,bqueue<a>>
  match front
    SCons(x,xx) -> Just2(x, Bqueue(xx,front-len - 1,rear,rear-len).balance)
    SNil        -> Nothing2

pub fun main()
  benchmain(QueueI(bankers/empty, snoc, uncons))
