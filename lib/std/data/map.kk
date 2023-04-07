/*---------------------------------------------------------------------------
  Copyright 2020-2021, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

/* Map

   Todo.
*/
module std/data/map

pub effect ecompare<a>
  fun comp(a: a, b: a) : order

pub type color
  Red
  Black

pub type map<k,v>
  Node(color : color, lchild : map<k,v>, key : k, value : v, rchild : map<k,v>)
  Leaf
  
pub type zipper<k,v>
  NodeR(color : color, lchild : map<k,v>, key : k, value : v, zip : zipper<k,v>)
  NodeL(color : color, zip : zipper<k,v>, key : k, value : v, rchild : map<k,v>)
  Done

fun move-up(z : zipper<k,v>, t : map<k,v>) : map<k,v>
  match z
    NodeR(c, l, k, v, z1) -> z1.move-up(Node(c, l, k, v, t))
    NodeL(c, z1, k, v, r) -> z1.move-up(Node(c, t, k, v, r))
    Done -> t

fun balance-red( z : zipper<k,v>, l : map<k,v>, k : k, v : v, r : map<k,v> ) : map<k,v>
  match z
    NodeR(Black, l1, k1, v1, z1) -> z1.move-up( Node( Black, l1, k1, v1, Node(Red,l,k,v,r) ) )
    NodeL(Black, z1, k1, v1, r1) -> z1.move-up( Node( Black, Node(Red,l,k,v,r), k1, v1, r1 ) )
    NodeR(Red, l1, k1, v1, z1) -> match z1
      NodeR(_c2, l2, k2, v2, z2) -> z2.balance-red( Node(Black, l2, k2, v2, l1), k1, v1, Node(Black, l, k, v, r) )
      NodeL(_c2, z2, k2, v2, r2) -> z2.balance-red( Node(Black, l1, k1, v1, l), k, v, Node(Black, r, k2, v2, r2) )
      Done -> Node(Black, l1, k1, v1, Node(Red,l,k,v,r))
    NodeL(Red, z1, k1, v1, r1) -> match z1
      NodeR(_c2, l2, k2, v2, z2) -> z2.balance-red( Node(Black, l2, k2, v2, l), k, v, Node(Black, r, k1, v1, r1) )
      NodeL(_c2, z2, k2, v2, r2) -> z2.balance-red( Node(Black, l, k, v, r), k1, v1, Node(Black, r1, k2, v2, r2) )              
      Done -> Node(Black, Node(Red,l,k,v,r), k1, v1, r1)
    Done -> Node(Black,l,k,v,r)

fun ins(t : map<k,v>, k : k, v : v, z : zipper<k,v>) : ecompare<k> map<k,v>
  match t
    Node(c, l, kx, vx, r) -> 
      match k.comp(kx) 
        Lt -> ins(l, k, v, NodeL(c, z, kx, vx, r))
        Gt -> ins(r, k, v, NodeR(c, l, kx, vx, z))
        _ -> z.move-up(Node(c, l, kx, vx, r))  // z.move-up(t) is slower (but not a reuse bug); to be investigated
    Leaf -> z.balance-red(Leaf, k, v, Leaf)

// fun del(t: map<k,b>, k: k, z: zipper<k,v>) : ecompare<k> map<k,v>
//   match t
//     Leaf -> Leaf
//     Node(Red, Leaf, kx, vx, Leaf) ->
//       if k.comp(kx) == Eq then Leaf


pub fun insert(t : map<k,v>, k : k, v : v) : ecompare<k> map<k,v>
  ins(t, k, v, Done)

pub fun fold(t : map<k,v>, b : a, f: (k, v, a) -> a) : a
  match t
    Node(_, l, k, v, r) -> r.fold( f(k, v, l.fold(b, f)), f)
    Leaf                -> b


