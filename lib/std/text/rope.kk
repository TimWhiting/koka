module std/text/rope

// A rope is a type of binary tree where each leaf (end node) holds a string and a length (also known as a "weight"),
//   and each node further up the tree holds the sum of the lengths of all the leaves in its left subtree. 
// A node with two children thus divides the whole string into two parts: the left subtree stores the first part of the string, 
//   the right subtree stores the second part of the string, and a node's weight is the length of the first part.
abstract type rope
  RopeTree(left: rope, right: rope, len: int)
  RopeLeaf(str: string, len: int)
  RopeNil

fun rope_empty(): rope
  RopeTree(RopeNil, RopeNil, 0)

fbip(2) fun prepend(r: rope, s: string, i: int): rope
  match r
    RopeTree(left, right, len) -> RopeTree(prepend(left, s, i), right, len + i)
    RopeLeaf(str, len) -> RopeTree(RopeLeaf(s, i), RopeLeaf(str, len), i)
    RopeNil -> RopeLeaf(s, i)

fun rope_prepend(r: rope, s: string): rope 
  prepend(r, s, s.count)

fbip(2) fun append(r: rope, s: string, i: int): rope
  match r
    RopeTree(left, right, len) -> RopeTree(left, append(right, s, i), len)
    RopeLeaf(str, len) -> RopeTree(RopeLeaf(str, len), RopeLeaf(s, i), len)
    RopeNil -> RopeLeaf(s, i)

fun rope_append(r: rope, s: string): rope
  append(r, s, s.count)
