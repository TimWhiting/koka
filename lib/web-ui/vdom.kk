/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The mounted virtual dom: rendering `html<msg>` into real DOM elements,
// and diffing a mounted tree against a fresh `html<msg>` description.
//
// Semantics (see the design spec, "detach is a call, release is a drop"):
// structural changes to the visible DOM happen ONLY through explicit fringe
// calls made here (append/remove/insert); dropping a `node` value merely
// releases our references (element slots, listener slots) so the browser GC
// can reclaim detached nodes. The diff detaches; Perceus releases.
//
// Style rule from the spec: everything in this module is continuation-free
// (no async) — the mounted tree must stay uniquely owned for the future
// FBIP diff to apply.
module web-ui/vdom

import std/core/undiv
import web-ui/html
import web-ui/dom

// A mounted node: the vnode description that produced it, zipped with the
// live element and the Perceus-owned listener registrations attached to it.
// Dropping a `node` drops its element box and its `sub`s: listener slots
// deregister (removeEventListener) and element slots null — reference
// release only, never structural change.
pub type node<a>
  NElem( tag : string, attrs : list<attr<a>>, el : element, subs : list<sub>, kids : list<node<a>> )
  NText( text : string, el : element )

// The element of a mounted node.
pub fun node/element<msg>( n : node<msg> ) : element
  match n
    NElem(_, _, el, _, _) -> el
    NText(_, el) -> el

// ----------------------------------------------------------------
// Mounting: build real DOM for a description. `emit` routes a handler's
// message into the app's channel (the only callback, owned by the runtime,
// crossing from dom's dispatch into vdom — user code never sees it).

pub fun mount<msg>( h : html<msg>, parent : element, emit : msg -> ioc () ) : <ioc,exn> node<msg>
  val n = build(h, emit)
  parent.append-child(n.element)
  n

fun build<msg>( h : html<msg>, emit : msg -> ioc () ) : <ioc,exn> node<msg>
  match h
    Text(s) ->
      NText(s, create-text(s))
    Elem(tag, attrs, kids) ->
      val el = create-element(tag)
      val subs = attrs.apply-attrs(el, emit)
      val ns = kids.map fn(k)
        val kn = k.pretend-decreasing.build(emit)
        el.append-child(kn.element)
        kn
      NElem(tag, attrs, el, subs, ns)

// Apply attributes to a fresh element; returns the listener subscriptions.
fun apply-attrs<msg>( attrs : list<attr<msg>>, el : element, emit : msg -> ioc () ) : <ioc,exn> list<sub>
  attrs.list/flatmap-maybe fn(at)
    match at
      Attr(name, value) ->
        el.set-attribute(name, value)
        Nothing
      Key(_)            -> Nothing
      NoAttr            -> Nothing
      On(ev, m)         -> Just(el.subscribe(ev, fn() emit(m)))
      OnValue(ev, to-msg) -> Just(el.subscribe(ev, fn() emit(to-msg(el.get-value))))
      OnEvent(ev, to-msg) -> Just(el.subscribe(ev, fn() emit(to-msg(current-event()))))
      OnDo(ev, action)  -> Just(el.subscribe(ev, action))  // run the thunk directly, no message
      OnValueDo(ev, action) -> Just(el.subscribe(ev, fn() action(el.get-value)))
      OnEnterValue(to-msg) ->
        fun on-enter-keydown()
          if current-event().key == "Enter" then emit(to-msg(el.get-value))
        Just(el.subscribe("keydown", on-enter-keydown))

fun list/flatmap-maybe<a,b,e>( xs : list<a>, f : a -> e maybe<b> ) : e list<b>
  match xs
    Nil -> Nil
    Cons(x, rest) ->
      match f(x)
        Just(y) -> Cons(y, rest.list/flatmap-maybe(f))
        Nothing -> rest.list/flatmap-maybe(f)

// ----------------------------------------------------------------
// Diff + patch in one pass: `patch` consumes the old mounted tree and the
// new description, mutates the real DOM where they differ, and returns the
// new mounted tree. (v1 walks and re-applies; the FBIP fused version that
// reuses the old cells is a staged v2 experiment — the *shape* is already
// consume-and-rebuild to make that a drop-in.)

pub fun patch<msg>( old : node<msg>, new : html<msg>, parent : element, emit : msg -> ioc () ) : <ioc,exn> node<msg>
  match (old, new)
    (NText(s1, el), Text(s2)) ->
      if s1 != s2 then el.set-text(s2)
      NText(s2, el)
    (NElem(t1, attrs1, el, subs1, kids1), Elem(t2, attrs2, kids2)) | t1 == t2 ->
      // same tag: update attrs/handlers in place, reconcile children
      subs1.drop-subs                      // deregister old listeners (explicit, in the patcher)
      remove-old-attrs(attrs1, attrs2, el)
      val subs2 = attrs2.apply-attrs(el, emit)
      val kids  = patch-kids(kids1, kids2, el, emit)
      NElem(t1, attrs2, el, subs2, kids)
    (o, n) ->
      // shape changed: structural replace — detach old, build+attach new
      o.unsubscribe-tree   // deregister the discarded subtree's listeners
      val fresh = n.build(emit)
      parent.replace-child(fresh.element, o.element)
      fresh   // `o` is consumed here; dropping it releases its refs

// explicit deregistration point (destructor discipline: drops also do this
// idempotently, but the patcher does it eagerly and visibly)
fun drop-subs( subs : list<sub> ) : ioc ()
  subs.foreach(unsubscribe)

// Deregister every listener in a subtree being discarded. Dropping a `sub`
// releases its slot and host listener, but only `unsubscribe` removes the
// Koka-side registry entry — whose closure can own elements (e.g. OnValue
// captures its element to read the value at fire time). Every path that
// discards a mounted subtree must call this, or the registry pins the
// detached DOM alive (found by the `detached` slot check in the demo).
fun unsubscribe-tree<msg>( n : node<msg> ) : ioc ()
  match n
    NElem(_, _, _, subs, kids) ->
      subs.foreach(unsubscribe)
      kids.foreach fn(k) k.pretend-decreasing.unsubscribe-tree
    NText(_, _) -> ()

fun remove-old-attrs<msg>( old : list<attr<msg>>, new : list<attr<msg>>, el : element ) : ioc ()
  old.foreach fn(at)
    match at
      Attr(name, _) | !(new.has-attr(name)) -> el.remove-attribute(name)
      _ -> ()

fun has-attr<msg>( attrs : list<attr<msg>>, name : string ) : bool
  attrs.any fn(at)
    match at
      Attr(n, _) -> n == name
      _ -> False

// The key of a mounted node (from its stored attrs), if any.
fun node/node-key<msg>( n : node<msg> ) : maybe<string>
  match n
    NElem(_, attrs, _, _, _) -> attrs.key-of
    NText(_, _) -> Nothing

// Child reconciliation: keyed when BOTH sides are fully keyed (consume the
// old children into an association list, drain matches out -- reusing their
// mounted elements -- and let the leftovers unmount); index-based zip
// otherwise. Reordering keyed children moves the existing DOM nodes
// (append-child on an attached node is a move), so a pure reorder neither
// creates nor destroys elements -- the demo asserts this via live-slots.
fun patch-kids<msg>( olds : list<node<msg>>, news : list<html<msg>>, parent : element, emit : msg -> ioc () ) : <ioc,exn> list<node<msg>>
  if olds.all(fn(o) o.node-key.is-just) && news.all(fn(n) n.node-key.is-just)
     && (olds.is-cons || news.is-cons)
    then patch-keyed(olds, news, parent, emit)
    else patch-indexed(olds, news, parent, emit)

fun patch-keyed<msg>( olds : list<node<msg>>, news : list<html<msg>>, parent : element, emit : msg -> ioc () ) : <ioc,exn> list<node<msg>>
  // consume old children into (key, old-position, node) triples; `take`
  // drains matches, recording each reused node's OLD position so we can
  // move only the nodes that are actually out of order.
  val remaining = ref( olds.map-indexed(fn(i, o) (o.node/node-key.default(""), (i, o))) )
  // pass 1: patch/build every child in `news` order (no DOM moves yet);
  // oldpos = -1 marks genuinely new children (they always need placing).
  val patched = news.map fn(n)
    val k = n.node-key.default("")
    match take(remaining, k)
      Just((i, o)) -> (i, patch(o.pretend-decreasing, n, parent, emit))
      Nothing      -> (-1, n.build(emit))
  // leftovers were removed: detach them; their references release as the
  // remaining list drops here.
  (!remaining).foreach fn(entry)
    entry.snd.snd.unsubscribe-tree
    parent.remove-child(entry.snd.snd.element)
  // pass 2: minimal moves. Nodes whose old positions form the longest
  // increasing subsequence are already in relative order and stay put;
  // every other node is moved ONCE via insert-before, walking right-to-left
  // with the last settled node as the anchor. An unchanged order therefore
  // performs ZERO DOM moves (the demo asserts this).
  val keep = lis( patched.map(fst) )
  place( patched.reverse, keep.reverse, Nothing, parent )
  patched.map(snd)

// walk the (reversed) children right-to-left: `keep` positions stay and
// become the anchor; the rest insert-before the current anchor (or append
// when there is no anchor yet, i.e. they belong at the end).
fun place<msg>( rev : list<(int, node<msg>)>, keep : list<int>, anchor : maybe<element>, parent : element ) : <ioc,exn> ()
  match rev
    Nil -> ()
    Cons((oldpos, n), rest) ->
      if oldpos >= 0 && keep.head-or(-2) == oldpos
        then place(rest, keep.tail, Just(n.element), parent)  // in LIS: stays put, becomes anchor
        else
          match anchor
            Just(a) -> parent.insert-before(n.element, a)
            Nothing -> parent.append-child(n.element)         // move to end
          place(rest, keep, Just(n.element), parent)

fun head-or( xs : list<int>, default : int ) : int
  match xs
    Cons(x, _) -> x
    Nil -> default

// longest increasing subsequence of the non-negative entries (purely
// functional O(n^2) fold -- child lists are small; NOTE: an imperative
// version with local vars + `for` hit a C-codegen bug (undeclared iev_*
// identifiers in the yield-extend path), hence this shape).
// Returns the kept positions in order.
fun lis( xs : list<int> ) : list<int>
  // chains: for each element seen so far, the best increasing chain ENDING
  // at it, stored reversed (head = last element of the chain)
  val chains = xs.filter(fn(x) x >= 0).foldl([]) fn(acc : list<list<int>>, x : int)
    val best = acc.filter( fn(ch) ch.head-or(-1) < x ).longest
    Cons(Cons(x, best), acc)
  chains.longest.reverse

fun longest( xss : list<list<int>> ) : list<int>
  xss.foldl([]) fn(best, ch)
    if ch.length > best.length then ch else best

// drain the first pair with key `k` out of the ref'd association list
fun take<msg>( remaining : ref<global,list<(string, (int, node<msg>))>>, k : string ) : <st<global>,div> maybe<(int, node<msg>)>
  fun go( xs )
    match xs
      Nil -> (Nil, Nothing)
      Cons((key, entry), rest) ->
        if key == k then (rest, Just(entry))
        else
          val (rest2, found) = go(rest)
          (Cons((key, entry), rest2), found)
  val (rest, found) = go(!remaining)
  remaining := rest
  found

fun patch-indexed<msg>( olds : list<node<msg>>, news : list<html<msg>>, parent : element, emit : msg -> ioc () ) : <ioc,exn> list<node<msg>>
  match (olds, news)
    (Nil, Nil) -> Nil
    (Cons(o, os), Cons(n, ns)) ->
      val n2 = patch(o.pretend-decreasing, n, parent, emit)
      Cons(n2, patch-indexed(os, ns, parent, emit))
    (Cons(o, os), Nil) ->
      // fewer children: detach the extras (release happens as `o` drops)
      o.unsubscribe-tree
      parent.remove-child(o.element)
      patch-indexed(os, Nil, parent, emit)
    (Nil, Cons(n, ns)) ->
      val fresh = n.build(emit)
      parent.append-child(fresh.element)
      Cons(fresh, patch-indexed(Nil, ns, parent, emit))
