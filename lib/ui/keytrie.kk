/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The identity TRIE: widget identity as a tree of segments mirroring the widget
// tree, instead of per-frame concatenated key strings.
//
// - A `segment` is one step of identity: a named scope, a source line, or a list
//   index. `Named` comparison hits a pointer-equality fast path first: string
//   literals are stuck statics, so `scope("sidebar")` passes the SAME pointer
//   every frame and comparison is O(1) without reading the string.
// - A `knode` is a trie node carrying a process-unique int `id` -- THE identity.
//   Zipper moves rebuild nodes (FBIP-style), so node values are transient but the
//   `id` is assigned at first creation and preserved through every rebuild;
//   everything downstream (state cells, scroll metrics, anchor rects) keys off
//   the id, never off a node pointer.
// - The `keytree` effect is the single place of mutation: its handler (installed
//   once at the app root) owns the trie between frames. One effect = one tree;
//   a future parallel tree (e.g. a semantics tree) gets its OWN effect
//   definition, since same-effect handlers cannot be selected at the call site.
//
// RETENTION (the keep-alive design from samples/ui/aprime): state lifetime is
// a property OF THE KEY, not of mounting. Each identity carries a `keep`
// policy declared where it was minted. Unmount detection is by CONSUMPTION at
// memo boundaries: when a boundary RE-RUNS, `kt-open` moves its children to a
// `stale` list; the rebuild's descends claim them back one by one; whatever
// remains at `kt-close` is exactly the unmounted set -- Transient subtrees
// drop (their ids are returned so the state store can drop cells/edges too),
// KeepAlive subtrees move to a cold `retained` list (out of layout and paint
// entirely; no widget references them) and a later descend by the SAME
// segment promotes them back with cells, memo cache, and dirt intact.
module ui/keytrie

import std/core/unsafe    // unsafe-ptr-eq: literal segments compare by pointer first
import std/core/undiv
import std/num/int32
import std/data/int32-map // id -> path (Patricia, int32 keys: JS-cheap): assoc list was 2x slower overall

// One step of widget identity.
pub type segment
  Named( name : string )     // an explicit scope: `scope("sidebar")`
  Line( fl : string )        // a call site: `?kk-file-line`
  Index( i : int )           // a mapped-list disambiguator: `idx(3)`
  Slot( tag : string, fl : string )  // a library slot at a call site: tag + ?kk-file-line

// Segment equality: pointer fast path for the string cases (stuck literals give
// the same pointer every frame), content compare as the cold fallback.
pub fun segment/(==)( a : segment, b : segment ) : bool
  match (a, b)
    (Named(x), Named(y)) -> unsafe-ptr-eq(x, y) || x == y
    (Line(x), Line(y))   -> unsafe-ptr-eq(x, y) || x == y
    (Index(x), Index(y)) -> x == y
    (Slot(t1, x), Slot(t2, y)) ->
      (unsafe-ptr-eq(t1, t2) || t1 == t2) && (unsafe-ptr-eq(x, y) || x == y)
    _ -> False

pub fun segment/show( s : segment ) : string
  match s
    Named(n) -> "/" ++ n
    Line(fl) -> "/" ++ fl
    Index(i) -> "[" ++ i.show ++ "]"
    Slot(t, fl) -> "/" ++ t ++ "@" ++ fl

// What happens to an identity's subtree (cells, memo cache, descendants) when
// its parent memo boundary rebuilds WITHOUT it (unmount).
pub type keep
  Transient    // prune the subtree: state dies with the mount
  KeepAlive    // move to `retained`; remount by the SAME path finds all state
               // intact (tab scroll positions, expanders, field text)

fun is-keep-alive( k : keep ) : bool
  match k
    KeepAlive -> True
    Transient -> False

// A trie node. `id` is the persistent identity (survives zipper rebuilds);
// child lists are association lists (small fan-out, segment fast-eq makes the
// scan cheap). The node VALUE is transient -- never hold one across a move.
// `dirty` is the SUBTREE-dirty bit (this identity or any descendant has a
// dirty state reader): set by kt-mark-dirty, PROPAGATED upward by `ascend`
// as a natural part of zipper moves, cleared by a memo boundary's rebuild.
// Fields are ordered by access temperature: the hot path (descend's child
// scan, the dirty check) never touches the cold retention data.
pub struct knode
  nid      : int
  dirty    : bool
  children : list<(segment, knode)>  // HOT: live children (descend scans)
  keep     : keep                    // WARM: this identity's unmount policy
  stale    : list<(segment, knode)>  // unclaimed children of an OPEN rebuild
  retained : list<(segment, knode)>  // COLD: kept-alive unmounted subtrees

// Which of the parent's three child lists the focus rejoins on ascend: a
// claiming descend (identity minting during a build) always rejoins `children`;
// an administrative walk (re-rooting for a dirty mark) restores the child to
// wherever it was found, so admin traffic never counts as a mount.
type kplace
  InLive
  InStale
  InRetained

// The zipper: the focused node plus the path of contexts back to the root.
// A context is the parent minus the focused child (so moves are rebuilds, no
// balance discipline needed -- see the FBIP zipper style). `before`/`after`
// split the list named by `place`; the other two lists ride along whole (the
// slot matching `place` is unused -- ascend reads only the two others).
pub struct kctx
  seg      : segment            // which child of the parent the focus is
  pid      : int                // the parent's id
  pdirty   : bool               // the parent's own dirty bit (preserved on ascend)
  pkeep    : keep               // the parent's keep policy (preserved on ascend)
  place    : kplace             // list the focus rejoins on ascend
  before   : list<(segment, knode)>  // `place`-list siblings before the focus (reversed)
  after    : list<(segment, knode)>  // `place`-list siblings after the focus
  live-r   : list<(segment, knode)>  // parent's `children` when place != InLive
  stale-r  : list<(segment, knode)>  // parent's `stale`    when place != InStale
  ret-r    : list<(segment, knode)>  // parent's `retained` when place != InRetained

pub struct kzip
  focus : knode
  path  : list<kctx>

pub fun kzip/empty( root-id : int = 0 ) : kzip
  Kzip( Knode(root-id, False, [], Transient, [], []), [] )

// Move the focus into `seg`. A CLAIMING descend (`claim = True`: identity
// minting during a build) searches live children, then the open rebuild's
// stale list, then the retained store -- claiming from stale is a survival
// (still mounted), claiming from retained is a REMOUNT (the whole kept
// subtree promotes back, state intact); a miss creates the child with the
// given `keep` policy. A non-claiming descend (re-rooting walks) finds the
// child wherever it is and will restore it there. Returns the new zipper and
// the child's id.
pub fun descend( z : kzip, seg : segment, fresh : () -> e int,
                 claim : bool = True, keep : keep = Transient ) : e (kzip, int)
  match z.focus
    Knode(pid, pd, kids, pk, stale, retained) ->
      fun pick( rest : list<(segment, knode)>, pre : list<(segment, knode)> )
            : maybe<(knode, list<(segment, knode)>, list<(segment, knode)>)>
        match rest
          Cons((s, child), post) ->
            if s == seg then Just((child, pre, post))
            else pick(post.pretend-decreasing, Cons((s, child), pre))
          Nil -> Nothing
      fun enter( child : knode, kc : kctx ) : (kzip, int)
        (Kzip(child, Cons(kc, z.path)), child.nid)
      match pick(kids, [])
        Just((child, pre, post)) ->
          enter(child, Kctx(seg, pid, pd, pk, InLive, pre, post, [], stale, retained))
        Nothing -> match pick(stale, [])
          Just((child, pre, post)) ->
            if claim
              then enter(child, Kctx(seg, pid, pd, pk, InLive, [], kids, [], pre.reverse-append(post), retained))
              else enter(child, Kctx(seg, pid, pd, pk, InStale, pre, post, kids, [], retained))
          Nothing -> match pick(retained, [])
            Just((child, pre, post)) ->
              if claim
                then enter(child, Kctx(seg, pid, pd, pk, InLive, [], kids, [], stale, pre.reverse-append(post)))
                else enter(child, Kctx(seg, pid, pd, pk, InRetained, pre, post, kids, stale, []))
            Nothing ->
              val child = Knode(fresh(), False, [], keep, [], [])
              enter(child, Kctx(seg, pid, pd, pk, InLive, [], kids, [], stale, retained))

// Move the focus up one level, rebuilding the parent with the (possibly
// updated) focused child in its origin list.
pub fun ascend( z : kzip ) : kzip
  match z.path
    Cons(Kctx(seg, pid, pdirty, pkeep, place, before, after, live-r, stale-r, ret-r), up) ->
      val slot = before.reverse-append( Cons((seg, z.focus), after) )
      // subtree-dirty PROPAGATION: a dirty LIVE child taints the parent on
      // the way up -- ancestor bits are maintained by normal zipper motion.
      // Stale/retained children keep their own bit but do NOT taint: an
      // unmounted-but-dirty subtree must not pin an ancestor boundary into
      // rebuilding forever (its dirt travels with it on remount instead).
      match place
        InLive     -> Kzip( Knode(pid, pdirty || z.focus.dirty, slot, pkeep, stale-r, ret-r), up )
        InStale    -> Kzip( Knode(pid, pdirty, live-r, pkeep, slot, ret-r), up )
        InRetained -> Kzip( Knode(pid, pdirty, live-r, pkeep, stale-r, slot), up )
    Nil -> z

// Ascend all the way to the root (end of a frame / before a fresh walk).
pub fun to-root( z : kzip ) : kzip
  match z.path
    Nil -> z
    _   -> to-root( z.ascend.pretend-decreasing )

// the focus's path from the root (context segments, bottom-up -> reversed)
pub fun zip-path( z : kzip ) : list<segment>
  z.path.map(fn(c) c.seg).reverse

fun common-prefix-len( a : list<segment>, b : list<segment> ) : div int
  match (a, b)
    (Cons(x, xs), Cons(y, ys)) -> if x == y then 1 + common-prefix-len(xs.pretend-decreasing, ys) else 0
    _ -> 0

fun ascend-n( z : kzip, n : int ) : div kzip
  if n <= 0 then z else ascend-n(z.ascend, n - 1)

// every id in a subtree (live + stale + retained): the prune set of a
// Transient unmount, handed to the state store so cells/edges die too
fun node-ids( n : knode ) : div list<int>
  match n
    Knode(i, _, kids, _, stale, retained) ->
      Cons(i, (kids ++ stale ++ retained).flatmap(fn(sc) node-ids(sc.snd.pretend-decreasing)))

// close an OPEN node: whatever is still stale was not rebuilt = unmounted.
// KeepAlive children move to `retained` (prepended: a newer retention of the
// same segment shadows an older one until the pruning knob exists); Transient
// children drop, returning every id in their subtrees.
fun close-node( n : knode ) : div (knode, list<int>)
  match n
    Knode(i, d, kids, k, stale, retained) ->
      val (keepers, dropped) = stale.partition(fn(sc) sc.snd.keep.is-keep-alive)
      val pruned = dropped.flatmap(fn(sc) node-ids(sc.snd))
      (Knode(i, d, kids, k, [], keepers ++ retained), pruned)

// ----------------------------------------------------------------
// The identity-tree effect: ONE tree, its handler owns the zipper.

// A widget identity: a node in the identity trie. ABSTRACT -- the only mints
// are the helpers below (`here`/`idx`/`scope`) and the root, so identities can
// never be forged or accidentally shared by construction.
abstract value struct key( id : int )

// the root of the identity tree (the runtime's `with-keytree` owns node 0)
pub val root-key : key = Key(0)

pub fun key/show( k : key ) : string
  match k
    Key(i) -> "#" ++ i.show

pub effect keytree
  // enter (or create) the child `seg` of the node `of`, returning the child's
  // persistent id. `of` is the caller's current key: if it is not the current
  // focus, the handler re-roots first (ids are stable; nodes are not). `keep`
  // applies only when the child is CREATED (policy is fixed at first mint).
  fun kt-child-id( of : int, seg : segment, keep : keep ) : int
  // the memo/dirty protocol (see samples/ui/aprime): mark an identity's node
  // dirty (ancestors taint via ascend); ask whether an identity's SUBTREE is
  // dirty; clear an identity's bit after its boundary rebuilt.
  fun kt-mark-dirty( id : int ) : ()
  fun kt-subtree-dirty( id : int ) : bool
  fun kt-clean-dirty( id : int ) : ()
  // the retention protocol: a memo boundary brackets its rebuild with
  // kt-open (children -> stale) and kt-close (unclaimed stale = unmounted:
  // apply keep policies; returns the pruned ids for the state store).
  fun kt-open( id : int ) : ()
  fun kt-close( id : int ) : list<int>
  // selector resolution: every id whose root path matches `steps` (see
  // `path-matches`). A pure read of the id -> path table -- does NOT move
  // the zipper. Ids are returned sorted ascending for determinism.
  fun kt-find( steps : list<sel-step> ) : list<int>
  // the root-to-id path of an identity (rendered via `segment/show` for
  // ambiguity errors: "which of these did you mean"). `[]` for an unknown id.
  fun kt-path( id : int ) : list<segment>

// Derive a child identity (the common entry point). `keep` is the child's
// unmount policy, fixed at first mint (see `ui/ident` for the user helpers).
pub fun kt-child( of : key, seg : segment, keep : keep = Transient ) : keytree key
  match of
    Key(i) -> Key( kt-child-id(i, seg, keep) )

// The internal id of a key: for the store and the layout-tree node payloads
// (backends hit-test and publish by id). Not a way to forge keys -- there is
// no id -> key direction outside this module.
pub fun key/key-id( k : key ) : int
  match k
    Key(i) -> i

// ----------------------------------------------------------------
// Selector queries: a selector is a whitespace-separated sequence of
// DESCENDANT steps over the id -> path table (see docs/superpowers/specs
// selector-queries section). A step is `name` (`Named(name)`), `:i`
// (`Index(i)`), or `name:i` (an ADJACENT `Named(name)` immediately followed
// by `Index(i)` in the path -- one step, two path segments).
pub type sel-step
  SName( name : string )
  SIndex( i : int )
  SBoth( name : string, i : int )

fun sel-step/parse( t : string ) : sel-step
  match t.split(":")
    [name] -> SName(name)
    [name, idxs] -> match idxs.parse-int
      Just(i) -> if name.is-empty then SIndex(i) else SBoth(name, i)
      Nothing -> impossible("parse-selector: malformed index in step \"" ++ t ++ "\"")
    _ -> impossible("parse-selector: malformed step \"" ++ t ++ "\"")

// Parse a selector string into steps: `"todos row:3 bump"` ->
// `[SName("todos"), SBoth("row",3), SName("bump")]`. Empty (or all-whitespace)
// input parses to `[]`.
pub fun parse-selector( s : string ) : list<sel-step>
  val trimmed = s.trim
  if trimmed.is-empty then [] else trimmed.split(" ").filter(fn(t) !t.is-empty).map(sel-step/parse)

// Does `path` match `steps` as an ordered subsequence (gaps allowed between
// steps; `SBoth` requires its `Named`+`Index` pair to be ADJACENT in the
// path -- it consumes exactly those two segments) THAT REACHES THE END of
// the path: the last step must land on the path's last segment, so a
// selector addresses a specific identity, not its whole subtree (a bare
// name selector is unique for a unique name, as the old string-key lookup
// was). `Line`/`Slot` segments are never named by a step; they can only be
// skipped as gaps before/between steps.
// BACKTRACKING: at each segment a matching step may EITHER consume it OR
// skip it as a gap -- both are tried (`consumed || skip`). A greedy commit
// (consume-on-match with no fallback) makes an identity whose path repeats a
// step's segment value before the tail unaddressable: e.g. `"a"` over
// `root/a/a` must match the INNER a (the first a treated as a gap), and
// `find-ids("a")` returns BOTH (ambiguous). Structural recursion on `path`
// (both branches drop at least the head) -- terminating, total.
fun path-matches( path : list<segment>, steps : list<sel-step> ) : bool
  match steps
    Nil -> path.is-nil    // all steps consumed AND path fully consumed = tail-anchored
    Cons(step, rest) ->
      val consumed = match step
        SName(name) -> match path
          Cons(Named(n), tl) | n == name -> path-matches(tl, rest)
          _ -> False
        SIndex(i) -> match path
          Cons(Index(j), tl) | j == i -> path-matches(tl, rest)
          _ -> False
        SBoth(name, i) -> match path
          Cons(Named(n), Cons(Index(j), tl)) | n == name && j == i -> path-matches(tl, rest)
          _ -> False
      if consumed then True
      else match path       // skip this segment as a gap; keep all steps
        Cons(_, tl) -> path-matches(tl, steps)
        Nil -> False

// resolve a selector string to every matching id (parse + `kt-find`); see
// docs/superpowers/specs selector-queries for the grammar and semantics.
pub fun find-ids( sel : string ) : keytree list<int>
  kt-find(parse-selector(sel))

// no std sort over `list<int>` in this tree -- ids per selector are few
// (ambiguity is the exceptional case), so a plain insertion sort is fine.
fun ints/insert( xs : list<int>, x : int ) : list<int>
  match xs
    Cons(y, ys) -> if x <= y then Cons(x, xs) else Cons(y, ints/insert(ys, x))
    Nil -> [x]

fun ints/sort( xs : list<int> ) : list<int>
  xs.foldl([], ints/insert)

// The root handler: owns the trie between frames. Walking to an arbitrary
// `of` id is done by path: the handler keeps a map id -> path-from-root so a
// re-root is a replay of segments (ids are dense ints; see `ui/state` store).
// UNIQUENESS DISCIPLINE (measured in samples/ui/aprime/research/keytrie-bench):
// reading the zipper out of the ref with `!zip` before a move leaves it at
// rc>=2, so the zipper's fbip-style rebuilds cannot reuse -- `swap` takes it
// OUT at rc=1 (the ref briefly holds an empty dummy) and puts the moved
// zipper back. Together with int-map paths: ~2x on identity derivation.
pub fun with-keytree( action : () -> <keytree,div,st<global>|e> a ) : <div,st<global>|e> a
  val zip  : ref<global, kzip> = ref(kzip/empty())
  val next : ref<global, int>  = ref(1)
  val paths : ref<global, int32-map<list<segment>>> = ref(int32-map/empty().set(0.int32, []))  // id -> path from root
  fun path-of( id : int ) : <read<global>> list<segment>
    (!paths).lookup(id.int32).default([])
  fun walk-to( id : int ) : <div,st<global>> ()
    // LCA re-root: ascend only to the divergence point with the target's
    // path, then descend the remaining suffix -- NOT a full root replay.
    // (A deep component minting many children re-roots to its own depth
    // constantly; full replay made that O(depth) per sibling.) Non-claiming:
    // an admin walk must not count as a mount (see kplace).
    val target = path-of(id)
    val z0 = zip.swap(kzip/empty())
    val cur = z0.zip-path
    val common = common-prefix-len(cur, target)
    var z := z0.ascend-n(cur.length - common)
    target.drop(common).foreach fn(seg)
      val (z2, _) = z.descend(seg, fn() { val n = !next; next := n + 1; n }, claim = False)
      z := z2
    zip := z
  fun set-focus-dirty( d : bool ) : <div,st<global>> ()
    val z0 = zip.swap(kzip/empty())
    val z1 = match z0.focus
      Knode(id, _, kids, k, stale, retained) -> Kzip(Knode(id, d, kids, k, stale, retained), z0.path)
    zip := z1
  with handler
    fun kt-child-id( of, seg, keep )
      // fast path: deriving from the CURRENT focus (the normal tree-walk order)
      // needs no re-root; anything else replays the parent's path first.
      if (!zip).focus.nid != of then walk-to(of)
      val z0 = zip.swap(kzip/empty())
      fun mint() : <read<global>,write<global>> int
        val n = !next
        next := n + 1
        val pp = path-of(of) ++ [seg]      // BEFORE any further store swaps
        val p0 = paths.swap(int32-map/empty())
        paths := p0.set(n.int32, pp)
        n
      val (z2, cid) = z0.descend(seg, mint, claim = True, keep = keep)
      zip := z2
      cid
    fun kt-mark-dirty( id )
      if (!zip).focus.nid != id then walk-to(id)
      set-focus-dirty(True)
    fun kt-subtree-dirty( id )
      if (!zip).focus.nid != id then walk-to(id)
      (!zip).focus.dirty
    fun kt-clean-dirty( id )
      if (!zip).focus.nid != id then walk-to(id)
      set-focus-dirty(False)
    fun kt-open( id )
      if (!zip).focus.nid != id then walk-to(id)
      val z0 = zip.swap(kzip/empty())
      val z1 = match z0.focus
        Knode(i, d, kids, k, stale, retained) ->
          // children -> stale (merged with any leftover stale from an
          // interrupted rebuild); the build's descends claim them back
          Kzip(Knode(i, d, [], k, kids ++ stale, retained), z0.path)
      zip := z1
    fun kt-close( id )
      if (!zip).focus.nid != id then walk-to(id)
      val z0 = zip.swap(kzip/empty())
      val (n2, pruned) = close-node(z0.focus)
      zip := Kzip(n2, z0.path)
      if !pruned.is-nil then
        val p0 = paths.swap(int32-map/empty())
        paths := pruned.foldl(p0, fn(m, i) m.remove(i.int32))
      pruned
    fun kt-find( steps )
      (!paths).list.filter(fn(kv) path-matches(kv.snd, steps)).map(fn(kv) kv.fst.int).ints/sort
    fun kt-path( id )
      path-of(id)
  action()
