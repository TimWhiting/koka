// A-PRIME: the proposed memoization architecture for lib/ui, materialized as a
// self-contained console program (no UI backend) -- the decision artifact for
// probe 5 of the framework experiment. See docs/ui/design-notes.md entry 8.
//
// THE ARCHITECTURE
//
//   1. Anything CHANGEABLE lives behind dynamic ops over one root store
//      (lib/ui's `uistate`) -- including framework ambients like theme.
//      `with val` remains for genuine constants. Rationale (probes in
//      research/): a stored continuation FREEZES `effect val` evidence, so
//      continuation-based reactivity replays stale ambients; only live ops
//      read fresh. Both designs need this prerequisite -- and given it,
//      top-down re-running needs no continuations at all.
//
//   2. Reads are AUTO-TRACKED: the store records which memo identity is
//      building when a cell is read (no manual dependency lists). A cell
//      write dirties exactly its reader keys.
//
//   3. Dirtiness is SUBTREE dirtiness over the key TREE: a memo misses when
//      its own key OR ANY DESCENDANT key is dirty (prefix check on the key
//      path). This is what makes the grandchild case correct: grandchild
//      reads theme, its memoized parent does not -- on a theme change the
//      parent must still MISS (its subtree contains a dirty reader) so the
//      top-down pass descends the spine, re-installs every user handler on
//      the path, and rebuilds the grandchild under fresh ambient state.
//      Clean sibling branches still hit their own memos, so the cost of a
//      change is O(dirty spines), not O(tree).
//
//   4. Rebuild is TOP-DOWN inside the view call: user `with` handlers on the
//      path re-install naturally, so builds always see correct ambient state
//      for ARBITRARY user effects (the thing frozen continuations get wrong,
//      and the property that preserves ambient-instead-of-prop-drilling).
//
//   5. The CLOSED-ROW rule (future work, typed discipline): a builder may be
//      stored/spliced OUT of the view pass (animation leaves, C-prime
//      continuations) only if its effect row is CLOSED over framework
//      effects -- all dynamic ops. An open row (any user ambient) must go
//      top-down. The type checker polices capture scope.
//
// In real lib/ui: keys are the existing keytrie identities, the store is the
// uistate handler, memo hits return the SAME widget pointer so reconcile
// skips relayout via unsafe-ptr-eq (measured 17.5x fewer text measures in
// research/), and theme becomes a tracked cell.
module main

// a memo key is a PATH from the root (lib/ui: the keytrie identity)
alias path = list<string>

fun path/show( p : path ) : string
  p.join("/")

// is `p` an ancestor-or-self of `d`? (root-first paths: ancestor = prefix)
fun is-prefix( p : path, d : path ) : div bool
  match (p, d)
    (Nil, _) -> True
    (Cons(x, xs), Cons(y, ys)) -> x == y && is-prefix(xs, ys)
    _ -> False

// the store: reactive cells + tracked reads + subtree-dirty memo cache
// (lib/ui: these become uistate ops; the handler owns representation)
effect store
  fun cell-read( id : int ) : string          // TRACKED: attributes to the innermost memo
  fun cell-write( id : int, v : string ) : () // dirties exactly the readers of `id`
  fun memo-enter( key : path ) : bool         // True = miss (subtree dirty / cold): rebuild
  fun memo-exit( key : path, built : string ) : ()
  fun memo-cached( key : path ) : string

fun with-store( action : () -> <store,div|e> a ) : <div|e> a
  var cells   : list<(int,string)>    := []
  var deps    : list<(int,path)>      := []   // read edges: cell -> reader (innermost memo)
  var dirty   : list<path>            := []   // reader keys needing rebuild
  var cache   : list<(path,string)>   := []
  var current : list<path>            := []   // stack of memo keys being built
  with handler
    fun cell-read(id)
      match current
        Cons(k, _) ->
          if !deps.any(fn(d) d.fst == id && d.snd == k) then deps := Cons((id, k), deps)
        _ -> ()
      cells.lookup(fn(i) i == id).default("")
    fun cell-write(id, v)
      cells := Cons((id, v), cells.filter(fn(p) p.fst != id))
      dirty := deps.filter(fn(d) d.fst == id).map(snd) ++ dirty
    fun memo-enter(k)
      // MISS iff cold, or this key or ANY DESCENDANT is dirty (subtree check)
      val miss = !cache.any(fn(c) c.fst == k) || dirty.any(fn(d) is-prefix(k, d))
      if miss then
        deps := deps.filter(fn(d) d.snd != k)   // re-tracking: this key's own edges only
        current := Cons(k, current)
      miss
    fun memo-exit(k, built)
      cache := Cons((k, built), cache.filter(fn(c) c.fst != k))
      // the subtree under `k` was just (re)built: clear ITS dirt, including
      // entries for children that no longer exist (they re-register if alive)
      dirty := dirty.filter(fn(d) !is-prefix(k, d))
      current := current.drop(1)
    fun memo-cached(k)
      cache.lookup(fn(c) c == k).default("?")
  action()

// the memo combinator (lib/ui: keyed by ?key + call line like use-state;
// a HIT returns the cached value -- in lib/ui the SAME widget pointer, so
// reconcile skips the subtree's relayout via unsafe-ptr-eq)
fun memo( key : path, build : () -> <store,console,div|e> string ) : <store,console,div|e> string
  if memo-enter(key) then
    val w = build()
    memo-exit(key, w)
    println("    [built " ++ key.path/show ++ " -> " ++ w ++ "]")
    w
  else
    memo-cached(key)

// ---- the demo tree -------------------------------------------------------
//
//   root
//    +- child  (memo, does NOT read theme)          <- must MISS on theme
//    |   +- grandchild (memo, READS theme)             change via SUBTREE
//    +- sibling (memo, reads cell 1 only)              dirtiness, then hit
//                                                      its other branches
// theme = tracked cell 0

fun theme() : store string
  cell-read(0)

// a USER mid-tree ambient: arbitrary, re-installed on every top-down pass
effect val user-env : string

fun grandchild( key : path ) : <store,user-env,console,div> string
  memo(key) fn()
    "grandchild(theme=" ++ theme() ++ ", env=" ++ user-env ++ ")"

fun child( key : path ) : <store,user-env,console,div> string
  memo(key) fn()
    // note: reads NO cells itself -- a naive self-only dirty check would hit
    // here forever and starve the grandchild of the theme change
    "child[" ++ grandchild(key ++ ["gc"]) ++ "]"

fun sibling( key : path ) : <store,user-env,console,div> string
  memo(key) fn()
    "sibling(count=" ++ cell-read(1) ++ ")"

fun view( env : string ) : <store,console,div> string
  with val user-env = env    // user handler: fresh each pass, on the spine
  child(["child"]) ++ " | " ++ sibling(["sib"])

pub fun main()
  with with-store
  cell-write(0, "dark")
  cell-write(1, "0")
  println("frame 1 -- cold, everything builds:")
  println("  " ++ view("env-a"))
  println("frame 2 -- nothing changed, ZERO rebuilds:")
  println("  " ++ view("env-a"))
  cell-write(0, "light")
  println("frame 3 -- THEME changed: child misses via SUBTREE dirt (its own deps")
  println("           are unchanged!), descends, grandchild rebuilds under the")
  println("           fresh theme AND the freshly re-installed user env;")
  println("           sibling untouched:")
  println("  " ++ view("env-b"))
  cell-write(1, "42")
  println("frame 4 -- counter changed: ONLY sibling rebuilds:")
  println("  " ++ view("env-b"))
