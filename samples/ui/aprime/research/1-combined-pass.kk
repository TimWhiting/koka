// Small-scale memoization probe -- models lib/ui's essential structure:
// a widget tree, a `measure` effect (the expensive text-shaping cost, counted),
// and a combined build+layout pass. Tests: (1) does wrapping a stable subtree in
// `memo` skip its measures across frames, (2) can `memo`'s build use a NESTED
// effect (theme) -- the limitation Tim raised. Monomorphic (no msg) to focus on
// the memo mechanics; the real lib/ui erases the msg type in the store.
module probe
import std/core/unsafe

// ---- widgets + laid-out tree ----
type ltree
  Ltext( s : string, w : int )
  Lbox( w : int, child : ltree )
  Lrow( w : int, kids : list<ltree> )

// ---- the expensive resource: measuring text (counted) ----
effect measure
  fun measure-text( s : string ) : int    // "shaping" -- each call is cost

// ---- the ephemeral store (lib/ui's uistate): a memo cache keyed by identity ----
effect store
  fun cache-get( key : string ) : maybe<(string, ltree)>
  fun cache-put( key : string, deps : string, lt : ltree ) : ()

// ---- a nested effect a build might want (lib/ui's `theme`) ----
effect val theme : string

type widget
  Wtext( s : string )
  Wbox( child : widget )
  Wrow( kids : list<widget> )
  Wmemo( key : string, deps : string, build : () -> <measure,store,theme,div> widget )

fun width( t : ltree ) : int
  match t
    Ltext(_, w) -> w
    Lbox(w, _) -> w
    Lrow(w, _) -> w

// combined build+layout (immediate mode). The memo arm SKIPS both build and
// measure when deps are unchanged, returning the cached ltree.
fun render( w : widget ) : <measure,store,theme,div> ltree
  match w
    Wtext(s) -> Ltext(s, measure-text(s))
    Wbox(c) ->
      val lt = render(c)
      Lbox(lt.width + 4, lt)
    Wrow(kids) ->
      val lts = kids.map(render)
      Lrow(lts.map(width).foldl(0, (+)), lts)
    Wmemo(key, deps, build) ->
      match cache-get(key)
        Just((cdeps, clt)) | cdeps == deps ->
          clt                                // HIT: no build, no measure
        _ ->
          val lt = render(build())           // MISS: build (current effect ctx) + measure
          cache-put(key, deps, lt)
          lt

fun memo( key : string, deps : string, build : () -> <measure,store,theme,div> widget ) : widget
  Wmemo(key, deps, build)

fun with-store( action : () -> <store,div|e> a ) : <div|e> a
  var entries : list<(string,(string,ltree))> := []
  with handler
    fun cache-get(k)      entries.lookup(fn(kk) kk == k)
    fun cache-put(k, d, lt)
      entries := Cons((k, (d, lt)), entries.filter(fn(p) p.fst != k))
  action()

// ---- the view: a big STATIC list + one ANIMATING counter ----
fun view( frame : int ) : <measure,store,theme,div> widget
  val static-list = memo("list", "static") fn()
    Wrow(list(1, 20).map(fn(i) Wtext("item-" ++ i.show ++ "-" ++ theme)))
  val counter = Wtext("count: " ++ frame.show)   // changes every frame, not memoized
  Wrow([static-list, counter])

pub fun main()
  var measures := 0
  with fun measure-text(s) { measures := measures + 1; s.count }
  with val theme = "dark"
  with with-store
  list(1, 100).foreach fn(frame)
    render(view(frame)).width.ignore
  println("measures over 100 frames: " ++ measures.show)
  println("(no-memo would be 100*21 = 2100; memo target = 20 + 100 = 120)")
