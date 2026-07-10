// TWO-PASS probe (faithful to lib/ui): pass 1 = view() builds the widget tree
// WITH theme in scope; pass 2 = reconcile() lays out WITHOUT theme. Tests
// Option A: eager-build memo caches the WIDGET (pointer-stable across frames on
// unchanged deps), and reconcile short-circuits relayout via unsafe-ptr-eq.
module probe2
import std/core/unsafe

type widget
  Wtext( s : string )
  Wbox( child : widget )
  Wrow( kids : list<widget> )
  Wmemo( key : string, child : widget )   // child eagerly built (or cached) in view

type ltree
  Ltext( s : string, w : int )
  Lbox( w : int, child : ltree )
  Lrow( w : int, kids : list<ltree> )
  Lmemo( key : string, srcw : widget, child : ltree )   // srcw = widget that produced `child`

effect measure
  fun measure-text( s : string ) : int      // pass-2 cost (counted)

// pass-1 widget cache (lib/ui's uistate): key -> (deps, built widget)
effect wstore
  fun wget( key : string ) : maybe<(string, widget)>
  fun wput( key : string, deps : string, w : widget ) : ()

effect val theme : string

fun width( t : ltree ) : int
  match t
    Ltext(_, w) -> w
    Lbox(w, _) -> w
    Lrow(w, _) -> w
    Lmemo(_, _, c) -> c.width

// PASS 1 (view context: theme in scope). memo eagerly builds on deps-change and
// caches the WIDGET; on a hit it returns the SAME cached widget (pointer-stable).
fun memo( key : string, deps : string, build : () -> <wstore,theme,div> widget ) : <wstore,theme,div> widget
  match wget(key)
    Just((cdeps, cw)) | cdeps == deps -> Wmemo(key, cw)    // HIT: reuse widget, skip build
    _ ->
      val w = build()                                       // MISS: build uses theme (in scope now)
      wput(key, deps, w)
      Wmemo(key, w)

// PASS 2 (reconcile: NO theme). Short-circuit: if the incoming memo child is the
// SAME pointer as the widget that built the old ltree, reuse the old ltree.
fun reconcile( old : maybe<ltree>, w : widget ) : <measure,div> ltree
  match w
    Wtext(s) -> Ltext(s, measure-text(s))
    Wbox(c) ->
      val oc = match old { Just(Lbox(_, lc)) -> Just(lc); _ -> Nothing }
      val lt = reconcile(oc, c)
      Lbox(lt.width + 4, lt)
    Wrow(kids) ->
      val olds = match old { Just(Lrow(_, lks)) -> lks; _ -> [] }
      val lts = kids.map-indexed(fn(i, k) reconcile(olds.index-maybe(i), k))
      Lrow(lts.map(width).foldl(0, (+)), lts)
    Wmemo(key, child) ->
      match old
        Just(Lmemo(_, srcw, clt)) | unsafe-ptr-eq(srcw, child) ->
          Lmemo(key, child, clt)                            // HIT: no measure, reuse subtree
        _ ->
          val oc = match old { Just(Lmemo(_, _, lc)) -> Just(lc); _ -> Nothing }
          Lmemo(key, child, reconcile(oc, child))           // MISS: re-layout

fun index-maybe( xs : list<a>, i : int ) : maybe<a>
  xs.drop(i).head

fun with-wstore( action : () -> <wstore,div|e> a ) : <div|e> a
  var entries : list<(string,(string,widget))> := []
  with handler
    fun wget(k)        entries.lookup(fn(kk) kk == k)
    fun wput(k, d, w)  entries := Cons((k, (d, w)), entries.filter(fn(p) p.fst != k))
  action()

fun view( frame : int ) : <wstore,theme,div> widget
  val static-list = memo("list", "static") fn()
    Wrow(list(1, 20).map(fn(i) Wtext("item-" ++ i.show ++ "-" ++ theme)))
  val counter = Wtext("count: " ++ frame.show)
  Wrow([static-list, counter])

pub fun main()
  var measures := 0
  var prev : maybe<ltree> := Nothing
  with fun measure-text(s) { measures := measures + 1; s.count }
  with val theme = "dark"
  with with-wstore
  list(1, 100).foreach fn(frame)
    val w = view(frame)            // PASS 1: theme + wstore in scope
    val lt = reconcile(prev, w)    // PASS 2: measure only (no theme)
    prev := Just(lt)
  println("measures over 100 frames: " ++ measures.show)
  println("(no-memo would be 100*21 = 2100; memo target = 20 + 100 = 120)")
