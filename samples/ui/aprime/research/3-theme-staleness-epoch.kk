// The Option-A wart: `build` reads ambient `theme`, but if `deps` doesn't
// include it, a theme change leaves the memoized subtree STALE. Then: an
// "epoch" mitigation -- theme changes bump a counter that salts every memo's
// deps, so all memoized subtrees invalidate on a theme flip without the caller
// having to name theme.
module probe3
import std/core/unsafe

effect val theme : string
effect wstore
  fun wget( key : string ) : maybe<(string, string)>   // (deps, built-text) -- simplified: widget = its text
  fun wput( key : string, deps : string, w : string ) : ()
effect epoch
  fun theme-epoch() : int    // bumps when theme changes

// memo: deps is what the CALLER declares; we auto-salt with the theme epoch
fun memo( key : string, deps : string, build : () -> <wstore,theme,epoch,div> string ) : <wstore,theme,epoch,div> string
  val salted = deps ++ "#e" ++ theme-epoch().show      // <-- the mitigation
  match wget(key)
    Just((cdeps, cw)) | cdeps == salted -> cw
    _ ->
      val w = build()
      wput(key, salted, w)
      w

// memo WITHOUT the salt (the footgun version)
fun memo-naive( key : string, deps : string, build : () -> <wstore,theme,epoch,div> string ) : <wstore,theme,epoch,div> string
  match wget(key)
    Just((cdeps, cw)) | cdeps == deps -> cw
    _ ->
      val w = build()
      wput(key, deps, w)
      w

fun with-wstore( action : () -> <wstore,div|e> a ) : <div|e> a
  var entries : list<(string,(string,string))> := []
  with handler
    fun wget(k)        entries.lookup(fn(kk) kk == k)
    fun wput(k, d, w)  entries := Cons((k, (d, w)), entries.filter(fn(p) p.fst != k))
  action()

fun frame-dark() : <wstore,epoch,console,div> ()
  with val theme = "dark"
  val naive-a = memo-naive("k", "static") fn() "item-" ++ theme
  val salt-a  = memo("k2", "static") fn() "item-" ++ theme
  println("dark  : naive=" ++ naive-a ++ "  salted=" ++ salt-a)

fun frame-light() : <wstore,epoch,console,div> ()
  with val theme = "light"
  val naive-b = memo-naive("k", "static") fn() "item-" ++ theme
  val salt-b  = memo("k2", "static") fn() "item-" ++ theme
  println("light : naive=" ++ naive-b ++ "  salted=" ++ salt-b)
  println("(naive is STALE 'item-dark'; salted rebuilds 'item-light')")

pub fun main()
  var ep := 0
  with fun theme-epoch() ep
  with with-wstore
  frame-dark()
  ep := ep + 1        // theme flip bumps the epoch
  frame-light()
