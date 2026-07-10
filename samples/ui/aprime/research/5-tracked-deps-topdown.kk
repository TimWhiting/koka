// A-prime mechanics end-to-end: AUTO-tracked dependencies through dynamic
// ambient ops + TOP-DOWN dirty-checked memo. The store records which memo
// identity reads which cell during build; a cell write dirties exactly its
// readers; the next frame's view pass re-runs ONLY dirty builders -- and
// because re-run happens top-down INSIDE the view call tree, a USER's
// mid-tree `with val` handler is freshly re-installed around the re-run
// (the thing frozen continuations get wrong).
module probe5

effect store
  fun cell-read( id : int ) : int             // tracked read
  fun cell-write( id : int, v : int ) : ()    // dirties readers
  fun memo-enter( key : string ) : bool       // True = dirty, must rebuild
  fun memo-exit( key : string, w : string ) : ()
  fun memo-cached( key : string ) : string

effect val user-env : string                  // a USER ambient (mid-tree, arbitrary)

fun with-store( action : () -> <store,div|e> a ) : <div|e> a
  var cells   : list<(int,int)>       := []   // (id, value)
  var deps    : list<(int,string)>    := []   // (cell-id, memo-key) read edges
  var dirty   : list<string>          := []   // memo keys needing rebuild
  var cache   : list<(string,string)> := []   // (memo-key, built)
  var current : list<string>          := []   // stack of memo keys being built
  with handler
    fun cell-read(id)
      match current
        Cons(k, _) -> if !deps.any(fn(d) d.fst == id && d.snd == k) then deps := Cons((id, k), deps)
        Nil -> ()
      cells.lookup(fn(i) i == id).default(0)
    fun cell-write(id, v)
      cells := Cons((id, v), cells.filter(fn(p) p.fst != id))
      val readers = deps.filter(fn(d) d.fst == id).map(snd)
      dirty := readers ++ dirty
    fun memo-enter(k)
      val is-dirty = dirty.any(fn(d) d == k) || !cache.any(fn(c) c.fst == k)
      if is-dirty then
        deps := deps.filter(fn(d) d.snd != k)   // re-tracking: drop old edges
        current := Cons(k, current)
      is-dirty
    fun memo-exit(k, w)
      cache := Cons((k, w), cache.filter(fn(c) c.fst != k))
      dirty := dirty.filter(fn(d) d != k)
      current := current.drop(1)
    fun memo-cached(k)
      cache.lookup(fn(c) c == k).default("?")
  action()

fun memo( key : string, build : () -> <store,console,div|e> string ) : <store,console,div|e> string
  if memo-enter(key) then
    val w = build()
    memo-exit(key, w)
    println("  [rebuilt " ++ key ++ " -> " ++ w ++ "]")
    w
  else memo-cached(key)

// the view: TOP-DOWN every frame; user installs a mid-tree ambient; builders
// read cells through tracked ops
fun view( frame-env : string ) : <store,console,div> string
  with val user-env = frame-env             // USER mid-tree handler, fresh each pass
  val a = memo("A") fn()
    "A(c0=" ++ cell-read(0).show ++ ",env=" ++ user-env ++ ")"
  val b = memo("B") fn()
    "B(c1=" ++ cell-read(1).show ++ ")"
  a ++ " | " ++ b

pub fun main()
  with with-store
  println("frame 1 (both build):")
  println(view("env-v1"))
  println("frame 2 (nothing changed -> no rebuilds):")
  println(view("env-v1"))
  cell-write(1, 42)
  println("frame 3 (cell 1 changed -> ONLY B rebuilds):")
  println(view("env-v1"))
  cell-write(0, 7)
  println("frame 4 (cell 0 changed AND user env changed -> A rebuilds UNDER THE NEW ENV):")
  println(view("env-v2"))
