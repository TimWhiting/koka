// THE CRUX: what does a captured continuation see when resumed after ambient
// state changes?  `effect val` ambients are BAKED INTO the captured evidence
// (resume replays the OLD value); `fun` ops over live handler vars are read
// DYNAMICALLY at resume (the continuation sees the NEW value). The flip
// happens in the handler clause between capture and resume.
module probe4

effect val vtheme : string          // value ambient (baked into evidence)
effect dtheme
  fun dtheme-get() : string         // dynamic ambient (op over live var)
effect suspend
  ctl pause() : ()

fun build() : <suspend,dtheme,console> ()
  with val vtheme = "dark"
  println("build : vtheme=" ++ vtheme ++ " dtheme=" ++ dtheme-get())
  pause()
  // === the continuation resumes HERE, after the theme "changed" ===
  println("resume: vtheme=" ++ vtheme ++ " dtheme=" ++ dtheme-get())

pub fun main()
  var cur := "dark"
  with fun dtheme-get() cur          // dynamic ambient reads `cur` LIVE
  with handler
    raw ctl pause()
      cur := "light"                 // the ambient changes while suspended
      rcontext.resume(())
  build()
