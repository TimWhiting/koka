effect ctl myeffect() : ()

fun main() : <console> ()
  with top-protect
  with ctl myeffect()
    ()
  with ctl myeffect()
    myeffect()
  with finally
    println("cleanup")
  myeffect()
