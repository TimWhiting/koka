// probe: open a titled window from the render side, verify it comes alive, close it
module winprobe
import std/async
import ui/api/impeller/impeller
pub fun main()
  init("winprobe", 320, 200)
  val w = open-window(0, "probe", 240.0, 160.0)
  var tries := 0
  while { !window-alive(w) && tries < 100 }
    poll-events()
    tries := tries + 1
  println(if window-alive(w) then "alive" else "DEAD")
  close-window(w)
  poll-events()
  println(if window-alive(w) then "STILL-ALIVE" else "closed")
  val p = open-window(1, "panel", 160.0, 120.0)
  set-window-pos(p, 100.0, 100.0)
  var ptries := 0
  while { !window-alive(p) && ptries < 100 }
    poll-events()
    ptries := ptries + 1
  println(if window-alive(p) then "alive" else "DEAD")
  close-window(p)
  poll-events()
  println(if window-alive(p) then "STILL-ALIVE" else "closed")
