import std/os/signal

fun main()
  val n = ref(0)
  println("Running main")
  signal-start-oneshot(sSIGINT) fn() 
    println("Got SIGINT!")
    signal-start(sSIGINT) fn(s)
      println("Got SIGINT! x " ++ (!n).show)
      if !n == 5 then
        s.signal-stop()
        ()
      else
        n := !n + 1
    ()
  ()
