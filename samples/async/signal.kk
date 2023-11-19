import std/os/signal

fun main()
  println("Running main")
  signal-start-oneshot(sSIGINT, fn() println("Escape!"))
