import std/os/uv/tty
import std/os/uv/stream
import std/num/int32

fun main()
  val uv = uv-tty-init(0.int32).untry
  uv.stream.try-write(["Hello, world!\n".bytes])
  val size = uv.uv-tty-get-winsize().untry
  println("Window size is " ++ size.show)