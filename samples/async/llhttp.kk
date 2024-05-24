import llhttp/llhttp
import std/num/int32
import uv/event-loop

fun main()
  val p = http-req-parser()
  p.add-string("GET / HTTP/1.1\r\nHost: example.com\r\n\r\n")
  p.get-result().println


