pub import std/os/uv/generated
import std/core/cextern
import std/num/int32
import std/os/uv/utils

pub val sSIGINT = sigint().int
extern sigint(): int32
  c inline "SIGINT"

pub inline fun signal/uv-handle(p: uv-signal-sp): uv-handle-sp
  p.cptr-cast()

pub fun signal-start-oneshot(signum: int, cb: uv-unit-cb): io-event int
  val signal = uv-signal-sc();
  signal.retain()
  signal.with-ptr fn(s: uv-signal-sp)
    uv-loop().uv-signal-init(s.ptr)
    s.set-cb
      s.close()
      signal.keepalive(); // Keep the signal memory allocated at least until after the callback is called
      cb()
    s.ffi/uv-signal-start-oneshot(unit-cb, signum)

pub fun signal-start(signum: int, cb: uv-cb1<uv-signal-sc>): io-event int
  val signal = uv-signal-sc();
  signal.with-ptr fn(s: uv-signal-sp)
    uv-loop().uv-signal-init(s.ptr)
    val c = fn()
          fndup() // Ensure the callback can be called multiple times
          cb.fndup()
          signal.retain()
          cb(signal)
          signal.keepalive() // Retain the signal memory allocated at least until after the next callback is called
    c.fndup() // Ensure the callback isn't immediately freed on first callback
    s.set-cb(c)
    s.ffi/uv-signal-start(unit-cb, signum)

pub fun signal-stop(sig: uv-signal-sc): io-event ()
  sig.with-ptr fn(s: uv-signal-sp)
    s.ffi/uv-signal-stop()
    s.a/get-cb()
    sig.release() // Add another decref to offset the retains for the callbacks