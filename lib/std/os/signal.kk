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
  signal.with-ptr fn(s: uv-signal-sp)
    uv-loop().uv-signal-init(s.ptr)
    s.set-cb
      signal.keepalive(); 
      cb()
      s.close()
    s.ffi/uv-signal-start-oneshot(unit-cb, signum)

pub fun signal-start(signum: int, cb: uv-cb1<uv-signal-sc>): io-event int
  val signal = uv-signal-sc();
  signal.with-ptr fn(s: uv-signal-sp)
    uv-loop().uv-signal-init(s.ptr)
    s.set-cb
      cb(signal)
    s.ffi/uv-signal-start(unit-cb, signum)

pub fun signal-stop(sig: uv-signal-sc): io-event ()
  sig.with-ptr fn(s: uv-signal-sp)
    s.ffi/uv-signal-stop()
    s.a/get-cb()
    sig.consume()