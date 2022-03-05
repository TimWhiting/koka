import std/time
import std/os/process

effect cur_line
  fun setLine(v: int): ()
  fun getLine(): int

effect ehook
  fun hookExists(s: string): bool
  fun setHook(s: string, v: int): ()
  fun getHook(s: string): int

effect scheduler
  ctl taskSleep(ms: duration): ()
  ctl kill(): ()
  fun setBackgroundThread(b: bool): ()

effect width_eff
  val width: int

fun useHook(background: bool, id: string, init: int, h: (int) -> <scheduler|e> ()): <scheduler|e> int
  if hookExists(id) then
    setHook(id, init)
    setBackgroundThread(background)
    val i = getHook(id)
    h(i)
  getHook(id)

fun useBackgroundHook(id: string, init: int, h: (int) -> <scheduler|e> ()): <scheduler|e> int
  useHook(True, id, init, h)

fun animate(from: int, to: int, ms: int): <div, scheduler> ()
  var f := from
  yield()
  while { f < to }
    f := f + 1
    taskSleep(ms.milli-seconds)

fun animateLoop(from: int, to: int, ms: int): <div, scheduler> ()
  var f := from
  yield()
  while { True }
    f := (f + 1) % (to + 1)
    taskSleep(ms.milli-seconds)

fun text(s: string): <io> ()
  s.print

fun space(): <io> ()
  text(" ")

fun newLine(): <scheduler,io> ()
  setLine(getLine() + 1)
  text("\n")

fun progressBar(v: int, w: int): <io> ()
  var s := "["
  if w < 100 then s := s ++ r"\033[0;31m" else s := s ++ r"\033[0;32m"
  repeat(s.count)
    s := s ++ " "
  s.print

fun string(v: maybe<char>): string
  match v
    Nothing -> ""
    Just(c) -> c.show

fun spinner(): <scheduler> ()
  val d = useBackgroundHook("spinner", 0, fn(init) { animateLoop(init, 3, 200) })
  val chars = ['|', '/', '-', '\\']
  val c = chars[d]
  (r"\033[1m" ++ c.string ++ r"\033[22m").print

fun blinkText(s: string): <scheduler> ()
  val d = useBackgroundHook("blinkText", 0, fn(init) { animateLoop(init, 1, 800) })
  if d != 0 then s.print else repeat(s.count) { " ".print }

fun myBar(v: int): <scheduler, width_eff> ()
  progressBar(v, width)
  if (v < 100) then text(" " ++ v.show ++ "%") else text("done")
  newLine()

fun iface(): <scheduler> ()
  with val width = 30
  val a = useHook(False, "progressA", 0, fn(init) { animate(init, 100, 30) })
  val b = useHook(False, "progressB", 0, fn(init) { animate(init, 100, 100) })
  val c = useHook(False, "progressC", 0, fn(init) { animate(init, 100, 60) })
  val d = useHook(False, "progressD", 0, fn(init) { animate(init, 100, 40) })
  val e = useHook(False, "progressE", 0, fn(init) { animate(init, 100, 85) })
  val sum = a + b + c + d + e
  if (sum < 500) then
    spinner()
    space()
  text("progress: ")
  text((sum / 5).show)
  text("%")
  newLine()
  myBar(a)
  myBar(b)
  myBar(c)
  myBar(d)
  myBar(e)
  if (sum < 500) then 
    blinkText("Wait...") 
  else 
    text("ALL DONE!") 
    kill()
// struct thread (res: (int) -> (), wakeAt: instant, background: bool)

struct hook (pub hid: string, value: int)

fun background(t: maybe<pstate<e,a>>): bool
  match t
    Nothing -> False
    Just(th) -> th.background

fun yield()
  taskSleep(zero)

fun update(hooks: list<hook>, id: string, v: int): list<hook>
  match hooks
    Nil -> Nil
    Cons(Hook(hid, old), rest) -> if hid == id then Cons(Hook(hid, v), rest) else Cons(Hook(hid, old), rest.update(id, v))

fun enqueue(queue: list<pstate<e,a>>, t: pstate<e,a>): list<pstate<e,a>>
  match queue
    Nil -> Cons(t, Nil)
    Cons(h, tail) -> if h.wakeAt < t.wakeAt then Cons(h, tail.enqueue(t)) else Cons(t, queue)

fun notNil(l: list<a>): bool
  match l
    Nil -> False
    Cons(_, _) -> True

fun clear(): <cur_line, io> ()
  repeat(getLine())
    r"\033[2K\r\033[1F".print
  r"\033[2K\r".print
  setLine(0)

fun handle_lines(action)
  var lines := 0
  with handler
    fun getLine()
      lines
    fun setLine(v)
      lines := v
  action()

fun handle_hooks(action)
  var hooks := Nil
  with handler
    fun getHook(id)
      match hooks.find(fn(h) { h.hid == id })
        Nothing -> 0
        Just(Hook(_, v)) -> v
    fun setHook(id, v) hooks := hooks.update(id, v)
    fun hookExists(id)
      match hooks.find(fn(h) {h.hid == id})
        Nothing -> False
        Just(_) -> True
  action()

type pstate<e,a>
  Done(result : a)
  Paused(resumption : (int) -> e pstate<e,a>, wakeAt: instant, background: bool)

effect interrupt
  ctl interrupt() : ()

fun reify-process( action : () -> <interrupt|e> a ) : e pstate<e,a> 
  with raw ctl interrupt() Paused( fn() rcontext.resume(()) )
  Done(action())

fun scheduler( pstates : list<pstate<<div|e>,a>> ) : <div|e> list<a>
  fun schedule( todos : list<pstate<<div|e>,a>>, dones : list<a> ) : <div|e> list<a>
    match todos
      Nil -> dones
      Cons(Done(x),pp) -> schedule(pp, Cons(x,dones))
      // Cons(Paused(p),pp) -> 
      //   val ps = forking( p )
      //   schedule( pp ++ ps, dones)
  schedule(pstates,[])

// fun basic_scheduler(action): <div, io> ()
//   with handler
//     raw ctl taskSleep(m)
//       val t = now() + m
//       val b = getThread().background
//       Paused(fn(i) rcontext.resume(()), t, b)
//     ctl kill() ()
//     fun setBackgroundThread(b) ()
//   with handle_lines
//   with handle_hooks
//   setThread(Paused(fn(i){action(); ()}, now(), False))
//   r"\x1B[?25l".print
//   while { ~isEmpty }
//     match (getThread())
//       Just(Thread(_, __, True)) -> ()
//       _ -> ()
//     clear()
//     action()
//     val n = now()
//     match dequeue()
//       Nothing -> ()
//       Thread(res, wakeAt, background) -> 
//         if wakeAt > n then
//           sleep((wakeAt - n).milli-seconds)
//           ()
//         setThread(Thread(res, wakeAt, background))
//         res.resume(())
//         clear()
//         action()
//   r"\x1B[?25h".print

pub fun main(): <io, div> ()
  with basic_scheduler
  iface()