effect yield<a>
  ctl yield(r: a): ()

effect await<a>
  ctl await(): a

fun pipe(p: () -> <div,yield<b>> a, c: () -> <div,await<b>> a): div a
  handle(c)
    raw ctl await()
      copipe(fn(x) rcontext.resume-shallow(x), p)

fun copipe(c: (b) -> <div,await<b>> a, p: () -> <div,yield<b>> a): div a
  handle(p)
    raw ctl yield(p1)
      pipe(fn() rcontext.resume-shallow(()), fn() c(p1))

fun produce(i: int)
  if i == 0 then
    return i 
  yield(i)
  produce(i - 1)

fun consume()
  val x: int = await()
  trace(x.show ++ "\n")
  consume()
  x

fun main()
  val x = pipe(fn() produce(10), consume)
  println(x)