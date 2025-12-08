module state-handler

effect get
  ctl get(): int
effect set
  ctl set(i: int): ()

fun countdown()
  val i = get()
  if i == 0 then i else 
    set(i - 1)
    countdown()

fun analyze-state-countdown(): div int
  trace("Example get/set")
  val x = 2
  with ctl get() resume(x)
  with ctl set(a)
    with override ctl get() resume(a)
    resume(())
  countdown()
fun result-state-countdown() 0

fun test-state-countdown()
  val result = analyze-state-countdown()
  if result == result-state-countdown() then println("✓ test-state-countdown passed")
  else println("✗ test-state-countdown FAILED: expected " ++ result-state-countdown().show ++ ", got " ++ result.show)

fun main()
  println("Running state-handler tests...")
  test-state-countdown()
  println("state-handler tests complete")

