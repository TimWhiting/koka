
// Complex 6: 3 layers of handlers with mutable state
effect choice
  ctl flip(): bool

effect fail
  ctl fail(): a

fun analyze-complex-layers(): int
  trace("Complex 6 - 3 layers: state, choice, fail")
  var s := 0
  with handler
    ctl flip() 
      s := s + 1
      val r1 : int = resume(True)
      val r2 : int = resume(False)
      r1 + r2
    return(x: int) x
  
  with ctl fail() 0
  
  if flip() then
    if flip() then
      s := s + 10
      1
    else
      fail()
  else
    2
fun result-complex-layers() 3