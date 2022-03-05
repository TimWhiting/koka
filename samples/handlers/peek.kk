effect val peek : int             // get the state
effect ctl poke( x : int ) : ()   // set the state to x

fun ppstate( init : int, action : () -> <peek,poke|e> b ) : e b
  with val peek = init
  with ctl poke(x)
    mask<peek>
      with val peek = x
      resume(())
  action()

fun main()
  with ppstate(0)
  poke(1)
  peek.println