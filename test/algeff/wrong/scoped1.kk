//------------------------------------------------
// The choices handler is wrongly typed
// since it doesn't issue a 'resume'
//------------------------------------------------

effect nondet {
  ctl choice(xs : list<a>) : a;
}

fun fail() {
  choice([])
}

fun knapsack(w : int, vs : list<int> ) : <nondet,div> list<int> {
  if (w < 0) then fail()
  elif (w == 0) then []
  else {
    val v = choice(vs)
    Cons(v,knapsack(w - v, vs))
  }
}

val solutions = handler {
  return(x)  -> [x]
  ctl choice(xs) -> xs.flatmap(resume)
}

fun test1() {
  solutions{ knapsack(3,[3,2,1]) }
}


effect state<s> {
  fun get()    : s
  fun put(i:s) : ()
}

fun state(init,action)
  var s := init
  handle(action)
    fun get()  { s }
    fun put(x) { s := x }


fun incr(i = 1) : state<int> () {
  put(get()+i)
}

fun local(s,action) {
  solutions{ state(s,action) }
}

fun global(s,action) {
  state(s){ solutions(action) }
}





val choices = handler {
  ctl choice(xs) {
    incr(xs.length)
    // resume(choice(xs))
    choice(xs)
  }
}

fun intlist/show(sxss : (int,list<list<int>>)) : string {
  "(state=" + sxss.fst.show + ", " + sxss.snd.show + ")"
}

fun test2() {
  global(0){ choices{ knapsack(3,[3,2,1]) }}
}