
// basic I/O
effect bio
  // Write a string to a file descriptor
  fun write( fd : filedesc, s : string ) : ()

alias filedesc = int

val stdout = 0

fun echo( s : string ) : bio ()
  write(stdout,s)

fun bio( action1 : () -> <bio|e> a) : e (a,string)
  var buf := ""
  with fun write(fd,s) buf := buf ++ s
  (action1(),buf)

effect exit
  ctl exit( exitcode : int ) : a

fun status( action3 : () -> <exit|e> a ) : e int
  with final ctl exit(code) code                    // use `final` since we never resume
  action3()
  0

type user
  Root
  Alice
  Bob

fun user/show( user : user ) : string
  match user
    Root  -> "root"
    Alice -> "alice"
    Bob   -> "bob"

effect whoami
  fun whoami() : string
effect su
  ctl su( u : user ) : ()

fun session-manager3( initial-user : user, action6 : () -> <su,whoami|e> a ) : e a
  var user := initial-user
  with fun whoami() show(user)
  with fun su(u) user := u
  action6()

effect fork
  ctl fork() : bool     // true if this is the parent

fun forking( action : () -> <fork|e> a ) : e list<a>
  with handler
    return(x) [x]
    ctl fork() resume(True) ++ resume(False)
  action()


type pstate<e,a>
  Done(result : a)
  Paused(resumption : () -> e pstate<e,a> )

effect interrupt
  ctl interrupt() : ()

fun reify-process( action : () -> <interrupt|e> a ) : e pstate<e,a>
  with raw ctl interrupt() Paused( fn() rcontext.resume(()) )        // `raw` to have the resume outlive its lexical scope (otherwise finalizers are run automatically)
  Done(action())

fun scheduler( pstates : list<pstate<<fork,div|e>,a>> ) : <div|e> list<a>
  fun schedule( todos : list<pstate<<fork,div|e>,a>>, dones : list<a> ) : <div|e> list<a>
    match todos
      Nil -> dones
      Cons(Done(x),pp) -> schedule(pp, Cons(x,dones))
      Cons(Paused(p),pp) ->
        val ps = forking( p )
        schedule( pp ++ ps, dones )
  schedule(pstates,[])

fun timeshare( action : () -> <fork,interrupt,div|e> a ) : <div|e> list<a>
  val p = Paused( fn() reify-process(action) )
  scheduler([p])

fun ritchie() : <bio|e> ()
  echo("UNIX is basically ")
  echo("a simple operating system, ")
  echo("but ")
  echo("you have to be a genius to understand the simplicity.\n")

fun hamlet() : <bio|e> ()
  echo("To be, or not to be, ")
  echo("that is the question:\n")
  echo("Whether 'tis nobler in the mind to suffer\n")

pub fun analyze-example5()
  with return(x:(list<int>,string)) x.snd
  with bio
  with timeshare
  with status
  with session-manager3(Root)
  if fork() then
    su(Alice)
    ritchie()
  else
    su(Bob)
    hamlet()
pub fun example5()
  analyze-example5().println
fun result-example5()
  r"UNIX is basically a simple operating system, but you have to be a genius to understand the simplicity.
To be, or not to be, that is the question:
Whether 'tis nobler in the mind to suffer
"

