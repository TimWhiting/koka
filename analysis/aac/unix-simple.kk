
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

effect fork
  ctl fork() : bool     // true if this is the parent

fun forking( action : () -> <fork|e> a ) : e list<a>
  with handler
    return(x) [x]
    ctl fork() resume(True) ++ resume(False)
  action()

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
  with return(x:(list<()>, string)) x.snd
  with bio
  with forking
  if fork() then
    ritchie()
  else
    hamlet()
pub fun example5()
  analyze-example5().println
fun result-example5()
  r"UNIX is basically a simple operating system, but you have to be a genius to understand the simplicity.
To be, or not to be, that is the question:
Whether 'tis nobler in the mind to suffer"
