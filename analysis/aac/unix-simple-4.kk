
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

pub fun analyze-example4()
  with bio
  with status
  with session-manager3(Root)
  echo("hi ")
  echo(whoami())
  su(Alice)
  echo(", and hi ")
  echo(whoami())
fun result-example4() : (int,string)
  (0, "hi root, and hi alice")
