import samples/basic/list

type hello
  Hello

type even<t>
  Even(o1: odd<t>)
  Zero(t: t)

type odd<t>
  Odd(o1: even<t>)

type vvalue
  IntV(i: int)
  BoolV(b: bool)
  CharV(c: char)
  StringV(s: string)

alias primop = (vvalue) -> <console,pure> vvalue

type expr
  Int(i: int)
  Bool(b: bool)
  Char(c: char)
  String(s: string)
  Var(s: string)
  Lam(x: string, y: expr)
  // App(op: expr, args: list<expr>)
  PrimOp(name: string, prim: primop)

fun printPrim(v: vvalue): console vvalue
  v.show.println
  v

fun main() 
  Hello.show.println
  Even(Odd(Zero(0))).show(show).println
  val x = Lam("x", Var("x"))
  val y = PrimOp("print", printPrim)
  // val y = App(x, Char('a'))
  (==)(x,y).show.println
  (==)(x,x).show.println
  x.show.println
  y.show.println
