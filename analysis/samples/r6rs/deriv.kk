// DERIV -- Symbolic derivation.

// Returns the wrong answer for quotients.
// Fortunately these aren't used in the benchmark.

type ast
  List(l: list<ast>)
  Sym(a: char)
  Num(i: int)
  Err(s: string)

fun map2(ls: list<a>, f: (a) -> e b): e list<b>
  match ls
    Nil -> Nil
    Cons(x, xs) -> Cons(f(x), xs.map2(f))

fun map(a: ast, f: ast -> e ast): e ast
  match a
    List(a') -> List(a'.map(f))
    Sym(a') -> Sym(a')
    Num(i) -> Num(i)
    Err(s) -> Err(s)

fun deriv(a: ast): div ast
  match a
    Sym('x') -> Num(1)
    Sym(_) -> Num(0)
    Num(_) -> Num(0)
    List(Cons(Sym('+'), a2)) ->
      List(Cons(Sym('+'), a2.map2(deriv)))
    List(Cons(Sym('-'), a2)) ->
      List(Cons(Sym('-'), a2.map2(deriv)))
    List(Cons(Sym('*'), a2)) ->
      List([Sym('*'), a, List(Cons(Sym('+'), a2.map2(fn(a') List([Sym('/'), a'.deriv, a']))))])
    List(Cons(Sym('/'), Cons(a1, Cons(a2, Nil)))) ->
      List([Sym('-'), List([Sym('/'), a1.deriv, a2]), List([Sym('/'), a1, List([Sym('*'), a2, a2, a2.deriv])])])
    _ -> Err("No derivation method available")

fun ast/show(a: ast): div string
  match a
    List(a') -> 
      val res = a'.map2(show)
      "List" // "(" ++ .join(" ") ++ ")"
    Sym(a') -> "'" ++ a'.show-char
    Num(i) -> i.show
    Err(s) -> "ERR: " ++ s

fun analyze()
  val eq = List([Sym('+'), List([Sym('*'), Num(3), Sym('x'), Sym('x')]), List([Sym('*'), Sym('a'), Sym('x'), Sym('x')]), List([Sym('*'), Sym('b'), Sym('x')]), Num(5)])        
  eq.deriv

fun main()
  val eq = List([Sym('+'), List([Sym('*'), Num(3), Sym('x'), Sym('x')]), List([Sym('*'), Sym('a'), Sym('x'), Sym('x')]), List([Sym('*'), Sym('b'), Sym('x')]), Num(5)])        
  val d = eq.deriv
  println(d.show)