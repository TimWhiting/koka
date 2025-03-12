// Lazy constructor evaluation

// TODO: Improve visualization of constructor results

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

fun map3(ls: list<a>, f: (a) -> e b): e list<b>
  match ls
    Nil -> Nil
    Cons(x, xs) -> Cons(f(x), xs.map3(f))

fun ast/show(a: ast): div string
  match a
    List(a') -> 
      val res = a'.map3(show)
      "List(" ++ res.join(" ") ++ ")"
    Sym(a') -> "'" ++ a'.show-char
    Num(i) -> i.show
    Err(s) -> "ERR: " ++ s

fun main()
  val eq = List([Sym('*'), Num(3), Sym('x'), Sym('x')]) 
  val d = eq.deriv
  println(d.show)