type expr0
  Val0(i: int)
  Add0(e1: expr0, e2: expr0)

fun e0/eval(e: expr0): int
  match e
    Val0(i) -> i
    Add0(x, y) -> eval(x) + eval(y)

fun e0/render(e: expr0): string
  match e
    Val0(i) -> i.show
    Add0(x, y) -> "(" ++ render(x) ++ " + " ++ render(y) ++ ")"

type expr1<f>
  In(expr: f<expr1<f>>)

struct val1<e>
  x: int

alias intexpr = expr1<val1>;

value struct add1<e>
  x: e
  y: e

alias addexpr = expr1<add1>;

value type sum<f,g,a>
  Inl(l: f<a>)
  Inr(r: g<a>)

pub type odd
pub type even

fun val1/map<a,b>(e: val1<a>, f: (a) -> div b): div val1<b>
  match e
    Val1(e') -> Val1(e')

fun add1/map<a,b>(e: add1<a>, f: (a) -> div b): div add1<b>
  Add1(f(e.x), f(e.y))

fun sum/map(e: sum<f,g,a>, f: (a) -> div b, ?l/map: forall<a1,b1> (f<a1>, a1 -> div b1) -> div f<b1>, ?r/map: forall<a2,b2> (g<a2>, a2 -> div b2) -> div g<b2>): div sum<f,g,b>
  match e
    Inl(x) -> Inl(l/map(x, f))
    Inr(x) -> Inr(r/map(x, f))

fun expr1/fold(e:expr1<f>, f1: f<a> -> div a, ?map: forall<b,c> (f<b>, b -> div c) -> div f<c>): div a
  match e
    In(x) -> f1(?map(x, fn(x') expr1/fold(x', f1)))

fun val1/eval(v: val1<int>): div int
  v.x

fun add1/eval(a: add1<int>): div int
  a.x + a.y

fun sum/eval(s: sum<f,g,int>, ?f/eval: (f<int> -> div int), ?g/eval: (g<int> -> div int)): div int
  match s
    Inl(x) -> f/eval(x)
    Inr(x) -> g/eval(x)

val addExample = In(Inr(Add1(In(Inl(Val1(118))), In(Inl(Val1(1219))))))

fun doEval/runEval(e: expr1<f>, ?eval: f<int> -> div int, ?map: forall<b,c> (f<b>, (b -> div c)) -> div f<c>): div int
  expr1/fold(e, ?eval, ?map=?map)

fun test()
  val res = doEval/runEval(addExample, ?map=fn(a, b) sum/map(a,b))
  res.show.println

fun val1(x : int, ?inj : (val1<a>) -> e sum<f,g,expr1<sum<f,g>>>): e expr1<sum<f,g>>
  In(?inj(Val1(x)))

fun add1(x : a, y : a, ?inj : (add1<a>) -> e sum<f,g,expr1<sum<f,g>>>): e expr1<sum<f,g>>
  In(?inj(Add1(x, y)))

fun inl/inj(x, ?inj1)
  Inl(?inj1(x))

fun inl/inj1(x, ?inj1)
  Inl(?inj1(x))

fun inr/inj(x)
  Inr(x)

fun inr/inj1(x, ?inj1)
  Inr(?inj1(x))

fun idx/inj1(x)
  x

val addExample2 = val1(30000).add1(val1(1330)).add1(val1(7))

fun test2()
  val res = doEval/runEval(addExample2, ?map=fn(a, b) sum/map(a,b))
  res.show.println

value struct mul1<e>
  x: e
  y: e

alias mulexpr = expr1<mul1>;

fun mul1/map<a,b>(e: mul1<a>, f: (a) -> div b): div mul1<b>
  Mul1(f(e.x), f(e.y))

fun mul1/eval(a: mul1<int>): div int
  a.x * a.y

fun mul1(x: a, y: a, ?inj : (mul1<a>) -> e sum<f,g,expr1<sum<f,g>>>): e expr1<sum<f,g>>
  In(inj(Mul1(x, y)))

// fun test3()
  // val justMul = mul1(val1(80), val1(5))
  // val val0 = val1(4)
  // val mulExample = add1(val0, justMul)
  // val mulExample = In(Inl(Add1(In(Inr(In(Inl(Val1(4))))), In(Inr(Mul1(In(Inl(Val1(80))), In(Inl(Val1(5)))))))))
  // val res = doEval/runEval(mulExample, ?map=fn(a, b) sum/map(a,b))
  // res.show.println