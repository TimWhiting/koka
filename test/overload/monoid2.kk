import std/num/float64

value struct monoid<a>
  mzero : a
  mplus : (a,a) -> a

fun zero( .?monoid : monoid<a> ) : a
  mzero

fun plus( x : a, y : a, .?monoid : monoid<a> ) : a
  mplus(x,y)


val intplus/monoid = Monoid(0,(+))
val intmul/monoid  = Monoid(1,(*))
val float/monoid   = Monoid(0.0,(+))

fun msum( xs, ?monoid )
  xs.foldl(zero(),plus) // fn(x,y) plus(x,y))
  // note1: zero is a function now..
  // note2: we need to eta expand `plus` to match the type `(a,a,?monoid:monoid<a>) -> a` to `(a,a) -> a`
  // maybe we can do this kind of conversion automatically in the compiler?

fun msum-expand( xs, .?monoid )
  xs.foldl(mzero,mplus)
  // note: with auto expansion, to:  match monoid
  //                                   Monoid(mzero,mplus) -> xs.foldl(mzero,mplus)
  // no eta expansion is needed anymore and mzero is a value.

fun list/monoid( ?monoid : monoid<a>)  : monoid<list<a>>
  Monoid([zero()], fn(xs,ys) zipwith(xs,ys,plus)) //fn(x,y) plus(x,y)))  // again eta expansion

fun monoid-expand( .?monoid )
  Monoid([mzero],fn(xs,ys) zipwith(xs,ys,mplus))


fun test1()
  [1.0,2.0].msum

fun test2()
  [[1.0],[2.0]].msum.msum

fun main()
  test1().println