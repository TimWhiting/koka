value struct subtype<s0,s1>
  inj: s0 -> s1 // injection
  prj: s1 -> maybe<s0> // projection

value type or<a,b>
  L(a:a)
  R(b:b)

val or/subtype = Subtype(fn(a) L(a), fn(b) match b {L(x) -> Just(x); _ -> Nothing})

fun convert/subtype(.?subtype: subtype<a,b>): subtype<a,or<c,b>>
  Subtype(fn(a) R(inj(a)), fn(b) match b {R(a) -> prj(a); _ -> Nothing})

alias value = or<int, or<func, ()>>;
alias term = or<terma, ()> // , or<termf, or<termr, or<terml, or<termt, or<termc, termn>>>>>>;

type terma
  Num(i: int)
  Add(l: term, r: term)

div type func
  Funct(f: some<e> interpm<value> -> e interpm<value>)

struct interpm<t>
  interp: some<e> t -> e interpm<t>

fun main()
  val x: or<int,or<string,()>> = (or/subtype.inj)(1)  // using or<int,or<func,()>> gives weird errors
  x.show.println

fun test1( x : or<int,()> )
  x.show

fun test1a( x : or<int,()> )
  x.show(?b/show=unit/show)

fun test2( x : or<int,or<string,()>> )
  x.show


fun or/show(or: or<a,b>, ?a/show: a -> string, ?b/show: b -> string): string
  match or
    L(a) -> show(a)
    R(b) -> show(b)

