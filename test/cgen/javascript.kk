module javascript

fun prematureReturn(xs: list<int>): bool {
  val x = match(xs) {
    Nil       -> return True // returning bool here..
    Cons(x,_) -> x           // while `x` is an `int`!
  }
  if(x == 0) then True else False
}

fun deepPatternMatching(xs : list<int>) : exn int {
  match(xs) {
    Nil -> 1
    Cons(_,Nil) -> 2
    Cons(_,Cons(_,Nil)) -> 3
    Cons(_,Cons(_,Cons(_,Nil))) -> 4
    Cons(_,Cons(_,Cons(_,Cons(_,Nil)))) -> 5
  }
}

fun last2(xs : list<a>) : exn a {
  match(xs) {
    Cons(x,Nil) -> x
    Cons(_,zs)  -> last2(zs)
  }
}

fun main() {
  print(show(deepPatternMatching([1,2])))
}

/* optimizations to do: tco
   desired output:

    fun last2(xs) /* forall<a> (xs : list<a>) -> exn a */
    { tailcall: for(;;) {
      if(xs != null /* asCons */ && xs.tail == null /* singleton */ ) {
        return xs.head
      }
      if(xs != null /* asCons */) {
        var zs = xs.tail;
        {
          xs = zs;
          continue tailcall;
        }
      }
      return system_core.patternMatchError("test\u005Ccodegen\u005Cjavascript.kk(4, 3)","last2");;
    }}
*/

fun inlineConditional1(x : bool) : int {
  if(x) then 0 else 1
}

/* optimizations to do: inline with conditional expression
   desired output:

   var inlineConditional1 = fn(x) {
     return x?0:1;
   };
*/

fun dontCheckLastCase(x: list<int>) : int {
  match(x) {
    Cons(_, _) -> 0
    Nil        -> 1
  }
}

/* optimizations to do: don't pattern match in last case, since core guarantees full coverage
   desired output:

    var dontCheckLastCase = fn(x /* system_core._list<int> */) {
      if(x[0] === 2) {
        return 0;
      }
      return 1;
    };
*/

value struct person(age: int, name: string)

fun matchOnStruct(person: person) : int {
  match(person)
  { Person(age, _) -> age
    _              -> 7
  }
}

/* optimizations to do: don't pattern match in last case, since core guarantees full coverage
   desired output:

    fun matchOnStruct(person) /* (person : person) -> int */
    {
      return person.age
    }
*/


fun tcoWhile( predicate : () -> <div|e> bool, action : () -> <div|e> () ) : <div|e> ()
{
  if (predicate()) then {
    action()
    tcoWhile(predicate, action)
  }
}

fun foo( i : int ) {
  if (i < 0) then return Lt
  elif (i > 0) then return Gt
  else Eq
}

fun foo2( i : int ) {
  if (i < 0) then return Lt
  elif (i > 0) then return Gt
  else return Eq
}

fun foo3( i : int ) {
  if (i < 0) then  Lt
  elif (i > 0) then  Gt
  else Eq
}

/* optimizations to do: tco
   desired output:

    { tailcall: for(;;) {
      if(predicate()) {
        action();;
        {
          predicate = predicate;
          action = action;
          continue tailcall;
        }
      } else {
        return system_core.__0unit_;;
      };
    }}

*/