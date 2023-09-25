module nqueens
// import std/num/int32

alias solution = list<int8>
alias solutions = list<list<int8>>

fun safe( queen : int8, diag : int8, ^xs : solution ) : bool 
  match xs
    Cons(q,qs) -> (queen != q && queen != (q+diag) && queen != (q - diag) && safe(queen,diag.inc,qs))
    _          -> True

fun append-safe( queen : int8, xs : solution, xss : solutions ) : div solutions 
  if queen <= 0.int8 then xss
  elif safe(queen,1.int8,xs) then append-safe( queen.dec, xs, Cons(Cons(queen,xs),xss) )
  else append-safe( queen.dec, xs, xss )

fun extend( queen : int8, acc : solutions, xss : solutions ) : div solutions
  match xss 
    Cons(xs,rest) -> extend(queen, append-safe(queen,xs,acc), rest)
    Nil           -> acc

fun find-solutions( n : int8, queen : int8 ) : div solutions
  if queen.is-zero
   then [[]]
   else extend(n, [], find-solutions(n,queen.dec))

pub fun queens( n : int8 ) : div int
  find-solutions(n,n).length

pub fun main()
  queens(13.int8).println

