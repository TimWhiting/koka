fun error/(*)(i: int, f: (int) -> int): console ()
  println("error")
fun error/map(l: list<a>, b: ()): console ()
  println("error")
fun regular/plus(x: int, y: int): int
  x + y
fun error/plus(x: (int) -> int, y: b): int
  9

fun main()
  [1, 2, 3].map(_ + 1).println
  [1, 2, 3].dupmap(_ * _).println
  // [0, 1, 2].println(?show=list/show(_, ?show=int/show(_)))
 
  [1,2].map( 3 + _ ).println  //  => [1,2].map( fn(x) 3 + x ) or
                       //   fn(x) [1,2].map( 3 + x )
  [1,2].map( (+)(3,_) ).println // => [1,2].map( fn(x) (+)(3,x) ) or
                        //    fn(x) [1,2].map( 3 + x )
  [1,2].map( inc(_) ).println  //   [1,2].map( inc(fn(x) x) )  or  
                     // => [1,2].map( fn(x) inc(x) )  or
  [1,2].map( _.inc ).println   //   [1,2].map( inc(fn(x) x) )  or  
                     // => [1,2].map( fn(x) x.inc )  or  
                     //     [1,2].(fn(x) map( inc(x) ))  or
                     //     fn(x) [1,2].map( inc(x) )  or

  [1,2].map( 2 + _.inc).println //            [1,2].map( 2 + (fn(x) x).inc) or 
                       //           [1,2].map( 2 + fn(x) x.inc ) or 
                      //          => [1,2].map( fn(x) 2 + x.inc)  or 
                      //            fn(x) [1,2].map( 2 + x.inc)

  [1,2].map((*)(2,_.inc))//   => [1,2].map( (+)(2,fn(x) x.inc) )
                          //    [1,2].map( fn(x) (+)(2,x.inc) )
  [1,2].map( 2 + inc(_)).println  //    [1,2].map( 2 + (fn(x) x).inc) or 
                          //    [1,2].map( 2 + fn(x) x.inc ) or 
                         // => [1,2].map( fn(x) 2 + x.inc)  or 
                         //     fn(x) [1,2].map( 2 + x.inc)         
  [1, 2].dupmap(_.inc.plus(_)).println  // ~> fn(x,y) x.inc.plus(y)
  //===>                    !=
  [1, 2].map(plus(inc(_),_)).println // ~> fn(y) plus(fn(x) inc(x),y)
  

fun dupmap(l : list<a>, f: (a, a) -> b): list<b>
  match l
    Cons(h, t) -> Cons(f(h, h), dupmap(t, f))
    Nil -> Nil