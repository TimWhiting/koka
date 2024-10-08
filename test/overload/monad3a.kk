// monads as implicit parameters
// use .? to unpack pure and bind

struct monad<m>
  pure : forall<a> a -> m<a>
  bind : forall<a,b> (m<a>, a -> m<b>) -> m<b>

struct monadplus<m>
  xmonad : monad<m>
  plus   : forall<a> (m<a>,m<a>) -> m<a>

// sequence a list of actions
fun sequence( ms, .?monad )
  match ms
    Nil -> pure([])
    Cons(m,mm) ->
      with x  <- bind(m)
      with xx <- bind(sequence(mm))
      pure(Cons(x,xx))

val list/monad  = Monad( fn(x) [x], fn(m,f) m.flatmap(f) )
val maybe/monad = Monad( fn(x) Just(x), fn(m,f) match m { Just(x) -> f(x); _ -> Nothing } )

val list/monadplus  = Monadplus( list/monad, (++) )
val maybe/monadplus = Monadplus( maybe/monad, fn(m1,m2) match m1
                                                          Nothing -> m2
                                                          Just    -> m1
                               )

fun monadplus/monad( .?monadplus : monadplus<m> ) : monad<m>
  xmonad


fun mbind( m, f, .?monad )
  bind(m,f)

fun mpure( x : a, .?monad : monad<m> ) : m<a>
  pure(x)

fun testtwice<m,a>( m : m<a>, .?monadplus : monadplus<m> ) : m<list<a>>
  // works because `?monad` gets resolved to `monad_monadplus(monadplus)` for `mbind/mpure`
  with x <- mbind(plus(m,m))
  mpure([x])

// exceptions
fun test1()
  match [Just(1), Just(2)].sequence // resolves to `(?monad=monad_maybe)` as `monad_monadplus(monadplus_maybe)` is longer
    Just(xs) -> xs.show
    Nothing  -> "Nothing"

// list of successes
fun test2()
  [[1],[2,3],[4,5,6]].sequence.show

fun test3()
  [[1],[2,3]].testtwice.concat.sequence.show