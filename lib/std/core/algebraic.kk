module std/core/algebraic
import std/core/types
import std/core/int
import std/core/list
import std/core/undiv

// A semigroup is a set (type) with an associative operation.
pub value struct semigroup<t>
  associative-op: (t, t) -> t

// Combines two elements using the associative operation.
pub inline fun default/semigroup/(++)(x: t, y: t, .?semigroup: semigroup<t>) : t
  associative-op.(x, y)
// Combines two elements using the associative operation.
pub inline fun default/semigroup/combine(x: t, y: t, .?semigroup: semigroup<t>) : t
  associative-op.(x, y)
// Repeats the associative operation `n` times on `x` with itself
pub inline fun default/semigroup/repeat(x: t, n: int, .?semigroup: semigroup<t>) : t
  if n == 0 then x 
  else x ++ x.pretend-decreasing.repeat(n - 1)
// Concatenates a list of elements using the semigroup operation.
// This does a `foldl` with the accumulated list on the left of the semigroup operation. 
// This may or may not be most efficient depending on the semigroup operation.
pub inline fun default/semigroup/concat(xs: list<t>, .?semigroup: semigroup<t>) : maybe<t>
  match xs
    Nil -> Nothing
    Cons(x, rst) -> Just(rst.foldl(x, fn(acc, v) acc ++ v))
// Joins a list of elements interspersed with `y` using the semigroup operation.
// This does a `foldl` with the accumulated list on the left of the semigroup operation. 
// This may or may not be most efficient depending on the semigroup operation.
pub inline fun default/semigroup/join(xs: list<t>, y: t, .?semigroup: semigroup<t>) : maybe<t>
  match xs
    Nil -> Nothing
    Cons(x, rst) -> Just(rst.foldl(x, fn(acc, v) acc ++ y ++ v))
// Reverse the order of the semigroup operation.
pub inline fun default/semigroup/reverse(.?semigroup: semigroup<t>) : semigroup<t>
  Semigroup(fn(x, y) associative-op(y, x))

// A monoid is a semigroup (set with an associative operation) 
//  with the addition of an identity element.
pub value struct monoid<t>
  identity: t
  associative-op: (t, t) -> t

// Cast to a semigroup for basic semigroup operations.
pub inline fun default/monoid/semigroup(.?monoid: monoid<t>): semigroup<t>
  Semigroup(associative-op)

// An alternative name for the monoid's identity element
pub inline fun default/monoid/empty(?monoid: monoid<t>): t
  monoid.identity

// Additive monoids commonly use zero and + as the identity and associative operation.
pub inline fun default/additive/monoid/zero(?additive-monoid: monoid<t>) : t
  additive-monoid.identity
pub inline fun default/additive/monoid/(+)(x: t, y: t, ?additive-monoid: monoid<t>) : t
  additive-monoid.associative-op.(x, y)
pub inline fun default/additive/monoid(?additive-monoid: monoid<t>) : monoid<t>
  additive-monoid

// Multiplicative monoids commonly use one and * as the identity and associative operation.
pub inline fun default/multiplicative/monoid/one(?multiplicative-monoid: monoid<t>) : t
  multiplicative-monoid.identity
pub inline fun default/multiplicative/monoid/(*)(x: t, y: t, ?multiplicative-monoid: monoid<t>) : t
  multiplicative-monoid.associative-op.(x, y)
pub inline fun default/multiplicative/monoid(?multiplicative-monoid: monoid<t>) : monoid<t>
  multiplicative-monoid

// A group is a set (type) with an associative operation, inverse operation and identity element.
pub value struct group<t>
  associative-op: (t, t) -> t
  inverse: t -> t
  identity: t

// Cast to monoid for inherited operations.
pub inline fun default/group/monoid(.?group: group<t>): monoid<t>
  Monoid(identity, associative-op)
// Alternate names for default group operations
pub inline fun default/group/(~)(x: t, .?group: group<t>): t
  inverse(x)
pub inline fun default/group/inverse(x: t, .?group: group<t>): t
  inverse(x)

// Additive groups commonly use zero and + as the identity and associative operation.
pub inline fun default/additive/group/additive-monoid(?additive-group: group<t>) : monoid<t>
  Monoid(additive-group.identity, additive-group.associative-op)
pub inline fun default/additive/group(?additive-group: group<t>) : group<t>
  additive-group

// with the inverse operation being negation `(~)` which we use to define the binary operator subtraction `(-)`
pub inline fun default/additive/group/(-)(x: t, y: t, ?additive-group: group<t>) : t
  additive-group.associative-op.(x, additive-group.inverse.(y))
pub inline fun default/additive/group/(~)(x: t, ?additive-group: group<t>) : t
  additive-group.inverse.(x)


// Multiplicative groups commonly use one and * as the identity and associative operation.
pub inline fun default/multiplicative/group/multiplicative-monoid(?multiplicative-group: group<t>) : monoid<t>
  Monoid(multiplicative-group.identity, multiplicative-group.associative-op)
pub inline fun default/multiplicative/group(?multiplicative-group: group<t>) : group<t>
  multiplicative-group

// with the inverse operation being reciprocation `(~)` which we use to define the binary operator division `(/)`
pub inline fun default/multiplicative/group/(/)(x: t, y: t, ?multiplicative-group: group<t>) : t
  multiplicative-group.associative-op.(x, multiplicative-group.inverse.(y))
pub inline fun default/multiplicative/group/(~)(x: t, ?multiplicative-group: group<t>) : t
  multiplicative-group.inverse.(x)
