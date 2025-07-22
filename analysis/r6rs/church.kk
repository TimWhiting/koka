// Can't seem to get the types to work here
// alias church = church -> div church

// fun plus(p1: church, p2: church): div church
//   fn(pf: church): div church
//     fn(x: church): div church
//       p1(pf)(p2(pf)(x))

// fun mult(m1, m2)
//   fn(mf)
//     m2(m1(mf))

// fun idchurch(x: church): div church
//   x

// fun pred(n: church): div church
//   fn(rf: church): div church
//     fn(rx: church): div church
//       n(fn(g: church) fn(h: church) h(g(rf)))(fn(ignored: church) rx)(fn(id: church) id)

// fun sub(s1: church, s2: church): div church
//   s2(pred)(s1)

// fun church0(f0: church): div church
//   fn(x0) x0

// fun church1(f1: church): div church
//   fn(x1) f1(x1)

// fun church2(f2: church): div church
//   fn(x2) f2(f2(x2))

// fun church3(f3: church): div church
//   fn(x3) f3(f3(f3(x3)))

// fun isChurch0(z)
//   with handler 
//     final ctl isZero() False
//     return(x) True
//   z(fn(zx) {isZero(); zx})(fn(x) x)

// fun eqChurch(e1, e2)
//   if isChurch0(e1) then isChurch0(e2)
//   else if isChurch0(e2) then False
//   else
//     eqChurch(sub(e1, church1), sub(e2, church1))

// fun main()
  // multiplication distributes over addition
  // eqChurch(mult(church2, plus(church1, church3)), plus(mult(church2, church1), mult(church2)(church3)))
