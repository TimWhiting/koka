// Standalone check of `ui/transform`'s `mat4` type: identity/apply-point,
// translate/scale composition order, invert round-trip (+ singular case),
// and the unproject (screen -> child z=0 plane) round-trip. Not the
// test-scenarios harness -- a plain program with its own pass/fail counter.
module mat4

import std/core/unsafe
import std/num/float64
import std/num/int32
import ui/transform

val passed : ref<global,int> = unsafe-total{ ref(0) }
val failed : ref<global,int> = unsafe-total{ ref(0) }

// process exit with a nonzero code on failure: `koka -e` does not propagate
// a child program's exit code, so the pass/fail line below is what the
// test suite actually greps -- this is just for direct/CI invocation.
extern exit-code( code : int32 ) : io ()
  c inline "exit((int)(#1))"
  js inline "process.exit(#1)"

fun check( name : string, cond : bool )
  if cond
    then passed := !passed + 1
    else
      failed := !failed + 1
      println("FAIL: " ++ name)

fun approx( a : float64, b : float64, eps : float64 ) : bool
  abs(a - b) < eps

fun check-approx( name : string, got : float64, want : float64, eps : float64 = 1e-9 )
  check(name ++ " (got " ++ got.show ++ ", want " ++ want.show ++ ")", approx(got, want, eps))

pub fun main()
  // identity applied to a point returns it
  val (ix,iy,iz,iw) = apply-point(identity(), 3.0, 4.0, 5.0)
  check-approx("identity X", ix, 3.0)
  check-approx("identity Y", iy, 4.0)
  check-approx("identity Z", iz, 5.0)
  check-approx("identity W", iw, 1.0)

  // translate3 moves a point
  val (tx,ty,tz,tw) = apply-point(translate3(10.0,20.0,0.0), 1.0, 2.0, 0.0)
  check-approx("translate X", tx, 11.0)
  check-approx("translate Y", ty, 22.0)
  check-approx("translate Z", tz, 0.0)
  check-approx("translate W", tw, 1.0)

  // compose order: (translate3 * scale3) applied to a point scales FIRST,
  // then translates -- (1,0,0) -> scale(2,2,2) -> (2,0,0) -> translate(10,0,0)
  // -> (12,0,0). PINS `a*b` as "apply b then a" (column-vector convention).
  val cm = translate3(10.0,0.0,0.0) * scale3(2.0,2.0,2.0)
  val (cx,cy,cz,cw) = apply-point(cm, 1.0, 0.0, 0.0)
  check-approx("compose order X", cx, 12.0)
  check-approx("compose order Y", cy, 0.0)
  check-approx("compose order Z", cz, 0.0)
  check-approx("compose order W", cw, 1.0)

  // invert round-trip: invert(m) * m ~ identity
  val rm = perspective(800.0) * rotate-x(0.5) * translate3(30.0,40.0,0.0)
  match invert(rm)
    Just(irm) ->
      val prod = irm * rm
      val idm = identity()
      for(0, 15) fn(i)
        check-approx("invert round-trip[" ++ i.show ++ "]", (prod.m)[i], (idm.m)[i])
    Nothing -> check("invert round-trip: matrix unexpectedly singular", False)

  // invert of a singular matrix -> Nothing
  check("invert singular -> Nothing", invert(scale3(0.0,1.0,1.0)).is-nothing)

  // unproject round-trip: forward-project a child-local point through
  // M = perspective(800) * rotate-y(0.4), dehomogenize to a screen point,
  // then unproject that screen point back through M and recover (lx,ly)
  val projm = perspective(800.0) * rotate-y(0.4)
  val lx = 15.0
  val ly = -7.0
  val (px,py,_pz,pw) = apply-point(projm, lx, ly, 0.0)
  val sx = px / pw
  val sy = py / pw
  match unproject(projm, sx, sy)
    Just((ux,uy)) ->
      check-approx("unproject round-trip X", ux, lx, 1e-6)
      check-approx("unproject round-trip Y", uy, ly, 1e-6)
    Nothing -> check("unproject round-trip: unexpectedly Nothing", False)

  println("MAT4: " ++ (!passed).show ++ "/" ++ (!passed + !failed).show ++ " passed")
  if !failed > 0 then
    println("MAT4: FAILED (" ++ (!failed).show ++ " failures)")
    exit-code(1.int32)
