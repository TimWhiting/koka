/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// A 4x4, ROW-major matrix of `float64` (16 elements, index `[r*4+c]`) for
// perspective-projected 2D UI transforms (card flips, tilts, etc). This is
// pure math -- no widget/backend dependency. Later consumers:
//   - the native Impeller backend concatenates this matrix, transposed to
//     column-major, for the SDK's own matrix type
//   - the web backend emits it directly as a CSS `matrix3d(...)`
//   - the shared hit-test walk uses `unproject` to map a screen click back
//     into a transformed child's local (z=0) plane
module ui/transform

import std/num/float64   // cos, sin, sqrt, abs

// A row-major 4x4 matrix: `m[r*4+c]` is row `r`, column `c`.
pub value struct mat4( m : vector<float64> )

fun mat4/raw( xs : list<float64> ) : mat4
  Mat4(xs.vector)

// Total element read (`vector`'s `[]` can raise `exn` on an out-of-bounds
// index; every index used here is a compile-time-known 0..15 or 0..8, so
// fall back to 0.0 rather than thread `exn` through every function).
fun at0( v : vector<float64>, i : int ) : float64
  match v.at(i)
    Just(x) -> x
    Nothing -> 0.0

// The 4x4 identity matrix.
pub fun identity() : mat4
  mat4/raw([
    1.0, 0.0, 0.0, 0.0,
    0.0, 1.0, 0.0, 0.0,
    0.0, 0.0, 1.0, 0.0,
    0.0, 0.0, 0.0, 1.0,
  ])

// A perspective matrix: identity except `m[14] = -1/depth`, so that
// projecting a point at depth `z` divides its (x,y) by `w = 1 - z/depth`
// after the perspective divide -- larger `depth` is a flatter (more
// orthographic) look, smaller `depth` is a stronger, closer-camera effect.
pub fun perspective( depth : float64 ) : mat4
  val nd = 0.0 - (1.0 / depth)
  mat4/raw([
    1.0, 0.0, 0.0, 0.0,
    0.0, 1.0, 0.0, 0.0,
    0.0, 0.0, 1.0, 0.0,
    0.0, 0.0, nd,  1.0,
  ])

// Rotation about the X axis by `rad` radians.
pub fun rotate-x( rad : float64 ) : mat4
  val c = cos(rad)
  val s = sin(rad)
  val ns = 0.0 - s
  mat4/raw([
    1.0, 0.0, 0.0, 0.0,
    0.0, c,   ns,  0.0,
    0.0, s,   c,   0.0,
    0.0, 0.0, 0.0, 1.0,
  ])

// Rotation about the Y axis by `rad` radians.
pub fun rotate-y( rad : float64 ) : mat4
  val c = cos(rad)
  val s = sin(rad)
  val ns = 0.0 - s
  mat4/raw([
    c,   0.0, s,   0.0,
    0.0, 1.0, 0.0, 0.0,
    ns,  0.0, c,   0.0,
    0.0, 0.0, 0.0, 1.0,
  ])

// Rotation about the Z axis by `rad` radians.
pub fun rotate-z( rad : float64 ) : mat4
  val c = cos(rad)
  val s = sin(rad)
  val ns = 0.0 - s
  mat4/raw([
    c,   ns,  0.0, 0.0,
    s,   c,   0.0, 0.0,
    0.0, 0.0, 1.0, 0.0,
    0.0, 0.0, 0.0, 1.0,
  ])

// Translation by `(x,y,z)`.
pub fun translate3( x : float64, y : float64, z : float64 ) : mat4
  mat4/raw([
    1.0, 0.0, 0.0, x,
    0.0, 1.0, 0.0, y,
    0.0, 0.0, 1.0, z,
    0.0, 0.0, 0.0, 1.0,
  ])

// Wrap `m` so it applies about the point `(cx,cy)` rather than the origin:
// translate the pivot to the origin, apply `m`, translate back. This is the
// ONE piece of centering math shared by both the paint arm (native backend,
// `LTransform3d`) and the hit-test walk (`ui/widget`'s `hit-go`) -- both must
// concatenate the identical M' or hit and paint silently disagree.
pub fun centered( m : mat4, cx : float64, cy : float64 ) : mat4
  translate3(cx, cy, 0.0) * m * translate3(0.0 - cx, 0.0 - cy, 0.0)

// Non-uniform scale by `(x,y,z)`.
pub fun scale3( x : float64, y : float64, z : float64 ) : mat4
  mat4/raw([
    x,   0.0, 0.0, 0.0,
    0.0, y,   0.0, 0.0,
    0.0, 0.0, z,   0.0,
    0.0, 0.0, 0.0, 1.0,
  ])

// Matrix product: `a*b` applies `b` THEN `a` to a column vector (i.e.
// `(a*b)*v == a*(b*v)`, the standard column-vector convention). Standard
// row-major multiply: `c[r*4+col] = sum_k a[r*4+k] * b[k*4+col]`.
pub fun mat4/(*)( a : mat4, b : mat4 ) : mat4
  fun elem( r : int, col : int ) : float64
    fun term( k : int ) : float64
      a.m.at0(r*4+k) * b.m.at0(k*4+col)
    term(0) + term(1) + term(2) + term(3)
  Mat4(vector-init-total(16, fn(i) elem(i / 4, i % 4)))

// 2x2 determinant helper for the 4x4 cofactor expansion.
fun det2( a : float64, b : float64, c : float64, d : float64 ) : float64
  a*d - b*c

// The standard cofactor/adjugate 4x4 inverse (MESA's `gluInvertMatrix`,
// adapted to row-major indexing). Returns `Nothing` if the matrix is
// singular (`det == 0`).
pub fun invert( a : mat4 ) : maybe<mat4>
  val e = a.m
  fun g(i : int) : float64
    e.at0(i)
  val inv0  = g(5)*g(10)*g(15) - g(5)*g(11)*g(14) - g(9)*g(6)*g(15) + g(9)*g(7)*g(14) + g(13)*g(6)*g(11) - g(13)*g(7)*g(10)
  val inv4  = 0.0 - g(4)*g(10)*g(15) + g(4)*g(11)*g(14) + g(8)*g(6)*g(15) - g(8)*g(7)*g(14) - g(12)*g(6)*g(11) + g(12)*g(7)*g(10)
  val inv8  = g(4)*g(9)*g(15) - g(4)*g(11)*g(13) - g(8)*g(5)*g(15) + g(8)*g(7)*g(13) + g(12)*g(5)*g(11) - g(12)*g(7)*g(9)
  val inv12 = 0.0 - g(4)*g(9)*g(14) + g(4)*g(10)*g(13) + g(8)*g(5)*g(14) - g(8)*g(6)*g(13) - g(12)*g(5)*g(10) + g(12)*g(6)*g(9)
  val inv1  = 0.0 - g(1)*g(10)*g(15) + g(1)*g(11)*g(14) + g(9)*g(2)*g(15) - g(9)*g(3)*g(14) - g(13)*g(2)*g(11) + g(13)*g(3)*g(10)
  val inv5  = g(0)*g(10)*g(15) - g(0)*g(11)*g(14) - g(8)*g(2)*g(15) + g(8)*g(3)*g(14) + g(12)*g(2)*g(11) - g(12)*g(3)*g(10)
  val inv9  = 0.0 - g(0)*g(9)*g(15) + g(0)*g(11)*g(13) + g(8)*g(1)*g(15) - g(8)*g(3)*g(13) - g(12)*g(1)*g(11) + g(12)*g(3)*g(9)
  val inv13 = g(0)*g(9)*g(14) - g(0)*g(10)*g(13) - g(8)*g(1)*g(14) + g(8)*g(2)*g(13) + g(12)*g(1)*g(10) - g(12)*g(2)*g(9)
  val inv2  = g(1)*g(6)*g(15) - g(1)*g(7)*g(14) - g(5)*g(2)*g(15) + g(5)*g(3)*g(14) + g(13)*g(2)*g(7) - g(13)*g(3)*g(6)
  val inv6  = 0.0 - g(0)*g(6)*g(15) + g(0)*g(7)*g(14) + g(4)*g(2)*g(15) - g(4)*g(3)*g(14) - g(12)*g(2)*g(7) + g(12)*g(3)*g(6)
  val inv10 = g(0)*g(5)*g(15) - g(0)*g(7)*g(13) - g(4)*g(1)*g(15) + g(4)*g(3)*g(13) + g(12)*g(1)*g(7) - g(12)*g(3)*g(5)
  val inv14 = 0.0 - g(0)*g(5)*g(14) + g(0)*g(6)*g(13) + g(4)*g(1)*g(14) - g(4)*g(2)*g(13) - g(12)*g(1)*g(6) + g(12)*g(2)*g(5)
  val inv3  = 0.0 - g(1)*g(6)*g(11) + g(1)*g(7)*g(10) + g(5)*g(2)*g(11) - g(5)*g(3)*g(10) - g(9)*g(2)*g(7) + g(9)*g(3)*g(6)
  val inv7  = g(0)*g(6)*g(11) - g(0)*g(7)*g(10) - g(4)*g(2)*g(11) + g(4)*g(3)*g(10) + g(8)*g(2)*g(7) - g(8)*g(3)*g(6)
  val inv11 = 0.0 - g(0)*g(5)*g(11) + g(0)*g(7)*g(9) + g(4)*g(1)*g(11) - g(4)*g(3)*g(9) - g(8)*g(1)*g(7) + g(8)*g(3)*g(5)
  val inv15 = g(0)*g(5)*g(10) - g(0)*g(6)*g(9) - g(4)*g(1)*g(10) + g(4)*g(2)*g(9) + g(8)*g(1)*g(6) - g(8)*g(2)*g(5)
  val det = g(0)*inv0 + g(1)*inv4 + g(2)*inv8 + g(3)*inv12
  if det == 0.0 then Nothing else
    val invdet = 1.0 / det
    val cof = [inv0,inv1,inv2,inv3, inv4,inv5,inv6,inv7, inv8,inv9,inv10,inv11, inv12,inv13,inv14,inv15]
    Just(Mat4(cof.map(fn(x) x * invdet).vector))

// Apply `a` to a homogeneous point `(x,y,z,1)`, returning the (undivided)
// homogeneous result `(X,Y,Z,W)` -- callers dehomogenize by `W` themselves
// (e.g. for a screen-space (x,y), divide by `W`).
pub fun apply-point( a : mat4, x : float64, y : float64, z : float64 ) : (float64,float64,float64,float64)
  val e = a.m
  val bigX = e.at0(0)*x + e.at0(1)*y + e.at0(2)*z + e.at0(3)
  val bigY = e.at0(4)*x + e.at0(5)*y + e.at0(6)*z + e.at0(7)
  val bigZ = e.at0(8)*x + e.at0(9)*y + e.at0(10)*z + e.at0(11)
  val bigW = e.at0(12)*x + e.at0(13)*y + e.at0(14)*z + e.at0(15)
  (bigX, bigY, bigZ, bigW)

// 3x3 adjugate/determinant inverse used by both `invert`'s cousin below
// (kept private) and `unproject`.
fun invert3( h : vector<float64> ) : maybe<vector<float64>>
  fun g(i : int) : float64
    h.at0(i)
  val det = g(0)*det2(g(4),g(5),g(7),g(8)) - g(1)*det2(g(3),g(5),g(6),g(8)) + g(2)*det2(g(3),g(4),g(6),g(7))
  if abs(det) < 1e-12 then Nothing else
    val invdet = 1.0 / det
    val inv0 = det2(g(4),g(5),g(7),g(8)) * invdet
    val inv1 = det2(g(2),g(1),g(8),g(7)) * invdet
    val inv2 = det2(g(1),g(2),g(4),g(5)) * invdet
    val inv3 = det2(g(5),g(3),g(8),g(6)) * invdet
    val inv4 = det2(g(0),g(2),g(6),g(8)) * invdet
    val inv5 = det2(g(2),g(0),g(5),g(3)) * invdet
    val inv6 = det2(g(3),g(4),g(6),g(7)) * invdet
    val inv7 = det2(g(1),g(0),g(7),g(6)) * invdet
    val inv8 = det2(g(0),g(1),g(3),g(4)) * invdet
    Just([inv0,inv1,inv2,inv3,inv4,inv5,inv6,inv7,inv8].vector)

// Map a screen point `(px,py)` back to the child's local `(x,y)` on its
// z=0 plane through `a`'s inverse: extract the 3x3 homography `H` for the
// z=0 plane from rows/cols `{0,1,3}` of `a` (dropping the z row/col -- a
// z=0 point's contribution through column 2 is always zero), invert `H`,
// apply it to `(px,py,1)`, and dehomogenize by the 3rd component. `Nothing`
// if `H` is singular or the point maps behind the camera (`w <= 0`).
pub fun unproject( a : mat4, px : float64, py : float64 ) : maybe<(float64,float64)>
  val e = a.m
  val h = [e.at0(0),e.at0(1),e.at0(3), e.at0(4),e.at0(5),e.at0(7), e.at0(12),e.at0(13),e.at0(15)].vector
  match invert3(h)
    Nothing -> Nothing
    Just(hi) ->
      val x = hi.at0(0)*px + hi.at0(1)*py + hi.at0(2)
      val y = hi.at0(3)*px + hi.at0(4)*py + hi.at0(5)
      val w = hi.at0(6)*px + hi.at0(7)*py + hi.at0(8)
      if w <= 0.0 then Nothing else Just((x / w, y / w))
