// REGRESSION TEST: mutual-recursion specialization must terminate.
//
// mutualspec-lib's build/patch/patch-kids are mutually recursive and all
// carry a function-typed parameter; called from here with a literal lambda
// they form a specialization ring: specializing `patch` exposes a
// specializable `build`/`patch-kids` call in its body, whose specialized
// body exposes `patch` again -- before the ancestry guard in
// Core/Specialize.hs each lap minted a fresh @spec name (no cache can
// catch it) and -O2 builds never terminated (compiler at 100% cpu).
//
// The guard admits re-specializing an ancestor only at a strictly smaller
// instantiation weight (the decreasing measure of implicit-parameter
// inference, see isDecreasingChain in Type/InferMonad.hs): legitimate
// multi-step specialization shrinks its instantiations each step (see
// twostep-large2.kk) and still works; this ring re-instantiates at the same
// types every lap and is cut off after one round.
//
// First hit 2026-07-10 by samples/wasi-web/framework's vdom + bench. NOTE:
// this minimized module pair exercises the shape but did NOT reproduce the
// divergence on the pre-fix compiler by itself (the full framework bench at
// -O2 needed additional cross-module inline/unroll interplay) -- it guards
// the code path; the framework -O2 build is the live reproducer.
module cgen/specialize/mutualspec
import cgen/specialize/mutualspec-lib

fun view( sel : int ) : html<int>
  Elem(0, list(1, 4).map( fn(i) Elem(i, [Text(if i == sel then 1 else 0)]) ))

pub fun main()
  val emit = fn(m : int) ()
  val t0 = build(view(0), emit)
  val t1 = patch(t0, view(1), emit)
  val t2 = patch(t1, view(2), emit)
  match t2
    NElem(_, kids) -> println(kids.length)
    NText(_) -> println(-1)
