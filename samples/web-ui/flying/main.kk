// Flying spans -- a port of Koka v1's `demo/dom/flyingDivs.kk`: phrases hop
// to random positions and pastel colors on a timer. In v1 this was raw DOM
// mutation (`span.style.left := ...`); here the positions live in the model
// and `view` just describes them -- the diff moves the spans.
module main

import std/async
import std/time/duration
import web-ui/html
import web-ui/app

struct sprite( label : string, x : int, y : int, r : int, g : int, b : int )

struct model( sprites : list<sprite>, seed : int, hz : int )

type msg
  Hop
  SetHz( s : string )

fun lcg( seed : int ) : int
  (seed * 1103515245 + 12345) % 2147483648

// place a sprite at a random spot with a random pastel color, threading the seed
fun place( label : string, seed0 : int ) : (sprite, int)
  val s1 = lcg(seed0)
  val s2 = lcg(s1)
  val s3 = lcg(s2)
  val s4 = lcg(s3)
  val s5 = lcg(s4)
  ( Sprite(label, s1 % 70, 10 + s2 % 70, 155 + s3 % 100, 155 + s4 % 100, 155 + s5 % 100), s5 )

fun hop-all( sprites : list<sprite>, seed0 : int ) : (list<sprite>, int)
  match sprites
    Nil -> (Nil, seed0)
    Cons(sp, rest) ->
      val (sp2, s1) = place(sp.label, seed0)
      val (rest2, s2) = hop-all(rest, s1)
      (Cons(sp2, rest2), s2)

fun sprite-view( sp : sprite ) : html<msg>
  span([class_("fly"),
        style("position:absolute;left:" ++ sp.x.show ++ "vw;top:" ++ sp.y.show ++ "vh;"
              ++ "background:rgb(" ++ sp.r.show ++ "," ++ sp.g.show ++ "," ++ sp.b.show ++ ");"
              ++ "transition:left .8s ease,top .8s ease,background 1s")],
       [text(sp.label)])

fun view( m : model ) : html<msg>
  div([], [
    h1([], [text("Koka is all about having fun!")]),
    div([class_("controls")], [
      label([for_("speed")], [text("speed")]),
      input([id_("speed"), type_("range"), attr("min","1"), attr("max","20"), attr("step","1"),
             value(m.hz.show), on-input(SetHz)]),
      span([], [text(m.hz.show ++ " hops/second")])
    ]),
    div([], m.sprites.map(sprite-view))
  ])

// self-scheduling chain: each Hop spawns the next with the current delay,
// so the slider takes effect on the next hop
fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Hop ->
      spawn fn()
        wait((1000 / m.hz.max(1)).milli-seconds)
        Hop
      val (sprites, s) = hop-all(m.sprites, m.seed)
      Model(sprites, s, m.hz)
    SetHz(s) -> m(hz = s.parse-int.default(m.hz))

fun kick( ch : channel<msg> ) : <async,ioc> ()
  ch.emit-io(Hop)

pub fun main()
  val labels = ["This is Koka!", "Enjoy our new typesafe language!", "Koka is all about having fun!"]
  val (sprites, s) = hop-all(labels.map(fn(l) Sprite(l, 10, 10, 200, 200, 200)), 42)
  app( Model(sprites, s, 1), view, update, "app", subs = [kick] )
