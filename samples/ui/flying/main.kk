// Flying phrases (a port of Koka v1's flyingDivs) on the unified ui
// framework: sprites live in the model and hop on a self-scheduling spawn
// chain; `stack` places them absolutely. Same code on all three backends.
module main

import std/async
import std/time/duration
import std/num/float64
import ui/widget
import ui/style/default
import ui/app

struct sprite( label : string, x : float64, y : float64, color : color )

struct model( sprites : list<sprite>, seed : int, hz : int )

type msg
  Hop
  SetHz( hz : float64 )

fun lcg( seed : int ) : int
  (seed * 1103515245 + 12345) % 2147483648

fun chan( s : int ) : float64
  0.55 + ((s / 65536) % 100).float64 / 250.0

fun place( label : string, seed0 : int ) : (sprite, int)
  val s1 = lcg(seed0)
  val s2 = lcg(s1)
  val s3 = lcg(s2)
  val s4 = lcg(s3)
  val s5 = lcg(s4)
  ( Sprite(label, ((s1 / 65536) % 300).float64, 60.0 + ((s2 / 65536) % 240).float64,
           Color(chan(s3), chan(s4), chan(s5))), s5 )

fun hop-all( sprites : list<sprite>, seed0 : int ) : (list<sprite>, int)
  match sprites
    Nil -> (Nil, seed0)
    Cons(sp, rest) ->
      val (sp2, s1) = place(sp.label, seed0)
      val (rest2, s2) = hop-all(rest, s1)
      (Cons(sp2, rest2), s2)

fun sprite-view( sp : sprite ) : widget<msg>
  box( text(sp.label, 14.0, rgb(0.08, 0.08, 0.12)), padding = 9.0,
       bg = Just(Fill(sp.color, 8.0)) )

fun themed-view( m : model ) : <keytree,theme> widget<msg>
  val controls = row([ body("hops/second"),
                       slider(m.hz.float64, fn(v) SetHz(v), lo = 1.0, hi = 20.0, step = 1.0),
                       accented(m.hz.show) ])
  val sprites = stack(m.sprites.map(fn(sp) (sp.x, sp.y, sprite-view(sp))))
  box( center( page("Koka is all about having fun!", [controls, sprites]), 640.0 ),
       padding = 18.0, bg = Just(Fill(theme.bg)) )

fun view( m : model, key : key ) : widget<msg>
  with val theme = dark
  themed-view(m)

fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Hop ->
      spawn fn()
        wait((1000 / m.hz.max(1)).milli-seconds)
        Hop
      val (sprites, s) = hop-all(m.sprites, m.seed)
      Model(sprites, s, m.hz)
    SetHz(v) -> m(hz = v.int.max(1))

fun kick( ch : channel<msg> ) : <async,ioc> ()
  ch.emit-io(Hop)

pub fun main()
  val labels = ["This is Koka!", "Enjoy our new typesafe language!", "Koka is all about having fun!"]
  val (sprites, s) = hop-all(labels.map(fn(l) Sprite(l, 10.0, 60.0, rgb(0.8, 0.8, 0.8))), 42)
  app( Model(sprites, s, 1), view, update,
       App-config("Koka is all about having fun!", 480, 400), subs = [kick] )
