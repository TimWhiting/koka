// Conway's game of life -- a port of Koka v1's `demo/dom/conway.kk` (HTML5
// canvas + raw DOM) to the web-ui framework: the world is the model, `view`
// renders the grid as plain elements, and the generation clock is just a
// subscription strand emitting `Tick`.
module main

import std/async
import std/time/duration
import web-ui/html
import web-ui/app

alias grid = list<list<bool>>

val size = 20

type msg
  Tick
  ToggleRun
  Randomize
  Clear
  SetHz( s : string )
  ToggleCell( row : int, col : int )

struct model( grid : grid, running : bool, gen : int, seed : int, hz : int )

// deterministic pseudo-randomness: the seed lives in the model
fun lcg( seed : int ) : int
  (seed * 1103515245 + 12345) % 2147483648

fun random-grid( seed0 : int ) : (grid, int)
  var s := seed0
  val g = list(1, size).map fn(_r)
    list(1, size).map fn(_c)
      s := lcg(s)
      (s / 65536) % 4 == 0   // high bits: LCG low bits cycle with a tiny period
  (g, s)

fun empty-grid() : grid
  list(1, size).map fn(_r) list(1, size).map(fn(_c) False)

fun at( g : grid, row : int, col : int ) : bool
  val r = (row + size) % size
  val c = (col + size) % size
  match g[r]
    Just(cells) -> cells[c].default(False)
    Nothing     -> False

fun neighbors( g : grid, row : int, col : int ) : int
  [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]
    .filter( fn(d) g.at(row + d.fst, col + d.snd) )
    .length

fun evolve( g : grid ) : grid
  g.map-indexed fn(r, cells)
    cells.map-indexed fn(c, alive)
      val n = g.neighbors(r, c)
      if alive then n == 2 || n == 3 else n == 3

fun population( g : grid ) : int
  g.map(fn(cells) cells.filter(fn(b) b).length).sum

fun view( m : model ) : html<msg>
  div([class_("wrap")], [
    h1([], [text("Conway's Game of Life")]),
    div([class_("controls")], [
      button([id_("run"), on-click(ToggleRun)], [text(if m.running then "Pause" else "Run")]),
      button([id_("rand"), on-click(Randomize)], [text("Randomize")]),
      button([id_("clear"), on-click(Clear)], [text("Clear")]),
      span([id_("gen")], [text("generation " ++ m.gen.show ++ ", alive " ++ m.grid.population.show)])
    ]),
    div([class_("controls")], [
      label([for_("speed")], [text("speed")]),
      input([id_("speed"), type_("range"), attr("min","1"), attr("max","60"), attr("step","1"),
             value(m.hz.show), on-input(SetHz)]),
      span([], [text(m.hz.show ++ " Hz (generations/second)")])
    ]),
    p([class_("hint")], [text("Click cells to toggle them (pause first for precision surgery).")]),
    div([id_("grid"), class_("grid")], m.grid.map-indexed(row-view))
  ])

fun row-view( r : int, cells : list<bool> ) : html<msg>
  div([class_("gridrow")], cells.map-indexed(fn(c, alive) cell-view(r, c, alive)))

fun cell-view( r : int, c : int, alive : bool ) : html<msg>
  div([classes([("cell", True), ("alive", alive)]), on-click(ToggleCell(r, c))], [])

fun toggle( g : grid, row : int, col : int ) : grid
  g.map-indexed fn(r, cells)
    if r != row then cells
    else cells.map-indexed fn(c, alive) (if c == col then !alive else alive)

// the clock is a self-scheduling chain: every Tick spawns the next one
// with the CURRENT delay, so the slider takes effect on the next beat --
// no timer to cancel or restart. Pausing just skips the evolution.
fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Tick ->
      spawn fn()
        wait((1000 / m.hz.max(1)).milli-seconds)
        Tick
      if m.running then m(grid = m.grid.evolve, gen = m.gen + 1) else m
    ToggleRun -> m(running = !m.running)
    Randomize ->
      val (g, s) = random-grid(m.seed)
      Model(g, m.running, 0, s, m.hz)
    Clear -> m(grid = empty-grid(), gen = 0, running = False)
    SetHz(s) -> m(hz = s.parse-int.default(m.hz))
    ToggleCell(r, c) -> m(grid = m.grid.toggle(r, c))

// a one-shot subscription strand: emit the first Tick to start the chain
fun kick( ch : channel<msg> ) : <async,ioc> ()
  ch.emit-io(Tick)

pub fun main()
  val (g, s) = random-grid(20260711)
  app( Model(g, True, 0, s, 5), view, update, "app", subs = [kick] )
