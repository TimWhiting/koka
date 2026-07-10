// Conway's game of life on the unified ui framework: the SAME code runs on
// wasi-web, jsweb, and native Impeller. The clock is a self-scheduling
// spawn chain; speed is a Slider in Hz.
module main

import std/async
import std/time/duration
import std/num/float64
import ui/widget
import ui/style/default
import ui/app

alias grid = list<list<bool>>

val grid-size = 20
val cell = 16.0

type msg
  Tick
  ToggleRun
  Randomize
  Clear
  SetHz( hz : float64 )
  ToggleCell( row : int, col : int )

struct model( grid : grid, running : bool, gen : int, seed : int, hz : int )

fun lcg( seed : int ) : int
  (seed * 1103515245 + 12345) % 2147483648

fun random-grid( seed0 : int ) : (grid, int)
  var s := seed0
  val g = list(1, grid-size).map fn(_r)
    list(1, grid-size).map fn(_c)
      s := lcg(s)
      (s / 65536) % 4 == 0
  (g, s)

fun empty-grid() : grid
  list(1, grid-size).map fn(_r) list(1, grid-size).map(fn(_c) False)

fun at( g : grid, row : int, col : int ) : bool
  val r = (row + grid-size) % grid-size
  val c = (col + grid-size) % grid-size
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

fun cell-view( r : int, c : int, alive : bool ) : theme widget<msg>
  rect(cell, cell,
       bg = Just(Fill(if alive then rgb(0.62, 0.81, 0.42) else theme.palette/surface, 2.0)),
       on-click = Just(ToggleCell(r, c)))

fun grid-row( r : int, cells : list<bool> ) : theme widget<msg>
  row(cells.map-indexed(fn(c, alive) cell-view(r, c, alive)), gap = 1.0)

fun grid-view( g : grid ) : <theme,ioc> widget<msg>
  column(g.map-indexed(grid-row), gap = 1.0)

fun themed-view( m : model, key : key ) : <keytree,uistate,theme,ioc> widget<msg>
  // the controls and grid are DIRECT children of the filling page, so each
  // cross-centers at a stable offset even as the "alive N" text reflows
  val controls = row([ primary-button(if m.running then "Pause" else "Run", ToggleRun),
                       quiet-button("Randomize", Randomize),
                       quiet-button("Clear", Clear),
                       body("gen " ++ m.gen.show ++ ", alive " ++ m.grid.population.show) ])
  val speed = row([ body("speed"),
                    slider(m.hz.float64, fn(v) SetHz(v), lo = 1.0, hi = 60.0, step = 1.0),
                    accented(m.hz.show ++ " Hz") ])
  box( center( page("Game of Life", [controls, speed, grid-view(m.grid)]), 640.0 ),
       padding = 20.0, bg = Just(Fill(theme.bg)) )

fun view( m : model, key : key ) : <keytree,uistate,ioc> widget<msg>
  with val theme = dark
  themed-view(m, key)

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
    SetHz(v) -> m(hz = v.int.max(1))
    ToggleCell(r, c) -> m(grid = m.grid.toggle(r, c))

fun toggle( g : grid, row : int, col : int ) : grid
  g.map-indexed fn(r, cells)
    if r != row then cells
    else cells.map-indexed fn(c, alive)
      if c == col then !alive else alive

fun kick( ch : channel<msg> ) : <async,ioc> ()
  ch.emit-io(Tick)

pub fun main()
  val (g, s) = random-grid(20260712)
  app( Model(g, True, 0, s, 5), view, update,
       App-config("Game of Life", 420, 500), subs = [kick] )
