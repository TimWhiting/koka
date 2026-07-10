// The memoization demo (a-prime integration): an ANIMATING bar next to a BIG
// STATIC list wrapped in one `memo` boundary. While the bar animates, the
// list's build+layout is skipped every frame (reconcile reuses the laid-out
// subtree via ptr-eq); hover a list button and ONLY that boundary rebuilds
// (its is-hovered read was auto-tracked). `use-memo = False` for the A/B.
module main

import std/num/float64
import ui/widget
import ui/style/default
import ui/app

val use-memo = True
val rows = 150

struct model( spinning : bool = False )

type msg
  ToggleSpin

fun bounce-bar( spinning : bool, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val (phase, set-phase) = use-state(True)
  val target = if !spinning then 0.0 elif phase then 240.0 else 20.0
  val w = animate(target, duration = 500.0, ease = ease-in-out)
  if spinning && w == target then
    set-phase(fn(p) !p)
  stack([ (0.0, 0.0, rect(240.0, 10.0, bg = Just(Fill(theme.palette/surface, 5.0)))),
          (0.0, 0.0, rect(w.max(4.0), 10.0, bg = Just(Fill(theme.accent, 5.0)))) ])

fun big-list( key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  column( list(1, rows).map fn(i)
    row([ text("row " ++ i.show, 13.0, theme.fg),
          spacer(),
          text("static content item " ++ i.show, 13.0, theme.accent) ])
  , gap = 2.0 )

fun themed-view( m : model, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val listw = if use-memo
    then ui/state/memo(fn(k) big-list(k))
    else big-list(scope("list"))
  column([
    row([ primary-button(if m.spinning then "Stop" else "Animate", ToggleSpin) ]),
    bounce-bar(m.spinning, scope("bar")),
    listw,
  ], gap = 10.0)

fun view( m : model, key : key ) : <keytree,uistate,ioc> widget<msg>
  with val theme = dark
  box( themed-view(m, key), padding = 16.0, bg = Just(Fill(theme/dark.bg)) )

fun update( m : model, msg : msg ) : model
  match msg
    ToggleSpin -> m(spinning = !m.spinning)

pub fun main()
  app( Model(), view, update, App-config("Koka × memo", 520, 640) )
