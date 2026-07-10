// A portable counter on the unified ui framework: the SAME code runs on
// wasi-web, jsweb, and native Impeller. `AddSlowly` proves the unified
// async loop: spawn a task, its result returns as a message on every
// backend.
module main

import std/async
import std/time/duration
import ui/widget
import ui/style/default
import ui/app

struct model( count : int, pending : bool )

type msg
  Inc
  Dec
  AddSlowly
  Added( n : int )

fun themed-view( m : model , key : key) : <keytree,uistate,ioc,theme> widget<msg>
  val counter = row([
    primary-button("−", Dec, size = 22.0),
    spacer(),
    body(m.count.show, size = 40.0),
    spacer(),
    primary-button("+", Inc, size = 22.0)
  ])
  val slow = quiet-button(if m.pending then "Adding…" else "Add 10 (async)", AddSlowly)
  box( center( page("Koka × ui", [card(column([counter, slow], gap = 16.0))]), 640.0 ),
       padding = 24.0, bg = Just(Fill(theme.bg)) )

fun view( m : model , key : key) : <keytree,uistate,ioc> widget<msg>
  with val theme = dark
  themed-view(m, key)

fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Inc -> m(count = m.count + 1)
    Dec -> m(count = m.count - 1)
    AddSlowly ->
      if m.pending then m else
        spawn fn()
          wait(500.milli-seconds)
          Added(10)
        m(pending = True)
    Added(n) -> Model(m.count + n, False)

pub fun main()
  app( Model(0, False), view, update, App-config("Koka × ui", 380, 260) )
