/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The app shell: hash routing + two embedded components (todos, counter),
// each with its own closed msg/model, composed with map-msg / map-dispatch.
// Navigating away from a page unmounts it -- its DOM references (externref
// slots) are released by Perceus drops, which the page's verify hook asserts.
module main

import std/async
import std/num/float64
import web-ui/html
import web-ui/vdom
import web-ui/dom
import web-ui/app
import web-ui/theme
import web-ui/ui
import todos
import counter

// ---- routing ---------------------------------------------------------------

type page
  Home
  TodosPage
  CounterPage

fun route( hash : string ) : page
  match hash
    "#/todos"   -> TodosPage
    "#/counter" -> CounterPage
    _           -> Home

fun page/show( p : page ) : string
  match p
    Home        -> "Home"
    TodosPage   -> "Todos"
    CounterPage -> "Counter"

// ---- shell model / messages -------------------------------------------------

type msg
  HashChanged( hash : string )
  ClickedAt( x : float64, y : float64 )
  ToggleTheme
  TodosMsg( m : todos/msg )
  CounterMsg( m : counter/msg )

struct model( page : page, todos : todos/model, counter : counter/model,
              last-click : maybe<(int,int)> = Nothing,
              dark : bool = False )

// the shell handles the `theme` effect: everything below (including the
// embedded components' styled widgets) reads the palette ambiently, and
// toggling is just re-handling the same views with the other palette.
fun view( m : model ) : html<msg>
  with val theme = if m.dark then theme/dark else theme/light
  themed-view(m)

fun themed-view( m : model ) : theme html<msg>
  // the shell paints the WHOLE viewport with the theme; content width is
  // constrained by the inner container, not the body
  div([class_("shell"), id_("shell"),
       page-style("min-height:100vh;padding:2rem 1rem;box-sizing:border-box")], [
    // a flex column filling the viewport: the spacer grows, pushing the
    // footer to the bottom regardless of page height
    div([style("max-width:34rem;margin:0 auto;display:flex;flex-direction:column;"
               ++ "min-height:calc(100vh - 4rem)")], [
      header([], [
        row([], [
          h1([accent-style("margin:0;flex:1")], [text("Koka SPA Demo")]),
          nav([], [row([], [
            anchor([href("#/"),         accent-style()], [text("Home")]),
            anchor([href("#/todos"),    accent-style()], [text("Todos")]),
            anchor([href("#/counter"),  accent-style()], [text("Counter")]),
            quiet-button([id_("themebtn"), title_("switch color theme"), on-click(ToggleTheme)],
                         [text(if m.dark then "Light" else "Dark")])
          ], gap = "14px")])
        ])
      ]),
      page-view(m),
      spacer(),
      footer([], [p([attr("id","where")], [text("Page: " ++ m.page.show)])])
    ])
  ])

fun click-text( m : model ) : string
  match m.last-click
    Nothing -> "Click anywhere in this box — the pointer coordinates arrive as a typed message."
    Just((x,y)) -> "Clicked at " ++ x.show ++ "," ++ y.show ++ " — delivered as a typed message."

fun page-view( m : model ) : <keytree,theme> html<msg>
  match m.page
    Home ->
      page("Welcome", [
        p([], [text("An Elm-style app written in Koka, running as a plain "
                 ++ "WebAssembly core module. Each component owns its own typed "
                 ++ "messages, async work is an effect, DOM references are owned "
                 ++ "by Perceus — and the color theme is a reader effect the "
                 ++ "shell handles (try the Dark button above).")]),
        // coordinate payloads: the click position rides in the message; the
        // dashed accent border marks out the clickable area
        div([id_("clickbox"), class_("clickbox"), on-click-at(ClickedAt),
             surface-style("border:2px dashed " ++ theme.accent ++ ";border-radius:10px;"
                           ++ "padding:24px;cursor:pointer;text-align:center")],
            [text(m.click-text)])
      ])
    TodosPage   -> map-msg( todos/view(m.todos), TodosMsg )
    CounterPage -> map-msg( counter/view(m.counter), CounterMsg )

fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    HashChanged(h) -> m(page = route(h))
    ClickedAt(x,y) -> m(last-click = Just((x.int, y.int)))
    ToggleTheme    -> m(dark = !m.dark)
    TodosMsg(tm)   -> m(todos = todos/update(m.todos, tm))
    CounterMsg(cm) ->
      // counter's update spawns tasks in ITS msg type; map-dispatch wraps
      // them into ours, so the async result comes back as CounterMsg(Added..)
      val c2 = map-dispatch(CounterMsg) fn()
        counter/update(m.counter, cm)
      m(counter = c2)

// ---- subscriptions: the hash as a message stream ----------------------------

fun hash-sub( ch : channel<msg> ) : <async,ioc> ()
  ch.emit-io( HashChanged(get-hash()) )      // initial route
  val changes = window().events("hashchange")
  while { True }
    changes.receive
    ch.emit-io( HashChanged(get-hash()) )

pub fun main()
  app( Model(Home, todos/init(), counter/init()), view, update, "app",
       subs = [hash-sub] )
