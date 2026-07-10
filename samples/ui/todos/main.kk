// The app shell: hash ROUTING via ui/router + two embedded components (todos,
// counter), each with its own closed msg/model, composed with map-msg /
// map-dispatch. Each page is a real route: the sidebar items are `link`s
// (real <a href="#/..."> on the web), a `route-sub` turns the location hash --
// deep-links and browser back/forward included -- into `Navigated` messages,
// and the same routing runs natively over ui/nav's in-memory hash. The initial
// light/dark palette follows the OS (`system-dark`), with a manual toggle. The
// SAME code runs on wasi-web, jsweb, and native.
module main

import std/async
import std/num/float64
import ui/widget
import ui/style/default
import ui/router
import ui/app
import todos
import counter

type page
  Home
  TodosPage
  CounterPage

fun page/show( p : page ) : string
  match p
    Home        -> "Home"
    TodosPage   -> "Todos"
    CounterPage -> "Counter"

// route <-> hash-path mapping (the router owns the hash; this owns the names)
fun parse-route( path : string ) : page
  match path
    "todos"   -> TodosPage
    "counter" -> CounterPage
    _         -> Home

fun print-route( p : page ) : string
  match p
    Home        -> ""
    TodosPage   -> "todos"
    CounterPage -> "counter"

type msg
  Navigated( page : page )
  ToggleTheme
  ClickedAt( x : float64, y : float64 )
  TodosMsg( m : todos/msg )
  CounterMsg( m : counter/msg )

struct model( page : page, todos : todos/model, counter : counter/model,
              dark : bool = True, last-click : maybe<(int,int)> = Nothing )

// a sidebar item is a real link to the target route (an <a href="#/..."> on
// the web; a click-to-navigate target natively). The active route is filled
// with the accent color.
fun nav-link( label : string, target : page, current : page ) : theme widget<msg>
  val active = target.show == current.show
  val bg = if active then Fill(theme.accent, 8.0) else Fill(theme.surface, 8.0)
  val fg = if active then rgb(1.0, 1.0, 1.0) else theme.fg
  link( print-route(target), box(text(label, 15.0, fg), padding = 9.0, bg = Just(bg)) )

fun click-text( m : model ) : string
  match m.last-click
    Nothing -> "Click anywhere in this box — the pointer coordinates arrive as a typed message."
    Just((x,y)) -> "Clicked at " ++ x.show ++ "," ++ y.show ++ " — delivered as a typed message."

fun page-view( m : model, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  match m.page
    Home ->
      page("Welcome", [
        body("An Elm-style app in Koka: typed messages per component, async "
             ++ "via effects, and one widget vocabulary across web and native."),
        box( body(m.click-text), padding = 24.0,
             bg = Just(Fill(theme.palette/surface, 10.0)),
             on-click-at = Just(fn(x, y) ClickedAt(x, y)) ),
        // ephemeral state: the open/closed lives in ui/state, NOT the model
        expander("Ephemeral state demo",
                 body("Open/closed lives in ui/state, keyed by widget identity — not the app model."),
                 here())
      ])
    TodosPage   -> map-msg( todos/view(m.todos, key), TodosMsg )
    CounterPage -> map-msg( counter/view(m.counter, key), CounterMsg )

fun themed-view( m : model, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  // the outer box fills the full viewport (background), `center` caps + centers
  // the content column at 640px
  box( center( column([
    row([
      accented("Koka × ui", 20.0),
      spacer(),
      nav-link("Home", Home, m.page),
      nav-link("Todos", TodosPage, m.page),
      nav-link("Counter", CounterPage, m.page),
      quiet-button(if m.dark then "light" else "dark", ToggleTheme)
    ]),
    page-view(m, key),
    spacer(),
    body("Page: " ++ m.page.show, 13.0)
  ], gap = 18.0, fill = True), 640.0 ), padding = 22.0, bg = Just(Fill(theme.bg)) )

fun view( m : model, key : key ) : <keytree,uistate,ioc> widget<msg>
  // whole-theme crossfade: one animated t interpolates the palette
  val t = animate(if m.dark then 1.0 else 0.0, duration = 250.0)
  with val theme = theme/light.mix(theme/dark, t)
  themed-view(m, key)

fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Navigated(p)   -> m(page = p)      // from route-sub (deep-link / back-forward / link)
    ToggleTheme    -> m(dark = !m.dark)
    ClickedAt(x,y) -> m(last-click = Just((x.int, y.int)))
    TodosMsg(tm)   -> m(todos = todos/update(m.todos, tm))
    CounterMsg(cm) ->
      val c2 = map-dispatch(CounterMsg) fn()
        counter/update(m.counter, cm)
      m(counter = c2)

pub fun main()
  // start in the OS light/dark preference; route-sub emits the initial route
  // (deep-link) and every hash change
  app( Model(Home, todos/init(), counter/init(), dark = system-dark()), view, update,
       App-config("Koka × ui", 640, 520),
       subs = [ fn(ch) route-sub(ch, parse-route, Navigated) ] )
