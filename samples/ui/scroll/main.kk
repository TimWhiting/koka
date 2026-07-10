module main
import ui/widget
import ui/style/default
import ui/app

struct model( n : int )
type msg { Noop }

fun rows( tag : string , key : key) : theme list<widget<msg>>
  list(1, 40).map fn(i) box(body(tag ++ " row " ++ i.show, size = 18.0), padding = 10.0,
    bg = Just(Fill(if i.is-even then Color(0.2,0.2,0.3) else Color(0.15,0.15,0.22))))

fun cards( key : key ) : theme list<widget<msg>>
  list(1, 20).map fn(i) box(body("card " ++ i.show, size = 18.0), padding = 24.0,
    bg = Just(Fill(if i.is-even then Color(0.2,0.25,0.3) else Color(0.15,0.2,0.25), 6.0)))

fun view( m : model , key : key) : <keytree,uistate,ioc> widget<msg>
  with val theme = dark
  column([
    box(body("HEADER (fixed)", size = 22.0), padding = 12.0, bg = Just(Fill(Color(0.3,0.1,0.1)))),
    expanded( row([
      // LEFT: no manual bar -- the scene composer AUTO-places a scrollbar view
      // over this region's right edge (native; the browser draws web's).
      expanded( scroll( column(rows("auto", key), gap = 4.0), name = "left" ) ),
      // RIGHT: a MANUAL scrollbar placed inline -- auto is suppressed for it.
      expanded( row([
        expanded( scroll( column(rows("manual", key), gap = 4.0), name = "right" ) ),
        scrollbar("right", 240.0),
      ], gap = 4.0, fill = True) ),
    ], gap = 16.0, fill = True), flex = 2.0 ),
    // HORIZONTAL scroll (opt-in): a wide row that scrolls sideways, with an
    // auto bar on the bottom edge (native).
    expanded( scroll( row(cards(key), gap = 8.0), name = "carousel", horizontal = True ), flex = 1.0 ),
  ], fill = True)

fun update( m : model, msg : msg ) : model
  m

// the auto scrollbar is built by the scene composer (outside the view's theme
// scope), so this builder discharges its own theme (self-contained).
fun auto-bar( info, axis ) : ioc widget<msg>
  with val theme = dark
  themed-scrollbar(info, axis)

pub fun main()
  app( Model(0), view, update, App-config("scrolltest", 520, 320), scrollbar = auto-bar )
