// Overlays via the unified VIEW/anchor model: a widget anywhere emits a
// positioned view into the scene with `overlay(...)` (the `scene` portal effect,
// discharged by `with-scene`), anchored + aligned by `ui/anchor` and clamped
// on-screen. The app's `view : model -> ioc widget` signature is unchanged --
// only overlay-using views wrap their body in `with-scene`. Context menus,
// dropdowns and a modal dialog, drawn identically on jsweb, wasi-web and native.
module main

import std/num/float64
import ui/widget
import ui/anchor
import ui/view
import ui/style/default
import ui/app

// which floating layer (if any) is open -- app state
type popup-state
  NoPopup
  Menu( at : (float64, float64), kind : menu-kind )
  Dialog

type menu-kind
  EditMenu
  SortMenu

struct model( popup : popup-state, status : string, sort : string, dropped : bool )

type msg
  OpenMenuAt( x : float64, y : float64 )
  OpenDropdown
  OpenDialog
  Pick( label : string )
  SetSort( by : string )
  Dropped( what : string )
  Close

val edit-items : list<(string, msg)> = [("Cut", Pick("Cut")), ("Copy", Pick("Copy")), ("Paste", Pick("Paste"))]
val sort-items : list<(string, msg)> = [("Name", SetSort("Name")), ("Date", SetSort("Date")), ("Size", SetSort("Size"))]

// the main (non-floating) view
fun main-view( m : model , key : key) : <keytree,uistate,ioc,theme> widget<msg>
  val target = box( text("Right-click for a context menu", 15.0, theme.fg),
                    padding = 14.0, bg = Just(Fill(theme.palette/surface, 8.0)),
                    on-context-at = Just(fn(x, y) OpenMenuAt(x, y)) )
  val controls = row([
    // mint the dropdown trigger's own identity so its menu can anchor to it
    // (Scope("sort-btn"))
    dropdown("Sort", sort-items, OpenDropdown, ?key = scope("sort-btn")),
    primary-button("Open dialog", OpenDialog),
  ])
  // drag & drop is also the view model: a drag is a positioned ghost view that
  // follows the pointer (unified native/web). Drag the chip into the bin.
  val chip = if m.dropped then spacer()
             else box( text("▤ Drag me", 14.0, theme.fg), padding = 10.0,
                       bg = Just(Fill(theme.palette/surface, 6.0)), drag = Just("card") )
  val bin  = box( text(if m.dropped then "holds: card" else "Drop here", 14.0, theme.fg),
                  padding = 16.0, bg = Just(Fill(theme.palette/bg, 6.0)),
                  on-drop = Just(fn(what) Dropped(what)) )
  simple/page("Koka × overlays", [
    body("Overlays are positioned VIEWS emitted into the scene -- anchored, aligned, and clamped on-screen."),
    target,
    controls,
    row([chip, bin]),
    text("status: " ++ m.status, 14.0, theme.fg),
    text("sort by: " ++ m.sort, 14.0, theme.fg),
  ])

// the modal dialog's content: a themed card
fun dialog-content( key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  card( column([
    accented("Dialog title", 18.0),
    body("A modal dialog, centered by anchor alignment with a dimmed scrim. Click Close or the scrim to dismiss."),
    row([ spacer(), primary-button("Close", Close) ]),
  ], gap = 12.0), padding = 18.0 )

// emit the floating overlay VIEWS for the current model state
fun emit-overlays( m : model, key : key ) : <keytree,uistate,ioc,theme,scene<msg>> ()
  match m.popup
    NoPopup -> ()
    Dialog  ->
      // centered on the display, dimmed, in the Modal band; capped width so the
      // wrapping body self-sizes instead of filling the viewport
      overlay("dialog", dialog-content(key), target-align = center, self-align = center,
              band = Modal, dim = True, on-dismiss = Just(Close), max-width = 360.0)
    Menu(at, kind) ->
      match kind
        // the context menu anchors to the cursor point (Display target + offset)
        EditMenu -> overlay("menu", context-menu(edit-items), offset-x = at.fst, offset-y = at.snd,
                            band = Popover, on-dismiss = Just(Close))
        // the dropdown anchors to its BUTTON's rect: the button's bottom-left
        // meets the menu's top-left (Scope + alignment)
        SortMenu -> overlay("menu", context-menu(sort-items), target = Scope("sort-btn"),
                            target-align = bottom-left, self-align = top-left,
                            band = Popover, on-dismiss = Just(Close))

fun view( m : model , key : key) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  with val theme = dark
  // the app runtime composes the scene: overlays emitted here (from anywhere, via
  // the ambient `scene` effect) are composited over the main content. No
  // with-scene wrapper needed -- `app` installs the handler.
  emit-overlays(m, key)
  box( center( main-view(m, key), 460.0 ), padding = 20.0, bg = Just(Fill(theme.palette/bg)) )

fun update( m : model, msg : msg ) : model
  match msg
    OpenMenuAt(x, y) -> m(popup = Menu((x, y), EditMenu), status = "context menu opened")
    OpenDropdown     -> m(popup = Menu((40.0, 210.0), SortMenu), status = "dropdown opened")
    OpenDialog       -> m(popup = Dialog, status = "dialog opened")
    Pick(l)          -> m(popup = NoPopup, status = "picked " ++ l)
    SetSort(by)      -> m(popup = NoPopup, sort = by, status = "sorted by " ++ by)
    Dropped(what)    -> m(dropped = True, status = "dropped " ++ what)
    Close            -> m(popup = NoPopup, status = "dismissed")

pub fun main()
  app( Model(NoPopup, "ready", "Name", False), view, update, App-config("Koka × overlays", 480, 420) )
