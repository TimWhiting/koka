// How-to: lay out a screen.
module pages/how-to

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import blocks
import pages/common

pub fun howto-rows-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("Two calls cover most layouts: `column` stacks children top to "
          ++ "bottom, `row` places them left to right. Drop a `spacer()` "
          ++ "into either list to push everything after it to the far "
          ++ "edge:"),
    code-block([
      "column([ header, body ], gap = 12.0)",
      "row([ left, spacer(), right ])   // spacer pushes apart",
    ]) ]

pub fun howto-fill-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("You have a header and a scrolling list below it, and you want "
          ++ "the list to take whatever space is left. `expanded` is the "
          ++ "primitive for that — it grows a child to fill whatever room "
          ++ "the rigid (non-expanded) siblings didn't use:"),
    code-block([
      "column([",
      "  header,                       // natural height",
      "  expanded( scroll( list ) ),   // takes the rest, scrolls",
      "], fill = True)",
    ]) ]

// two independent counters side by side. They MUST sit on different source
// lines (so `?child-key`, which includes the line, differs) -- this is the
// idiomatic way to give same-shaped sibling widgets distinct identities.
fun with-two-counters<a>( key : key ) : <keytree,uistate,ioc,theme> widget<a>
  val left  = live-counter(here())
  val right = live-counter(here())
  row([ left, right ], gap = 16.0)

pub fun howto-center-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("On a wide window, content stretched edge to edge is hard to "
          ++ "read. Cap it and center it in one call:"),
    code-block([
      "center( content, max-width = 640.0 )   // the app-shell idiom",
    ]),
    prose("Two live counters below, independent of each other because "
          ++ "ephemeral state keys by call site — put both `live-counter` "
          ++ "calls on the same source line instead of two different ones "
          ++ "and they'd share state and move together:"),
    // NOTE: distinct source lines -> distinct `?child-key` -> independent state
    // (two `live-counter()` on ONE line would share a key and move together)
    with-two-counters(key) ]
