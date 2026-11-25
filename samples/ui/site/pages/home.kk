// Home page (outside the quadrants).
module pages/home

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import blocks
import pages/common

pub fun home-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ doc-title("Koka × ui"),
    prose("Below is a counter. Click it — what you're clicking is a lib/ui "
          ++ "widget, and this whole page (sidebar, layout, the counter's own "
          ++ "state) is one lib/ui app, written in Koka."),
    live-counter(here()),
    prose("The counter's count lives in ui/state, not in this page's own "
          ++ "model — embedding it above took no wiring beyond that one "
          ++ "function call. See how ephemeral state works for what that "
          ++ "means and why it matters once a page has more than one "
          ++ "interactive thing on it:"),
    // a CROSS-PAGE ANCHOR: this link switches to the explanation page AND
    // scrolls it so that section sits at the top -- one hash, both effects
    doc-link( "explanation-one-core#state-without-the-model",
              "how ephemeral state works (explanation)",
              ?key = scope("jump-state") ),
    heading("Where to go from here"),
    prose("New to lib/ui? Start with \"Your first app\" — it builds a "
          ++ "complete counter app from a blank file in four steps. "
          ++ "Reference documents individual widgets and functions; how-to "
          ++ "guides answer one task at a time; explanation covers the "
          ++ "model underneath.") ]
