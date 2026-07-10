// Tutorial: your first app.
module pages/tutorial

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import blocks
import pages/common

pub fun tut-model-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ code-block([
      "struct model( count : int )",
      "type msg",
      "  Inc",
      "  Dec",
    ]) ]

pub fun tut-view-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("A view maps the model to widgets. Handlers are message VALUES:"),
    code-block([
      "fun view( m : model ) : widget<msg>",
      "  row([",
      "    primary-button(\"-\", Dec),",
      "    text(m.count.show, 28.0),",
      "    primary-button(\"+\", Inc),",
      "  ])",
    ]) ]

pub fun tut-update-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ code-block([
      "fun update( m : model, msg : msg ) : model",
      "  match msg",
      "    Inc -> m(count = m.count + 1)",
      "    Dec -> m(count = m.count - 1)",
    ]) ]

pub fun tut-result-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("That's the whole app — three top-level functions. Here it is, "
          ++ "live, running right on this page:"),
    live-counter(here()) ]
