// Pins the AMBIGUITY-THROW path of the tester's selector resolution
// (`ui/test`'s `resolve1`, lib/ui/test.kk:89-93): `find`/`click`/`texts` all
// resolve a selector via `find-ids`, and when it matches MORE than one
// identity, `resolve1` throws (through the ordinary `exn` path, same
// mechanism as every other tester failure) listing every candidate's
// root-to-leaf path. `test/ui/selector.kk` already pins that `find-ids`
// itself returns >1 id for an ambiguous shape (two `Named("x")` under
// different parents); this file pins the TESTER-LEVEL consequence -- that
// `find`/`click`/`texts` actually raise, not silently pick one.
module selector-ambiguity

import std/async
import std/num/float64
import std/core/sslice
import ui/widget
import ui/state
import ui/test

pub struct model()
pub type msg
  Bump

// two branches, each with a `scope("dup")` child -- same name, different
// parents, exactly like `selector.kk`'s "ambiguous x" shape, but built
// through the real widget tree (`column`/`box`) instead of raw `kt-child`,
// so it exercises the SAME layout/keytree path `find`/`click`/`texts` use.
pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  column([
    box(text("left", 13.0, ?key = scope("dup", ?key = scope("left"))), ?key = scope("box-left")),
    box(text("right", 13.0, ?key = scope("dup", ?key = scope("right"))), ?key = scope("box-right")),
    text("unique", 13.0, ?key = scope("solo")),
  ], gap = 4.0)

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    Bump -> m

pub fun ambiguity-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  // sanity: the unambiguous selector still resolves normally
  check-eq("unique selector resolves", t.texts("solo"), ["unique"])
  // `find` on the ambiguous bare name must THROW, not silently pick one
  match error/try( fn() t.find("dup") )
    Error(exn) ->
      check("find(\"dup\") throws", True)
      check("throw message reports ambiguity", exn.message.starts-with("ui/test: selector \"dup\" is ambiguous").is-just)
      // one header line + one line per candidate path (two candidates here
      // -- two "\n" separators)
      check-eq("throw message lists both candidate paths", exn.message.count("\n"), 2)
    Ok(_) ->
      check("find(\"dup\") throws", False)
  // `click` and `texts` share `resolve1` -- pin they throw too, not just `find`
  match error/try( fn() t.click("dup") )
    Error(_) -> check("click(\"dup\") throws", True)
    Ok(_)    -> check("click(\"dup\") throws", False)
  match error/try( fn() t.texts("dup") )
    Error(_) -> check("texts(\"dup\") throws", True)
    Ok(_)    -> check("texts(\"dup\") throws", False)

pub fun main()
  test-scenarios("selector ambiguity", Model(), view, update,
                 [("ambiguity", ambiguity-scenario)])
