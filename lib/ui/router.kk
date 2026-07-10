/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Portable routing over the `ui/nav` hash façade. An app supplies two pure
// functions between its own `route` type and a path string:
//
//   parse : string -> route     ("todos/42" -> Todo(42))
//   print : route  -> string    (Todo(42)  -> "todos/42")
//
// and gets links, deep-links and back/forward on every backend:
//
//   subs = [ route-sub(parse, Navigated) ]     // deep-link + back/forward
//   link( print(Todo(42)), text("open") )      // a real <a> on the web
//   navigate( print, Todo(42) )                 // set the hash from `update`
//
// The route <-> path mapping is the app's; the router only owns the hash
// plumbing. Because it is all built on `ui/nav`, swapping the hash for the
// History API later is a change behind the façade, not here or in apps.
module ui/router

import std/async
import ui/keytrie   // the key type for link's ?key implicit
import ui/widget
import ui/state   // scroll-to: the fragment half of a route
import ui/nav

// the route path carried by a raw location hash: strip the leading "#" and
// "/" ("#/todos/42" -> "todos/42", "" -> "").
pub fun hash-path( hash : string ) : string
  hash.list.drop-while(fn(c) c == '#' || c == '/').string

// A subscription (for `app`'s `subs`) that emits `to-msg(parse(path))` once at
// startup (the deep-link) and again on every hash change (browser
// back/forward, a link click, or `navigate`). Generalizes the hand-written
// `hash-sub` the web-ui samples use. Wire it as:
//   subs = [ fn(ch) route-sub(ch, parse, Navigated) ]
pub fun route-sub<msg,route>( ch : channel<msg>, parse : (string) -> route, to-msg : (route) -> msg ) : <async,ioc> ()
  ch.emit-io( to-msg( parse( hash-path( current-hash() ) ) ) )   // deep-link on start
  val changes = hash-events()
  while { True }
    changes.receive
    ch.emit-io( to-msg( parse( hash-path( current-hash() ) ) ) )

// Navigate to a route from `update` (or anywhere): sets the hash, which
// records history on the web and fires the change that `route-sub` observes.
pub fun navigate<route>( print : (route) -> string, r : route ) : ioc ()
  goto-hash("#/" ++ print(r))

// Split a path into its page and optional "#fragment" ("explanation#keys" ->
// ("explanation", Just("keys"))). The fragment names a SECTION -- a scope slug
// `scroll-to` can resolve -- so a link can target a scroll position on another
// page. Only the first '#' splits; a fragment containing '#' is nobody's slug.
pub fun split-fragment( path : string ) : (string, maybe<string>)
  match path.split("#")
    Cons(p, Cons(f, _)) | !f.is-empty -> (p, Just(f))
    _ -> (path, Nothing)

// `route-sub` with fragments: parses the page half into the app's route as
// usual, and when the hash carries "#section" ALSO requests `scroll-to` on it
// -- so one navigation both switches the page and scrolls it, and the anchor
// resolves on the frame the new page first paints (see ui/state's scroll-to).
// This lives in the SUB rather than the app's `update` because `update` is
// pure modulo `dispatch`; the hash side effects belong to the hash observer.
pub fun anchor-route-sub<msg,route>( ch : channel<msg>, parse : (string) -> route, to-msg : (route) -> msg ) : <async,ioc> ()
  fun emit-current()
    val (p, frag) = split-fragment( hash-path( current-hash() ) )
    ch.emit-io( to-msg( parse(p) ) )
    match frag
      Just(f) -> scroll-to(f)
      Nothing -> ()
  emit-current()                     // deep-link on start, fragment included
  val changes = hash-events()
  while { True }
    changes.receive
    emit-current()

// The route the current hash denotes (a convenience for `init`).
pub fun current-route<route>( parse : (string) -> route ) : ioc route
  parse( hash-path( current-hash() ) )

// A link to a route: `link(route, print, child)` lowers to a real anchor on
// the web (href "#/<path>") and a click-to-navigate target on native. This is
// sugar over `ui/widget/link` that takes the typed route + its printer.
pub fun route/link<msg,route>( route : route, print : (route) -> string, child : widget<msg>, ?key : key ) : widget<msg>
  widget/link(print(route), child)
