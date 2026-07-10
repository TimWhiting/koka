/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Pure virtual-dom data for the Koka web framework: `html<msg>` trees whose
// event handlers are *message values* (or value-carrying message functions),
// never raw callbacks. See docs/superpowers/specs/2026-07-09-koka-web-framework-design.md.
module web-ui/html

import std/core/undiv
import web-ui/dom

// An attribute of a virtual node. Handlers carry messages, not closures:
// the runtime routes every DOM event into the app's single message channel.
pub type attr<a>
  Attr( name : string, value : string )
  On( event : string, msg : a )              // e.g. on("click", Increment)
  OnValue( event : string, to-msg : string -> a )         // element value read at fire time
  OnEvent( event : string, to-msg : event -> ioc a )  // payload read at fire time
  OnDo( event : string, action : () -> ioc () )  // run a thunk directly (no message; used by ui/state)
  OnValueDo( event : string, action : string -> ioc () )  // element value -> thunk (uncontrolled fields writing ui/state)
  OnEnterValue( to-msg : string -> a )       // keydown filtered to Enter, with the element's CURRENT value (field commit)
  Key( key : string )                        // identity for keyed reconciliation
  NoAttr                                     // conditional helpers (disabled(False), ...)

// A virtual DOM tree, pure data produced by `view`.
pub type html<a>
  Elem( tag : string, attrs : list<attr<a>>, children : list<html<a>> )
  Text( text : string )

// ----------------------------------------------------------------
// Smart constructors: `view` code reads like markup.

pub fun elem<msg>( tag : string, attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  Elem(tag, attrs, children)

pub fun text<msg>( s : string ) : html<msg>
  Text(s)

pub fun attr<msg>( name : string, value : string ) : attr<msg>
  Attr(name, value)

pub fun on<msg>( event : string, msg : msg ) : attr<msg>
  On(event, msg)

pub fun on-click<msg>( msg : msg ) : attr<msg>
  On("click", msg)

// run a thunk directly on an event (no message flows through the app channel);
// the runtime's own callback for framework side-effects such as ui/state writes
pub fun on-do<msg>( event : string, action : () -> ioc () ) : attr<msg>
  OnDo(event, action)

// element value on an event, into a thunk (no message) -- uncontrolled fields
pub fun on-value-do<msg>( event : string, action : string -> ioc () ) : attr<msg>
  OnValueDo(event, action)

pub fun on-double-click<msg>( msg : msg ) : attr<msg>
  On("dblclick", msg)

pub fun on-blur<msg>( msg : msg ) : attr<msg>
  On("blur", msg)

pub fun on-focus<msg>( msg : msg ) : attr<msg>
  On("focus", msg)

// element value on every keystroke (for controlled inputs)
pub fun on-input<msg>( to-msg : string -> msg ) : attr<msg>
  OnValue("input", to-msg)

// element value when editing commits (checkboxes, selects, blur of a text input)
pub fun on-change<msg>( to-msg : string -> msg ) : attr<msg>
  OnValue("change", to-msg)

// an event handler whose message is built from the live event's payload
pub fun on-event<msg>( event : string, to-msg : event -> ioc msg ) : attr<msg>
  OnEvent(event, to-msg)

// keydown with the key name ("Enter", "a", "ArrowUp", ...) in the message
pub fun on-key<msg>( to-msg : string -> msg ) : attr<msg>
  OnEvent("keydown", fn(ev) to-msg(ev.key))

// Enter pressed in an input: the message carries the input's CURRENT value
// (an uncontrolled field's commit -- the model never saw the keystrokes)
pub fun on-enter-value<msg>( to-msg : string -> msg ) : attr<msg>
  OnEnterValue(to-msg)

// click with the pointer position (client coordinates) in the message
pub fun on-click-at<msg>( to-msg : (float64, float64) -> msg ) : attr<msg>
  OnEvent("click", fn(ev) to-msg(ev.client-x, ev.client-y))

// ---- drag & drop (declarative; see the host page for the mechanics) ----
// Mark an element draggable, carrying `data` as its drag payload: on
// dragstart the HOST fills dataTransfer from this attribute -- no imperative
// setData call ever appears in Koka code.
pub fun draggable<msg>( data : string ) : list<attr<msg>>
  [Attr("draggable","true"), Attr("data-drag", data)]

// A drop target: the message is built from the dragged payload (the
// dataTransfer text the source's `draggable` attribute declared).
// Registering a drop listener makes the host auto-allow dragover.
pub fun on-drop<msg>( to-msg : string -> msg ) : attr<msg>
  OnEvent("drop", fn(ev) to-msg(ev.drag-data))

pub fun key<msg>( k : string ) : attr<msg>
  Key(k)

// ----------------------------------------------------------------
// common attributes. Names that could clash with keywords, fields, or
// element helpers get a trailing underscore (`class_`, `id_`, `type_`,
// `for_`, `title_`); the rest read plainly.

pub fun id_<msg>( v : string ) : attr<msg>
  Attr("id", v)

// the element's live value (kept in sync by the patcher: controlled inputs)
pub fun value<msg>( v : string ) : attr<msg>
  Attr("value", v)

pub fun placeholder<msg>( s : string ) : attr<msg>
  Attr("placeholder", s)

pub fun style<msg>( css : string ) : attr<msg>
  Attr("style", css)

pub fun type_<msg>( t : string ) : attr<msg>
  Attr("type", t)

pub fun name_<msg>( n : string ) : attr<msg>
  Attr("name", n)

pub fun for_<msg>( target-id : string ) : attr<msg>
  Attr("for", target-id)

pub fun title_<msg>( tip : string ) : attr<msg>
  Attr("title", tip)

pub fun src<msg>( url : string ) : attr<msg>
  Attr("src", url)

pub fun alt<msg>( s : string ) : attr<msg>
  Attr("alt", s)

// boolean attributes: present when true, absent when false (the patcher
// also syncs the live property so form controls follow the model)
pub fun disabled<msg>( b : bool ) : attr<msg>
  if b then Attr("disabled","") else NoAttr

pub fun checked<msg>( b : bool ) : attr<msg>
  if b then Attr("checked","") else NoAttr

pub fun selected<msg>( b : bool ) : attr<msg>
  if b then Attr("selected","") else NoAttr

pub fun autofocus<msg>( b : bool = True ) : attr<msg>
  if b then Attr("autofocus","") else NoAttr

// conditional class list: `classes([("item",True),("done",it.done)])`
pub fun classes<msg>( cs : list<(string,bool)> ) : attr<msg>
  Attr("class", cs.filter(snd).map(fst).join(" "))

// common elements
pub fun div<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("div", attrs, children)

pub fun span<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("span", attrs, children)

pub fun button<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("button", attrs, children)

pub fun input<msg>( attrs : list<attr<msg>> = [] ) : html<msg>
  elem("input", attrs, [])

pub fun ul<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("ul", attrs, children)

pub fun li<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("li", attrs, children)

pub fun h1<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("h1", attrs, children)

pub fun h2<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("h2", attrs, children)

pub fun p<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("p", attrs, children)

pub fun nav<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("nav", attrs, children)

pub fun section<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("section", attrs, children)

pub fun header<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("header", attrs, children)

pub fun footer<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("footer", attrs, children)

pub fun ol<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("ol", attrs, children)

pub fun label<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("label", attrs, children)

pub fun form<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("form", attrs, children)

pub fun select<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("select", attrs, children)

pub fun option<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("option", attrs, children)

pub fun textarea<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("textarea", attrs, children)

pub fun strong<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("strong", attrs, children)

pub fun em<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("em", attrs, children)

pub fun pre<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("pre", attrs, children)

pub fun code<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("code", attrs, children)

pub fun small<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("small", attrs, children)

pub fun img<msg>( attrs : list<attr<msg>> = [] ) : html<msg>
  elem("img", attrs, [])

pub fun br<msg>() : html<msg>
  elem("br", [], [])

pub fun hr<msg>() : html<msg>
  elem("hr", [], [])

pub fun table<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("table", attrs, children)

pub fun thead<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("thead", attrs, children)

pub fun tbody<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("tbody", attrs, children)

pub fun tr<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("tr", attrs, children)

pub fun td<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("td", attrs, children)

pub fun th<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("th", attrs, children)

// `anchor` not `a`: avoids visual confusion with type variables in this file.
pub fun anchor<msg>( attrs : list<attr<msg>> = [], children : list<html<msg>> = [] ) : html<msg>
  elem("a", attrs, children)

pub fun class_<msg>( name : string ) : attr<msg>
  Attr("class", name)

pub fun href<msg>( url : string ) : attr<msg>
  Attr("href", url)

// ----------------------------------------------------------------
// `html` is a functor: components own a *closed* msg type and parents embed
// them with `map-msg`, keeping per-component match exhaustiveness.

pub fun attr/map-msg<a,b>( at : attr<a>, f : a -> b ) : attr<b>
  match at
    Attr(n,v)     -> Attr(n,v)
    On(ev,m)      -> On(ev, f(m))
    OnValue(ev,g) -> OnValue(ev, fn(s) f(g(s)) )
    OnValueDo(ev,a) -> OnValueDo(ev, a)
    OnEnterValue(g) -> OnEnterValue( fn(s) f(g(s)) )
    OnEvent(ev,g) -> OnEvent(ev, fn(e) f(g(e)) )
    OnDo(ev,act)  -> OnDo(ev, act)        // no message: unchanged under map-msg
    Key(k)        -> Key(k)
    NoAttr        -> NoAttr

pub fun html/map-msg<a,b>( h : html<a>, f : a -> b ) : html<b>
  match h
    Text(s) -> Text(s)
    Elem(tag, attrs, kids) ->
      Elem(tag, attrs.map(fn(at) at.map-msg(f)),
           kids.map(fn(k) k.pretend-decreasing.map-msg(f)))

// The key of a node, if it has one (for keyed reconciliation).
pub fun node-key<msg>( h : html<msg> ) : maybe<string>
  match h
    Elem(_, attrs, _) -> attrs.key-of
    Text(_) -> Nothing

pub fun key-of<msg>( attrs : list<attr<msg>> ) : maybe<string>
  match attrs
    Nil -> Nothing
    Cons(Key(k), _) -> Just(k)
    Cons(_, rest) -> rest.key-of
