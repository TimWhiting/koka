/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The todos page as a self-contained COMPONENT: its own closed msg type
// (exhaustively matched), its own model, pure update -- the parent embeds it
// with `map-msg(view, TodosMsg)` (see main.kk). Exercises element
// creation/removal (externref slot churn), JS→Koka strings (the input's
// value), and listener lifecycle via the patcher.
module todos

import web-ui/html
import web-ui/app
import web-ui/theme
import web-ui/ui

// messages: a closed type — the compiler checks `update` covers every case.
pub type msg
  SetInput( s : string )
  Add
  Toggle( id : int )
  Delete( id : int )
  Reverse
  KeyPressed( key : string )
  DropOn( dragged : string, target : int )   // dragged id (payload) onto target row

pub struct item( id : int, done : bool, label : string )

pub struct model( input : string, next-id : int, items : list<item> )

pub fun init() : model
  Model("", 1, [])

fun move-before( items : list<item>, dragged : int, target : int ) : list<item>
  if dragged == target then items else
    match items.filter(fn(it) it.item/id == dragged)
      Nil -> items
      Cons(d, _) ->
        items.filter(fn(it) it.item/id != dragged).flatmap fn(it)
          if it.item/id == target then [d, it] else [it]

pub fun view( m : model ) : <keytree,theme> html<msg>
  page("Todos", [div([class_("todo")], [column([], [
    row([], [
      text-input([id_("new"), value(m.input), placeholder("What needs doing?"),
                  on-input(SetInput), on-key(KeyPressed)]),
      primary-button([id_("add"), on-click(Add)], [text("Add")]),
      quiet-button([id_("reverse"), title_("reverse the list order"), on-click(Reverse)],
                   [text("Reverse")])
    ]),
    if m.items.is-nil
      then p([class_("empty")], [text("Nothing here yet — type above and press Enter to add your first item.")])
      else ul([id_("items"), style("list-style:none;margin:0;padding:0;display:flex;"
                                   ++ "flex-direction:column;gap:8px")],
              m.items.map(item-view)),
    div([id_("count"), accent-style()],
        [text(m.items.filter(fn(it) it.done).length.show ++ "/" ++ m.items.length.show ++ " done")])
  ])])])

fun item-view( it : item ) : theme html<msg>
  li([key(it.item/id.show), classes([("done", it.done), ("todo", !it.done)]),
      surface-style("border-radius:6px;padding:6px 10px;display:flex;"
                    ++ "align-items:center;gap:10px"),
      title_("drag to reorder"),
      on-drop(fn(payload) DropOn(payload, it.item/id))]
     ++ draggable(it.item/id.show), [
    span([style("flex:1")], [text(it.label)]),
    quiet-button([class_("toggle"), title_(if it.done then "mark as not done" else "mark as done"),
                  on-click(Toggle(it.item/id))],
                 [text(if it.done then "Undo" else "Done")]),
    quiet-button([class_("delete"), title_("delete this item"), on-click(Delete(it.item/id))],
                 [text("✕")])
  ])

pub fun update( m : model, msg : msg ) : model
  match msg
    SetInput(s) -> m(input = s)
    Add -> m.add-item
    Toggle(id) ->
      m(items = m.items.map(fn(it) if it.item/id == id then it(done = !it.done) else it))
    Delete(id) ->
      m(items = m.items.filter(fn(it) it.item/id != id))
    Reverse ->
      m(items = m.items.reverse)
    KeyPressed(k) ->
      if k == "Enter" then m.add-item else m
    DropOn(dragged, target) ->
      m(items = m.items.move-before(dragged.parse-int.default(-1), target))

fun add-item( m : model ) : model
  if m.input.is-empty then m
  else Model("", m.next-id + 1, m.items ++ [Item(m.next-id, False, m.input)])

