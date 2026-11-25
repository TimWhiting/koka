// The todos page as a self-contained COMPONENT: its own closed msg type,
// model, and pure update -- the parent embeds it with `map-msg(view,
// TodosMsg)`. Exercises text input (controlled value + Enter-to-add),
// identity-addressed list rows (`idx(i)`), and drag-to-reorder -- all
// portable widgets.
module todos

import std/num/float64
import ui/widget
import ui/style/default
import ui/app

pub type msg
  SetInput( s : string )
  Add
  AddText( label : string )   // from the UNCONTROLLED field (value read at click/enter time)
  Toggle( id : int )
  Delete( id : int )
  Reverse
  KeyPressed( key : string )
  DropOn( dragged : string, target : int )

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

fun item-view( it : item, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  box(row([
        body(it.label),
        spacer(),
        quiet-button(if it.done then "undo" else "done", Toggle(it.item/id)),
        quiet-button("x", Delete(it.item/id))
      ]),
      padding = 8.0,
      bg = Just(Fill(theme.palette/surface, 6.0)),
      drag = Just(it.item/id.show),
      on-drop = Just(fn(payload) DropOn(payload, it.item/id)))

pub fun view( m : model, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  val header = row([
    text-input(m.input, SetInput, placeholder = "what needs doing?",
               on-key = Just(KeyPressed)),
    primary-button("add", Add),
    quiet-button("reverse", Reverse)
  ])
  // the UNCONTROLLED twin: keystrokes never touch the model -- the value lives
  // in ui/state under the field's identity. The app hears about it exactly
  // twice: Enter commits, and the submit button READS it at click time
  // (`act-msg` computes the message from ui/state) and clears it.
  val fk = field-key("quick-add")
  fun submit() : <uistate,ioc> msg             // read the field AT CLICK TIME, then clear it
    val label = field-text(fk)
    set-field-text(fk, "")
    AddText(label)
  val header2 = row([
    field("quick-add", placeholder = "uncontrolled: model never sees keystrokes",
          width = 300.0, on-enter = Just(AddText)),
    // NOTE: act-msg's child must not be clickable itself (an inner target would
    // win the hit) -- a plain styled box, not a button
    act-msg( box( text("add²", 15.0, theme.fg), padding = 9.0,
                  bg = Just(Fill(theme.surface, 6.0)) ), submit )
  ])
  val item-list = if m.items.is-nil
    then body("nothing yet — type above and press Enter")
    else column(m.items.map-indexed(fn(i, it) item-view(it, idx(i))), gap = 6.0)
  val count = accented(m.items.filter(fn(it) it.done).length.show
                       ++ "/" ++ m.items.length.show ++ " done")
  page("todos", [header, header2, item-list, count])

pub fun update( m : model, msg : msg ) : model
  match msg
    SetInput(s) -> m(input = s)
    Add -> m.add-item
    AddText(label) ->
      if label.is-empty then m
      else Model(m.input, m.next-id + 1, m.items ++ [Item(m.next-id, False, label)])
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
