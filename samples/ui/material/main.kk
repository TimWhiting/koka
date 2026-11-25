// A Material 3 demo on the unified ui framework: the SAME widget<msg> code runs
// on wasi-web, jsweb, and native Impeller. It swaps `ui/style/default` for
// `ui/style/material` -- the button CALL SHAPE is unchanged, only the design
// language (M3 filled / tonal / elevated / text, fully-rounded, M3 palette) and
// the ambient `theme` differ. Proves the style library is a drop-in layer.
module main

import ui/widget
import ui/style/material
import ui/style/default/system   // system-dark() (host OS light/dark)
import ui/state     // set-time-dilation (the slow-motion knob below)
import ui/app

struct model( count : int, night : bool )

type msg
  Inc
  Dec
  Reset
  Toggle

fun themed-view( m : model , key : key) : <keytree,uistate,ioc,theme> widget<msg>
  val counter = row([
    filled-tonal-button("−", Dec),
    spacer(),
    text(m.count.show, 40.0, theme.on-background),
    spacer(),
    filled-button("+", Inc)
  ])
  val actions = row([
    text-button("Reset", Reset),
    spacer(),
    elevated-button(if m.night then "Light theme" else "Dark theme", Toggle)
  ])
  // intrinsic-width: the card hugs its widest row's NATURAL width; the
  // spacer-rows then spread within it (positioning, not sizing)
  val card = box( intrinsic-width(column([counter, actions], gap = 16.0)),
                  padding = 20.0, bg = Just(Fill(theme.surface-container, 16.0)) )
  // the × takes a full spin on every theme switch (paint-only rotation; it
  // passes through + at the quarter turns)
  val spin = animate(if m.night then 360.0 else 0.0, duration = 450.0, ease = ease-in-out)
  val title = row([ text("Koka", 24.0, theme.on-background),
                    rotated(text("×", 24.0, theme.primary), spin),
                    text("Material 3", 24.0, theme.on-background) ], gap = 7.0)
  box( center( column([ title, card ], gap = 20.0 ) ),
       padding = 24.0, bg = Just(Fill(theme.background)) )

fun view( m : model , key : key) : <keytree,uistate,ioc> widget<msg>
  // whole-theme crossfade: one animated t interpolates the ENTIRE scheme, so
  // background, surfaces, text, and buttons all ease together (the buttons'
  // own 110ms color animation just chases the moving target and settles)
  val t = animate(if m.night then 1.0 else 0.0, duration = 500.0)
  with val theme = theme/light.mix(theme/dark, t)
  themed-view(m, key)

fun update( m : model, msg : msg ) : model
  match msg
    Inc    -> m(count = m.count + 1)
    Dec    -> m(count = m.count - 1)
    Reset  -> m(count = 0)
    Toggle -> m(night = m.night.not)

pub fun main()
  val d = system-dark()
  // SLOW MOTION: the ink ripple is ~400ms, which is right to use and too fast
  // to inspect. Raise this to watch the splash grow and fade -- 8.0 stretches
  // it to a few seconds. It scales time, not the frame rate, so the motion
  // stays smooth; put it back to 1.0 to feel the real thing.
  set-time-dilation(1.0)
  app( Model(0, d), view, update, App-config("Koka × Material 3", 420, 320) )
