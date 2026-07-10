# windows

Native multi-window: `window(...)` tears off a real second OS window;
`overlay(..., chrome = Panel, ...)` floats a borderless tooltip anchored to a
keyed region. `koka -e build.kk -- native` then `./app-native`.

To eyeball on native:

- Click "Open inspector": a second, real titled window appears (not an
  in-window layer). Click "Bump" in EITHER window -- the count updates in
  both, proving they share the one model/msg.
- Close the inspector via its native titlebar close button (not just the
  in-app "Close inspector" button) and confirm `on-dismiss` fires: the main
  window's button reverts to "Open inspector".
- Click "Show tip": a small borderless panel appears below the "hover target"
  label. Drag the MAIN window around the screen -- the panel follows it and
  can visibly extend past the main window's own edges (it is not clipped to
  it), showing the Panel chrome escapes the parent bounds.
- On jsweb/wasi-web the same sample degrades to in-window layers (no real OS
  window support there) -- same model/view/update code, no branching needed.
