// Explanation: one core, three backends.
module pages/explanation

import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/widget
import ui/style/default
import blocks

pub fun expl-backends-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("The web backend (jsweb and wasi-web) lowers the laid-out tree "
          ++ "to absolutely-positioned DOM; the native backend paints it "
          ++ "with Impeller. "
          ++ "Text measurement — the one thing layout can't do without "
          ++ "asking a backend how wide a string actually is — is an "
          ++ "ambient effect each backend installs beneath layout, rather "
          ++ "than layout hard-coding one backend's font metrics. That's "
          ++ "the seam: the layout pass calls the same effect either "
          ++ "way, and never branches on which backend is running.") ]

pub fun expl-style-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("The core only knows typed colors, not a design system — style "
          ++ "lives behind one ambient `theme` effect that components "
          ++ "read from, instead of being threaded as a parameter through "
          ++ "every call. `ui/style/default` and `ui/style/material` "
          ++ "(Material 3) each install a different `theme`: same "
          ++ "component names, same call shapes, different palette and "
          ++ "shapes underneath.") ]

pub fun expl-state-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("Hover, press, expand/collapse, and animation are EPHEMERAL, not "
          ++ "app state. ui/state keeps them keyed by widget identity, so "
          ++ "a component owns its transient UI without the app model "
          ++ "needing to track it — which is how the live counters "
          ++ "scattered across this site work.") ]

pub fun expl-reconcile-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("Re-renders reconcile the new tree against the retained one, "
          ++ "reusing node cells in place (a technique called FBIP — "
          ++ "functional but in place) wherever the new tree's shape "
          ++ "lines up with the old one, instead of discarding everything "
          ++ "and rebuilding from scratch.") ]
