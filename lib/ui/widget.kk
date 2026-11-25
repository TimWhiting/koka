/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The portable widget vocabulary and its layout: `view : model -> widget<msg>`
// builds pure data (handlers are message values, never callbacks); layout
// runs constraints-down/sizes-up with the parent positioning its children
// (Flutter-style). Text is measured through the ambient `measure` effect,
// whose handler each backend installs -- so the SAME layout pass runs on
// every backend (web lowers the laid-out tree to absolutely-positioned DOM,
// native paints it with Impeller).
module ui/widget

import std/num/float64
import std/num/int32
import std/core/undiv
import ui/ident
import std/core/unsafe   // unsafe-ptr-eq: the memo reconcile short-circuit
import ui/reactive   // the uistate effect: click thunks (`act`/`act-msg`) write ephemeral state    // the ambient `?key` widget identity (for scroll-region identity)
import ui/keytrie  // segments + keytree effect (scroll-region ids are trie-derived)
import ui/anchor   // alignment + anchored placement (for `positioned`)
import ui/transform   // mat4 (row-major 4x4) for `transform3d`
pub import ui/image   // `image-fit` -- its own module (Fill would clash with `fill`'s ctor here); re-exported so `import ui/widget` alone reaches Contain/Cover/Fill/ImgNone

// ----------------------------------------------------------------
// colors (backend-neutral)

// an sRGB color (components 0.0 to 1.0)
pub value struct color( r : float64, g : float64, b : float64, a : float64 = 1.0 )

pub fun rgb( r : float64, g : float64, b : float64 ) : color
  Color(r, g, b)

// componentwise equality / linear interpolation (alpha included) -- the
// primitives theme crossfades and color animation build on
pub fun color/same( x : color, y : color ) : bool
  x.r == y.r && x.g == y.g && x.b == y.b && x.a == y.a

// black or white, whichever will actually be seen against `c` -- for an ink
// splash on a surface whose own foreground colour is not to hand. Rec. 601
// luma, thresholded a little above the midpoint because a splash is drawn at
// low opacity and needs the darker choice on genuinely mid-tone surfaces.
pub fun color/contrasting( c : color ) : color
  val luma = 0.299 * c.r + 0.587 * c.g + 0.114 * c.b
  if luma < 0.6 then Color(1.0, 1.0, 1.0) else Color(0.0, 0.0, 0.0)

pub fun color/mix( x : color, y : color, t : float64 ) : color
  Color(x.r + (y.r - x.r) * t, x.g + (y.g - x.g) * t,
        x.b + (y.b - x.b) * t, x.a + (y.a - x.a) * t)

// css encoding (used by the web lowering)
pub fun to-css( c : color ) : string
  fun chan(x : float64) : string
    (x.max(0.0).min(1.0) * 255.0).int.show
  "rgba(" ++ chan(c.r) ++ "," ++ chan(c.g) ++ "," ++ chan(c.b) ++ "," ++ c.a.show ++ ")"

// a rounded background fill for a box
// What actually fills a surface, beyond a flat colour. Every case here is a
// native primitive on BOTH backends -- an Impeller `ColorSource` and a CSS
// `background` -- so none of it is emulated on either side.
//
// Geometry is given as FRACTIONS of the box being filled: (0,0) is its
// top-left, (1,1) its bottom-right. One source then describes a button and a
// full-bleed header without knowing either size, and each backend resolves the
// fractions the way it wants -- Impeller wants absolute points, CSS wants an
// angle or a position.
//
// Gradients are TWO-STOP for now: it covers what UI actually asks for, and N
// stops need array marshalling across the C ABI that nothing needs yet.
pub type paint-source
  // a linear gradient from (fx,fy) to (tx,ty)
  SLinear( fx : float64, fy : float64, tx : float64, ty : float64,
           from-color : color, to-color : color )
  // a radial gradient centred at (cx,cy), reaching `radius` (a fraction of the
  // box's WIDTH, so a circle stays a circle whatever the box's aspect)
  SRadial( cx : float64, cy : float64, radius : float64,
           inner-color : color, outer-color : color )
  // an image painted across the box, scaled by `fit`. The same `src` an
  // `image` widget takes; the backends resolve it the same way (an `<img>`
  // URL on web, the identity-cached decode+upload natively) so a surface
  // textured this way costs no more than the same picture drawn as a widget.
  SImage( src : string, fit : image-fit = Cover )

// A surface fill: a solid colour, optionally overridden by a `source`, with
// rounded corners. `source` is an extra FIELD rather than a `fill` variant so
// that every existing `Fill(colour, radius)` keeps working unchanged; the
// colour stays the fallback any backend or test that ignores sources renders.
pub struct fill( color : color, radius : float64 = 0.0,
                 source : maybe<paint-source> = Nothing )

// multiply a color's channels (clamped) -- the native hover/press affordance,
// mirroring the web CSS `filter: brightness(...)`
pub fun brighten( c : color, factor : float64 ) : color
  Color((c.r * factor).min(1.0), (c.g * factor).min(1.0), (c.b * factor).min(1.0), c.a)

// ----------------------------------------------------------------
// typography (backend-neutral)

// A font: a family stack (system / web-safe names), a pixel size, a CSS
// weight (100..900, 400 = normal, 700 = bold) and an italic flag. Backends
// realize it their own way -- web builds a CSS `font` shorthand, native sets
// the Impeller family / size / weight / style. Family strings are arbitrary,
// so any installed system or web-safe face works; custom font-file loading is
// a later addition (see the framework readme).
pub struct font( family : string, size : float64, weight : int = 400, italic : bool = False )

// system font stacks (the three every platform ships)
pub fun sans( size : float64 = 15.0 ) : font
  Font("system-ui, -apple-system, Segoe UI, Roboto, sans-serif", size)
pub fun serif( size : float64 = 15.0 ) : font
  Font("Georgia, 'Times New Roman', serif", size)
pub fun mono( size : float64 = 14.0 ) : font
  Font("ui-monospace, SFMono-Regular, Menlo, Consolas, monospace", size)

// a font from an explicit family stack
pub fun font( family : string, size : float64 = 15.0, weight : int = 400, italic : bool = False ) : font
  Font(family, size, weight, italic)

// a bolded copy of a font
pub fun bold( f : font ) : font
  f(weight = 700)

// the CSS `font` shorthand for a font: "[italic ]<weight> <size>px <family>"
pub fun css-font( f : font ) : string
  (if f.italic then "italic " else "") ++ f.weight.show ++ " " ++ f.size.show ++ "px " ++ f.family

// application configuration; each backend reads what it needs (web: root-id
// and the fixed canvas size; native: window title and size)
pub struct app-config( title : string = "Koka UI", width : int = 480, height : int = 360,
                       root-id : string = "app" )

// ----------------------------------------------------------------
// build: widgets are pure data

// pointer input for a box, GROUPED so the box signature stays small and new
// events don't proliferate a field across every tree match (see
// docs/ui-api-audit.md). `click`/`click-at` are the LEFT button; `context-at` is
// the RIGHT button (with position); `drag`/`drop` are drag-and-drop.
pub struct pointer<a>
  click      : maybe<a> = Nothing
  click-at   : maybe<(float64, float64) -> a> = Nothing
  context-at : maybe<(float64, float64) -> a> = Nothing
  drag       : maybe<string> = Nothing
  drop       : maybe<string -> a> = Nothing

// `owner` (first field of every ctor) is the ambient key identity when the
// widget was CONSTRUCTED (stamped by the smart constructor under the keytree
// effect). It is copied verbatim by `layout` onto the produced ltree node and
// read only by the owner-geometry queries (`owner-rect`/`owner-texts`); it is
// inert to layout/paint/hit. See docs/superpowers/specs owner-identity-design.
pub type widget<a>
  Text( owner : int32, content : string, font : font, wrap : bool, color : color )
  Rich( owner : int32, content : string, base-font : font, base-color : color,
        spans : list<text-span<a>>, wrap : bool )
  WBox( owner : int32, pad : float64, bg : maybe<fill>, on : pointer<a>, child : widget<a> )
  Flex( owner : int32, horizontal : bool, gap : float64, fill : bool, children : list<widget<a>> )
  Spacer( owner : int32 )
  Expanded( owner : int32, flex : float64, child : widget<a> )             // grow to share the flex parent's leftover main-axis space
  Stack( owner : int32, children : list<(float64, float64, widget<a>)> )   // absolute placement
  Link( owner : int32, to : string, child : widget<a> )                    // navigate to a route path on click
  Scroll( owner : int32, key : int, horizontal : bool, child : widget<a> )  // scrollable viewport (key = call-site id for the offset); horizontal scrolls along x (content unwrapped) instead of y
  Center( owner : int32, max-width : float64, child : widget<a> )          // self-sizing child capped at max-width; centered when stretched
  IntrinsicWidth( owner : int32, child : widget<a> )                       // width = the child's NATURAL width (growers collapsed), then laid out tight at it
  Rotated( owner : int32, degrees : float64, child : widget<a> )           // paint-only rotation about the child's center; layout/hit unrotated
  Overlaid( owner : int32, child : widget<a> )                             // paint `child` at its NATURAL size while reporting NO size to layout and taking NO input: a decoration (an ink splash) that must not resize or block what it decorates
  Clipped( owner : int32, radius : float64, w : maybe<float64>, h : maybe<float64>, child : widget<a> )   // clip the child to this node's rounded rect (paint AND hit); w/h pin the clip's extent independently of the child's measured size (Nothing = take the child's), so an oversize child overflows INTO the clip and is cut instead of growing it
  Transform3d( owner : int32, m : mat4, child : widget<a> )                // paint-only 4x4 (perspective/tilt) about the child's center; layout unchanged, hit APPROXIMATE (untransformed) until task 3's unproject
  Fixed( owner : int32, w : maybe<float64>, h : maybe<float64>, child : widget<a> )  // pin an axis's extent regardless of the child's measured size (Nothing falls back to the child's own extent on that axis); the child is laid out CAPPED at the fixed extent but NOT clipped, so an oversize child overflows visually at its own spot without perturbing this node's reported size -- the tool for a caller (e.g. `ui/lazy`) that needs a row's geometry to be exact by construction
  Memo( owner : int32, mid : int, child : widget<a> )                      // memo boundary: reconcile skips relayout when `child` is the SAME cached pointer
  Positioned( owner : int32, target : maybe<(float64,float64,float64,float64)>, target-align : alignment, self-align : alignment, offset-x : float64, offset-y : float64, max-width : float64, max-height : float64, absorb : bool, child : widget<a> )  // a full-viewport layer with `child` anchored (target = Nothing means the viewport); the child is self-sized within max-width/max-height; `absorb` swallows clicks that land ON the content but hit no handler (so a modal body / menu padding does not fall through to a dismiss scrim), while clicks outside the content still fall through
  Act( owner : int32, onact : () -> <uistate,ioc> (), child : widget<a> )            // run a thunk on click (ui/state writes; no msg)
  Interactive( owner : int32, key : int, onclick : maybe<a>, slop : float64, child : widget<a> )  // click + hover/press by key; `slop` expands the hit area (layout-neutral)
  TextInput( owner : int32, key : int, value : string, placeholder : string, width : float64,
             oninput : string -> a, onkey : maybe<string -> a> )
  TextField( owner : int32, key : int, placeholder : string, width : float64, onenter : maybe<string -> a> )  // UNCONTROLLED: value lives in ui/state under `key`
  ActMsg( owner : int32, child : widget<a>, to-msg : () -> <uistate,ioc> a )         // click computes a msg from ui/state (form submit)
  Slider( owner : int32, lo : float64, hi : float64, step : float64, value : float64,
          width : float64, onchange : float64 -> a )
  SizedBox( owner : int32, w : float64, h : float64, bg : maybe<fill>, onclick : maybe<a> )
  Image( owner : int32, src : string, fit : image-fit, w : float64, h : float64 )   // a picture from a path/URL; web decodes via `<img>`, native decodes+uploads a texture (task 5) -- the box exists before pixels

pub val default-fg : color = Color(0.9, 0.9, 0.94)

// single-line text (clips if it overflows). Overloaded by the second
// argument: `text(s, 18.0)` picks the size (system sans), `text(s, mono(14.0))`
// picks a whole font.
pub fun size/text<msg>( content : string, size : float64 = 15.0, color : color = default-fg, ?key : key ) : widget<msg>
  Text(?key.key-id.int32, content, sans(size), False, color)

pub fun font/text<msg>( content : string, font : font, color : color = default-fg, ?key : key ) : widget<msg>
  Text(?key.key-id.int32, content, font, False, color)

// multi-line text that wraps to the available width. Same size/font overload.
pub fun size/paragraph<msg>( content : string, size : float64 = 15.0, color : color = default-fg, ?key : key ) : widget<msg>
  Text(?key.key-id.int32, content, sans(size), True, color)

pub fun font/paragraph<msg>( content : string, font : font, color : color = default-fg, ?key : key ) : widget<msg>
  Text(?key.key-id.int32, content, font, True, color)

// single-line monospaced text (inline code / identifiers)
pub fun code<msg>( content : string, size : float64 = 14.0, color : color = default-fg, ?key : key ) : widget<msg>
  Text(?key.key-id.int32, content, mono(size), False, color)

// a styled sub-range of a `rich` widget's content, by CODEPOINT offset
// (the same convention `.count`/`.pad-right` use elsewhere -- not grapheme
// clusters; combining marks/emoji sequences can misalign) -- `Nothing`
// on `font`/`color` inherits the base style; `on-click` makes just this
// span a click target, resolved by `hit-go`'s `LRich` case below even
// when the span's text wraps across a line break (its resolved rects,
// plural, come from `measure-rich`).
pub struct text-span<a>
  start    : int
  end      : int
  font     : maybe<font> = Nothing
  color    : maybe<color> = Nothing
  on-click : maybe<a> = Nothing

// text that carries multiple styled/clickable sub-ranges ("spans"),
// flowing and wrapping as ONE unit (inline code spans in prose, later
// syntax highlighting). Same size/font overload as `text`/`paragraph`.
pub fun size/rich<a>( content : string, size : float64 = 15.0, color : color = default-fg,
                      spans : list<text-span<a>> = [], wrap : bool = True, ?key : key ) : widget<a>
  Rich(?key.key-id.int32, content, sans(size), color, spans, wrap)

pub fun font/rich<a>( content : string, font : font, color : color = default-fg,
                      spans : list<text-span<a>> = [], wrap : bool = True, ?key : key ) : widget<a>
  Rich(?key.key-id.int32, content, font, color, spans, wrap)

// children on a padded surface; `bg` fills with rounded corners; `on-click`
// makes the box a LEFT-click target; `on-click-at` also carries the position;
// `on-context-at` is the RIGHT-click (context menu) target; `drag` marks a drag
// source with a payload; `on-drop` accepts payloads. The flat params here bundle
// into one `pointer` field on the box (see docs/ui-api-audit.md).
pub fun box<msg>( child : widget<msg>, padding : float64 = 0.0,
                  bg : maybe<fill> = Nothing,
                  on-click : maybe<msg> = Nothing,
                  on-click-at : maybe<(float64, float64) -> msg> = Nothing,
                  on-context-at : maybe<(float64, float64) -> msg> = Nothing,
                  drag : maybe<string> = Nothing,
                  on-drop : maybe<string -> msg> = Nothing, ?key : key ) : widget<msg>
  WBox(?key.key-id.int32, padding, bg, Pointer(on-click, on-click-at, on-context-at, drag, on-drop), child)

// `fill`: stretch across the parent's cross axis (so cross-centered children
// sit at fixed offsets regardless of how a sibling's size reflows)
pub fun row<msg>( children : list<widget<msg>>, gap : float64 = 10.0, fill : bool = False, ?key : key ) : widget<msg>
  Flex(?key.key-id.int32, True, gap, fill, children)

pub fun column<msg>( children : list<widget<msg>>, gap : float64 = 12.0, fill : bool = False, ?key : key ) : widget<msg>
  Flex(?key.key-id.int32, False, gap, fill, children)

// greedily takes the remaining main-axis space of its flex parent
pub fun spacer<msg>( ?key : key ) : widget<msg>
  Spacer(?key.key-id.int32)

// grow to fill the flex parent's LEFTOVER main-axis space (Flutter's Expanded):
// rigid siblings are laid out first, then each `expanded` child gets a share of
// what remains, proportional to `flex`. Its main-axis extent is tightened to
// that share, so `expanded(scroll(list))` in a column gives the scroll region
// exactly the height left after the fixed rows -- the prerequisite for a
// bounded scroll viewport. Multiple `expanded`s split the leftover by weight.
pub fun expanded<msg>( child : widget<msg>, flex : float64 = 1.0, ?key : key ) : widget<msg>
  Expanded(?key.key-id.int32, flex, child)

// children at absolute offsets within the space given by the parent
pub fun stack<msg>( children : list<(float64, float64, widget<msg>)>, ?key : key ) : widget<msg>
  Stack(?key.key-id.int32, children)

// a link to a route path (the hash path, no leading '#'). On the web it lowers
// to a real `<a href="#/...">` (right-click / open-in-new-tab / deep-link all
// work); natively it is a click target the router turns into a navigation.
// The href/click is wired by the backend against `ui/router`'s hash.
pub fun link<msg>( to : string, child : widget<msg>, ?key : key ) : widget<msg>
  Link(?key.key-id.int32, to, child)

// the identity key of a scroll region. Auto (call-site) when `name` is empty,
// or a stable named handle within the ambient `?key` scope -- pass the SAME
// `name` to `scroll` and to a scrollbar so they link. `scroll-state(scroll-key
// name)` then reads the region's live offset/content/viewport.
pub fun scroll-key( name : string = "", ?key : key, ?kk-file-line : string ) : keytree int
  if name.is-empty then kt-child( ?key, Slot("sc", ?kk-file-line) ).key-id
                   else kt-child( ?key, Named(name) ).key-id

// which axis a scrollbar view serves (a region can overflow vertically,
// horizontally, or both -- horizontal is opt-in, see `scroll`)
pub type scroll-axis
  Vertical
  Horizontal

// a scrollable viewport: the child is laid out at the viewport's width with
// unbounded height, and scrolls if it is taller than the viewport. The viewport
// takes the size its parent offers, so put `scroll` where the parent bounds the
// height -- typically `expanded(scroll(...))` in a column, so it fills the space
// left after the fixed rows. On the web the browser scrolls; natively the
// backend keeps a scroll offset (keyed by `?key`/`name` + call site) and clips.
// Give `name` a value to link a scrollbar to this region (see `scroll-key`).
// `horizontal = True` scrolls along x instead of y: the child is laid out at the
// viewport HEIGHT with unbounded width (so it does NOT wrap), and scrolls
// sideways -- for carousels / wide tables. Default (vertical) wraps to the width.
pub fun scroll<msg>( child : widget<msg>, name : string = "", horizontal : bool = False, ?key : key, ?kk-file-line : string ) : <keytree> widget<msg>
  val sk = scroll-key(name, ?key = ?key, ?kk-file-line = ?kk-file-line)
  Scroll(sk.int32, sk, horizontal, child)

// the keys of every scroll region in a widget tree (pre-layout), so the scene
// composer emits an auto-scrollbar only for regions actually present THIS frame
// (their metrics/rects come from the previous frame's registries, which persist
// across frames -- a removed region would otherwise leave a phantom bar)
pub fun scroll-keys<a>( w : widget<a> ) : list<(int, bool)>
  match w
    Scroll(_, key, horizontal, child) -> Cons((key, horizontal), child.scroll-keys)
    WBox(_, _, _, _, child) -> child.scroll-keys
    Expanded(_, _, child) -> child.scroll-keys
    Link(_, _, child) -> child.scroll-keys
    Center(_, _, child) -> child.scroll-keys
    IntrinsicWidth(_, child) -> child.scroll-keys
    Rotated(_, _, child) -> child.scroll-keys
    Clipped(_, _, _, _, child) -> child.scroll-keys
    Overlaid(_, child) -> child.scroll-keys
    Transform3d(_, _, child) -> child.scroll-keys
    Fixed(_, _, _, child) -> child.scroll-keys
    Memo(_, _, child) -> child.scroll-keys
    Positioned(_, _, _, _, _, _, _, _, _, child) -> child.scroll-keys
    Act(_, _, child) -> child.scroll-keys
    Interactive(_, _, _, _, child) -> child.scroll-keys
    Flex(_, _, _, _, children) -> children.flatmap(fn(c) c.pretend-decreasing.scroll-keys)
    Stack(_, children) -> children.flatmap(fn(e) e.thd.pretend-decreasing.scroll-keys)
    _ -> []

// lay the child out at most `max-width` and let it SELF-SIZE (never stretched
// to fill). When the parent stretches center itself (e.g. the app-root box under
// the tight window constraints), the child is centered horizontally in that
// extent -- the responsive app-shell idiom (full-width background, capped
// centered content); in a loose parent (a card, a column) center shrink-wraps.
pub fun center<msg>( child : widget<msg>, max-width : float64 = 640.0, ?key : key ) : widget<msg>
  Center(?key.key-id.int32, max-width, child)

// size to the child's NATURAL width -- growers (spacer/expanded) collapsed --
// then lay the child out tight at it, so spacers spread within the natural
// width (positioning, not sizing). The shrink-wrap for spread-apart content:
// `box(intrinsic-width(column([...spacer rows...])))` hugs its widest row
// with no pixel constants. Costs a second layout pass of the subtree.
pub fun intrinsic-width<msg>( child : widget<msg>, ?key : key ) : widget<msg>
  IntrinsicWidth(?key.key-id.int32, child)

// rotate the child's PAINT by `degrees` (clockwise) about its center. Layout
// and hit-testing stay unrotated (the child keeps its laid-out rect) -- meant
// for decorative spins (an icon, a glyph), not rotated interactive regions.
pub fun rotated<msg>( child : widget<msg>, degrees : float64, ?key : key ) : widget<msg>
  Rotated(?key.key-id.int32, degrees, child)

// Clip `child` to this node's rounded rect. Layout is unchanged -- the child is
// laid out exactly as it would be unclipped -- but it can neither PAINT nor be
// TOUCHED outside the rect, which is what makes an expanding ink ripple stay
// inside its button. Both backends have the primitive natively
// (`ImpellerDisplayListBuilderClipRoundedRect`; `overflow:hidden` plus
// `border-radius`), so this costs no emulation on either.
//
// Hit-testing clips to the RECT, not the rounded corners: a press in the
// corner cutout of a heavily rounded clip still reaches the child. That is the
// same approximation a scroll viewport already makes, and it keeps the hit
// walk arithmetic-only.
// Paint `child` at its natural size while contributing NOTHING to layout and
// NOTHING to hit-testing -- a pure decoration. An ink splash is the motivating
// case: it must be free to grow past its button without resizing it, and must
// never swallow the click that started it.
//
// This is NOT `fixed(child, 0, 0)`. `fixed` CAPS the child's layout at the
// pinned extent, so a splash wrapped in it is constrained to zero and paints
// nothing -- which is exactly the bug this replaces. Here the child is laid
// out UNBOUNDED and only the size reported upward is zero.
pub fun overlay<msg>( child : widget<msg>, ?key : key ) : widget<msg>
  Overlaid(?key.key-id.int32, child)

pub fun clip<msg>( child : widget<msg>, radius : float64 = 0.0,
                   width : maybe<float64> = Nothing, height : maybe<float64> = Nothing,
                   ?key : key ) : widget<msg>
  Clipped(?key.key-id.int32, radius, width, height, child)

// apply a 4x4 matrix (see `ui/transform`: perspective/rotate-x/y/z/translate3/
// scale3, composed with `*`) to the child's PAINT only, about its center --
// layout stays unchanged (the child keeps its laid-out rect). Hit-testing is
// ACCURATE: `hit-go`'s `LTransform3d` arm unprojects the click through the
// same center-wrapped matrix the paint arm concatenates (see `unproject` in
// `ui/transform`), so a rotated/tilted child (e.g. a card flip's BACK face)
// hit-tests against its actual on-screen (projected) quad, not its
// untransformed layout rect.
pub fun transform3d<msg>( child : widget<msg>, m : mat4, ?key : key ) : widget<msg>
  Transform3d(?key.key-id.int32, m, child)

// pin `child`'s extent on the given axes: the axis is laid out CAPPED at the
// given size (the child may measure smaller; it is never stretched) but this
// node always REPORTS exactly that size to its parent, regardless of what the
// child actually measured -- an oversize child overflows visually at its own
// position (no clip) instead of growing this node and desyncing whatever
// arithmetic the parent based on the fixed extent (e.g. `ui/lazy`'s
// lead/trail spacer math, which needs a row's height to be exact by
// construction, not just "usually" exact). `Nothing` on an axis falls back
// to the child's own measured extent there (so `fixed(w, height = Just(h))`
// pins only height, leaving width to the child).
pub fun fixed<msg>( child : widget<msg>, width : maybe<float64> = Nothing, height : maybe<float64> = Nothing, ?key : key ) : widget<msg>
  Fixed(?key.key-id.int32, width, height, child)

// a FULL-VIEWPORT layer holding `child` anchored to a target rect: `child`'s
// `self-align` point is placed at the target's `target-align` point (+offset),
// clamped on-screen (see `ui/anchor`). `target = Nothing` anchors to the viewport
// itself (for cursor overlays via `offset`, and centered modals); a `Just` rect
// anchors to a specific region (a scroll viewport, or another widget's published
// rect). The scene compositor stacks these over the main view.
pub fun positioned<msg>( child : widget<msg>,
                         target : maybe<(float64,float64,float64,float64)> = Nothing,
                         target-align : alignment = top-left, self-align : alignment = top-left,
                         offset-x : float64 = 0.0, offset-y : float64 = 0.0,
                         max-width : float64 = unbounded-w, max-height : float64 = unbounded-w,
                         absorb : bool = False, ?key : key ) : widget<msg>
  Positioned(?key.key-id.int32, target, target-align, self-align, offset-x, offset-y, max-width, max-height, absorb, child)

// a click target that runs a thunk instead of emitting a message -- the door
// for `ui/state` writes (toggles, uncontrolled fields) that never touch the app
// model. The thunk typically enqueues a `use-state` transition. An inner
// message target (a button) still wins over the surrounding act.
pub fun act<msg>( child : widget<msg>, on-act : () -> <uistate,ioc> (), ?key : key ) : widget<msg>
  Act(?key.key-id.int32, on-act, child)

// a single-line editable text field; the value lives in the model
// (controlled): every edit emits `on-input(new-value)`. Focus is by widget
// identity (derived from the ambient `?key` + this call site).
pub fun text-input<msg>( value : string, on-input : string -> msg,
                         placeholder : string = "", width : float64 = 220.0,
                         on-key : maybe<string -> msg> = Nothing,
                         ?key : key, ?kk-file-line : string ) : <keytree> widget<msg>
  val k = kt-child(?key, Slot("ti", ?kk-file-line)).key-id
  // owner = ambient ?key (addressable by a caller's scope); `k` is the STATE
  // key only (its own Slot mint, per-call-site unique) -- see `interactive`.
  TextInput(?key.key-id.int32, k, value, placeholder, width, on-input, on-key)

// a single-line editable text field whose value lives in `ui/state` under this
// widget's identity (UNCONTROLLED): the app model never sees keystrokes. Give
// it a `name` and a sibling can read its live text with
// `field-text(field-key(name))` (same-parent derivation, like scroll/scrollbar)
// -- e.g. a submit button's `act-msg` reading the form. `on-enter` optionally
// maps commit (the Enter key) to a message.
pub fun field<msg>( name : string = "", placeholder : string = "", width : float64 = 220.0,
                    on-enter : maybe<string -> msg> = Nothing,
                    ?key : key, ?kk-file-line : string ) : <keytree> widget<msg>
  val k = if name.is-empty then kt-child(?key, Slot("tf", ?kk-file-line)).key-id
                           else field-key(name)
  // owner: a NAMED field IS its own addressable identity (field-key mints a
  // Named child -> address it by that name); an UNNAMED field takes the
  // ambient ?key (address it via a caller's scope). `k` stays the state key.
  val o = if name.is-empty then ?key.key-id else k
  TextField(o.int32, k, placeholder, width, on-enter)

// the identity of the named `field(name)` under the same parent -- so a
// sibling (a submit button's `act-msg`) can read its live text
pub fun field-key( name : string, ?key : key ) : keytree int
  kt-child(?key, Named(name)).key-id

// a click target whose message is COMPUTED at click time from `ui/state` --
// the form-submit primitive: read the fields, build one message
pub fun act-msg<msg>( child : widget<msg>, to-msg : () -> <uistate,ioc> msg, ?key : key ) : widget<msg>
  ActMsg(?key.key-id.int32, child, to-msg)

// a fixed-size (possibly clickable) colored box -- grid cells, swatches
pub fun rect<msg>( w : float64, h : float64, bg : maybe<fill> = Nothing,
                   on-click : maybe<msg> = Nothing, ?key : key ) : widget<msg>
  SizedBox(?key.key-id.int32, w, h, bg, on-click)

// NOTE: the user-facing `image(source, ...)` / `image-path(src, ...)` front
// doors live in `ui/backend` (task #53) -- they build a host-selected async
// `future-boundary` (native) or `<img>` (web) and so must sit ABOVE the
// backend in the module graph. `ui/widget` only owns the `Image` LEAF
// constructor + its layout/paint node; the loading policy is the backend's.

// a horizontal slider over [lo,hi] snapped to `step`
pub fun slider<msg>( value : float64, on-change : float64 -> msg,
                     lo : float64 = 0.0, hi : float64 = 1.0, step : float64 = 0.0,
                     width : float64 = 160.0, ?key : key ) : widget<msg>
  Slider(?key.key-id.int32, lo, hi, step, value, width, on-change)

// ----------------------------------------------------------------
// `widget` is a functor: components own closed msg types and parents embed
// them with `map-msg` (parity with web-ui's html/map-msg)

pub fun map-msg<a,b>( w : widget<a>, f : a -> b ) : widget<b>
  match w
    Text(o, s, font, wrap, c) -> Text(o, s, font, wrap, c)
    Rich(o, content, bf, bc, spans, wrap) ->
      Rich(o, content, bf, bc, spans.map(fn(s) Text-span(s.start, s.end, s.font, s.color, s.on-click.map(f))), wrap)
    WBox(o, pad, bg, on, child) ->
      WBox(o, pad, bg, Pointer(on.click.map(f), on.click-at.map(fn(g) fn(x,y) f(g(x,y))),
             on.context-at.map(fn(g) fn(x,y) f(g(x,y))),
             on.drag, on.drop.map(fn(g) fn(s) f(g(s)))), child.map-msg(f))
    Flex(o, h, gap, fl, kids) -> Flex(o, h, gap, fl, kids.map(fn(k) k.pretend-decreasing.map-msg(f)))
    Spacer(o) -> Spacer(o)
    Expanded(o, fl, child) -> Expanded(o, fl, child.pretend-decreasing.map-msg(f))
    Stack(o, kids) -> Stack(o, kids.map(fn(entry) (entry.fst, entry.snd, entry.thd.pretend-decreasing.map-msg(f))))
    Link(o, to, child) -> Link(o, to, child.map-msg(f))
    Scroll(o, key, horizontal, child) -> Scroll(o, key, horizontal, child.map-msg(f))
    Center(o, mw, child) -> Center(o, mw, child.map-msg(f))
    IntrinsicWidth(o, child) -> IntrinsicWidth(o, child.map-msg(f))
    Rotated(o, deg, child) -> Rotated(o, deg, child.map-msg(f))
    Clipped(o, r, cw, ch, child) -> Clipped(o, r, cw, ch, child.map-msg(f))
    Overlaid(o, child) -> Overlaid(o, child.map-msg(f))
    Transform3d(o, m, child) -> Transform3d(o, m, child.map-msg(f))
    Fixed(o, w0, h0, child) -> Fixed(o, w0, h0, child.map-msg(f))
    Memo(o, mid, child) -> Memo(o, mid, child.map-msg(f))   // NOTE: mapping rebuilds -> ptr-eq misses; memo is correct but unoptimized under map-msg
    Positioned(o, t, ta, sa, ox, oy, mw, mh, ab, child) -> Positioned(o, t, ta, sa, ox, oy, mw, mh, ab, child.map-msg(f))
    Act(o, onact, child) -> Act(o, onact, child.map-msg(f))   // thunk carries no msg
    Interactive(o, k, oc, slop, child) -> Interactive(o, k, oc.map(f), slop, child.map-msg(f))

    TextInput(o, k, v, ph, w0, oninput, onkey) ->
      TextInput(o, k, v, ph, w0, fn(s) f(oninput(s)), onkey.map(fn(g) fn(s) f(g(s))))
    TextField(o, k, ph, w0, onenter) -> TextField(o, k, ph, w0, onenter.map(fn(g) fn(s) f(g(s))))
    ActMsg(o, child, to-msg) -> ActMsg(o, child.map-msg(f), fn() f(to-msg()))
    Slider(o, lo, hi, st, v, w0, onchange) ->
      Slider(o, lo, hi, st, v, w0, fn(x) f(onchange(x)))
    SizedBox(o, w0, h0, bg, onclick) -> SizedBox(o, w0, h0, bg, onclick.map(f))
    Image(o, src, fit, w0, h0) -> Image(o, src, fit, w0, h0)   // no msg inside

// ----------------------------------------------------------------
// layout: constraints down, sizes up, parent positions

// the box constraints a parent passes down
pub struct constraints( min-w : float64, max-w : float64, min-h : float64, max-h : float64 )

fun same-constraints( a : constraints, b : constraints ) : bool
  a.min-w == b.min-w && a.max-w == b.max-w && a.min-h == b.min-h && a.max-h == b.max-h

pub fun tight( w : float64, h : float64 ) : constraints
  Constraints(w, w, h, h)

pub fun loose( w : float64, h : float64 ) : constraints
  Constraints(0.0, w, 0.0, h)

fun clamp-w( c : constraints, w : float64 ) : float64
  w.max(c.min-w).min(c.max-w)

fun clamp-h( c : constraints, h : float64 ) : float64
  h.max(c.min-h).min(c.max-h)

// the "unbounded" main-axis width a single (non-wrapping) line is measured at
// (also used by backends when re-shaping single-line text for paint)
pub val unbounded-w : float64 = 1.0e7
val neg-unbounded-w : float64 = 0.0 - 1.0e7   // clip sentinel for owner-rect's unbounded top/left

// whether an incoming max-constraint is an UNBOUNDED axis. A threshold, not
// equality against the sentinel: padding/chrome subtract from constraints on
// the way down (a padded box inside a scroll hands its child 1e7 - 28), and
// that is still unbounded -- no real viewport is a million pixels.
pub fun is-unbounded( x : float64 ) : bool
  x >= 1.0e6

// Text measurement is an ambient effect: layout asks the backend for the pixel
// box of a string set in a font at a maximum width (finite for wrapping text,
// `unbounded-w` for single-line). Each backend installs the handler -- native
// shapes an Impeller paragraph, web measures through the host canvas / a
// hidden div. Keeping it an effect (not a threaded callback) keeps layout
// backend-agnostic and lets a future caching / batching / line-breaking
// handler drop in with NO change to any layout code.
pub effect measure
  fun measure-text( content : string, font : font, max-w : float64 ) : (float64, float64)
  fun measure-rich( content : string, base-font : font, spans : list<(int,int,maybe<font>)>,
                    max-w : float64 ) : (float64, float64, list<list<(float64,float64,float64,float64)>>)

// The laid-out tree: every node knows its size; containers remember the
// offsets they assigned. Text keeps its content + font + wrap (backends draw
// it their way, re-shaping at the recorded width).
// `owner` (first field of every ltree ctor) is copied verbatim from the widget
// that produced this node during `layout` (which has no keytree and cannot
// re-derive it). Read only by `owner-rect`/`owner-texts`; inert everywhere else.
pub type ltree<a>
  LText( owner : int32, content : string, font : font, wrap : bool, color : color, w : float64, h : float64 )
  LRich( owner : int32, content : string, base-font : font, base-color : color,
         spans : list<text-span<a>>, wrap : bool, w : float64, h : float64,
         span-rects : list<(int, list<(float64,float64,float64,float64)>)> )
    // span-rects: (index into `spans`, that span's resolved rect(s) relative
    // to this node's own origin -- more than one rect iff the span's text
    // wraps across a line break)
  LBox( owner : int32, bg : maybe<fill>, on : pointer<a>,
        w : float64, h : float64, dx : float64, dy : float64, child : ltree<a> )
  LFlex( owner : int32, w : float64, h : float64, children : list<(float64, float64, ltree<a>)> )
  LLayer( owner : int32, w : float64, h : float64, kids : list<(float64, float64, ltree<a>)> )  // a scene layer marker (Positioned's viewport-sized layer): IDENTICAL to LFlex in every walk; only the web lowering treats it specially (pointer-transparent, see api/web/backend.kk)
  LLink( owner : int32, to : string, w : float64, h : float64, dx : float64, dy : float64, child : ltree<a> )
  LScroll( owner : int32, key : int, w : float64, h : float64, content : float64, offset : float64, horizontal : bool, child : ltree<a> )  // key = offset id; w,h viewport; `horizontal` picks the scroll axis; `content` = child size ALONG that axis; `offset` = scroll position along it (baked by the native backend)
  LAct( owner : int32, onact : () -> <uistate,ioc> (), w : float64, h : float64, dx : float64, dy : float64, child : ltree<a> )
  LRotate( owner : int32, degrees : float64, w : float64, h : float64, child : ltree<a> )   // paint-only spin about the center of (w,h)
  LOverlay( owner : int32, w : float64, h : float64, child : ltree<a> )     // painted at (w,h) but REPORTS (0,0) as its size, and is skipped by every hit walk
  LClip( owner : int32, radius : float64, w : float64, h : float64, child : ltree<a> )      // clip the child to the rounded rect (0,0,w,h,radius): both backends have this primitive (ClipRoundedRect / overflow:hidden + border-radius)
  LTransform3d( owner : int32, m : mat4, w : float64, h : float64, child : ltree<a> )   // paint-only 4x4 about the center of (w,h)
  LMemo( owner : int32, mid : int, srcw : widget<a>, lc : constraints, child : ltree<a> )    // memo boundary: `srcw` is the widget that produced `child`; `lc` = the constraints it was laid out under (reuse requires BOTH unchanged)
  LInteractive( owner : int32, key : int, onclick : maybe<a>, slop : float64, w : float64, h : float64, dx : float64, dy : float64, child : ltree<a> )
  LField( owner : int32, key : int, value : string, placeholder : string, onenter : maybe<string -> a>,
          w : float64, h : float64 )   // uncontrolled: value baked from ui/state by the backend
  LActMsg( owner : int32, to-msg : () -> <uistate,ioc> a, w : float64, h : float64, dx : float64, dy : float64, child : ltree<a> )
  LInput( owner : int32, key : int, value : string, placeholder : string,
          oninput : string -> a, onkey : maybe<string -> a>,
          w : float64, h : float64 )
  LSlider( owner : int32, lo : float64, hi : float64, step : float64, value : float64,
           onchange : float64 -> a, w : float64, h : float64 )
  LImage( owner : int32, src : string, fit : image-fit, w : float64, h : float64 )

pub fun size<msg>( ^t : ltree<msg> ) : (float64, float64)
  match t
    LText(_, _, _, _, _, w, h) -> (w, h)
    LRich(_, _, _, _, _, _, w, h, _) -> (w, h)
    LBox(_, _, _, w, h, _, _, _) -> (w, h)
    LFlex(_, w, h, _) -> (w, h)
    LLayer(_, w, h, _) -> (w, h)
    LLink(_, _, w, h, _, _, _) -> (w, h)
    LScroll(_, _, w, h, _, _, _, _) -> (w, h)
    LAct(_, _, w, h, _, _, _) -> (w, h)
    LRotate(_, _, w, h, _) -> (w, h)
    LOverlay(_, _, _, _) -> (0.0, 0.0)   // the whole point: contributes nothing to the parent's extent
    LClip(_, _, w, h, _) -> (w, h)
    LTransform3d(_, _, w, h, _) -> (w, h)
    LMemo(_, _, _, _, child) -> child.size
    LInteractive(_, _, _, _, w, h, _, _, _) -> (w, h)
    LInput(_, _, _, _, _, _, w, h) -> (w, h)
    LField(_, _, _, _, _, w, h) -> (w, h)
    LActMsg(_, _, w, h, _, _, _) -> (w, h)
    LSlider(_, _, _, _, _, _, w, h) -> (w, h)
    LImage(_, _, _, w, h) -> (w, h)

pub val input-height : float64 = 32.0
pub val slider-height : float64 = 28.0
pub val default-image-height : float64 = 100.0   // used when `image(...)` gets no explicit height
pub val default-image-width  : float64 = 100.0   // fallback when auto-width lands in an UNBOUNDED constraint (no 10M-px box)

// owner stamped on purely-structural ltree nodes that no widget built directly
// (empty flex placeholders for spacers/sized-box children, reconcile drains):
// the root id 0, never a query target.
pub val no-owner : int32 = 0.int32

pub fun layout<msg>( w : widget<msg>, c : constraints ) : <div,measure> ltree<msg>
  match w
    Text(o, content, font, wrap, color) ->
      val (tw, th) = measure-text(content, font, if wrap then c.max-w else unbounded-w)
      LText(o, content, font, wrap, color, clamp-w(c, tw), clamp-h(c, th))
    Rich(o, content, bf, bc, spans, wrap) ->
      val span-args = spans.map(fn(s) (s.start, s.end, s.font))
      val (tw, th, rects) = measure-rich(content, bf, span-args, if wrap then c.max-w else unbounded-w)
      val indexed-rects = spans.map-indexed(fn(i, _) i).zip(rects)
      LRich(o, content, bf, bc, spans, wrap, clamp-w(c, tw), clamp-h(c, th), indexed-rects)
    WBox(o, pad, bg, on, child) ->
      // pass min constraints through (minus padding): a stretched box
      // stretches its child, a loose box lets it self-size
      val inner = Constraints((c.min-w - 2.0*pad).max(0.0), (c.max-w - 2.0*pad).max(0.0),
                              (c.min-h - 2.0*pad).max(0.0), (c.max-h - 2.0*pad).max(0.0))
      val lchild = child.layout(inner)
      val (cw, ch) = lchild.size
      LBox(o, bg, on,
           clamp-w(c, cw + 2.0*pad), clamp-h(c, ch + 2.0*pad), pad, pad, lchild)
    Flex(o, horizontal, gap, fl, children) ->
      layout-flex(o, horizontal, gap, fl, children, c)
    Spacer(o) ->
      LFlex(o, 0.0, 0.0, [])     // a bare spacer outside a flex takes no space
    Expanded(_, _, child) ->
      child.layout(c)         // outside a flex there is nothing to grow into
    Stack(o, children) ->
      val kids = children.map fn(entry)
        val (dx, dy, kid) = entry
        (dx, dy, kid.pretend-decreasing.layout(Constraints(0.0, c.max-w, 0.0, c.max-h)))
      val w0 = kids.map(fn(entry) entry.fst + entry.thd.size.fst).maximum(0.0)
      val h0 = kids.map(fn(entry) entry.snd + entry.thd.size.snd).maximum(0.0)
      LFlex(o, clamp-w(c, w0), clamp-h(c, h0), kids)
    Link(o, to, child) ->
      val lchild = child.layout(c)
      val (cw, ch) = lchild.size
      LLink(o, to, clamp-w(c, cw), clamp-h(c, ch), 0.0, 0.0, lchild)
    Scroll(o, key, horizontal, child) ->
      // viewport = the size the parent offers. Vertical: child gets the viewport
      // width + unbounded height (taller -> scrolls). Horizontal: child gets the
      // viewport height + unbounded width (wider -> scrolls, no wrap).
      // In an axis the parent leaves UNBOUNDED (a scroll nested inside a scroll
      // of the other axis) the viewport shrink-wraps to the child instead, so
      // it never becomes a 1e7-px box.
      val lchild = if horizontal
        then child.layout(Constraints(0.0, unbounded-w, 0.0, c.max-h))
        else child.layout(Constraints(0.0, c.max-w, 0.0, unbounded-w))
      val (cw, ch) = lchild.size
      val vw = clamp-w(c, if is-unbounded(c.max-w) then cw else c.max-w)
      val vh = clamp-h(c, if is-unbounded(c.max-h) then ch else c.max-h)
      val content = if horizontal then cw else ch
      LScroll(o, key, vw, vh, content, 0.0, horizontal, lchild)
    Center(o, mw, child) ->
      // the child SELF-SIZES (min 0, capped at `mw`); center shrink-wraps it
      // unless the parent's min-width stretches center wider -- then the child
      // is centered in the stretched extent
      val lchild = child.layout(Constraints(0.0, c.max-w.min(mw), c.min-h, c.max-h))
      val (childw, childh) = lchild.size
      val w0 = clamp-w(c, childw)
      val x = ((w0 - childw) / 2.0).max(0.0)
      LFlex(o, w0, clamp-h(c, childh), [(x, 0.0, lchild)])
    IntrinsicWidth(o, child) ->
      // two passes: probe the child's NATURAL width (unbounded -> growers
      // collapse), then lay it out tight at that width so spacers/expanded
      // spread WITHIN it -- positioning, not sizing (Flutter's IntrinsicWidth)
      val probe = child.pretend-decreasing.layout(Constraints(0.0, unbounded-w, c.min-h, c.max-h))
      val w0 = clamp-w(c, probe.size.fst)
      val lchild = child.layout(Constraints(w0, w0, c.min-h, c.max-h))
      val (_, childh) = lchild.size
      LFlex(o, w0, clamp-h(c, childh), [(0.0, 0.0, lchild)])
    Rotated(o, deg, child) ->
      val lchild = child.layout(c)
      val (cw, ch) = lchild.size
      LRotate(o, deg, cw, ch, lchild)
    Overlaid(o, child) ->
      // unbounded on purpose: the child must reach its natural size even
      // though this node reports none (`fixed` CAPS instead, which is what
      // silently flattened the first ripple to zero width)
      val lchild = child.layout(Constraints(0.0, unbounded-w, 0.0, unbounded-w))
      val (cw, ch) = lchild.size
      LOverlay(o, cw, ch, lchild)
    Clipped(o, r, fw, fh, child) ->
      // the child is laid out under the INCOMING constraints, not the pinned
      // extent: it keeps its natural size and simply overflows into the clip,
      // which is the whole point (a ripple circle grows past the button and is
      // cut, instead of growing the button)
      val lchild = child.layout(c)
      val (cw, ch) = lchild.size
      LClip(o, r, fw.default(cw), fh.default(ch), lchild)
    Transform3d(o, m3, child) ->
      val lchild = child.layout(c)
      val (cw, ch) = lchild.size
      LTransform3d(o, m3, cw, ch, lchild)
    Fixed(o, mw, mh, child) ->
      // cap the child's constraints at the fixed extents (falling back to
      // `c`'s own max on the Nothing axis) -- the child may measure smaller,
      // never bigger-and-honored; then REPORT exactly the fixed extents
      // (falling back to what the child measured on the Nothing axis),
      // independent of the child's actual measured size. Lowered onto the
      // existing `LBox` node (no new ltree ctor): a plain box with no
      // padding/bg/handlers, so paint draws the child at its own measured
      // size without clipping to (w0,h0) -- an oversize child overflows
      // visually here, it does not resize this node.
      val capped-w = match mw { Just(fw) -> fw; Nothing -> c.max-w }
      val capped-h = match mh { Just(fh) -> fh; Nothing -> c.max-h }
      val lchild = child.layout(Constraints(0.0, capped-w, 0.0, capped-h))
      val (cw, ch) = lchild.size
      val w0 = match mw { Just(fw) -> fw; Nothing -> cw }
      val h0 = match mh { Just(fh) -> fh; Nothing -> ch }
      LBox(o, Nothing, Pointer(), clamp-w(c, w0), clamp-h(c, h0), 0.0, 0.0, lchild)
    Memo(o, mid, child) ->
      LMemo(o, mid, child, c, child.layout(c))
    Positioned(o, mtarget, ta, sa, ox, oy, maxw, maxh, absorb, child) ->
      // a full-viewport layer: measure the child within max-width/max-height (so
      // it SELF-SIZES -- content-sized unless it explicitly fills, capped at the
      // given max and the viewport), anchor it to the target rect (Nothing = the
      // viewport), clamp on-screen -- produced as an LFlex so the existing
      // paint/hit/stack machinery handles it with no new node.
      val vw = c.max-w
      val vh = c.max-h
      val lchild = child.layout(Constraints(0.0, vw.min(maxw), 0.0, vh.min(maxh)))
      val (cw, ch) = lchild.size
      val (tx, ty, tw, th) = match mtarget
        Just(r) -> r
        Nothing -> (0.0, 0.0, vw, vh)
      val (x, y) = place(tx, ty, tw, th, cw, ch, ta, sa, ox, oy, vw, vh)
      // when absorbing, an invisible content-sized click swallower sits UNDER the
      // content (a no-op LAct): a click on the content that hits no handler lands
      // on it (blocking a dismiss scrim below), while the real content -- a later
      // sibling -- wins for its own handlers, and clicks outside (cw,ch) miss both
      val kids = if absorb
        then [(x, y, LAct(o, fn() (), cw, ch, 0.0, 0.0, LFlex(no-owner, 0.0, 0.0, []))), (x, y, lchild)]
        else [(x, y, lchild)]
      // LLayer: marks this viewport-sized layer so the WEB lowering can make
      // its container pointer-transparent -- a composited layer's DIV
      // otherwise swallows elementFromPoint/native focus for everything under
      // it (inputs, links). Hit-testing is unaffected (every walk treats
      // LLayer identically to LFlex).
      LLayer(o, clamp-w(c, vw), clamp-h(c, vh), kids)
    Act(o, onact, child) ->
      val lchild = child.layout(c)
      val (cw, ch) = lchild.size
      LAct(o, onact, clamp-w(c, cw), clamp-h(c, ch), 0.0, 0.0, lchild)
    Interactive(o, k, oc, slop, child) ->
      // layout-neutral: sized to the child; `slop` only widens the hit area
      val lchild = child.layout(c)
      val (cw, ch) = lchild.size
      LInteractive(o, k, oc, slop, clamp-w(c, cw), clamp-h(c, ch), 0.0, 0.0, lchild)
    TextInput(o, k, v, ph, w0, oninput, onkey) ->
      LInput(o, k, v, ph, oninput, onkey, clamp-w(c, w0), clamp-h(c, input-height))
    TextField(o, k, ph, w0, onenter) ->
      LField(o, k, "", ph, onenter, clamp-w(c, w0), clamp-h(c, input-height))   // value baked from ui/state by the backend
    ActMsg(o, to-msg-child, to-msg) ->
      val lchild = to-msg-child.layout(c)
      val (cw, ch) = lchild.size
      LActMsg(o, to-msg, clamp-w(c, cw), clamp-h(c, ch), 0.0, 0.0, lchild)
    Slider(o, lo, hi, st, v, w0, onchange) ->
      LSlider(o, lo, hi, st, v, onchange, clamp-w(c, w0), clamp-h(c, slider-height))
    SizedBox(o, w0, h0, bg, onclick) ->
      LBox(o, bg, Pointer(click = onclick),
           clamp-w(c, w0), clamp-h(c, h0), 0.0, 0.0, LFlex(no-owner, 0.0, 0.0, []))
    Image(o, src, fit, w0, h0) ->
      // the box exists BEFORE the pixels decode: width fills the constraint
      // (but a finite default in an UNBOUNDED constraint -- intrinsic-width /
      // horizontal-scroll -- so it never becomes a 1e7-px box), height a
      // sensible default; both clamped like every other leaf
      val bw = if w0 > 0.0 then w0 elif is-unbounded(c.max-w) then default-image-width else c.max-w
      val bh = if h0 > 0.0 then h0 else default-image-height
      LImage(o, src, fit, clamp-w(c, bw), clamp-h(c, bh))

// Flex layout: non-spacer children are laid out with loose constraints and
// their sizes flow back; leftover main-axis space is divided over the
// spacers; then the parent assigns offsets (cross-axis centered).
fun child-constraints( horizontal : bool, c : constraints ) : constraints
  val main-max  = if horizontal then c.max-w else c.max-h
  val cross-max = if horizontal then c.max-h else c.max-w
  if horizontal then Constraints(0.0, main-max, 0.0, cross-max)
                else Constraints(0.0, cross-max, 0.0, main-max)

// a child of a flex during layout: either already laid out at its natural size
// (rigid), or a grower (spacer / expanded) whose main-axis extent is only known
// once the leftover space is divided -- `build` realizes it at its allotted size.
type flexchild<a>
  Rigid( t : ltree<a> )
  Grow( weight : float64, build : (float64) -> <div,measure> ltree<a> )

// tighten `c`'s main axis to exactly `sz` (the share an expanded child fills)
fun main-tight( horizontal : bool, c : constraints, sz : float64 ) : constraints
  if horizontal then Constraints(sz, sz, c.min-h, c.max-h)
                else Constraints(c.min-w, c.max-w, sz, sz)

fun layout-flex<msg>( o : int32, horizontal : bool, gap : float64, fill : bool, children : list<widget<msg>>,
                      c : constraints ) : <div,measure> ltree<msg>
  val child-c = child-constraints(horizontal, c)
  val fchildren = children.map fn(child)
    match child
      Spacer(so)        -> Grow(1.0, fn(sz) if horizontal then LFlex(so, sz, 0.0, []) else LFlex(so, 0.0, sz, []))
      Expanded(_, fl, ch)  -> Grow(fl.max(0.0), fn(sz) ch.pretend-decreasing.layout(main-tight(horizontal, child-c, sz)))
      _                 -> Rigid(child.pretend-decreasing.layout(child-c))
  finish-flex(o, horizontal, gap, fill, fchildren, c)

// divide the leftover main-axis space among the growers and assemble the LFlex.
fun finish-flex<msg>( o : int32, horizontal : bool, gap : float64, fill : bool,
                      fchildren : list<flexchild<msg>>, c : constraints ) : <div,measure> ltree<msg>
  val main-max  = if horizontal then c.max-w else c.max-h
  val cross-max = if horizontal then c.max-h else c.max-w
  val count   = fchildren.length
  val gaps    = gap * (count - 1).float64.max(0.0)
  val used    = fchildren.map(fn(fc) match fc { Rigid(t) -> t.main-extent(horizontal); Grow(_, _) -> 0.0 }).total
  val weight  = fchildren.map(fn(fc) match fc { Grow(w, _) -> w; Rigid(_) -> 0.0 }).total
  // an unbounded main axis has no leftover to divide: growers collapse and the
  // flex takes its natural size (the intrinsic-width probe relies on this)
  val canflex = main-max < 100000.0
  val leftover = if canflex then (main-max - used - gaps).max(0.0) else 0.0
  val kids = fchildren.map fn(fc)
    match fc
      Rigid(t)        -> t
      Grow(w, build)  -> build(if weight > 0.0 then leftover * (w / weight) else 0.0)
  val shrink-cross = kids.map(fn(t) t.cross(horizontal)).maximum(0.0)
  val cross-min = if horizontal then c.min-h else c.min-w
  // a min-stretched flex places (cross-centers) children in the FULL extent,
  // so the reported size and the placement extent stay consistent
  val cross = if fill && cross-max < 100000.0 then cross-max else shrink-cross.max(cross-min)
  val mainsz = if weight > 0.0 && canflex then main-max else used + gaps
  val placed = kids.place-main(horizontal, gap, 0.0, cross)
  if horizontal
    then LFlex(o, clamp-w(c, mainsz), clamp-h(c, cross), placed)
    else LFlex(o, clamp-w(c, cross), clamp-h(c, mainsz), placed)

fun main-extent<msg>( t : ltree<msg>, horizontal : bool ) : float64
  val (w, h) = t.size
  if horizontal then w else h

fun cross<msg>( t : ltree<msg>, horizontal : bool ) : float64
  val (w, h) = t.size
  if horizontal then h else w

fun place-main<msg>( kids : list<ltree<msg>>, horizontal : bool, gap : float64,
                     at : float64, cross-size : float64 ) : list<(float64, float64, ltree<msg>)>
  match kids
    Nil -> Nil
    Cons(t, rest) ->
      val center = (cross-size - t.cross(horizontal)) / 2.0    // cross-axis centered
      val pos = if horizontal then (at, center) else (center, at)
      Cons((pos.fst, pos.snd, t),
           rest.place-main(horizontal, gap, at + t.main-extent(horizontal) + gap, cross-size))

fun total( xs : list<float64> ) : float64
  xs.foldl(0.0, (+))

fun maximum( xs : list<float64>, default : float64 ) : float64
  xs.foldl(default, max)

// ----------------------------------------------------------------
// reconcile: lay out `spec` against the PREVIOUS laid-out tree, reusing its
// cells in place where the constructor shapes still line up (FBIP -- the
// matched old node is dropped and the same-shape new node built in its
// scope, so Perceus reuses the cell). Shape mismatches fall back to a fresh
// layout of that subtree. The old tree must be UNIQUELY owned by the caller
// (see the backend: take it out of its ref before reconciling) or no reuse
// fires. Backend-agnostic; the native backend retains the ltree and uses it.

pub fun reconcile<msg>( old : ltree<msg>, spec : widget<msg>, c : constraints ) : <div,measure> ltree<msg>
  match old
    LText(_, _, _, _, _, _, _) ->
      match spec
        Text(o, content, font, wrap, color) ->
          val (tw, th) = measure-text(content, font, if wrap then c.max-w else unbounded-w)
          LText(o, content, font, wrap, color, clamp-w(c, tw), clamp-h(c, th))
        _ -> spec.layout(c)
    LRich(_, _, _, _, _, _, _, _, _) -> spec.layout(c)   // no fast path yet -- always relayout
    LBox(_, _, _, _, _, _, _, ochild) ->
      match spec
        WBox(o, pad, bg, on, child) ->
          val inner = Constraints((c.min-w - 2.0*pad).max(0.0), (c.max-w - 2.0*pad).max(0.0),
                                  (c.min-h - 2.0*pad).max(0.0), (c.max-h - 2.0*pad).max(0.0))
          val lchild = reconcile(ochild, child, inner)
          val (cw, ch) = lchild.size
          LBox(o, bg, on, clamp-w(c, cw + 2.0*pad), clamp-h(c, ch + 2.0*pad), pad, pad, lchild)
        SizedBox(o, w0, h0, bg, onclick) ->
          LBox(o, bg, Pointer(click = onclick), clamp-w(c, w0), clamp-h(c, h0), 0.0, 0.0, ochild.reuse-empty)
        Fixed(o, mw, mh, child) ->
          val capped-w = match mw { Just(fw) -> fw; Nothing -> c.max-w }
          val capped-h = match mh { Just(fh) -> fh; Nothing -> c.max-h }
          val lchild = reconcile(ochild, child, Constraints(0.0, capped-w, 0.0, capped-h))
          val (cw, ch) = lchild.size
          val w0 = match mw { Just(fw) -> fw; Nothing -> cw }
          val h0 = match mh { Just(fh) -> fh; Nothing -> ch }
          LBox(o, Nothing, Pointer(), clamp-w(c, w0), clamp-h(c, h0), 0.0, 0.0, lchild)
        _ -> spec.layout(c)
    LFlex(_, _, _, okids) ->
      match spec
        Flex(o, horizontal, gap, fill, children) -> reconcile-flex(o, okids, horizontal, gap, fill, children, c)
        Stack(o, children) -> reconcile-stack(o, okids, children, c)
        Center(o, mw, child) -> reconcile-center(o, okids, mw, child, c)
        IntrinsicWidth(o, child) -> reconcile-intrinsic(o, okids, child, c)
        Spacer(o) -> LFlex(o, 0.0, 0.0, okids.drop-kids)
        _ -> spec.layout(c)
    // LLayer only ever comes from `Positioned`'s layout, which has no
    // reconcile arm of its own (falls to `spec.layout(c)` below just like
    // every other old-tree-shape mismatch) -- an old LLayer node is never
    // reused, matching the pre-LLayer LKeyed-wrapped-LFlex behavior exactly.
    LLayer(_, _, _, _) -> spec.layout(c)
    LLink(_, _, _, _, _, _, ochild) ->
      match spec
        Link(o, to, child) ->
          val lchild = reconcile(ochild, child, c)
          val (cw, ch) = lchild.size
          LLink(o, to, clamp-w(c, cw), clamp-h(c, ch), 0.0, 0.0, lchild)
        _ -> spec.layout(c)
    LScroll(_, _, _, _, _, _, _, ochild) ->
      match spec
        Scroll(o, key, horizontal, child) ->
          val vw = clamp-w(c, c.max-w)
          val vh = clamp-h(c, c.max-h)
          val lchild = if horizontal
            then reconcile(ochild, child, Constraints(0.0, unbounded-w, 0.0, vh))
            else reconcile(ochild, child, Constraints(0.0, vw, 0.0, unbounded-w))
          val (cw, ch) = lchild.size
          val content = if horizontal then cw else ch
          LScroll(o, key, vw, vh, content, 0.0, horizontal, lchild)
        _ -> spec.layout(c)
    LAct(_, _, _, _, _, _, ochild) ->
      match spec
        Act(o, onact, child) ->
          val lchild = reconcile(ochild, child, c)
          val (cw, ch) = lchild.size
          LAct(o, onact, clamp-w(c, cw), clamp-h(c, ch), 0.0, 0.0, lchild)
        _ -> spec.layout(c)
    LRotate(_, _, _, _, ochild) ->
      match spec
        Rotated(o, deg, child) ->
          val lchild = reconcile(ochild, child, c)
          val (cw, ch) = lchild.size
          LRotate(o, deg, cw, ch, lchild)
        _ -> spec.layout(c)
    LOverlay(_, _, _, ochild) ->
      match spec
        Overlaid(o, child) ->
          val lchild = reconcile(ochild, child, Constraints(0.0, unbounded-w, 0.0, unbounded-w))
          val (cw, ch) = lchild.size
          LOverlay(o, cw, ch, lchild)
        _ -> spec.layout(c)
    LClip(_, _, _, _, ochild) ->
      match spec
        Overlaid(o, child) ->
          val lchild = reconcile(ochild, child, Constraints(0.0, unbounded-w, 0.0, unbounded-w))
          val (cw, ch) = lchild.size
          LOverlay(o, cw, ch, lchild)
        Clipped(o, r, fw, fh, child) ->
          val lchild = reconcile(ochild, child, c)
          val (cw, ch) = lchild.size
          LClip(o, r, fw.default(cw), fh.default(ch), lchild)
        _ -> spec.layout(c)
    LTransform3d(_, _, _, _, ochild) ->
      match spec
        Transform3d(o, m3, child) ->
          val lchild = reconcile(ochild, child, c)
          val (cw, ch) = lchild.size
          LTransform3d(o, m3, cw, ch, lchild)
        _ -> spec.layout(c)
    LMemo(_, oid, srcw, olc, olt) ->
      match spec
        Memo(o, mid, child) ->
          // THE SHORT-CIRCUIT: an unchanged memo hit hands back the SAME
          // cached widget pointer -- reuse the laid-out subtree untouched.
          // The CONSTRAINTS must match too: a sibling changing size gives
          // this boundary different room, and a stale layout would misplace
          // everything after it (flutter's relayout-boundary rule).
          if mid == oid && unsafe-ptr-eq(srcw, child) && same-constraints(olc, c)
            then LMemo(o, oid, srcw, olc, olt)
          else LMemo(o, mid, child, c, reconcile(olt, child, c))
        _ -> spec.layout(c)
    LInteractive(_, _, _, _, _, _, _, _, ochild) ->
      match spec
        Interactive(o, k, oc, slop, child) ->
          val lchild = reconcile(ochild, child, c)
          val (cw, ch) = lchild.size
          LInteractive(o, k, oc, slop, clamp-w(c, cw), clamp-h(c, ch), 0.0, 0.0, lchild)
        _ -> spec.layout(c)
    LField(_, _, _, _, _, _, _) ->
      match spec
        TextField(o, k, ph, w0, onenter) ->
          LField(o, k, "", ph, onenter, clamp-w(c, w0), clamp-h(c, input-height))  // value re-baked
        _ -> spec.layout(c)
    LActMsg(_, _, _, _, _, _, ochild) ->
      match spec
        ActMsg(o, child, to-msg) ->
          val lchild = reconcile(ochild, child, c)
          val (cw, ch) = lchild.size
          LActMsg(o, to-msg, clamp-w(c, cw), clamp-h(c, ch), 0.0, 0.0, lchild)
        _ -> spec.layout(c)
    LInput(_, _, _, _, _, _, _, _) ->
      match spec
        TextInput(o, k, v, ph, w0, oninput, onkey) -> LInput(o, k, v, ph, oninput, onkey, clamp-w(c, w0), clamp-h(c, input-height))
        _ -> spec.layout(c)
    LSlider(_, _, _, _, _, _, _, _) ->
      match spec
        Slider(o, lo, hi, st, v, w0, onchange) -> LSlider(o, lo, hi, st, v, onchange, clamp-w(c, w0), clamp-h(c, slider-height))
        _ -> spec.layout(c)
    LImage(_, _, _, _, _) ->
      match spec
        Image(o, src, fit, w0, h0) ->
          val bw = if w0 > 0.0 then w0 elif is-unbounded(c.max-w) then default-image-width else c.max-w
          val bh = if h0 > 0.0 then h0 else default-image-height
          LImage(o, src, fit, clamp-w(c, bw), clamp-h(c, bh))
        _ -> spec.layout(c)

// reuse an old subtree's cell as the empty child of a sized box (drop its
// contents; if it was already an empty flex the cell reuses directly)
fun reuse-empty<msg>( old : ltree<msg> ) : ltree<msg>
  match old
    LFlex(_, _, _, _) -> LFlex(no-owner, 0.0, 0.0, [])
    _ -> LFlex(no-owner, 0.0, 0.0, [])

// drain a positioned child list to its bare ltrees so they drop
fun drop-kids<msg>( kids : list<(float64, float64, ltree<msg>)> ) : list<a>
  match kids
    Nil -> Nil
    Cons(_, rest) -> rest.drop-kids

// Flex reconcile. Fast path (same child count, no spacers -- grids, rows,
// most lists): reconcile+measure in one traversal and reposition in a
// second, BOTH reusing the old `cons` cells and `(dx,dy,ltree)` tuples in
// place, so only genuinely new content allocates. Spacers or a changed
// count fall back to a fresh flex layout (correctness over reuse).
fun reconcile-flex<msg>( o : int32, okids : list<(float64, float64, ltree<msg>)>, horizontal : bool, gap : float64,
                         fill : bool, children : list<widget<msg>>, c : constraints ) : <div,measure> ltree<msg>
  if same-length(okids, children) && !children.has-spacer then
    val child-c = child-constraints(horizontal, c)
    val (laid, summain, maxcross) = zip-measure(okids, children, horizontal, child-c)
    val count = laid.length
    val gaps = gap * (count - 1).float64.max(0.0)
    val cross-max = if horizontal then c.max-h else c.max-w
    val cross-min = if horizontal then c.min-h else c.min-w
    val cross = if fill && cross-max < 100000.0 then cross-max else maxcross.max(cross-min)
    val mainsz = summain + gaps
    val placed = reposition(laid, horizontal, gap, 0.0, cross)
    if horizontal then LFlex(o, clamp-w(c, mainsz), clamp-h(c, cross), placed)
                  else LFlex(o, clamp-w(c, cross), clamp-h(c, mainsz), placed)
  else
    okids.foreach(fn(_) ())      // drop the old positioned children
    layout-flex(o, horizontal, gap, fill, children, c)

// reconcile each child against the positionally-matching old child and
// accumulate the main-axis sum and max cross-axis; reuses cons + tuple cells
fun zip-measure<msg>( okids : list<(float64, float64, ltree<msg>)>, news : list<widget<msg>>,
                      horizontal : bool, c : constraints ) : <div,measure> (list<(float64, float64, ltree<msg>)>, float64, float64)
  match news
    Nil -> (Nil, 0.0, 0.0)                   // remaining okids drop
    Cons(w, wrest) ->
      match okids
        Cons(otup, orest) ->
          match otup
            (_, _, olt) ->
              val nlt = reconcile(olt, w.pretend-decreasing, c)
              val (nw, nh) = size(nlt)       // borrows nlt (see `size`)
              val (rest, sm, mc) = zip-measure(orest, wrest, horizontal, c)
              val mainv  = if horizontal then nw else nh
              val crossv = if horizontal then nh else nw
              (Cons((0.0, 0.0, nlt), rest), sm + mainv, mc.max(crossv))
        Nil ->
          val nlt = w.pretend-decreasing.layout(c)
          val (nw, nh) = size(nlt)
          val (rest, sm, mc) = zip-measure([], wrest, horizontal, c)
          val mainv  = if horizontal then nw else nh
          val crossv = if horizontal then nh else nw
          (Cons((0.0, 0.0, nlt), rest), sm + mainv, mc.max(crossv))

// assign cross-centered positions along the main axis; reuses cons + tuple
fun reposition<msg>( laid : list<(float64, float64, ltree<msg>)>, horizontal : bool, gap : float64,
                     at : float64, cross : float64 ) : list<(float64, float64, ltree<msg>)>
  match laid
    Nil -> Nil
    Cons(tup, rest) ->
      match tup
        (_, _, lt) ->
          val (w, h) = size(lt)
          val ext = if horizontal then w else h
          val crs = if horizontal then h else w
          val center = (cross - crs) / 2.0
          val ndx = if horizontal then at else center
          val ndy = if horizontal then center else at
          Cons((ndx, ndy, lt), reposition(rest, horizontal, gap, at + ext + gap, cross))

// reconcile a `center`: reuse the single child ltree, recompute the centering
fun reconcile-center<msg>( o : int32, okids : list<(float64, float64, ltree<msg>)>, mw : float64,
                           child : widget<msg>, c : constraints ) : <div,measure> ltree<msg>
  val inner = Constraints(0.0, c.max-w.min(mw), c.min-h, c.max-h)
  val lchild = match okids
    Cons(otup, orest) ->
      orest.foreach(fn(_) ())        // drop any extra old children
      reconcile(otup.thd, child, inner)
    Nil -> child.layout(inner)
  val (childw, childh) = lchild.size
  val w0 = clamp-w(c, childw)
  val x = ((w0 - childw) / 2.0).max(0.0)
  LFlex(o, w0, clamp-h(c, childh), [(x, 0.0, lchild)])

// reconcile an `intrinsic-width`: the probe is a fresh throwaway layout (its
// natural width depends on new content), but the real pass reuses the old child
fun reconcile-intrinsic<msg>( o : int32, okids : list<(float64, float64, ltree<msg>)>,
                              child : widget<msg>, c : constraints ) : <div,measure> ltree<msg>
  val probe = child.pretend-decreasing.layout(Constraints(0.0, unbounded-w, c.min-h, c.max-h))
  val w0 = clamp-w(c, probe.size.fst)
  val inner = Constraints(w0, w0, c.min-h, c.max-h)
  val lchild = match okids
    Cons(otup, orest) ->
      orest.foreach(fn(_) ())        // drop any extra old children
      reconcile(otup.thd, child, inner)
    Nil -> child.layout(inner)
  val (_, childh) = lchild.size
  LFlex(o, w0, clamp-h(c, childh), [(0.0, 0.0, lchild)])

fun reconcile-stack<msg>( o : int32, okids : list<(float64, float64, ltree<msg>)>, children : list<(float64, float64, widget<msg>)>,
                          c : constraints ) : <div,measure> ltree<msg>
  if same-length(okids, children) then
    val inner = Constraints(0.0, c.max-w, 0.0, c.max-h)
    val (kids, w0, h0) = zip-stack(okids, children, inner)
    LFlex(o, clamp-w(c, w0), clamp-h(c, h0), kids)
  else
    okids.foreach(fn(_) ())
    Stack(o, children).layout(c)

// reconcile stacked children keeping their new offsets; reuses cons + tuple
fun zip-stack<msg>( okids : list<(float64, float64, ltree<msg>)>, news : list<(float64, float64, widget<msg>)>,
                    c : constraints ) : <div,measure> (list<(float64, float64, ltree<msg>)>, float64, float64)
  match news
    Nil -> (Nil, 0.0, 0.0)
    Cons(ntup, nrest) ->
      match ntup
        (ndx, ndy, w) ->
          match okids
            Cons(otup, orest) ->
              match otup
                (_, _, olt) ->
                  val nlt = reconcile(olt, w.pretend-decreasing, c)
                  val (nw, nh) = size(nlt)
                  val (rest, mw, mh) = zip-stack(orest, nrest, c)
                  (Cons((ndx, ndy, nlt), rest), (ndx + nw).max(mw), (ndy + nh).max(mh))
            Nil ->
              val nlt = w.pretend-decreasing.layout(c)
              val (nw, nh) = size(nlt)
              val (rest, mw, mh) = zip-stack([], nrest, c)
              (Cons((ndx, ndy, nlt), rest), (ndx + nw).max(mw), (ndy + nh).max(mh))

// borrow helpers for the fast-path guard (no consume)
fun same-length<a,b>( ^xs : list<a>, ^ys : list<b> ) : bool
  match xs
    Nil -> match ys { Nil -> True; _ -> False }
    Cons(_, xr) -> match ys { Nil -> False; Cons(_, yr) -> same-length(xr, yr) }

// does the flex contain a grower (spacer / expanded)? such children need the
// leftover-space division in `layout-flex`, so the fast reconcile path bails.
fun has-spacer<msg>( ^ws : list<widget<msg>> ) : bool
  match ws
    Nil -> False
    Cons(Spacer(_), _) -> True
    Cons(Expanded(_, _, _), _) -> True
    Cons(_, r) -> has-spacer(r)

// ----------------------------------------------------------------
// hit-testing over the laid-out tree (used by pointer-driven backends;
// the web backend uses DOM listeners from the lowering instead)

// what lives under a point
pub type hit<a>
  HitMsg( msg : a )
  HitAt( to-msg : (float64, float64) -> a, x : float64, y : float64 )
  HitInput( key : int )                                        // focus the input with this identity
  HitSlider( to-msg : float64 -> a, value : float64 )          // value from position
  HitLink( to : string )                                       // navigate to a route path
  HitAct( act : () -> <uistate,ioc> () )                                 // run a thunk (ui/state write)
  HitMsgIoc( to-msg : () -> <uistate,ioc> a )                            // compute a message from ui/state at click time (act-msg / form submit)                                 // run a thunk (ui/state write); an opaque surface uses `HitAct(fn() ())` to absorb a click without falling through

// the front-most interactive target under (px,py); text inputs are
// identified by their widget identity (stable across re-renders and reorders)
pub fun hit<msg>( t : ltree<msg>, px : float64, py : float64 ) : div maybe<hit<msg>>
  t.hit-go(px, py, 0.0, 0.0)

fun hit-go<msg>( t : ltree<msg>, px : float64, py : float64,
                 x : float64, y : float64 ) : div maybe<hit<msg>>
  match t
    LText -> Nothing
    LImage -> Nothing
    LRich(_, _, _, _, spans, _, w, h, rects) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else
        fun rect-hit( r : (float64,float64,float64,float64) ) : bool
          val (rx,ry,rw,rh) = r
          px >= x + rx && px <= x + rx + rw && py >= y + ry && py <= y + ry + rh
        val hit-span = rects.find fn(entry)
          val (_, span-rects) = entry
          span-rects.any(rect-hit)
        match hit-span
          Just((idx, _)) ->
            match spans.drop(idx).head
              Just(s) -> s.on-click.map(HitMsg)
              Nothing -> Nothing
          Nothing -> Nothing
    LRotate(_, _, _, _, child) -> child.hit-go(px, py, x, y)   // hit at the unrotated rect
    // a clip is a real hit boundary, not just a paint one: a point outside the
    // rect cannot reach the child (corner radii are approximated by the rect,
    // the same approximation LScroll's viewport clip makes)
    LClip(_, _, w, h, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-go(px, py, x, y)
    LOverlay(_, _, _, _) -> Nothing   // decoration: never swallows a click
    LTransform3d(_, m3, w0, h0, child) ->
      // rebuild the SAME center-wrapped M' the paint arm concatenates (see
      // ui/api/impeller/backend.kk's LTransform3d paint arm) and unproject
      // the click through its inverse. `unproject` returns coordinates
      // already in the child's own pre-transform (x,y)-based absolute
      // frame -- the SAME frame `hit-go` threads everywhere else -- so the
      // result is passed straight through as the new (px,py); the (x,y)
      // accumulator is unchanged (see the frame note in
      // test/ui/transform-hit.kk).
      val cx = x + w0 / 2.0
      val cy = y + h0 / 2.0
      val m4 = m3.centered(cx, cy)
      match m4.unproject(px, py)
        Just((lx, ly)) -> child.hit-go(lx, ly, x, y)
        Nothing -> Nothing
    LMemo(_, _, _, _, child) -> child.hit-go(px, py, x, y)
    LLink(_, to, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h
        then Nothing
        else
          match child.hit-go(px, py, x + dx, y + dy)
            Just(r) -> Just(r)                 // an inner target wins over the link
            Nothing -> Just(HitLink(to))
    LScroll(_, _, w, h, _, offset, horizontal, child) ->
      // clip to the viewport; the child is painted shifted by `offset` along the
      // scroll axis, so hit-test it at the same shifted origin
      if px < x || px > x + w || py < y || py > y + h
        then Nothing
        else if horizontal then child.hit-go(px, py, x - offset, y)
             else child.hit-go(px, py, x, y - offset)
    LAct(_, onact, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h
        then Nothing
        else
          match child.hit-go(px, py, x + dx, y + dy)
            Just(r) -> Just(r)                 // an inner msg target wins over the act
            Nothing -> Just(HitAct(onact))
    LInteractive(_, _, onclick, slop, w, h, dx, dy, child) ->
      if px < x - slop || px > x + w + slop || py < y - slop || py > y + h + slop
        then Nothing
        else
          match child.hit-go(px, py, x + dx, y + dy)   // slop area falls through to the act below
            Just(r) -> Just(r)                 // an inner target wins
            Nothing -> onclick.map(fn(m) HitMsg(m))
    LInput(_, key, _, _, _, _, w, h) ->
      if px >= x && px <= x + w && py >= y && py <= y + h
        then Just(HitInput(key)) else Nothing
    LField(_, key, _, _, _, w, h) ->
      if px >= x && px <= x + w && py >= y && py <= y + h
        then Just(HitInput(key)) else Nothing
    LActMsg(_, to-msg, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h
        then Nothing
        else
          match child.hit-go(px, py, x + dx, y + dy)
            Just(r) -> Just(r)                 // an inner target wins
            Nothing -> Just(HitMsgIoc(to-msg))
    LSlider(_, lo, hi, step, _, onchange, w, h) ->
      // generous vertical hit band (the visible track is thin)
      if px >= x - 4.0 && px <= x + w + 4.0 && py >= y - 8.0 && py <= y + h + 8.0
        then Just(HitSlider(onchange, snap(lo + (hi - lo) * ((px - x).max(0.0).min(w) / w.max(1.0)), lo, hi, step)))
        else Nothing
    LBox(_, _, on, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h
        then Nothing
        else
          match child.hit-go(px, py, x + dx, y + dy)
            Just(r) -> Just(r)                 // children are on top of their box
            Nothing ->
              match on.click-at
                Just(g) -> Just(HitAt(g, px, py))
                Nothing -> on.click.map(fn(m) HitMsg(m))
    LFlex(_, _, _, children) ->
      children.hit-list(px, py, x, y)
    LLayer(_, _, _, children) ->
      children.hit-list(px, py, x, y)

// the TOPMOST overlapping sibling wins: children paint in source order (later
// on top), so a later hitting child (an overlay layer, a dismiss scrim) claims
// the click over an earlier one.
fun hit-list<msg>( children : list<(float64, float64, ltree<msg>)>,
                   px : float64, py : float64, x : float64, y : float64 ) : div maybe<hit<msg>>
  match children
    Nil -> Nothing
    Cons((dx, dy, child), rest) ->
      val r = child.hit-go(px, py, x + dx, y + dy)
      match rest.hit-list(px, py, x, y)
        Just(rr) -> Just(rr)       // a later (topmost) sibling wins
        Nothing -> r

fun snap( v : float64, lo : float64, hi : float64, step : float64 ) : float64
  val vv = v.max(lo).min(hi)
  if step <= 0.0 then vv else lo + ((vv - lo) / step).round * step

// the front-most drag-source payload under a point (pointer press)
pub fun hit-drag<msg>( t : ltree<msg>, px : float64, py : float64,
                       x : float64 = 0.0, y : float64 = 0.0 ) : div maybe<string>
  match t
    LLink(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-drag(px, py, x + dx, y + dy)
    LScroll(_, _, w, h, _, offset, horizontal, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else if horizontal then child.hit-drag(px, py, x - offset, y)
           else child.hit-drag(px, py, x, y - offset)
    LAct(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-drag(px, py, x + dx, y + dy)
    LInteractive(_, _, _, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-drag(px, py, x + dx, y + dy)
    LBox(_, _, on, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing else
        match child.hit-drag(px, py, x + dx, y + dy)
          Just(p) -> Just(p)
          Nothing -> on.drag
    LFlex(_, _, _, children) -> children.drag-list(px, py, x, y)
    LLayer(_, _, _, children) -> children.drag-list(px, py, x, y)
    _ -> Nothing

fun drag-list<msg>( children : list<(float64, float64, ltree<msg>)>,
                    px : float64, py : float64, x : float64, y : float64 ) : div maybe<string>
  match children
    Nil -> Nothing
    Cons((dx, dy, child), rest) ->
      match child.hit-drag(px, py, x + dx, y + dy)
        Just(p) -> Just(p)
        Nothing -> rest.drag-list(px, py, x, y)

// the front-most drop-target handler under a point (pointer release)
pub fun hit-drop<msg>( t : ltree<msg>, px : float64, py : float64,
                       x : float64 = 0.0, y : float64 = 0.0 ) : div maybe<string -> msg>
  match t
    LMemo(_, _, _, _, child) -> child.hit-drop(px, py, x, y)
    LLink(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-drop(px, py, x + dx, y + dy)
    LScroll(_, _, w, h, _, offset, horizontal, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else if horizontal then child.hit-drop(px, py, x - offset, y)
           else child.hit-drop(px, py, x, y - offset)
    LAct(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-drop(px, py, x + dx, y + dy)
    LInteractive(_, _, _, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-drop(px, py, x + dx, y + dy)
    LBox(_, _, on, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing else
        match child.hit-drop(px, py, x + dx, y + dy)
          Just(g) -> Just(g)
          Nothing -> on.drop
    LFlex(_, _, _, children) -> children.drop-list(px, py, x, y)
    LLayer(_, _, _, children) -> children.drop-list(px, py, x, y)
    _ -> Nothing

fun drop-list<msg>( children : list<(float64, float64, ltree<msg>)>,
                    px : float64, py : float64, x : float64, y : float64 ) : div maybe<string -> msg>
  match children
    Nil -> Nothing
    Cons((dx, dy, child), rest) ->
      match child.hit-drop(px, py, x + dx, y + dy)
        Just(g) -> Just(g)
        Nothing -> rest.drop-list(px, py, x, y)

// the front-most RIGHT-click (context-menu) handler under a point. Mirrors
// `hit-drop`: the innermost `pointer.context-at` under the pointer wins, and it
// carries the pointer position so the caller can anchor a menu at the cursor.
pub fun hit-context<msg>( t : ltree<msg>, px : float64, py : float64,
                          x : float64 = 0.0, y : float64 = 0.0 ) : div maybe<(float64, float64) -> msg>
  match t
    LMemo(_, _, _, _, child) -> child.hit-context(px, py, x, y)
    LLink(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-context(px, py, x + dx, y + dy)
    LScroll(_, _, w, h, _, offset, horizontal, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else if horizontal then child.hit-context(px, py, x - offset, y)
           else child.hit-context(px, py, x, y - offset)
    LAct(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-context(px, py, x + dx, y + dy)
    LInteractive(_, _, _, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hit-context(px, py, x + dx, y + dy)
    LBox(_, _, on, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing else
        match child.hit-context(px, py, x + dx, y + dy)
          Just(g) -> Just(g)
          Nothing -> on.context-at
    LFlex(_, _, _, children) -> children.context-list(px, py, x, y)
    LLayer(_, _, _, children) -> children.context-list(px, py, x, y)
    _ -> Nothing

fun context-list<msg>( children : list<(float64, float64, ltree<msg>)>,
                       px : float64, py : float64, x : float64, y : float64 ) : div maybe<(float64, float64) -> msg>
  match children
    Nil -> Nothing
    Cons((dx, dy, child), rest) ->
      match child.hit-context(px, py, x + dx, y + dy)
        Just(g) -> Just(g)
        Nothing -> rest.context-list(px, py, x, y)

// an active drag, shared by both backends: the payload, the ghost subtree that
// follows the pointer, the grab offset (pointer minus the box's top-left at
// press) and the live pointer position. Composited as a top layer at
// (x - grab-x, y - grab-y) -- a drag is just another positioned view.
pub struct drag-st<a>
  payload : string
  ghost   : ltree<a>
  grab-x  : float64
  grab-y  : float64
  x       : float64
  y       : float64

// the front-most DRAG SOURCE under a point: its payload, its laid-out subtree
// (to render as the drag ghost that follows the pointer), and the subtree's
// absolute top-left. Both backends snapshot this on press and composite the
// ghost as a top layer -- so a drag is just another positioned view.
pub fun drag-at<msg>( t : ltree<msg>, px : float64, py : float64,
                      x : float64 = 0.0, y : float64 = 0.0 ) : div maybe<(string, ltree<msg>, float64, float64)>
  match t
    LMemo(_, _, _, _, child) -> child.drag-at(px, py, x, y)
    LLink(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.drag-at(px, py, x + dx, y + dy)
    LScroll(_, _, w, h, _, offset, horizontal, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else if horizontal then child.drag-at(px, py, x - offset, y)
           else child.drag-at(px, py, x, y - offset)
    LAct(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.drag-at(px, py, x + dx, y + dy)
    LInteractive(_, _, _, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.drag-at(px, py, x + dx, y + dy)
    LBox(o, bg, on, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing else
        match child.drag-at(px, py, x + dx, y + dy)   // an inner drag source wins
          Just(r) -> Just(r)
          Nothing -> match on.drag
            Just(p) -> Just((p, LBox(o, bg, on, w, h, dx, dy, child), x, y))  // ghost = this box
            Nothing -> Nothing
    LFlex(_, _, _, children) -> children.drag-at-list(px, py, x, y)
    LLayer(_, _, _, children) -> children.drag-at-list(px, py, x, y)
    _ -> Nothing

fun drag-at-list<msg>( children : list<(float64, float64, ltree<msg>)>,
                       px : float64, py : float64, x : float64, y : float64 ) : div maybe<(string, ltree<msg>, float64, float64)>
  match children
    Nil -> Nothing
    Cons((dx, dy, child), rest) ->
      match child.drag-at(px, py, x + dx, y + dy)
        Just(r) -> Just(r)
        Nothing -> rest.drag-at-list(px, py, x, y)

// the text input with identity `k` (for focus-directed key events)
pub fun input-with-key<msg>( t : ltree<msg>, k : int ) : div maybe<ltree<msg>>
  match t
    LInput(_, key, _, _, _, _, _, _) -> if key == k then Just(t) else Nothing
    LField(_, key, _, _, _, _, _) -> if key == k then Just(t) else Nothing
    LActMsg(_, _, _, _, _, _, child) -> child.input-with-key(k)
    LRotate(_, _, _, _, child) -> child.input-with-key(k)
    LClip(_, _, _, _, child) -> child.input-with-key(k)
    LOverlay(_, _, _, child) -> child.input-with-key(k)
    LTransform3d(_, _, _, _, child) -> child.input-with-key(k)
    LMemo(_, _, _, _, child) -> child.input-with-key(k)
    LLink(_, _, _, _, _, _, child) -> child.input-with-key(k)
    LScroll(_, _, _, _, _, _, _, child) -> child.input-with-key(k)
    LAct(_, _, _, _, _, _, child) -> child.input-with-key(k)
    LInteractive(_, _, _, _, _, _, _, _, child) -> child.input-with-key(k)
    LBox(_, _, _, _, _, _, _, child) -> child.input-with-key(k)
    LFlex(_, _, _, children) -> children.input-with-key-list(k)
    LLayer(_, _, _, children) -> children.input-with-key-list(k)
    _ -> Nothing

fun input-with-key-list<msg>( children : list<(float64, float64, ltree<msg>)>, k : int ) : div maybe<ltree<msg>>
  match children
    Nil -> Nothing
    Cons((_, _, child), rest) ->
      match child.input-with-key(k)
        Just(r) -> Just(r)
        Nothing -> rest.input-with-key-list(k)

// the absolute rect (x,y,w,h) of the front-most interactive element under a
// point -- used by pointer-driven backends to draw the hover/press affordance
// (the web backend uses CSS `:hover` instead). "Interactive" = a clickable
// box, a link, or an act; the innermost one wins (a button inside a card).
pub fun hover-rect<msg>( t : ltree<msg>, px : float64, py : float64,
                         x : float64 = 0.0, y : float64 = 0.0 ) : div maybe<(float64,float64,float64,float64)>
  match t
    LRotate(_, _, _, _, child) -> child.hover-rect(px, py, x, y)
    LClip(_, _, w, h, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hover-rect(px, py, x, y)
    LOverlay(_, _, _, _) -> Nothing
    LTransform3d(_, _, _, _, child) -> child.hover-rect(px, py, x, y)
    LMemo(_, _, _, _, child) -> child.hover-rect(px, py, x, y)
    LLink(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else match child.hover-rect(px, py, x + dx, y + dy)
        Just(r) -> Just(r)
        Nothing -> Just((x, y, w, h))
    LAct(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else match child.hover-rect(px, py, x + dx, y + dy)
        Just(r) -> Just(r)
        Nothing -> Just((x, y, w, h))
    LBox(_, _, on, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else match child.hover-rect(px, py, x + dx, y + dy)
        Just(r) -> Just(r)
        Nothing -> if on.click.is-just || on.click-at.is-just || on.context-at.is-just || on.drag.is-just || on.drop.is-just
                     then Just((x, y, w, h)) else Nothing
    LScroll(_, _, w, h, _, offset, horizontal, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else if horizontal then child.hover-rect(px, py, x - offset, y)
           else child.hover-rect(px, py, x, y - offset)
    LFlex(_, _, _, children) -> children.hover-list(px, py, x, y)
    LLayer(_, _, _, children) -> children.hover-list(px, py, x, y)
    _ -> Nothing

fun hover-list<msg>( children : list<(float64, float64, ltree<msg>)>,
                     px : float64, py : float64, x : float64, y : float64 ) : div maybe<(float64,float64,float64,float64)>
  match children
    Nil -> Nothing
    Cons((dx, dy, child), rest) ->
      match child.hover-rect(px, py, x + dx, y + dy)
        Just(r) -> Just(r)
        Nothing -> rest.hover-list(px, py, x, y)

// the identity key of the front-most `interactive` element under a point (for
// the pump to write into `ui/state`'s hovered-key -- the builder-driven hover)
// The front-most interactive element under a point, as (key, x, y, w, h) --
// the SAME walk `hover-key` makes, keeping the element's rect instead of
// throwing it away. An ink ripple needs the press in the pressed element's own
// coordinates, and `hover-rect` cannot answer that: it deliberately reports
// only clickable BOXES, links and acts, so that a native backend's hover
// affordance does not also frame every `interactive`-built button. Rather than
// widen that (a visible change) or copy this traversal, `hover-key` is now
// defined in terms of this one.
pub fun hover-key-rect<msg>( t : ltree<msg>, px : float64, py : float64,
                        x : float64 = 0.0, y : float64 = 0.0 ) : div maybe<(int, float64, float64, float64, float64)>
  match t
    LRotate(_, _, _, _, child) -> child.hover-key-rect(px, py, x, y)
    LClip(_, _, w, h, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else child.hover-key-rect(px, py, x, y)
    LOverlay(_, _, _, _) -> Nothing
    LTransform3d(_, _, _, _, child) -> child.hover-key-rect(px, py, x, y)
    LMemo(_, _, _, _, child) -> child.hover-key-rect(px, py, x, y)
    LInteractive(_, key, _, slop, w, h, dx, dy, child) ->
      if px < x - slop || px > x + w + slop || py < y - slop || py > y + h + slop then Nothing
      else match child.hover-key-rect(px, py, x + dx, y + dy)
        Just(k) -> Just(k)                 // an inner interactive wins
        Nothing -> Just((key, x, y, w, h))
    LLink(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing else child.hover-key-rect(px, py, x + dx, y + dy)
    LAct(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing else child.hover-key-rect(px, py, x + dx, y + dy)
    LBox(_, _, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing else child.hover-key-rect(px, py, x + dx, y + dy)
    LScroll(_, _, w, h, _, offset, horizontal, child) ->
      if px < x || px > x + w || py < y || py > y + h then Nothing
      else if horizontal then child.hover-key-rect(px, py, x - offset, y)
           else child.hover-key-rect(px, py, x, y - offset)
    LFlex(_, _, _, children) -> children.hover-key-rect-list(px, py, x, y)
    LLayer(_, _, _, children) -> children.hover-key-rect-list(px, py, x, y)
    _ -> Nothing

fun hover-key-rect-list<msg>( children : list<(float64, float64, ltree<msg>)>,
                         px : float64, py : float64, x : float64, y : float64 ) : div maybe<(int, float64, float64, float64, float64)>
  match children
    Nil -> Nothing
    Cons((dx, dy, child), rest) ->
      match child.hover-key-rect(px, py, x + dx, y + dy)
        Just(k) -> Just(k)
        Nothing -> rest.hover-key-rect-list(px, py, x, y)

pub fun hover-key<msg>( t : ltree<msg>, px : float64, py : float64,
                        x : float64 = 0.0, y : float64 = 0.0 ) : div maybe<int>
  t.hover-key-rect(px, py, x, y).map(fn(r) r.fst)

// Where owner `id` sits INSIDE its innermost enclosing VERTICAL scroll
// region: `(scroll-key, y, content, viewport)` with `y` relative to the
// scroll CONTENT's origin -- i.e. the offset that puts the owner's top at the
// viewport's top. This is the geometry half of scroll-to-anchor (ui/state's
// `scroll-to`): scrolling is Koka-owned, so "jump to #section" means setting
// that region's offset, not asking a browser.
//
// Content coordinates, deliberately: children inside an `LScroll` are laid
// out UNSHIFTED (painting applies the offset), so accumulating dy from the
// scroll child's origin measures pure content geometry -- the current offset
// never enters into it, which is what lets this run before `bake-scroll`
// writes offsets. `content`/`viewport` come from the SAME tree, so clamping
// needs no (possibly stale) published metrics. A target outside any vertical
// scroll returns Nothing: there is nothing to scroll.
pub fun scroll-anchor-pos<msg>( ^t : ltree<msg>, id : int,
                                scroll : maybe<(int, float64, float64)> = Nothing,
                                y : float64 = 0.0 ) : div maybe<(int, float64, float64, float64)>
  if t.owner.int == id then
    match scroll
      Just((skey, content, vp)) -> Just((skey, y, content, vp))
      Nothing -> Nothing
  else match t
    LScroll(_, key, w, h, content, _, horizontal, child) ->
      if horizontal
        then child.scroll-anchor-pos(id, scroll, y)   // horizontal: pass through (vertical anchor context unchanged)
        else child.scroll-anchor-pos(id, Just((key, content, h)), 0.0)
    LBox(_, _, _, _, _, _, dy, child) -> child.scroll-anchor-pos(id, scroll, y + dy)
    LLink(_, _, _, _, _, dy, child) -> child.scroll-anchor-pos(id, scroll, y + dy)
    LAct(_, _, _, _, _, dy, child) -> child.scroll-anchor-pos(id, scroll, y + dy)
    LActMsg(_, _, _, _, _, dy, child) -> child.scroll-anchor-pos(id, scroll, y + dy)
    LInteractive(_, _, _, _, _, _, _, dy, child) -> child.scroll-anchor-pos(id, scroll, y + dy)
    LRotate(_, _, _, _, child) -> child.scroll-anchor-pos(id, scroll, y)
    LClip(_, _, _, _, child) -> child.scroll-anchor-pos(id, scroll, y)
    LOverlay(_, _, _, child) -> child.scroll-anchor-pos(id, scroll, y)
    LTransform3d(_, _, _, _, child) -> child.scroll-anchor-pos(id, scroll, y)
    LMemo(_, _, _, _, child) -> child.scroll-anchor-pos(id, scroll, y)
    LFlex(_, _, _, kids) -> kids.anchor-list(id, scroll, y)
    LLayer(_, _, _, kids) -> kids.anchor-list(id, scroll, y)
    _ -> Nothing

fun anchor-list<msg>( kids : list<(float64, float64, ltree<msg>)>, id : int,
                      scroll : maybe<(int, float64, float64)>, y : float64 ) : div maybe<(int, float64, float64, float64)>
  match kids
    Nil -> Nothing
    Cons((_, dy, child), rest) ->
      match child.scroll-anchor-pos(id, scroll, y + dy)
        Just(r) -> Just(r)
        Nothing -> rest.anchor-list(id, scroll, y)

// every SCROLLABLE region containing a point, INNERMOST FIRST: each entry is
// (key, content-extent, viewport-extent, horizontal). Only regions whose
// content exceeds the viewport qualify. `apply-wheel` (ui/state) walks this
// chain rather than just the innermost region -- a wheel gesture whose axis
// doesn't match the innermost region (e.g. a vertical wheel tick over a
// horizontal code-block scroll nested inside a page's own vertical scroll)
// can still reach an enclosing region on the matching axis, instead of
// being trapped by whichever region is physically closest to the cursor.
pub fun scroll-at<msg>( t : ltree<msg>, px : float64, py : float64,
                        x : float64 = 0.0, y : float64 = 0.0 ) : div list<(int,float64,float64,bool)>
  match t
    LMemo(_, _, _, _, child) -> child.scroll-at(px, py, x, y)
    LLink(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then [] else child.scroll-at(px, py, x + dx, y + dy)
    LAct(_, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then [] else child.scroll-at(px, py, x + dx, y + dy)
    LInteractive(_, _, _, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then [] else child.scroll-at(px, py, x + dx, y + dy)
    LBox(_, _, _, w, h, dx, dy, child) ->
      if px < x || px > x + w || py < y || py > y + h then [] else child.scroll-at(px, py, x + dx, y + dy)
    LScroll(_, key, w, h, content, offset, horizontal, child) ->
      if px < x || px > x + w || py < y || py > y + h then []
      else
        val inner = if horizontal then child.scroll-at(px, py, x - offset, y)
                    else child.scroll-at(px, py, x, y - offset)   // deeper regions come first
        val vp = if horizontal then w else h
        if content > vp then inner ++ [(key, content, vp, horizontal)] else inner
    LFlex(_, _, _, children) -> children.scroll-at-list(px, py, x, y)
    LLayer(_, _, _, children) -> children.scroll-at-list(px, py, x, y)
    _ -> []

fun scroll-at-list<msg>( children : list<(float64, float64, ltree<msg>)>,
                         px : float64, py : float64, x : float64, y : float64 ) : div list<(int,float64,float64,bool)>
  match children
    Nil -> []
    Cons((dx, dy, child), rest) ->
      val r = child.scroll-at(px, py, x + dx, y + dy)
      if r.is-cons then r else rest.scroll-at-list(px, py, x, y)

// visit every scroll region in the tree with its (key, content-height,
// viewport-height) -- the backend uses this to keep ui/state's scroll metrics
// in sync with the laid-out tree, so a linked scrollbar sizes correctly.
pub fun each-scroll<msg>( t : ltree<msg>, f : (int, float64, float64) -> <uistate,ioc> () ) : <uistate,ioc> ()
  match t
    LScroll(_, key, w, h, content, _, horizontal, child) ->
      f(key, content, if horizontal then w else h)   // metrics ALONG the scroll axis
      child.each-scroll(f)
    LBox(_, _, _, _, _, _, _, child) -> child.each-scroll(f)
    LLink(_, _, _, _, _, _, child) -> child.each-scroll(f)
    LAct(_, _, _, _, _, _, child) -> child.each-scroll(f)
    LActMsg(_, _, _, _, _, _, child) -> child.each-scroll(f)
    LInteractive(_, _, _, _, _, _, _, _, child) -> child.each-scroll(f)
    LRotate(_, _, _, _, child) -> child.each-scroll(f)
    LClip(_, _, _, _, child) -> child.each-scroll(f)
    LOverlay(_, _, _, child) -> child.each-scroll(f)
    LTransform3d(_, _, _, _, child) -> child.each-scroll(f)
    LMemo(_, _, _, _, child) -> child.each-scroll(f)
    LFlex(_, _, _, children) -> children.each-scroll-list(f)
    LLayer(_, _, _, children) -> children.each-scroll-list(f)
    _ -> ()

fun each-scroll-list<msg>( children : list<(float64, float64, ltree<msg>)>,
                           f : (int, float64, float64) -> <uistate,ioc> () ) : <uistate,ioc> ()
  match children
    Nil -> ()
    Cons((_, _, child), rest) ->
      child.each-scroll(f)
      rest.each-scroll-list(f)

// ----------------------------------------------------------------
// owner-identity queries over the laid-out tree (the addressing foundation):
// a node's `owner` is the content-addressed key id that built it, so a
// selector resolved to an id can be turned into geometry / text with NO
// keytree handler in scope (the ltree carries the id directly).

// the absolute rect (x,y,w,h) of the SHALLOWEST node whose `owner == id`,
// accumulating positions exactly like the paint walk (dx/dy at wrapper nodes,
// the baked offset at scroll viewports, child entry offsets in a flex) AND
// clipping to the enclosing scroll viewports exactly as `hit` does (see
// task-50: a target scrolled out of its viewport must not report an
// off-screen-but-present rect -- a fully-clipped node reports Nothing, same
// "not there" reading `hit`/`find` give an unmounted widget).
// `Nothing` if no node in the tree carries that identity, or it is entirely
// clipped away by an ancestor scroll viewport.
pub fun owner-rect<msg>( t : ltree<msg>, id : int, x : float64 = 0.0, y : float64 = 0.0,
                         cl : float64 = neg-unbounded-w, ct : float64 = neg-unbounded-w,
                         cr : float64 = unbounded-w,  cb : float64 = unbounded-w ) : div maybe<(float64,float64,float64,float64)>
  if t.owner == id.int32 then
    val (w, h) = t.size
    val ix0 = x.max(cl); val iy0 = y.max(ct)
    val ix1 = (x + w).min(cr); val iy1 = (y + h).min(cb)
    if ix1 > ix0 && iy1 > iy0 then Just((ix0, iy0, ix1 - ix0, iy1 - iy0)) else Nothing
  else
    match t
      LBox(_, _, _, _, _, dx, dy, child) -> child.owner-rect(id, x + dx, y + dy, cl, ct, cr, cb)
      LFlex(_, _, _, children) -> children.owner-rect-list(id, x, y, cl, ct, cr, cb)
      LLayer(_, _, _, children) -> children.owner-rect-list(id, x, y, cl, ct, cr, cb)
      LLink(_, _, _, _, dx, dy, child) -> child.owner-rect(id, x + dx, y + dy, cl, ct, cr, cb)
      LAct(_, _, _, _, dx, dy, child) -> child.owner-rect(id, x + dx, y + dy, cl, ct, cr, cb)
      LActMsg(_, _, _, _, dx, dy, child) -> child.owner-rect(id, x + dx, y + dy, cl, ct, cr, cb)
      LInteractive(_, _, _, _, _, _, dx, dy, child) -> child.owner-rect(id, x + dx, y + dy, cl, ct, cr, cb)
      LRotate(_, _, _, _, child) -> child.owner-rect(id, x, y, cl, ct, cr, cb)
      LClip(_, _, _, _, child) -> child.owner-rect(id, x, y, cl, ct, cr, cb)
      LOverlay(_, _, _, child) -> child.owner-rect(id, x, y, cl, ct, cr, cb)
      LTransform3d(_, _, _, _, child) -> child.owner-rect(id, x, y, cl, ct, cr, cb)
      LMemo(_, _, _, _, child) -> child.owner-rect(id, x, y, cl, ct, cr, cb)
      LScroll(_, _, w, h, _, offset, horizontal, child) ->
        // the child is clipped to THIS viewport (intersected with the inherited
        // clip); recurse at the scrolled origin so its rect lands where painted
        val ncl = x.max(cl); val nct = y.max(ct)
        val ncr = (x + w).min(cr); val ncb = (y + h).min(cb)
        if horizontal then child.owner-rect(id, x - offset, y, ncl, nct, ncr, ncb)
        else child.owner-rect(id, x, y - offset, ncl, nct, ncr, ncb)
      _ -> Nothing

fun owner-rect-list<msg>( children : list<(float64, float64, ltree<msg>)>, id : int,
                          x : float64, y : float64,
                          cl : float64, ct : float64, cr : float64, cb : float64 ) : div maybe<(float64,float64,float64,float64)>
  match children
    Nil -> Nothing
    Cons((dx, dy, child), rest) ->
      match child.pretend-decreasing.owner-rect(id, x + dx, y + dy, cl, ct, cr, cb)
        Just(r) -> Just(r)
        Nothing -> rest.owner-rect-list(id, x, y, cl, ct, cr, cb)

// all text content in the subtree rooted at the SHALLOWEST node whose
// `owner == id` (the target id, or any descendant identity -- everything under
// that node). `[]` if the id is not present in the tree.
pub fun owner-texts<msg>( t : ltree<msg>, id : int ) : div list<string>
  match t.owner-find-texts(id.int32)
    Just(ts) -> ts
    Nothing  -> []

// is `id` present as a node ANYWHERE in this tree (NOT clipped -- distinct
// from owner-rect, which returns Nothing for a scrolled-out node)? Used to
// filter selector candidates to the ones actually mounted this frame: a
// KeepAlive-retained but UNMOUNTED identity lingers in the keytrie id->path
// table (so kt-find lists it) yet has no node here, and must not count toward
// a selector's ambiguity.
pub fun owner-present<msg>( t : ltree<msg>, id : int ) : div bool
  t.owner-find-texts(id.int32).is-just

fun owner-find-texts<msg>( t : ltree<msg>, target : int32 ) : div maybe<list<string>>
  if t.owner == target then Just(t.subtree-texts)
  else
    match t
      LBox(_, _, _, _, _, _, _, child) -> child.owner-find-texts(target)
      LLink(_, _, _, _, _, _, child) -> child.owner-find-texts(target)
      LAct(_, _, _, _, _, _, child) -> child.owner-find-texts(target)
      LActMsg(_, _, _, _, _, _, child) -> child.owner-find-texts(target)
      LInteractive(_, _, _, _, _, _, _, _, child) -> child.owner-find-texts(target)
      LRotate(_, _, _, _, child) -> child.owner-find-texts(target)
      LClip(_, _, _, _, child) -> child.owner-find-texts(target)
      LOverlay(_, _, _, child) -> child.owner-find-texts(target)
      LTransform3d(_, _, _, _, child) -> child.owner-find-texts(target)
      LMemo(_, _, _, _, child) -> child.owner-find-texts(target)
      LScroll(_, _, _, _, _, _, _, child) -> child.owner-find-texts(target)
      LFlex(_, _, _, children) -> children.owner-find-texts-list(target)
      LLayer(_, _, _, children) -> children.owner-find-texts-list(target)
      _ -> Nothing

fun owner-find-texts-list<msg>( children : list<(float64, float64, ltree<msg>)>, target : int32 ) : div maybe<list<string>>
  match children
    Nil -> Nothing
    Cons((_, _, child), rest) ->
      match child.pretend-decreasing.owner-find-texts(target)
        Just(ts) -> Just(ts)
        Nothing  -> rest.owner-find-texts-list(target)

// all text content anywhere in a subtree (LText plus the visible text of the
// leaf input widgets), used by `owner-texts` once the owner root is found
fun subtree-texts<msg>( t : ltree<msg> ) : div list<string>
  match t
    LText(_, content, _, _, _, _, _) -> [content]
    LRich(_, content, _, _, _, _, _, _, _) -> [content]
    LField(_, _, value, ph, _, _, _) -> [if value == "" then ph else value]
    LInput(_, _, value, ph, _, _, _, _) -> [if value == "" then ph else value]
    LBox(_, _, _, _, _, _, _, child) -> child.subtree-texts
    LLink(_, _, _, _, _, _, child) -> child.subtree-texts
    LAct(_, _, _, _, _, _, child) -> child.subtree-texts
    LActMsg(_, _, _, _, _, _, child) -> child.subtree-texts
    LInteractive(_, _, _, _, _, _, _, _, child) -> child.subtree-texts
    LRotate(_, _, _, _, child) -> child.subtree-texts
    LClip(_, _, _, _, child) -> child.subtree-texts
    LOverlay(_, _, _, child) -> child.subtree-texts
    LTransform3d(_, _, _, _, child) -> child.subtree-texts
    LMemo(_, _, _, _, child) -> child.subtree-texts
    LScroll(_, _, _, _, _, _, _, child) -> child.subtree-texts
    LFlex(_, _, _, children) -> children.flatmap(fn(e) e.thd.subtree-texts)
    LLayer(_, _, _, children) -> children.flatmap(fn(e) e.thd.subtree-texts)
    _ -> []
