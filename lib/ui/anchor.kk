/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Pure anchoring primitives shared by every positioned VIEW (an overlay, a
// window, a scrollbar -- all one concept). A view hangs off a target rect (the
// display, another view, or a widget region) by two ALIGNMENTS -- a point on
// the target and a point on the view -- plus an offset; `place` computes the
// view's top-left so those points coincide, then clamps it inside the display
// bounds (this is what stops a popover overflowing the screen).
//
// Ordering is RELATIVE, never a numeric layer: a view is always painted above
// its anchor (a hard floor, enforced structurally by the anchor tree), and a
// coarse `band` gives the default order between otherwise-unordered views
// (attached < popover < modal < window), with insertion order breaking ties.
// The default is `attached` -- "just above my anchor", so above its content but
// below a later dialog or window.
//
// This module is a leaf (depends only on std): the geometry and the ordering
// key are pure and unit-testable on their own, before any effect / backend.
module ui/anchor

import std/num/float64

// ----------------------------------------------------------------
// alignment: a fractional point on a rect. (0,0) = top-left, (1,1) =
// bottom-right, (0.5,0.5) = center. Any fractional point is valid (e.g.
// Alignment(0.25, 1.0)); the named constants below cover the usual nine.

pub struct alignment
  ax : float64
  ay : float64

pub val top-left     : alignment = Alignment(0.0, 0.0)
pub val top          : alignment = Alignment(0.5, 0.0)
pub val top-right    : alignment = Alignment(1.0, 0.0)
pub val center-left  : alignment = Alignment(0.0, 0.5)
pub val center       : alignment = Alignment(0.5, 0.5)
pub val center-right : alignment = Alignment(1.0, 0.5)
pub val bottom-left  : alignment = Alignment(0.0, 1.0)
pub val bottom       : alignment = Alignment(0.5, 1.0)
pub val bottom-right : alignment = Alignment(1.0, 1.0)

// the absolute point of an alignment within a rect at (x,y) sized (w,h)
pub fun at( a : alignment, x : float64, y : float64, w : float64, h : float64 ) : (float64, float64)
  (x + a.ax * w, y + a.ay * h)

// ----------------------------------------------------------------
// placement: position a view of size (cw,ch) so its `self` alignment point
// meets the target rect's `target` alignment point (plus `offset`), then clamp
// the result to stay within the display of size (view-w, view-h). Clamping
// keeps a view fully on-screen when it fits; when the view is larger than the
// display on an axis it is pinned to the top/left of that axis.

pub fun clamp1( v : float64, lo : float64, hi : float64 ) : float64
  if hi < lo then lo else v.max(lo).min(hi)   // oversized content pins to the near edge

// returns the view's top-left (x,y) in display coordinates.
pub fun place( target-x : float64, target-y : float64, target-w : float64, target-h : float64,
               content-w : float64, content-h : float64,
               target-align : alignment, self-align : alignment,
               offset-x : float64, offset-y : float64,
               view-w : float64, view-h : float64 ) : (float64, float64)
  val (tpx, tpy) = target-align.at(target-x, target-y, target-w, target-h)  // point on the target
  val (spx, spy) = self-align.at(0.0, 0.0, content-w, content-h)            // point on the content
  val x = tpx - spx + offset-x
  val y = tpy - spy + offset-y
  ( clamp1(x, 0.0, view-w - content-w),
    clamp1(y, 0.0, view-h - content-h) )

// ----------------------------------------------------------------
// ordering: a coarse priority band. A view's paint order among its siblings is
// (band, insertion-seq); the anchor "above my target" floor is enforced by the
// anchor tree, not here. New bands can be inserted without renumbering because
// callers use the names, not `priority`.

pub type band
  Attached    // just above the anchor: tooltips, inline popovers (the default)
  Popover     // menus, dropdowns, comboboxes
  Modal       // dialogs (over the page, under system windows)
  Window      // top-level / detached windows

pub fun priority( b : band ) : int
  match b
    Attached -> 0
    Popover  -> 1
    Modal    -> 2
    Window   -> 3

// order two views by (band, then insertion seq): the paint order of siblings
pub fun order/before( band1 : band, seq1 : int, band2 : band, seq2 : int ) : bool
  val (p1, p2) = (band1.priority, band2.priority)
  if p1 != p2 then p1 < p2 else seq1 < seq2
