/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Widget identity helpers. Identity is a `key` -- an abstract node in the
// identity trie (`ui/keytrie`). The ambient `?key` implicit carries the current
// identity; a STATEFUL COMPONENT takes an explicit, REQUIRED `key : key`
// parameter (named `key`, so everything in its body derives from it by
// ordinary implicit resolution), and the caller mints it with a short helper:
//
//   expander("Files", tree, here())            // one instance per call site
//   items.map-indexed(fn(i,it) row(it, idx(i)))  // one per list index
//
// `here()` captures the CALL SITE (`?kk-file-line` resolves fresh there, since
// components never declare it); forgetting the parameter is a type error, and
// `key` is abstract so identities cannot be forged or accidentally reused.
// There is deliberately NO ambient root default: a view that mints identity
// must declare `?key : key`, and the runtime supplies the root at the view
// boundary -- so every identity is provided by a parent, all the way up.
module ui/ident

import ui/keytrie

// mint an identity for THIS call site (under the ambient `?key`): the standard
// argument for a stateful component's required `key` parameter. `keep` is the
// identity's unmount policy (see ui/keytrie): `Transient` (default) prunes
// its state when a memo boundary rebuilds without it; `KeepAlive` retains the
// whole subtree's state (cells, scroll, fields, memo cache) until the same
// path remounts -- tab panes, off-screen wizard steps, collapsed editors.
pub fun here( keep : keep = Transient, ?key : key, ?kk-file-line : string ) : keytree key
  kt-child( ?key, Line(?kk-file-line), keep )

// mint an identity for list item `i` (disambiguates a shared call site):
// `items.map-indexed(fn(i, it) row(it, idx(i)))`
pub fun idx( i : int, keep : keep = Transient, ?key : key ) : keytree key
  kt-child( ?key, Index(i), keep )

// mint a NAMED identity (an explicit scope; also how a scrollbar links to a
// named scroll region under the same parent):
// `scope("settings-tab", keep = KeepAlive)` is the retained-tab idiom.
pub fun scope( name : string, keep : keep = Transient, ?key : key ) : keytree key
  kt-child( ?key, Named(name), keep )
