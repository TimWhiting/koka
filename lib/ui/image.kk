/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// `image-fit` lives in its OWN module rather than `ui/widget` for one reason:
// its `Fill` variant would otherwise collide with `ui/widget`'s `fill` struct
// (which also mints a `Fill` constructor) -- Koka does not allow two
// same-named top-level constructors in one module, even at different arities.
// `ui/widget` re-exports this module (`pub import`), so a caller that only
// imports `ui/widget` sees `Contain`/`Cover`/`Fill`/`ImgNone` unqualified;
// the one spot that pattern-matches `Fill` alongside the struct's `Fill` (the
// web backend's `fit-css`) qualifies it as `ui/image/Fill`.
module ui/image

// how an image's pixels map onto its (possibly different-aspect) box,
// mirroring CSS `object-fit`: `Contain` letterboxes to fit inside (whole
// image visible, box may show empty bars), `Cover` crops to fill the box
// (box fully covered, image may be cropped), `Fill` stretches to the box
// (aspect not preserved), `ImgNone` paints at native size (unscaled, may
// overflow or underfill the box).
pub type image-fit { Contain; Cover; Fill; ImgNone }

// where an image's pixels come from (task #53). `FromPath` is an asset path
// (native: a file decode; web: an `<img src>` path/URL). `FromBytes` is an
// in-memory encoded PNG/JPEG (e.g. bytes from a fetch) decoded off-thread.
// `FromPixels` is already-decoded, tightly-packed RGBA8888 (`w*h*4` bytes) --
// no decode, straight to a texture / `<canvas>`.
pub type image-source
  FromPath( path : string )
  FromBytes( bytes : vector<int8> )
  FromPixels( rgba : vector<int8>, w : int, h : int )

// how an image loads (task #53). `Async` (default) shows the `placeholder`,
// decodes off the render thread, then uploads on it -- no frame hitch.
// `Sync` decodes+uploads inline on first paint (a one-frame hitch, no
// placeholder / min-load); it applies to `FromPath` only -- `FromBytes` and
// `FromPixels` always load via the async boundary.
pub type image-load { Async; Sync }

// the `src` marker an ASYNC image leaf carries (native). The async path does
// NOT decode in paint -- the boundary's `run` already decoded off-thread and
// uploaded on the render thread (`put-image-texture`), so the leaf just draws
// the texture cached under its owner id. The backend's `image-for` HITS on this
// marker (cached-src == leaf-src, so no re-decode is attempted); on the rare
// miss (an async texture pruned while its leaf was briefly unmounted) a decode
// of this sentinel simply fails to the placeholder fill rather than crashing.
// A SYNC `FromPath` image instead carries its real path and decodes in paint.
// A normal string (no illegal escapes) that will never be a real asset path.
pub val async-image-src : string = "@ui/async-image@"
