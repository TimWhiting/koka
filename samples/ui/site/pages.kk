// The docs site's pages, as `doc-page` DATA (spec: docs/superpowers/specs/
// 2026-07-29-docs-site-ia-design.md). Quadrant pages (tutorial/how-to/reference/
// explanation) are `Doc-page` values built from top-level section-body functions;
// home stays OUTSIDE the quadrants as a plain widget-list function. Every "live"
// demo drives itself with EPHEMERAL state (ui/state `use-state` + `act`), so a
// page can host an interactive widget WITHOUT threading an app message through
// the shell -- the same mechanism a real component library uses for
// uncontrolled UI. Bodies are polymorphic in the message type (`a`) because
// they emit none of their own.
//
// Each quadrant/topic's section bodies live in their own file under pages/ --
// see that directory for the shared ephemeral-state helpers (pages/common) and
// one file per page/topic. This file only assembles them into `site-pages`.
// `pub import`ed so `main` can keep calling `home-body` through `pages` alone.
module pages

import model
pub import pages/home
pub import pages/tutorial
pub import pages/how-to
pub import pages/reference-layout
pub import pages/reference-text
pub import pages/reference-interaction
pub import pages/reference-paint
pub import pages/reference-state
pub import pages/reference-async
pub import pages/reference-app-routing
pub import pages/reference-theming
pub import pages/reference-testing
pub import pages/explanation

// ---- the pages, as data ------------------------------------------------------

pub fun site-pages<a>() : list<doc-page<a>>
  [ Doc-page(QTutorial, "tutorial-first-app", "Your first app",
      "You're about to build a counter app in three functions: a model, "
      ++ "an update, and a view. The runtime owns the render loop for you.",
      [ Doc-section("The model and messages", tut-model-body),
        Doc-section("The view", tut-view-body),
        Doc-section("The update", tut-update-body),
        Doc-section("The result", tut-result-body) ]),

    Doc-page(QHowTo, "howto-layout", "Lay out a screen",
      "The layout primitives you reach for constantly: putting things in a "
      ++ "row or column, making one thing fill whatever space is left, and "
      ++ "keeping content centered and readable on a wide window.",
      [ Doc-section("Rows and columns", howto-rows-body),
        Doc-section("Fill the leftover space", howto-fill-body),
        Doc-section("Center with a max width", howto-center-body) ]),

    Doc-page(QReference, "reference-widgets", "Layout & containers",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. Layout containers: "
      ++ "boxes, flex, scrolling, clipping, positioning, and long lists.",
      [ Doc-section("Boxes and flex", ref-boxes-flex-body),
        Doc-section("Scrolling and space", ref-scroll-space-body),
        Doc-section("Clipping and overlays", ref-clip-overlay-body),
        Doc-section("Long lists", ref-lazy-body) ]),

    Doc-page(QReference, "reference-text-content", "Text & content",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. The leaf widgets that "
      ++ "actually draw something: text, images, and plain colored "
      ++ "rects.",
      [ Doc-section("Text and content", ref-text-body) ]),

    Doc-page(QReference, "reference-interaction", "Interaction",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. Buttons, fields, links, "
      ++ "and the lower-level primitives they're built on.",
      [ Doc-section("Interactive", ref-interactive-body) ]),

    Doc-page(QReference, "reference-paint-effects", "Paint & effects",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. Fills, colors, and the "
      ++ "paint-only transforms: rotation, 3D, and the press ripple every "
      ++ "themed button uses.",
      [ Doc-section("Paint and effects", ref-paint-body) ]),

    Doc-page(QReference, "reference-state-animation", "State & animation",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. Ephemeral state that "
      ++ "doesn't touch the app model, and the primitives that animate it "
      ++ "smoothly.",
      [ Doc-section("State and animation", ref-state-anim-body) ]),

    Doc-page(QReference, "reference-async", "Async",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. The primitive async "
      ++ "work in lib/ui is built on, and how `update` requests it "
      ++ "without doing it inline.",
      [ Doc-section("Async", ref-async-body) ]),

    Doc-page(QReference, "reference-app-routing", "App & routing",
      "The entry point every app starts from, and the router that turns "
      ++ "URL hashes into route messages.",
      [ Doc-section("App and routing", ref-app-routing-body) ]),

    Doc-page(QReference, "reference-theming", "Theming",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. The ambient effect "
      ++ "every themed component reads from, the default component "
      ++ "library, and how to swap in a different look or build your "
      ++ "own.",
      [ Doc-section("Theming", ref-theming-body) ]),

    Doc-page(QReference, "reference-testing", "Testing your app",
      "How to test what you build: headless scenarios that assert on "
      ++ "what a user sees, not on your model's internals.",
      [ Doc-section("Testing your app", ref-testing-body) ]),

    Doc-page(QExplanation, "explanation-one-core", "One core, three backends",
      "ui/widget is the core: a data type of widgets, and a layout pass "
      ++ "that turns them into a laid-out tree (ltree). Nothing in that "
      ++ "core knows about the DOM or Impeller — backends are a separate, "
      ++ "later step, covered below.",
      [ Doc-section("Backends lower the SAME tree", expl-backends-body),
        Doc-section("Style is a swappable layer", expl-style-body),
        Doc-section("State without the model", expl-state-body),
        Doc-section("Reconcile and reuse", expl-reconcile-body) ]),
  ]
