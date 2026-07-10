# Reference Pages Rollout (Rollout Step 2)

Design for building the docs site's 9 topic-based reference pages (IA spec:
`2026-07-29-docs-site-ia-design.md`, "Reference: 9 pages" section — the
per-topic widget/demo lists there are authoritative and not repeated here),
each written under the content style guide's rules and reference-depth
standard (`2026-07-31-docs-site-content-style-design.md`). This is rollout
step 2 of 5 from the original IA spec's rollout order.

## What exists today, and what changes

The current `reference-widgets` page (built in rollout step 1 as a proof of
the content model, not as "topic 1 of 9") is a cross-topic sampler: a "Text
and content" section (3 entries), a "Containers" section (7 entries, rebuilt
to the depth standard during the content-style pass), an "Interactive"
section (4 entries, likewise rebuilt), and a standalone "Live sample"
section (one `live-progress` demo that doesn't correspond to any of the 9
topics).

That doesn't map onto the IA spec's 9-topic structure, so it's retired as a
sampler and its content redistributed:

- **"Containers" stays on `reference-widgets`**, which becomes topic 1
  (Layout & containers) proper — same slug, retitled "Reference: layout &
  containers" to match its now-narrower scope, and extended with the
  topic's remaining widgets (`fixed`, `intrinsic-width`, `clip`, `overlay`,
  `lazy-column`, `positioned`) that the sampler never covered.
- **"Text and content" moves to a new page**, topic 2 (Text & content
  leaves), its 3 existing entries carried over as-is (already at the depth
  standard) and extended with the topic's remaining coverage (`rect`,
  `image`/`image-path`, fonts).
- **"Interactive" moves to a new page**, topic 3 (Interaction), its 4
  existing entries carried over as-is and extended (`interactive`,
  `act-msg`, `field`, drag & drop, `hit-slop`, `disabled`).
- **"Live sample" is dropped entirely.** Its ground (a value driving an
  animated bar via `use-state`/`animate`) belongs to topic 5 (State &
  animation), which will cover `use-state`/`animate` properly with real
  api-entries rather than one ad-hoc filler demo.

Carrying entries over "as-is" means literally moving the existing
`ref-text-body`/`ref-interactive-body` function bodies from `pages.kk` into
their new pages' section-body functions — no rewriting, since they already
meet the depth standard from the content-style pass.

## Slugs

Matching the site's existing `reference-` / `howto-` / `tutorial-`
convention (slug derives from title, but these are declared explicitly
since the page titles below aren't literally `slugify`'d from the topic
names in the IA spec):

| # | Topic | Slug | Title |
|---|---|---|---|
| 1 | Layout & containers | `reference-widgets` (reused) | Reference: layout & containers |
| 2 | Text & content leaves | `reference-text-content` | Reference: text & content |
| 3 | Interaction | `reference-interaction` | Reference: interaction |
| 4 | Paint & effects | `reference-paint-effects` | Reference: paint & effects |
| 5 | State & animation | `reference-state-animation` | Reference: state & animation |
| 6 | Async | `reference-async` | Reference: async |
| 7 | App & routing | `reference-app-routing` | Reference: app & routing |
| 8 | Theming & styled components | `reference-theming` | Reference: theming |
| 9 | Testing your app | `reference-testing` | Reference: testing your app |

Reusing `reference-widgets` for topic 1 means no inbound link (home's
`doc-link`, the smoke test's cross-page checks) needs to change — the route
stays the same, only the page's content and title change under it.

## No content-model code changes

`model.kk`'s `doc-page`/`doc-section` and `blocks.kk`'s `api-entry`/
`demo-panel`/`code-block` are unchanged — every new page is built from the
same primitives the content-revision pass already used and validated
(including the `intrinsic-width`-in-`demo-panel` fix, which every new
`demo-panel` call gets for free). `site-pages()` already derives the
sidebar/routing from the `doc-page` list, so adding 8 more entries there is
the only structural change `main.kk` needs — and `main.kk` itself needs no
edits, since `site-pages()` lives in `pages.kk`.

## Content rules (unchanged, carried forward)

Every new entry follows the content style guide's four rules and the
reference-depth standard from `2026-07-31-docs-site-content-style-design.md`
verbatim — this spec doesn't restate them. Two things worth calling out
given this rollout's scale:

- **Rule 1 (receipted claims) gets harder at topics like Async and App &
  routing**, where a live demo genuinely can't show timing/routing behavior
  as directly as a layout demo can. The content-revision pass already
  established the honest pattern for this (state plainly when a demo isn't
  achievable, per the depth standard's own escape clause, and ground the
  claim in mechanism instead) — that pattern is reused here, not
  re-invented per page.
- **Demo width discipline**: the `intrinsic-width` framework fix keeps
  `demo-panel`'s code half from overflowing, but the final-review pass on
  the content-revision plan found that `fixed(width = Just(N))` around a
  demo's LIVE half can still overflow if the chosen value doesn't fit — any
  new page using `fixed` to tidy a demo's width must be verified in a
  browser at a realistic viewport, not just typechecked, exactly as Task
  4's fix round established.

## Execution: 3 plans

Given the depth this pass demands per entry (Task 4's single topic-area
rebuild — containers + interaction, roughly 2 of these 9 topics' worth —
took a full implementation task plus one fix round), building all 9 topics
as one plan would make the per-task review loop unwieldy. Three plans,
each executed via `subagent-driven-development` independently (its own
tasks, its own final whole-plan review) before the next starts:

1. **Group 1 — topics 1-3** (Layout & containers, Text & content,
   Interaction): retitle/extend `reference-widgets`, split its content into
   the two new pages, retire "Live sample." Closest to already-proven
   ground since 3 of its content areas already exist at the depth standard.
2. **Group 2 — topics 4-6** (Paint & effects, State & animation, Async):
   entirely new pages. State & animation absorbs the retired live-progress
   ground properly.
3. **Group 3 — topics 7-9** (App & routing, Theming, Testing): entirely new
   pages. Testing is the one page whose subject is testing itself — its
   examples should be real, runnable scenario snippets, not merely
   described.

This design covers Group 1's scope in enough detail to write its plan now.
Groups 2 and 3 get their own brief scoping pass (not necessarily a full
brainstorming cycle, since the IA spec already specifies their content —
likely just confirming per-page slug/title and any topic-specific judgment
calls) before their plans are written, once Group 1 is complete and
reviewed.

## Non-goals

- No shell/visual changes (still deferred to the shell spec).
- No changes to explanation, how-to, or tutorial pages (rollout steps 3-4).
- No change to `doc-page`/`doc-section`/`api-entry`'s code shape unless a
  genuine gap surfaces while writing — same carve-out as the content-style
  spec, not scope creep into this pass.
