# Docs Site Content Style: Learning-First, Not Hype-First

Design for correcting the lib/ui docs site's content philosophy before
continuing the rollout (spec: `2026-07-29-docs-site-ia-design.md`). The IA
spec's structure (23+ pages across the four Diátaxis quadrants) is sound and
unchanged by this document; what's wrong is the *content* the five sample
pages shipped with, and it needs fixing before it propagates to the other
18+ pages.

## Problem

Feedback on the five pages built in rollout step 1: too hype / narrow
focused, making claims the page itself doesn't back up, leaking framework
internals into material a first-time reader didn't ask for, opening with
what the framework IS rather than what the reader is about to DO, and simply
not enough depth to call itself documentation for the whole surface a UI
framework needs to cover.

## The content style guide

Four rules. Each is illustrated with a real line from the current site and
what it becomes, because the rules exist to be pattern-matched by whoever
(human or subagent) writes the next page — an abstract rule doesn't transfer
as reliably as a concrete correction does.

### Rule 1 — No claim without a receipt on the same page

A claim about the framework ("runs on three backends", "nothing emulated")
is only allowed where the page itself proves it to the reader, immediately.
If the page can't prove it, cut the claim or move it to the page that can.

- Before (home): *"A portable, declarative UI framework in Koka. One widget
  vocabulary (widget<msg>) runs unchanged on three backends: the browser
  (jsweb and wasi-web) and native desktop via Impeller."* — four assertions,
  zero receipts, before the reader has seen a single widget.
- After: *"Koka × ui: build a UI once, in Koka. This page — sidebar, live
  counter, everything — is one `lib/ui` app."* The claim is that the page
  itself is proof, and it's checkable by scrolling.

### Rule 2 — Task-first opening, not property-first

Lead with the reader's problem or the thing they're about to build.
Framework properties (portable, declarative, powerful) get demonstrated
through use; they don't open the page as adjectives.

- Before (how-to): *"Layout is Flutter-style: constraints flow down, sizes
  flow up, the parent positions its children."*
- After: *"You have a header and a scrolling list below it, and you want the
  list to take whatever space is left. Here's the primitive for that:
  `expanded`."* The Flutter comparison survives as a one-line aside, not the
  opening frame.

### Rule 3 — Internals stay on the page the reader opted into

A mention of Perceus, FBIP, reconciliation, or backend lowering belongs on
the explanation page *about* that mechanism. It doesn't belong in a
reference entry, how-to step, or tutorial that a first-time reader reached
without asking for internals.

- `explanation-one-core`'s reconciliation paragraph ("reusing node cells in
  place (FBIP)") is fine as written — that page is where a reader who wants
  the mechanism goes looking for it. The rule's effect is mostly pruning:
  internals asides that currently leak into reference/tutorial/how-to bodies
  move to the explanation page they belong on, or get cut if no reader of
  that page needs them to proceed.

### Rule 4 — No unearned superlatives or adjectives

"Powerful", "elegant", "simply", "just" — replace with the specific,
verifiable behavior. If the specific behavior can't be named, the claim
doesn't belong yet.

## Reference-page depth standard

Every `api-entry` moves from signature + one paragraph to a fixed shape:

1. Signature (as now).
2. One paragraph: what it does, framed as the reader's problem it solves.
3. Every non-obvious parameter: what it controls, its default, when you'd
   change it from the default. (Obvious parameters — e.g. a `label : string`
   that's exactly what it says — don't need their own sentence.)
4. A "vs." note wherever a nearby alternative exists (`text` vs `paragraph`,
   `use-state` vs `use-state-quiet`, `box` vs `stack`), stated as a decision
   rule for the reader ("use X when Y; use Z when W"), not a feature-parity
   table.
5. A live demo, unless the entry has nothing visual to show (e.g. a pure
   data type with no rendering of its own).

This is the biggest content-depth gap today: only 2 of the current
`reference-widgets` entries have a demo, and none have parameter-by-parameter
coverage or a vs.-note. This standard becomes the template the other 8
reference pages are built against.

## Application plan

**This plan's deliverable is scoped to the 5 existing pages.** They set the
pattern every later page copies, so fixing the pattern now — rather than
after more pages exist — avoids re-fixing everything downstream. The IA
spec's rollout steps 2-5 (reference pages 2-9, explanation pages 2-8,
how-to recipes, tutorials) remain separate future passes, each still its own
scoped piece of work; this document governs their content once undertaken,
but writing them is not part of the implementation plan that follows this
spec.

- `home-body`: rewrite the opening under Rule 1/2.
- `tutorial-first-app`, `howto-layout`: mostly a framing fix (Rule 2) on
  section intros; the mechanics are already reasonably taught.
- `reference-widgets`: rebuilt to the depth standard above — the largest
  single piece of work in this pass, and the template for reference pages
  2-9.
- `explanation-one-core`: audited against Rule 3, not rewritten wholesale —
  the fix here is confirming it's teaching the mechanism (not just naming
  it), not deleting internals content that belongs on this page.

No change to `doc-page`/`doc-section`/`api-entry` *code* (model.kk,
blocks.kk) is anticipated — this is a content pass over page bodies
(pages.kk and its successors), not a framework or content-model change. If
writing to the depth standard surfaces a genuine gap in `api-entry`'s shape
(e.g. nowhere to put a "vs." note as structured data rather than prose), that
becomes its own small follow-up, not scope creep into this pass.

## Process

Executed like the content-model rollout: one SDD task per page (home,
tutorial-first-app, howto-layout, reference-widgets, explanation-one-core —
5 tasks). Each task brief includes this document as required reading. The
task reviewer's rubric gains the four style-guide rules and, for
`reference-widgets`, the depth standard, as explicit spec-compliance checks
— a page that builds and passes the smoke suite but opens with an unbacked
claim, or ships a signature-only reference entry, fails review exactly as a
page missing a required section would.

Future rollout-step passes (reference pages 2-9, etc.) reuse this same
process and cite this document as required reading in their own task
briefs, once undertaken as their own planned work.

## Non-goals

- No visual/shell changes (typography, layout, responsive design )— that's
  the separate shell spec, still deferred per the IA spec's rollout order.
- No change to the IA spec's page structure or count.
- No retroactive claim-audit of code comments or design-notes ledger
  entries — this governs docs *site* content (pages.kk and successors)
  only.
