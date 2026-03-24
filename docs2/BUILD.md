# Building the Koka Documentation

## Overview

The Koka docs use a two-stage build pipeline, plus an optional SPA bundling step:

1. **Koka preprocessing** — `.mdk` files are passed through the Koka compiler to generate rich type tooltips for code blocks
2. **Madoko publishing** — The preprocessed markdown is rendered to standalone HTML pages
3. **SPA bundling** (optional) — All pages are merged into a single `spa.html` for zero-flash navigation

## Prerequisites

- [Koka](https://github.com/koka-lang/koka) compiler (built via `stack`)
- [Madoko](https://github.com/koka-lang/madoko) markdown processor (`npm install -g madoko`)
- [Node.js](https://nodejs.org) (for the SPA bundler)

## Quick Start

```sh
# Build all HTML pages
stack run koka -- util/build-new-docs.kk -e

# Bundle into SPA (optional)
node util/bundle-spa.js out

# Preview locally
open out/index.html          # multi-page (or open out/spa.html for SPA)
# or
cd out && python3 -m http.server 8787   # SPA with clean URLs at localhost:8787/spa.html
```

## Directory Structure

```
docs2/                  # Source files
├── learn/              # "Learn Koka" quickstart (condensed, for experienced programmers)
├── tutorial/           # "The Koka Book" (progressive, comprehensive)
├── guides/             # How-to guides (task-oriented recipes)
├── concepts/           # Design rationale and theory
├── reference/          # Precise language reference
├── blog/               # Release announcements
├── styles/modern.css   # Main stylesheet (light/dark theme)
├── scripts/docs.js     # Sidebar, theme toggle, tooltips, prefetch
├── sidebar.mdk         # Sidebar for root-level pages
├── sidebar-sub.mdk     # Sidebar for sub-directory pages
├── lang/               # Syntax colorizer definitions (koka.json, unchecked.json)
└── images/             # Logos and screenshots

util/
├── build-new-docs.kk   # Main build script (Koka)
└── bundle-spa.js       # SPA post-processor (Node.js)

out/                    # Generated output (gitignored)
├── *.html              # Individual pages
├── spa.html            # Single-page application (all content bundled)
└── gen/                # Intermediate build artifacts
```

## Build Pipeline Details

### Stage 1: Koka Preprocessing (`build-new-docs.kk`)

The build script:
1. Copies `.mdk` source files to `out/gen/` as `.kk.md`
2. Runs `koka -c -v0 -l --html` on each file — this compiles the Koka code blocks and generates rich HTML with type tooltips (hover to see inferred types)
3. Handles filename mangling (Koka converts hyphens to `_dash_`)
4. Tracks dependencies for incremental builds (skips unchanged files)

### Stage 2: Madoko Publishing

After Koka preprocessing, Madoko converts the generated `.md` files to HTML:
- Applies the sidebar template and CSS
- Renders markdown formatting, math, bibliography references
- Produces standalone HTML pages in `out/`

If Koka compilation fails for a file (e.g., type errors in code blocks), Madoko falls back to the original `.mdk` source — the page still renders, just without type tooltips.

### Stage 3: SPA Bundling (`bundle-spa.js`)

The SPA bundler post-processes the Madoko output:
1. Reads all `.html` files from `out/`
2. Extracts the `<div class="content">` from each page
3. Stores all content fragments as JSON in a single `spa.html`
4. Injects a client-side router that swaps content on navigation

**Routing behavior:**
- On `file://` protocol: uses hash-based routing (`spa.html#/learn/basics.html`)
- On `http://` protocol: uses `pushState` with clean URLs (`/learn/basics.html`)

**Link resolution:**
- Sidebar links resolve relative to the root (they use paths like `learn/basics.html`)
- Content links resolve relative to their source page (e.g., a link `../guides/effect-handlers.html` in `learn/effects.html` correctly resolves to `guides/effect-handlers.html`)

## Writing Documentation

### File Format

Each `.mdk` file needs:
```
Title: Page Title
[INCLUDE=../sidebar-sub.mdk]    (or sidebar.mdk for root pages)

# Heading { .heading-no-number }

... content ...

~ end content
~ end main-layout
```

### Code Blocks

- `` ```koka `` — Koka code, compiled for type tooltips. All blocks in a file compile as one module.
- `` ```unchecked `` — Displayed as Koka syntax but not compiled. Use for signatures, partial examples, or code that would conflict.
- `` ```koka {.hidden} `` — Compiled but not displayed. Use for imports at the top of a file.

**Important:** Since all `` ```koka `` blocks in a file compile together, avoid duplicate `main` functions. Name example functions uniquely (e.g., `example-square`, `example-dot`).

**Import pattern:** Put imports in a hidden block at the top, and show them again in an `unchecked` block where pedagogically useful:

```
`` `koka {.hidden}
import std/num/float64
`` `

...later in the page...

`` `unchecked
import std/num/float64
`` `
```

### Section Purposes

| Section | Purpose | Audience |
|---------|---------|----------|
| `learn/` | Condensed quickstart, learn by example | Experienced programmers |
| `tutorial/` | Comprehensive linear progression | Anyone willing to invest time |
| `guides/` | Task-oriented recipes ("How do I...?") | Working Koka programmers |
| `concepts/` | Design rationale ("Why does Koka...?") | Curious about foundations |
| `reference/` | Precise lookup for every feature | Need exact details |

### Adding a New Page

1. Create `docs2/<section>/my-page.mdk` with the standard template
2. Add `"my-page"` to the appropriate list in `util/build-new-docs.kk`
3. Add a sidebar entry in both `sidebar.mdk` and `sidebar-sub.mdk`
4. Rebuild: `stack run koka -- util/build-new-docs.kk -e`
