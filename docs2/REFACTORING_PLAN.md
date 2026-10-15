# Koka Documentation — Current State & Roadmap

## Structure

The documentation follows a multi-path approach with five sections:

### Learn Koka (`learn/`)
Condensed quickstart for experienced programmers (~4 pages). Covers syntax,
types, effects, and FBIP in minimal space. Think "Tour of Go."

### The Koka Book (`tutorial/`)
Comprehensive linear progression (~8 chapters). Teaches from scratch with
progressive examples. Think "The Rust Book."

Chapters:
1. Getting Started — values, REPL, basic types
2. Functions — dot notation, lambdas, `with`
3. Lists & Recursion — functional list processing
4. Your Own Types — structs, sum types, pattern matching
5. Side Effects — effect types, rows, polymorphism
6. Custom Effects — handlers, val/ctl/fun ops, state, composition
7. Calculator — capstone project (parts 1 & 2)

### How-to Guides (`guides/`)
Task-oriented recipes for working programmers. Each guide links back to the
Book for foundational context. Covers: functions, ADTs, pattern matching,
types, overloading, implicits, effect types, effect handlers, advanced
handlers, FBIP, and performance optimization.

### Concepts (`concepts/`)
Design rationale and theory: "Minimal but General" philosophy, effect types
& handlers (with denotational semantics), Perceus & FBIP.

### Reference (`reference/`)
Precise lookup: language spec (BNF grammar), effect semantics, advanced
handlers, types & representation, REPL & tooling.

## Build System

See [BUILD.md](BUILD.md) for the full build pipeline documentation.

Quick version:
```sh
stack run koka -- util/build-new-docs.kk -e   # build HTML pages
node util/bundle-spa.js out                    # bundle SPA (optional)
```

## Remaining Work

### High Priority
- [ ] **Book Chapter 8: FBIP** — Progressive tutorial on Perceus, reuse analysis, fip/fbip keywords. Assemble from guides/fbip.mdk and concepts/perceus-and-fbip.mdk content.
- [ ] **Spec audit** — Compare reference/spec.mdk against the current Koka parser source to ensure the grammar is accurate (lazy match, scoped handlers, applier syntax, etc.)
- [ ] **Concepts: Perceus & FBIP revision** — Refocus on "why" after tutorial ch8 absorbs the "how". Restore ARM64 assembly output from old docs as concrete evidence.

### Medium Priority
- [ ] **New guide: C Interop** (`guides/c-interop.mdk`) — `extern` keyword, inline C/JS, closures, type mapping. Source: `~/koka-community/koka-docs/less-known-features.kk.md`
- [ ] **New guide: Divergence** (`guides/divergence.mdk`) — When `:div` is inferred, `pretend-decreasing`, `pretend-no-div`. Source: community docs.
- [ ] **New guide: Modules** (`guides/modules.mdk`) — Module system, imports, visibility, qualified names. Currently undocumented.
- [ ] **Online playground** — Interactive code execution with sample dropdown.

### Lower Priority
- [ ] Search functionality (client-side index)
- [ ] Standard library API browser integration
- [ ] Visual FBIP diagrams showing memory reuse
- [ ] Blog posts for new features

## Contributing

### Adding Content

1. Create `docs2/<section>/my-page.mdk` using the template from BUILD.md
2. Add the filename to `util/build-new-docs.kk` in the appropriate section list
3. Add sidebar entries in both `docs2/sidebar.mdk` and `docs2/sidebar-sub.mdk`
4. Build and verify: `stack run koka -- util/build-new-docs.kk -e`

### Writing Guidelines

- **Don't be frivolous.** Every sentence should earn its place. Avoid filler like "In this section we will explore..." — just explain the thing.
- **Don't be too terse.** Give enough context that a reader can follow. Show the effect type. Explain *why* something works the way it does.
- **Show, don't list.** Demonstrate properties through examples rather than bullet-point feature lists. The while-loop-as-function-call example is better than "Koka has first-class functions."
- **Unique `fun` names.** All `koka` code blocks in a file compile as one module. Use names like `example-square` instead of `main` to avoid conflicts.
- **Hidden imports.** Put imports in `` ```koka {.hidden} `` at the top. Show them again in `` ```unchecked `` blocks where pedagogically useful.
- **Link between sections.** Guides link to the Book for fundamentals. The Book links to guides for advanced recipes. Reference links to both.

### Section Boundaries

Content may overlap in *topic* but each section serves a different *purpose*:
- The **Book** teaches progressively (here's what effects are, building up)
- **Guides** give recipes (how do I implement backtracking?)
- **Concepts** explain rationale (why effects instead of monads?)
- **Reference** states precise rules (what exactly does `mask<l>` do?)

Avoid duplicating *explanations* across sections. Instead, link to the canonical location and add the section-specific treatment (recipe, rationale, or specification).
