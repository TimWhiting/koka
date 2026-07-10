// The docs site's content model (spec: docs/superpowers/specs/
// 2026-07-29-docs-site-ia-design.md). Metadata is DATA -- everything
// navigation needs derives from `list<doc-page>` -- while section BODIES are
// widget functions, because they host live demos. Slugs derive from titles;
// a heading is its own anchor (blocks.kk), so a section's title is also its
// cross-page address: "reference-text-content#text-and-content".
module model

import ui/keytrie
import ui/widget
import ui/state
import ui/style/default

pub type quadrant
  QTutorial
  QHowTo
  QReference
  QExplanation

// sidebar group headers, in display order
pub fun quadrant/show( q : quadrant ) : string
  match q
    QTutorial -> "Learn"; QHowTo -> "Tasks"
    QReference -> "Reference"; QExplanation -> "Understand"

pub fun quadrant/same( a : quadrant, b : quadrant ) : bool
  a.show == b.show

pub struct doc-section<a>
  title : string                      // slug derives: slugify(title)
  body  : (key) -> <keytree,uistate,ioc,theme> list<widget<a>>

pub struct doc-page<a>
  quadrant : quadrant
  slug     : string                   // the route path segment
  title    : string
  intro    : string                   // one-paragraph lead
  sections : list<doc-section<a>>

// lowercase, spaces to dashes, everything else but letters/digits dropped
fun slug-char( c : char ) : char
  if c == ' ' then '-'
  elif (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' then c
  elif c >= 'A' && c <= 'Z' then (c.int + 32).char
  else '_'

pub fun slugify( s : string ) : string
  s.list.map(slug-char).filter(fn(c) c != '_').string

pub fun find-page<a>( pages : list<doc-page<a>>, target : string ) : maybe<doc-page<a>>
  pages.find(fn(p) p.slug == target)

// previous/next WITHIN the page's quadrant (reading order = list order);
// Nothing at either end, (Nothing, Nothing) for an unknown slug
pub fun next-prev<a>( pages : list<doc-page<a>>, target : string ) : (maybe<doc-page<a>>, maybe<doc-page<a>>)
  match pages.find(fn(p) p.slug == target)
    Nothing -> (Nothing, Nothing)
    Just(cur) ->
      val q = pages.filter(fn(p) p.quadrant.same(cur.quadrant))
      fun go( xs : list<doc-page<a>>, prev : maybe<doc-page<a>> ) : (maybe<doc-page<a>>, maybe<doc-page<a>>)
        match xs
          Cons(p, rest) | p.slug == target -> (prev, rest.head)
          Cons(p, rest) -> go(rest, Just(p))
          Nil -> (Nothing, Nothing)
      go(q, Nothing)
