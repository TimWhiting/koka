// The docs site's reusable content blocks: prose/heading/code primitives
// (moved here verbatim from content.kk) plus the higher-level blocks pages
// are built from -- doc-link, note, see-also, demo-panel, api-entry.
module blocks

import std/num/float64
import ui/keytrie   // ?key implicits (text/link now key their leaves)
import ui/ident
import ui/widget
import ui/state
import ui/style/default
import model

// ---- prose / code helpers --------------------------------------------------

pub fun doc-title<a>( s : string, ?key : key ) : theme widget<a>
  text(s, 30.0, theme.fg)

// a heading IS an anchor: its slug derives from its title (decision: derived
// slugs -- "State without the model" -> state-without-the-model), so every
// heading is a `scroll-to` / "#fragment" target with nothing extra declared
pub fun heading<a>( s : string, ?key : key ) : <keytree,theme> widget<a>
  text(s, 21.0, theme.accent, ?key = scope(slugify(s)))

// Markdown-style `` `code` `` backtick spans mark inline code inside prose.
// Finds every `` `...` `` range in `s` and returns the STRIPPED string
// (backticks removed) alongside a `text-span` per match, offset-adjusted
// for the characters already removed by earlier matches -- so span offsets
// land correctly against the RETURNED string, not the original. An
// unterminated trailing backtick (still "in code" when the input runs out)
// is dropped silently: no span for it, and the opening tick itself was
// already excluded from the output -- an acceptable degenerate case rather
// than something worth special-casing.
pub fun parse-code-spans<a>( s : string, mono-font : font ) : (string, list<text-span<a>>)
  val chars = s.list
  fun go( cs : list<char>, out : list<char>, pos : int, in-code : bool,
          code-start : int, spans : list<text-span<a>> ) : (list<char>, list<text-span<a>>)
    match cs
      Nil -> (out.reverse, spans.reverse)
      Cons(c, rest) ->
        if c == '`' then
          (if in-code
            then go(rest, out, pos, False, 0, Cons(Text-span(code-start, pos, font = Just(mono-font)), spans))
            else go(rest, out, pos, True, pos, spans))
        else go(rest, Cons(c, out), pos + 1, in-code, code-start, spans)
  val (result-chars, spans) = go(chars, [], 0, False, 0, [])
  (result-chars.string, spans)

pub fun prose<a>( s : string, ?key : key ) : theme widget<a>
  val (text, spans) = s.parse-code-spans(mono(16.0))
  rich(text, 16.0, theme.fg, spans, wrap = True)

// A monospaced code block: one padded surface panel; each line is a `code`
// row (text is single-line by design, so a block is a column of them), and
// the column rides a HORIZONTAL scroll so a long line pans instead of
// clipping mid-identifier or stretching the page. Highlighting comes later;
// this is the layout half (task #62 B).
//
// `column` centers each child on the CROSS axis (here, horizontal) within
// the column's own width -- fine for a column of same-width children, but a
// code block's lines are rarely the same length, so shorter lines drifted
// toward the middle instead of sitting flush with the block's left edge.
// Padding every line out to the longest line's length with trailing spaces
// (monospace, so padding is exact) makes every line the SAME rendered
// width, which makes cross-axis centering a no-op -- left-aligned in effect
// without needing an alignment mode `column`/`row` don't have.
//
// A `kk` tag plus an accent-tinted panel (rather than the plain
// `theme.surface` every other panel on this site -- `note`, `see-also`, a
// generic demo `box` -- already uses) mark this as CODE specifically:
// without some visual break, a code sample and a plain content panel read
// as the same kind of box, and only the monospace font told them apart.
//
// The tag is padded and set in the SAME font+size as the code lines, and
// -- unlike an earlier version of this function -- lives INSIDE the same
// scrolled column as the lines themselves, as an extra "line 0", rather
// than as a sibling of the `scroll` widget. It has to: `scroll` reports
// whatever width its OWN parent offers (the mechanism `demo-panel`'s
// comment above documents), which in a STANDALONE `code-block` (no
// `fixed`/`intrinsic-width` wrapper, e.g. every tutorial/how-to snippet
// and `api-entry`'s signature block) is the full page-content column --
// far wider than the code. A tag sitting OUTSIDE the scroll, as a sibling
// column child, was centered against that inflated width, not the code's.
// Inside the scroll, the tag shares the SAME inner (shrink-wrapped) column
// as the lines, so their relative alignment holds regardless of how wide
// the scroll's own viewport ends up being.
pub fun code-block<a>( lines : list<string>, ?key : key, ?kk-file-line : string ) : <keytree,theme> widget<a>
  val w = lines.map(fn(l) l.count).maximum("kk".count)
  val rows = [ code("kk".pad-right(w), 13.5, theme.accent, ?key = scope("tag")) ] ++
             lines.map-indexed(fn(i, l) code(l.pad-right(w), 13.5, theme.fg, ?key = idx(i)))
  box( scroll( column(rows, gap = 2.0), horizontal = True ),
       padding = 14.0, bg = Just(Fill(color/mix(theme.surface, theme.accent, 0.07), 10.0)) )

// ---- cross-page links / callouts / reference unit --------------------------

// a cross-page docs link: target is "page-slug" or "page-slug#section-slug"
// (the hash convention anchor-route-sub parses); label is the visible text
pub fun doc-link<a>( target : string, label : string, ?key : key ) : <keytree,theme> widget<a>
  link( target, accented("-> " ++ label, 15.0, ?key = scope("lbl")) )

// a callout: one tinted panel, for asides and warnings
pub fun note<a>( s : string, ?key : key ) : theme widget<a>
  val (text, spans) = s.parse-code-spans(mono(15.0))
  box( rich(text, 15.0, theme.fg, spans, wrap = True), padding = 12.0,
       bg = Just(Fill(theme.surface, 8.0)) )

// the standard link-out block tutorials and how-tos end with
pub fun see-also<a>( links : list<(string, string)>, ?key : key ) : <keytree,theme> widget<a>
  box( column( [ text("See also", 13.0, theme.accent, ?key = scope("hdr")) ] ++
               links.map-indexed(fn(i, l) doc-link(l.fst, l.snd, ?key = idx(i))),
               gap = 6.0 ),
       padding = 12.0, bg = Just(Fill(theme.surface, 8.0)) )

// code beside its LIVE result -- the gallery pattern (code left, demo right).
// `code-block` is a horizontal `scroll`, which -- like any scroll offered a
// bounded (non-unbounded) main-axis constraint -- reports the FULL width
// its row parent offers rather than shrinking to its own content (the
// correct behavior for a scroll's usual job, fill available space --
// test/ui/intrinsic-scroll-row.kk pins the mechanism). A fixed pixel width
// used to pin the code half against this, but that meant the code column
// stayed a fixed size regardless of how much room the page actually had,
// looking cramped on anything wider than that pin. `expanded` on BOTH
// halves instead splits the row's real available width evenly between
// them (flex 1.0 each, the `expanded` default) -- code left, demo right,
// each growing or shrinking with the page rather than one being fixed and
// the other soaking up (or starved of) whatever's left over.
//
// An "Output" label over `live` makes explicit what it otherwise wasn't:
// the widget beside the code IS that code's rendered result, not an
// unrelated bit of page furniture. `code-block`'s own "kk" tag (above) is
// this label's counterpart on the other half of the same row.
pub fun demo-panel<a>( code : list<string>, live : widget<a>,
                       ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<a>
  row( [ expanded(code-block(code, ?key = scope("code"))),
         expanded(column([ text("Output", 10.5, theme.accent, ?key = scope("output-lbl")), live ], gap = 6.0)) ],
       gap = 16.0 )

// the reference unit: an anchored name, its signature, one paragraph, and
// (when one shows something) a live demo of it
pub fun api-entry<a>( name : string, signature : list<string>, description : string,
                      demo : maybe<widget<a>> = Nothing,
                      ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<a>
  column( [ heading(name),                       // heading self-anchors: slugify(name)
            code-block(signature, ?key = scope("sig")),
            prose(description, ?key = scope("desc")) ] ++
          (match demo { Just(d) -> [d]; Nothing -> [] }),
          gap = 8.0 )
