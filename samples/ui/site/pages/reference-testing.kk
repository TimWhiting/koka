// Reference: testing your app.
module pages/reference-testing

import ui/keytrie   // ?key implicits
import ui/widget
import ui/style/default
import blocks

pub fun ref-testing-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("test-scenarios", ["test-scenarios(name, init, view, update, scenarios,",
                                  "               config = App-config())",
                                  "test-app(name, init, view, update, script,",
                                  "         config = App-config())"],
      "Runs your app headlessly against a list of named scenarios — each "
      ++ "one a function taking a `tester` and asserting against what the "
      ++ "app actually shows, not its internal model. This is how nearly "
      ++ "every UI-level regression check across `lib/ui` and this site "
      ++ "itself is written; the site you're reading this on has its own "
      ++ "smoke suite built exactly this way. `test-app` is the one-"
      ++ "script special case — literally `test-scenarios` called with a "
      ++ "single `(\"\", script)` entry — so reach for `test-app` when you "
      ++ "have one script and `test-scenarios` when several scripts share "
      ++ "one app instance (model/state reset between them). No live demo "
      ++ "here: both run a WHOLE separate app instance headlessly, not "
      ++ "something embeddable inside a reference page's own live app.",
      demo = Nothing),

    api-entry("tester ops: click, find, type-text, press-key, hover, scroll",
      ["t.click(selector)", "t.find(selector)   // -> maybe<(x,y,w,h)>",
       "t.type-text(selector, text)", "t.press-key(\"Enter\")",
       "t.hover(selector)", "t.scroll(selector, dy)"],
      "The actions a scenario drives the app with, each addressing a "
      ++ "widget by a SELECTOR string (below) rather than a pixel "
      ++ "coordinate — `click`/`hover` find the selector's target and act "
      ++ "on its center; `type-text` focuses a field first; `press-key` "
      ++ "sends \"Enter\"/\"Backspace\"/\"Escape\" to whatever's already "
      ++ "focused; `find` returns the target's laid-out rect (or "
      ++ "`Nothing` if nothing matches, or it's scrolled out of view) for "
      ++ "assertions that need geometry rather than just presence. "
      ++ "`scroll`'s `dy` follows wheel-delta sign, not screen direction: "
      ++ "`dy < 0` scrolls DOWN (revealing later content), the opposite "
      ++ "of what the sign might suggest.",
      demo = Nothing),

    api-entry("settle, texts, check / check-eq", ["t.settle()", "t.texts(selector = \"\")",
                                           "check(label, ok)", "check-eq(label, actual, expected)"],
      "`settle` is two fixed round-trips through the app's own message "
      ++ "loop — enough for an action's direct effect AND whatever that "
      ++ "effect itself queues (a re-render, a follow-on message); call "
      ++ "it after any action before asserting, so a scenario isn't "
      ++ "racing an animation or an async load. `texts` reads back all "
      ++ "visible text inside a selector's subtree (empty selector = the "
      ++ "whole app) — the assert-on-what-the-user-sees idiom this "
      ++ "page's intro describes; a selector matching NOTHING reads back "
      ++ "`[]`, the same as a selector matching a mounted-but-empty "
      ++ "subtree, so an empty result alone doesn't prove presence. "
      ++ "`check` is a plain boolean assertion with an optional detail "
      ++ "message; `check-eq` is the equality-specific version, building "
      ++ "its own \"expected X, got Y\" detail from the two values.",
      demo = Nothing),

    api-entry("selector grammar, scenario patterns, and the live tier", [],
      "A selector matches a widget by its `?key` scope path — a plain "
      ++ "string like `\"nav-home\"` matches any widget keyed with that "
      ++ "scope, anywhere in the tree; ambiguous matches throw, naming "
      ++ "every match found, so a genuinely ambiguous selector fails "
      ++ "loudly instead of silently picking one. Write scenarios that "
      ++ "assert what a user would actually see (`t.texts(...)`, a "
      ++ "button's visible state) rather than reaching into the model — "
      ++ "the model is an implementation detail a scenario shouldn't "
      ++ "need to know about. Beyond the headless tier `test-scenarios` "
      ++ "runs by default, `lib/ui` also has a LIVE tier that runs the "
      ++ "SAME script against a real window instead of the headless "
      ++ "harness — real text measurement, real layout, real paint/"
      ++ "present, and the real input path, for the paint/measure/input "
      ++ "bugs the headless tier can't see.",
      demo = Nothing) ]
