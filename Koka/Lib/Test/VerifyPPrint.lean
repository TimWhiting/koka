import Koka.Lib.PPrint

open Koka.Lib.PPrint

def test_pprint : IO Unit := do
  let d := textP "hello" <+> textP "world"
  IO.println s!"Texts: {texts d}"
  IO.println s!"RTexts: {rtexts d}"
  IO.println s!"Starts with 'hello': {dstartsWith d "hello"}"
  IO.println s!"Starts with 'hellp': {dstartsWith d "hellp"}"
  IO.println s!"Ends with 'world': {dendswith d "world"}"
  IO.println s!"Contains 'o': {dcontains d (· == 'o')}"

  let mdDoc := makeMarkdown (textP "a" <--> textP "b")
  IO.println s!"Markdown output: {asString mdDoc}"

#eval test_pprint
