import Koka.Lib.PPrint

open Koka.Lib.PPrint

-- Test PPrint
#guard asString (textP "hello" <+> textP "world") == "hello world"
#guard asString (tupled [textP "1", textP "2"]) == "(1, 2)"
