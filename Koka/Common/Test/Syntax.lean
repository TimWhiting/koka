import Koka.Common.Syntax

open Koka.Common.Syntax

-- Test sepBySpace
#guard sepBySpace ["hello", "", "world"] == "hello world"

-- Test memberDoc
#guard (memberDoc "" "test" ["a", "b"]).contains "test:"
