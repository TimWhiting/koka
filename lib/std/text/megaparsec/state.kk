module std/text/megaparsec/state

import std/text/megaparsec/pos
import std/text/megaparsec/error

struct state<s, e>
  input: s
  offset: int
  pos: posState
  parseErrors: list<parseError<s,e>>;

struct posState<s>
  input: s
  offset: int
  sourcePos: sourcePos
  tabWidth: pos
  linePrefix: string;

