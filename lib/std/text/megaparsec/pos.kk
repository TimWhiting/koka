module std/text/megaparsec/pos

import std/os/path

struct pos
  offset: int

pub fun show(p: pos): string
  "Pos " ++ p.offset.show

pub fun mkPos(offset: int): <invalid-position> pos
  if (offset <= 0)
    invalidPosition(offset)
  Pos(offset)

pub fun unPos(p: pos): int
  p.offset

pub val pos1 = Pos(1)

pub val defaultTabWidth = Pos(8)

pub fun (+)(p1: pos, p2: pos): pos
  Pos(p1.offset + p2.offset)

pub effect invalid-position
  final ctl invalidPosition(p: pos)

pub struct sourcePos
  name: path
  line: pos
  column: pos

pub fun show(p: sourcePos): string
  "SourcePos " ++ p.name.show ++ " " ++ p.line.show ++ " " ++ p.column.show

pub fun initialPos(n: path): sourcePos
  SourcePos(n, pos1, pos1)

pub fun sourcePosPretty(p: sourcePos): string
  val loc := p.line.show ++ ":" ++ p.column.show
  if p.name != "" then
    p.name ++ ":" ++ loc
  else
    loc
  
