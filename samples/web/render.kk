import std/num/double
import sys/dom/html/window
import sys/dom/html/htmlDivElement
import sys/dom/html/htmlElement
import sys/dom/document
import sys/dom/types
import sys/dom
import sys/dom/css/cssStyleDeclaration
import std/num/random


effect val window_val: window;
effect val parent_elem: htmlDivElement;
struct offset (dx : double, dy: double)

fun (==) (a: offset, b: offset) : bool
  a.dx == b.dx && a.dy == b.dy

fun (+) (a: offset, b: offset) : offset
  Offset(a.dx + b.dx, a.dy + b.dy)

fun (-) (a: offset, b: offset) : offset
  Offset(a.dx - b.dx, a.dy - b.dy)

struct size (width : double, height: double)

fun (==) (a: size, b: size) : bool
  a.width == b.width && a.height == b.height

struct boxConstraints (minWidth : double, maxWidth: double, minHeight: double, maxHeight: double)

fun min(b: boxConstraints) : size
  Size(b.minWidth, b.minHeight)

fun max(b: boxConstraints) : size
  Size(b.maxWidth, b.maxHeight)

fun constrain(b: boxConstraints, s: size): size
  val width = if s.width < b.minWidth then b.minWidth else if s.width > b.maxWidth then b.maxWidth else s.width
  val height = if s.height < b.minHeight then b.minHeight else if s.height > b.maxHeight then b.maxHeight else s.height
  Size(width, height)

fun withConstraints(b: boxConstraints, minWidth: double = b.minWidth, maxWidth: double = b.maxWidth,
         minHeight: double = b.minHeight, maxHeight: double = b.maxHeight ): boxConstraints
  BoxConstraints(minWidth, maxWidth, minHeight, maxHeight)

fun trimHeight(b: boxConstraints, height: double): boxConstraints
  val minHeight = if height > b.minHeight then 0.0 else b.minHeight - height
  val diffHeight = b.maxHeight - height
  val maxHeight = if diffHeight < minHeight then minHeight else diffHeight
  BoxConstraints(b.minWidth, b.maxWidth, minHeight, maxHeight)

fun (==) (a: boxConstraints, b: boxConstraints) : bool
  a.minWidth == b.minWidth && a.maxWidth == b.maxWidth && a.minHeight == b.minHeight && a.maxHeight == b.maxHeight

struct renderBox<a>(offset: offset = Offset(0.0,0.0), size: size = Size(0.0,0.0), 
           constraints: boxConstraints = BoxConstraints(0.0,0.0,0.0,0.0), node: a)

type renderTree<a>
  RenderEmpty
  RenderMultiChild(children: list<renderTree<a>>)
  RenderSingleChild(box: renderBox<a>)

effect val color: string;

fun render(b: renderBox<htmlDivElement>): <dom, random, parent_elem, window_val> renderBox<htmlDivElement>
  val divElement = b.node
  divElement.style.position := "absolute"
  divElement.style.left := b.offset.dx.show ++ "px"
  divElement.style.top := b.offset.dy.show ++ "px"
  divElement.style.width := b.size.width.show ++ "px"
  divElement.style.height := b.size.height.show ++ "px"
  with val color = if srandom-bool() then "red" else "blue"
  divElement.style.background := color
  parent_elem.appendChild(divElement.node)
  b

fun walk(b: renderTree<htmlDivElement>, transform: (renderBox<htmlDivElement>) -> <parent_elem|e> renderBox<htmlDivElement> ): <parent_elem|e> renderTree<htmlDivElement>
  match b
    RenderEmpty -> 
      RenderEmpty
    RenderSingleChild(box) -> 
      RenderSingleChild(box.transform)
    RenderMultiChild(children) -> 
      RenderMultiChild(children.map(fn (child){
        walk(child, transform)
      }))

fun layout(box: renderBox<htmlDivElement>): <window_val> ()
  ()

fun main()
  withWindow fn(w)
    with val window_val = w
    with val parent_elem = w.document.createHtmlDivElement()
    w.document.body.appendChild(parent_elem.node)
    val root = RenderMultiChild(
      Cons(
        RenderSingleChild(RenderBox(Offset(100.0,100.0), Size(100.0,100.0), BoxConstraints(0.0,0.0,0.0,0.0), w.document.createHtmlDivElement())), 
        Cons(RenderSingleChild(RenderBox(Offset(150.0,150.0), Size(100.0,100.0), BoxConstraints(0.0,0.0,0.0,0.0), w.document.createHtmlDivElement())), 
        Nil)))
    // val layout = root.box.layout
    val render = root.walk(render)
    ()