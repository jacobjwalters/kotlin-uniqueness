// Custom definitions and commands

#import "@preview/curryst:0.3.0": rule, proof-tree

// Language name
#let Lbase = $cal(L)_sans("Base")$

// Contexts
#let ctx = $thin upright("ctx")$
#let drop = math.op("drop")
#let normalise = math.op("normalise")
#let body = math.op("body")
#let args = math.op("args")

// Simulation of mathpar: wrap proof trees in an inline block to allow automatic flow
#let mathpar(..trees) = {
  align(center, {
    for tree in trees.pos() {
      box(inset: (x: 1em, y: 1em), tree)
    }
  })
}

// Judgements
#let ms = $op(~>)^*$

// Types
#let Addr = $sans("Addr")$
#let Nat = $sans("Nat")$
#let Bool = $sans("Bool")$

// Terms
#let Skip = $sans("skip")$
#let Alloc = $sans("alloc")$
#let Free = $sans("free")$
#let Begin = $sans("begin")$
#let Return = $sans("return")$
#let Unique = $sans("unique")$
#let Aliased = $sans("aliased")$
#let Borrowed = $sans("borrowed")$
#let Null = $sans("null")$
#let Var = $sans("var")$
#let If = $sans("if")$
#let Then = $sans("then")$
#let Else = $sans("else")$
#let True = $sans("true")$
#let False = $sans("false")$

// Rhetorical and definitional emphasis
#let remph(body) = emph(body)
#let demph(body) = emph(body)

// Todo notes (rendered as margin notes or highlighted text)
#let jtodo(content) = text(fill: blue)[*JW: TODO:* #content]
#let jq(content) = text(fill: blue)[*JW: Question:* #content]
#let jc(content) = text(fill: blue)[*JW: Comment:* #content]
