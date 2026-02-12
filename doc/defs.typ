// Custom definitions and commands

#import "@preview/curryst:0.3.0": rule, proof-tree

// Language name
#let Lbase = $cal(L)_sans("Base")$

// Better spacing for typing judgements
#let Colon = $thin :$

// Better spacing for statement sequences
#let Semi = $";" thin thin$

// Contexts
#let ctx = $thin upright("ctx")$

// Types
#let Nat = $sans("Nat")$
#let Bool = $sans("Bool")$

// Terms
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
#let jq(content) = text(fill: blue)[*JW:* #content]
#let jc(content) = text(fill: blue)[*JW:* #content]
