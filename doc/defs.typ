// Custom definitions and commands

#import "@preview/curryst:0.3.0": rule, proof-tree

// Language names
#let Lbase = $cal(L)_sans("Base")$
#let Lclass = $cal(L)_sans("Class")$

// Contexts
#let ctx = $thin upright("ctx")$
#let drop = math.op("drop")
#let trunc(e, n) = $#e attach(arrow.b, br: #n)$
#let normalise = math.op("normalise")
#let body = math.op("body")
#let args = math.op("args")
#let fields = math.op("fields")

// Simulation of mathpar: wrap proof trees in an inline block to allow automatic flow
#let mathpar(..trees) = {
  align(center, {
    for tree in trees.pos() {
      box(inset: (x: 1em, y: 1em), tree)
    }
  })
}

// Judgement forms
// Expression typing: Γ ⊢_σ e : τ ⊣ Γ'
#let typeExpr(gin, ret, e, t, gout) = $#gin attach(tack.r, br: #ret) #e : #t tack.l #gout$
// Statement typing: Γ ⊢_σ s ⊣ Γ'
#let typeStmt(gin, ret, s, gout) = $#gin attach(tack.r, br: #ret) #s tack.l #gout$

// CESK machine state: ⟨C | E | S | K⟩
#let cesk(c, e, s, k) = $chevron.l #c | #e | #s | #k chevron.r$
// Multi-step
#let ms = $op(~>)^*$

// Classes
#let Class = $sans("class")$

// Types
#let Nat = $sans("Nat")$
#let Bool = $sans("Bool")$

// Modalities
#let Unique = $sans("unique")$
#let Aliased = $sans("aliased")$
#let Borrowed = $sans("borrowed")$

// Exprs
#let Skip = $sans("skip")$
#let Return = $sans("return")$
#let Null = $sans("null")$
#let Var = $sans("var")$
#let If = $sans("if")$
#let Then = $sans("then")$
#let Else = $sans("else")$
#let True = $sans("true")$
#let False = $sans("false")$
#let IsZero = math.op("iszero")

// Statements
#let While = $sans("while")$
#let Break = $sans("break")$

// CESK continuation frames
#let fieldK = math.op("fieldK")
#let ifCondK = math.op("ifCondK")
#let ifDoneK = math.op("ifDoneK")
#let returnK = $sans("returnK")$
#let assignK = math.op("assignK")
#let seqK = math.op("seqK")
#let loopK = math.op("loopK")
#let argK = math.op("argK")
#let callK = math.op("callK")
#let binopLK = math.op("binopLK")
#let binopRK = math.op("binopRK")
#let unopK = math.op("unopK")
#let halt = $sans("halt")$

// Meta-level operator application
#let delta = $delta$

// Runtime signals
#let sig = $sans("sig")$
#let breaking = $sans("breaking")$
#let returning = $sans("returning")$

// Rhetorical and definitional emphasis
#let remph(body) = emph(body)
#let demph(body) = emph(body)

// Todo notes (rendered as margin notes or highlighted text)
#let jtodo(content) = text(fill: blue)[*JW: TODO:* #content]
#let jq(content) = text(fill: blue)[*JW: Question:* #content]
#let jc(content) = text(fill: blue)[*JW: Comment:* #content]
