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
// Expression typing: Γ | Δ ⊢_σ e : τ ⊣ Γ' | Δ'
#let typeExpr(gin, din, ret, e, t, gout, dout) = $#gin | #din tack.r_(#ret) #e : #t tack.l #gout | #dout$
// Statement typing: Γ | Δ ⊢_σ s ⊣ Γ' | Δ'
#let typeStmt(gin, din, ret, s, gout, dout) = $#gin | #din tack.r_(#ret) #s tack.l #gout | #dout$
// Evaluation step: ⟨S | H | t⟩ ~> ⟨S' | H' | t'⟩
#let step(s, h, t) = $chevron.l #s | #h | #t chevron.r$
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

// Statements
#let While = $sans("while")$
#let Break = $sans("break")$
#let InLoop = math.op("inloop")

// Rhetorical and definitional emphasis
#let remph(body) = emph(body)
#let demph(body) = emph(body)

// Todo notes (rendered as margin notes or highlighted text)
#let jtodo(content) = text(fill: blue)[*JW: TODO:* #content]
#let jq(content) = text(fill: blue)[*JW: Question:* #content]
#let jc(content) = text(fill: blue)[*JW: Comment:* #content]
