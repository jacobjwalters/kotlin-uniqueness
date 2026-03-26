// Custom definitions and commands

#import "@preview/curryst:0.3.0": proof-tree, rule

// Language names
#let Lbase = $cal(L)_sans("Base")$
#let Lclass = $cal(L)_sans("Class")$

// Contexts
#let ctx = $thin upright("ctx")$
#let drop = math.op("drop")
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

// Judgement forms (shared by Lbase and Lclass via jump context Δ)
// Expression typing: Γ | Δ ⊢ e : τ
#let typeExpr(gin, delta, e, t) = $#gin | #delta tack.r #e : #t$
// Statement typing: Δ | Γ ⊢ s ⊣ Γ'
#let typeStmt(delta, gin, s, gout) = $#delta | #gin tack.r #s tack.l #gout$
// Continuation typing: Γ | Δ ⊢ K : τ̄ and Γ | Δ ⊢ K
#let typeContE(gin, delta, k, t) = $#gin | #delta tack.r #k : overline(#t)$
#let typeContC(gin, delta, k) = $#gin | #delta tack.r #k$
// Coherence: E ~ Γ
#let coh(e, g) = $#e tilde #g$

// CEJK machine state: ⟨C | E | J | K⟩ with phase subscripts (Lbase)
#let cek(c, e, j, k) = $chevron.l #c | #e | #j | #k chevron.r$
#let cekE(c, e, j, k) = $chevron.l #c | #e | #j | #k chevron.r_e$
#let cekC(c, e, j, k) = $chevron.l #c | #e | #j | #k chevron.r_c$
// Jump stack coherence
#let jcoh(j, g, d) = $#j tilde.op #g | #d$
// CEJSK machine state: ⟨C | E | J | S | K⟩ with phase subscripts (Lclass)
#let cesk(c, e, j, s, k) = $chevron.l #c | #e | #j | #s | #k chevron.r$
#let ceskE(c, e, j, s, k) = $chevron.l #c | #e | #j | #s | #k chevron.r_e$
#let ceskC(c, e, j, s, k) = $chevron.l #c | #e | #j | #s | #k chevron.r_c$
// Multi-step
#let ms = $op(~>)^*$

// Classes
#let Class = $sans("class")$

// Types
#let Nat = $sans("Nat")$
#let Bool = $sans("Bool")$
#let Unit = $sans("Unit")$

// Exprs
#let Skip = $sans("skip")$
#let Return = $sans("return")$
#let New = $sans("new")$
#let Var = $sans("var")$
#let UnitVal = $sans("unit")$
#let Scope = $sans("scope")$
#let Do = $sans("do")$
#let If = $sans("if")$
#let Then = $sans("then")$
#let Else = $sans("else")$
#let True = $sans("true")$
#let False = $sans("false")$
#let IsZero = math.op("iszero")

// Statements
#let While = $sans("while")$
#let Break = $sans("break")$

// Jump context Δ
#let Loop = math.op("loop")
#let Method = math.op("method")

// CESK continuation frames
#let fieldK = math.op("fieldK")
#let ifCondK = math.op("ifCondK")
#let jumpK = math.op("jumpK")
#let declK = math.op("declK")
#let returnK = math.op("returnK")
#let assignK = math.op("assignK")
#let seqK = math.op("seqK")
#let loopK = math.op("loopK")
#let argK = math.op("argK")
#let callK = math.op("callK")
#let newK = math.op("newK")
#let binopLK = math.op("binopLK")
#let binopRK = math.op("binopRK")
#let unopK = math.op("unopK")
#let halt = math.op("halt")

// Lbase-specific continuation frames (scope/loop redesign)
#let scopeBodyK = math.op("scopeBodyK")
#let scopeExitK = math.op("scopeExitK")
#let loopContK = math.op("loopContK")
#let exprStmtK = math.op("exprStmtK")

// Operations
#let truncate(e, n) = $#e bar.v_#n$

// Continuation typing rule names (used in proof-tree labels and prose)
#let IfCondK = math.op("IfCondK")
#let DeclK = math.op("DeclK")
#let AssignK = math.op("AssignK")
#let BinOpLK = math.op("BinOpLK")
#let BinOpRK = math.op("BinOpRK")
#let UnOpK = math.op("UnOpK")
#let LoopK = math.op("LoopK")
#let LoopContK = math.op("LoopContK")
#let ScopeExitK = math.op("ScopeExitK")
#let ExprStmtK = math.op("ExprStmtK")
#let HaltK = math.op("HaltK")
#let SeqK = math.op("SeqK")
#let ScopeBodyK = math.op("ScopeBodyK")

// Meta-level operator application
#let delta = $delta$


// Rhetorical and definitional emphasis
#let remph(body) = emph(body)
#let demph(body) = emph(body)

// Todo notes (rendered as margin notes or highlighted text)
#let jtodo(content) = text(fill: blue)[*JW: TODO:* #content]
#let jq(content) = text(fill: blue)[*JW: Question:* #content]
#let jc(content) = text(fill: blue)[*JW: Comment:* #content]
