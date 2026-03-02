#import "../defs.typ": *

// Local definitions for simplified judgement forms (override defs.typ)
// Expression typing: Γ ⊢ e : τ (no heap Δ, no return type σ, no output context)
#let typeExpr(gin, e, t) = $#gin tack.r #e : #t$
// Statement typing: Γ ⊢ s ⊣ Γ' (no heap Δ, no return type σ)
#let typeStmt(gin, s, gout) = $#gin tack.r #s tack.l #gout$
// CEK machine state: ⟨C | E | K⟩ with phase subscripts
#let cek(c, e, k) = $chevron.l #c | #e | #k chevron.r$
#let cekE(c, e, k) = $chevron.l #c | #e | #k chevron.r_e$
#let cekC(c, e, k) = $chevron.l #c | #e | #k chevron.r_c$
// Drop operation on contexts: drop(Γ, ℓ)
#let drop(g, l) = $op("drop") (#g, #l)$
// Coherence: E ~ Γ
#let coh(e, g) = $#e tilde #g$
// Continuation typing: Γ ⊢_e K and Γ ⊢_c K
#let typeContE(gin, k) = $#gin tack.r_e #k$
#let typeContC(gin, k) = $#gin tack.r_c #k$

= #Lbase

#Lbase is a simple typed language consisting of sequentially ordered statements with conditionals and loops. There are no classes, methods, modes, or lambdas.

== Syntax

$
tau ::=& #Nat && "Naturals" \
  |& #Bool && "Booleans" \
e ::=& x && "Variable Access" \
  |& #True \
  |& #False \
  |& n in bb(N) && "Natural Numbers" \
  |& e_1 plus.o e_2 && "Binary Operator" \
  |& plus.o (e) && "Unary Operator" \
s ::=& #Var x : tau = e && "(Mutable) Variable Declaration" \
  |& x = e && "Variable Assignment/Mutation" \
  |& s_1; s_2 && "Statement Sequencing" \
  |& #If e #Then s_1 #Else s_2 && "If/Then/Else" \
  |& #While c brace.l s brace.r && "While Loop" \
$

A program $P$ is a statement $s$. $x$ represents an infinite set of variable names. While we write names as strings in this document, for formalisation purposes, we use de Bruijn indices.

We write $plus.o$ to range over binary operators ${+, ∸, ==}$ and unary operators ${#IsZero}$. The meta-level function $#delta$ maps an operator and its argument value(s) to the result:

$
#delta (+, n_1, n_2) &= n_1 + n_2 \
#delta (∸, n_1, n_2) &= max(n_1 - n_2, 0) \
#delta (==, v_1, v_2) &= cases(#True &"if" v_1 = v_2, #False &"otherwise") \
#delta (#IsZero, n) &= cases(#True &"if" n = 0, #False &"otherwise")
$

== Typing Contexts
Typing contexts (hereafter contexts) in #Lbase are ordered, rightwards-growing lists of names and their associated types.

The grammar for contexts is as follows:

$
Gamma ::=& dot && "Empty" \
  |& Gamma, x : tau && "Variable Extension"
$

Lookup ($Gamma(x) = tau$) returns the type from the rightmost binding of $x$ in $Gamma$, permitting shadowing.

== Type System
Herein we discuss the type system of #Lbase.

=== Expression Types
Since expressions in the simplified language are pure, we use the judgement form #typeExpr($Gamma$, $e$, $tau$).

#mathpar(
  proof-tree(rule(name: "TrueConst", typeExpr($Gamma$, $#True$, $#Bool$))),
  proof-tree(rule(name: "FalseConst", typeExpr($Gamma$, $#False$, $#Bool$))),
  proof-tree(rule(name: "NatConst", typeExpr($Gamma$, $n$, $#Nat$), $n in bb(N)$)),

  proof-tree(rule(name: "VarAccess", typeExpr($Gamma$, $x$, $tau$), $Gamma(x) = tau$)),

  proof-tree(rule(name: "Add", typeExpr($Gamma$, $e_1 + e_2$, $#Nat$), typeExpr($Gamma$, $e_1$, $#Nat$), typeExpr($Gamma$, $e_2$, $#Nat$))),
  proof-tree(rule(name: "Sub", typeExpr($Gamma$, $e_1 ∸ e_2$, $#Nat$), typeExpr($Gamma$, $e_1$, $#Nat$), typeExpr($Gamma$, $e_2$, $#Nat$))),
  proof-tree(rule(name: "IsZero", typeExpr($Gamma$, $#IsZero (e)$, $#Bool$), typeExpr($Gamma$, $e$, $#Nat$))),
  proof-tree(rule(name: "Eq", typeExpr($Gamma$, $e_1 == e_2$, $#Bool$), typeExpr($Gamma$, $e_1$, $tau$), typeExpr($Gamma$, $e_2$, $tau$), $tau in {#Nat, #Bool}$)),
)

The Eq rule restricts equality to ground types ($tau in {#Nat, #Bool}$). This side condition is necessary because future extensions (e.g. function types) may not admit decidable equality.

=== Statement Types
Since statements may update their context, we use a "small-step" typing judgement form #typeStmt($Gamma$, $s$, $Gamma'$), where $Gamma$ represents the context before the statement runs and $Gamma'$ represents the context after.

#mathpar(
  proof-tree(rule(name: "VarDecl", typeStmt($Gamma$, $#Var x : tau = e$, $Gamma, x : tau$), typeExpr($Gamma$, $e$, $tau$))),
  proof-tree(rule(name: "VarAssign", typeStmt($Gamma$, $x = e$, $Gamma$), $Gamma(x) = tau$, typeExpr($Gamma$, $e$, $tau$))),

  proof-tree(rule(name: "Seq", typeStmt($Gamma$, $s_1; s_2$, $Gamma''$), typeStmt($Gamma$, $s_1$, $Gamma'$), typeStmt($Gamma'$, $s_2$, $Gamma''$))),

  proof-tree(rule(name: "IfStmt", typeStmt($Gamma$, $#If e #Then s_1 #Else s_2$, $Gamma$), typeExpr($Gamma$, $e$, $#Bool$), typeStmt($Gamma$, $s_1$, $Gamma'$), typeStmt($Gamma$, $s_2$, $Gamma''$))),

  proof-tree(rule(name: "WhileStmt", typeStmt($Gamma$, $#While c brace.l s brace.r$, $Gamma$), typeExpr($Gamma$, $c$, $#Bool$), typeStmt($Gamma$, $s$, $Gamma'$))),
)

Variable declarations check the initialiser expression against the declared type, then extend the context, possibly shadowing an existing binding.

Variable assignment requires that $x : tau$ is present somewhere in the context via membership lookup. The expression $e$ is typed under the same context $Gamma$, which includes $x$; this allows self mutation (such as $x = x + 1$). The output context is unchanged.

Sequencing threads the context produced as the output of the first statement into the input of the second statement.

The while loop checks its condition against $#Bool$ and types the body under $Gamma$. The body may extend the context to $Gamma'$, but the output context of the whole loop is $Gamma$ since the body is scoped per iteration.

=== Properties

- *Output Context Determinacy:* if #typeStmt($Gamma$, $s$, $Gamma_1$) and #typeStmt($Gamma$, $s$, $Gamma_2$), then $Gamma_1 = Gamma_2$.

- *Expression Weakening (Extension):* if #typeExpr($Gamma$, $e$, $tau$) and $Gamma$ is a suffix of $Gamma'$, then #typeExpr($Gamma'$, $e$, $tau$).

- *Expression Weakening (Permutation):* if #typeExpr($Gamma$, $e$, $tau$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeExpr($Gamma'$, $e$, $tau$).

- *Statement Weakening (Extension):* if #typeStmt($Gamma$, $s$, $Gamma, Delta$) and $Gamma$ is a suffix of $Gamma'$, then #typeStmt($Gamma'$, $s$, $Gamma', Delta$).

- *Statement Weakening (Permutation):* if #typeStmt($Gamma$, $s$, $Gamma, Delta$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeStmt($Gamma'$, $s$, $Gamma', Delta$).

Note that in the statement weakening properties, $Gamma, Delta$ refers to $Gamma$ concatenated with another context $Delta$; $Delta$ is *not* a heap. We can't extend by a single variable as in the expression weakening rules since compound statements may extend $Gamma$ with any number of new variables.


== Evaluation
Evaluation of an #Lbase program begins with a program statement $s$. We define the operational semantics as a CEK machine; a state machine that makes evaluation order explicit via a continuation stack. We also introduce a run-time language.

=== Run-time Language
The CEK machine operates on a run-time language that extends the source syntax with run-time-only forms. This language is a strict extension of the source language; it has one additional syntactic construct, with a corresponding typing rule. We should show all of the properties of the source language's type system hold for the run-time language's type system.

==== Values
Values are fully evaluated expressions:

$
v ::=& #True |& #False |& n in bb(N)
$

We write $tack.r v : tau$ for value typing: $tack.r #True : #Bool$, $tack.r #False : #Bool$, and $tack.r n : #Nat$ for $n in bb(N)$.

==== Completion Marker
$#Skip$ is a run-time-only completion marker indicating that a statement has been fully executed. It does not appear in the source program. Since $#Skip$ can appear in the control during evaluation, it needs a typing rule:

#mathpar(
  proof-tree(rule(name: "Skip", typeStmt($Gamma$, $#Skip$, $Gamma$))),
)

$#Skip$ preserves the context unchanged.

=== Machine State
The machine state is a 3-tuple $#cek($C$, $E$, $K$)$. The machine operates in one of two phases, indicated by a subscript on the state. In _Expr_ mode ($#cekE($C$, $E$, $K$)$), the control holds a source expression or statement to be decomposed. In _Cont_ mode ($#cekC($C$, $E$, $K$)$), the control holds a value or completion marker and the machine dispatches on the continuation.

#table(
  columns: (auto, auto, 1fr),
  align: (center, left, left),
  table.header([*Component*], [*Name*], [*Description*]),
  [$C$], [Control], [The current expression, statement, value, or completion marker being processed],
  [$E$], [Environment], [Ordered map from variables to values],
  [$K$], [Continuation], [Stack of continuations],
)

==== Control ($C$)
The control component holds whatever syntactic construct the machine is currently processing:

$
C ::=& e && "Source expression (to evaluate)" \
  |& s && "Source statement (to execute)" \
  |& v && "Value (expression result)" \
  |& #Skip && "Statement completed"
$

Expression evaluation terminates with a value $v$ in the control. Statement execution terminates with $#Skip$.

==== Environment ($E$)
$
E ::=& dot && "Empty" \
  |& E, x := v && "Variable binding" \
  |& E, #scopeMark($ell$) && "Scope boundary (labelled" ell")"
$

The environment is an ordered, rightwards-growing list of variable-to-value bindings interspersed with labelled scope markers. Lookup and update scan right-to-left, skipping scope markers. Lookup finds the rightmost binding for a given variable name (permitting shadowing). Update ($E[x |-> v]$) modifies the rightmost binding of $x$ in place.

The environment is extended when variables are declared ($#Var x : tau = e$ adds $x := v$ to the rightmost position, where $v$ is the value of $e$) and individual bindings are updated on assignment ($x = v$ updates the rightmost $x$). Scoping constructs push a labelled scope marker $#scopeMark($ell$)$ before entering a new scope. The operation $#pop($E$, $ell$)$ removes everything from the rightmost $#scopeMark($ell$)$ (inclusive) to the end of $E$:

$
#pop($E, #scopeMark($ell$)$, $ell$) &= E \
#pop($E, x := v$, $ell$) &= #pop($E$, $ell$) \
#pop($E, #scopeMark($ell'$)$, $ell$) &= #pop($E$, $ell$) && quad ell' != ell
$

Note that $#pop($dot$, $ell$)$ is undefined; the type system ensures a matching marker is always present.

The scope markers $#scopeMark($ell$)$ are notational devices for delineating scopes within a flat list. A formalisation may prefer to represent environments explicitly as a stack of frames (i.e. a list of lists), where push/pop correspond to cons/uncons on the outer list.

==== Continuation ($K$)
The continuation is a stack of frames that describes what to do after the current control finishes:

$
K ::=& #halt && "Program complete" \
  |& #ifCondK (s_1, s_2) dot.c K && "After evaluating condition, branch" \
  |& #jumpK (ell) dot.c K && "After scoped block completes, pop to" #scopeMark($ell$) \
  |& #declK (x : tau) dot.c K && "After evaluating initialiser of type" tau ", bind" x "in" E \
  |& #assignK (x) dot.c K && "After evaluating RHS, assign to" x "in" E \
  |& #seqK (s) dot.c K && "After first statement completes, continue with" s \
  |& #binopLK (plus.o, e_2) dot.c K && "After evaluating left operand of" plus.o", evaluate" e_2 \
  |& #binopRK (plus.o, v_1) dot.c K && "After evaluating right operand of" plus.o", apply to" v_1 \
  |& #unopK (plus.o) dot.c K && "After evaluating operand of unary" plus.o", apply" \
  |& #loopK (c, s) dot.c K && "After evaluating while condition, dispatch or re-enter"
$

- $#halt$ signals that the program is finished; a terminal state is $#cekC($#Skip$, $E$, $#halt$)$.
- $#ifCondK (s_1, s_2)$ waits for the condition expression to evaluate to a value, then dispatches to the appropriate branch.
- $#jumpK (ell)$ waits for a scoped block to complete, then pops the environment to the rightmost $#scopeMark($ell$)$, dropping scope-local declarations while preserving mutations to outer-scope variables.
- $#declK (x : tau)$ waits for the initialiser expression to evaluate to a value $v$ of type $tau$, then extends the environment with $x := v$.
- $#assignK (x)$ waits for the RHS expression to evaluate to a value $v$, then updates the environment with $E[x |-> v]$.
- $#seqK (s)$ waits for the first statement to complete, then loads $s$ into the control.
- $#binopLK (plus.o, e_2)$ waits for the left operand to evaluate to $v_1$, then begins evaluating $e_2$ with $#binopRK (plus.o, v_1)$ on the stack.
- $#binopRK (plus.o, v_1)$ waits for the right operand to evaluate to $v_2$, then computes $#delta (plus.o, v_1, v_2)$.
- $#unopK (plus.o)$ waits for the operand to evaluate to $v$, then computes $#delta (plus.o, v)$.
- $#loopK (c, s)$ serves dual roles: as an expression continuation, it receives the condition value ($#True$ enters the body, $#False$ exits); as a statement continuation, it receives $#Skip$ after the body completes (via $#jumpK$) and re-evaluates $c$.

=== Transition Rules
We define a multi-step judgement $ms$ in the usual way.

==== Expr
#mathpar(
  proof-tree(rule(name: "Val", $#cekE($v$, $E$, $K$) ~> #cekC($v$, $E$, $K$)$)),
  proof-tree(rule(name: "Var", $#cekE($x$, $E$, $K$) ~> #cekC($E(x)$, $E$, $K$)$)),
  proof-tree(rule(name: "If", $#cekE($#If e #Then s_1 #Else s_2$, $E$, $K$) ~> #cekE($e$, $E$, $#ifCondK (s_1, s_2) dot.c K$)$)),
  proof-tree(rule(name: "VarDecl", $#cekE($#Var x : tau = e$, $E$, $K$) ~> #cekE($e$, $E$, $#declK (x : tau) dot.c K$)$)),
  proof-tree(rule(name: "Assign", $#cekE($x = e$, $E$, $K$) ~> #cekE($e$, $E$, $#assignK (x) dot.c K$)$)),
  proof-tree(rule(name: "Seq", $#cekE($s_1 ; s_2$, $E$, $K$) ~> #cekE($s_1$, $E$, $#seqK (s_2) dot.c K$)$)),

  proof-tree(rule(name: "BinOp", $#cekE($e_1 plus.o e_2$, $E$, $K$) ~> #cekE($e_1$, $E$, $#binopLK (plus.o, e_2) dot.c K$)$)),
  proof-tree(rule(name: "UnOp", $#cekE($#IsZero (e)$, $E$, $K$) ~> #cekE($e$, $E$, $#unopK (#IsZero) dot.c K$)$)),

  proof-tree(rule(name: "While", $#cekE($#While c brace.l s brace.r$, $E$, $K$) ~> #cekE($c$, $E$, $#loopK (c, s) dot.c K$)$)),
)
Val transitions a source value expression ($#True$, $#False$, $n$) into Cont mode. Var looks up the rightmost binding of $x$ in $E$. The remaining rules decompose a compound form by pushing a continuation frame. BinOp evaluates the left operand first (left-to-right evaluation order). UnOp evaluates its single operand.

==== Cont
#mathpar(
  proof-tree(rule(name: "IfTrue", $#cekC($#True$, $E$, $#ifCondK (s_1, s_2) dot.c K$) ~> #cekE($s_1$, $E, #scopeMark($"if"$)$, $#jumpK ("if") dot.c K$)$)),
  proof-tree(rule(name: "IfFalse", $#cekC($#False$, $E$, $#ifCondK (s_1, s_2) dot.c K$) ~> #cekE($s_2$, $E, #scopeMark($"if"$)$, $#jumpK ("if") dot.c K$)$)),
  proof-tree(rule(name: "ScopeDone", $#cekC($#Skip$, $E$, $#jumpK (ell) dot.c K$) ~> #cekC($#Skip$, $#pop($E$, $ell$)$, $K$)$)),
  proof-tree(rule(name: "VarDeclDone", $#cekC($v$, $E$, $#declK (x : tau) dot.c K$) ~> #cekC($#Skip$, $E, x := v$, $K$)$)),
  proof-tree(rule(name: "AssignDone", $#cekC($v$, $E$, $#assignK (x) dot.c K$) ~> #cekC($#Skip$, $E[x |-> v]$, $K$)$)),
  proof-tree(rule(name: "SeqDone", $#cekC($#Skip$, $E$, $#seqK (s_2) dot.c K$) ~> #cekE($s_2$, $E$, $K$)$)),

  proof-tree(rule(name: "BinOpL", $#cekC($v_1$, $E$, $#binopLK (plus.o, e_2) dot.c K$) ~> #cekE($e_2$, $E$, $#binopRK (plus.o, v_1) dot.c K$)$)),
  proof-tree(rule(name: "BinOpR", $#cekC($v_2$, $E$, $#binopRK (plus.o, v_1) dot.c K$) ~> #cekC($#delta (plus.o, v_1, v_2)$, $E$, $K$)$)),
  proof-tree(rule(name: "UnOpDone", $#cekC($v$, $E$, $#unopK (plus.o) dot.c K$) ~> #cekC($#delta (plus.o, v)$, $E$, $K$)$)),

  proof-tree(rule(name: "LoopTrue", $#cekC($#True$, $E$, $#loopK (c, s) dot.c K$) ~> #cekE($s$, $E, #scopeMark($"wh"$)$, $#jumpK ("wh") dot.c #loopK (c, s) dot.c K$)$)),
  proof-tree(rule(name: "LoopFalse", $#cekC($#False$, $E$, $#loopK (c, s) dot.c K$) ~> #cekC($#Skip$, $E$, $K$)$)),
  proof-tree(rule(name: "LoopCont", $#cekC($#Skip$, $E$, $#loopK (c, s) dot.c K$) ~> #cekE($c$, $E$, $#loopK (c, s) dot.c K$)$)),
)
IfTrue/IfFalse push a scope marker $#scopeMark($"if"$)$ and $#jumpK ("if")$ before entering a branch. ScopeDone pops the environment to the rightmost $#scopeMark($ell$)$. $E[x |-> v]$ updates the rightmost binding of $x$ in $E$. BinOpL/BinOpR implement left-to-right evaluation of binary operators: BinOpL saves the left value and begins the right operand; BinOpR applies $#delta$ to both values. UnOpDone applies $#delta$ to the single operand value. LoopTrue pushes a scope marker $#scopeMark($"wh"$)$ and enters the body with $#jumpK ("wh") dot.c #loopK (c, s)$ on the stack; after the body completes, ScopeDone pops the iteration scope and LoopCont re-evaluates the condition. LoopFalse exits the loop with $#Skip$.

The lifecycle of a while loop proceeds as follows. The While rule evaluates the condition $c$, pushing $#loopK (c, s)$ onto the continuation. If the condition is $#False$, LoopFalse produces $#Skip$ and the loop terminates. If the condition is $#True$, LoopTrue pushes a scope marker $#scopeMark($"wh"$)$ onto the environment and begins executing the body $s$ with the continuation $#jumpK ("wh") dot.c #loopK (c, s) dot.c K$. When the body completes with $#Skip$, ScopeDone fires on $#jumpK ("wh")$, popping the environment back to $#scopeMark($"wh"$)$ and discarding any variables declared during the iteration. The resulting $#Skip$ then reaches $#loopK (c, s)$, which triggers LoopCont to re-evaluate the condition $c$, beginning the next iteration. The $#loopK$ frame remains on the stack throughout, avoiding any per-iteration allocation.

=== Initial and Terminal States

$
"Initial:" && #cekE($s$, $dot$, $#halt$) && "where" s "is the program" \
"Terminal:" && #cekC($#Skip$, $E$, $#halt$)
$

=== Continuation Typing

For runtime typing purposes, we use the same scope marker device as environments: contexts may be extended with $#scopeMark($ell$)$ to delineate scopes. The source-level typing rules work unchanged on extended contexts since lookup skips markers. We define $#drop($Gamma$, $ell$)$ as the context-level counterpart of $#pop($E$, $ell$)$:

$
#drop($Gamma, #scopeMark($ell$)$, $ell$) &= Gamma \
#drop($Gamma, x : tau$, $ell$) &= #drop($Gamma$, $ell$) \
#drop($Gamma, #scopeMark($ell'$)$, $ell$) &= #drop($Gamma$, $ell$) && quad ell' != ell
$

As with environments, a formalisation may prefer a stack-of-frames representation over explicit markers.

We define well-typedness for continuations with two judgement forms mirroring the machine phases. _Statement continuations_ (#typeContC($Gamma$, $K$)) accept $#Skip$ in context $Gamma$. _Expression continuations_ (#typeContE($Gamma$, $K$)) accept a value in context $Gamma$; the expected type is determined internally by each frame.

==== Statement Continuations

#mathpar(
  proof-tree(rule(name: "KHalt", typeContC($Gamma$, $#halt$))),
  proof-tree(rule(name: "KJump", typeContC($Gamma$, $#jumpK (ell) dot.c K$), typeContC($#drop($Gamma$, $ell$)$, $K$))),
  proof-tree(rule(name: "KSeq", typeContC($Gamma$, $#seqK (s) dot.c K$), typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma'$, $K$))),
  proof-tree(rule(name: "KLoop", typeContC($Gamma$, $#loopK (c, s) dot.c K$), typeExpr($Gamma$, $c$, $#Bool$), typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma$, $K$))),
)

KJump uses $#drop($Gamma$, $ell$)$ to strip the context to the matching scope marker, mirroring $#pop($E$, $ell$)$ on environments. The tail $K$ is typed at the resulting outer context. KLoop checks the condition and body under $Gamma$; the tail $K$ is typed at $Gamma$ since the loop preserves the context.

==== Expression Continuations

#mathpar(
  proof-tree(rule(name: "KIfCond", typeContE($Gamma$, $#ifCondK (s_1, s_2) dot.c K$), typeStmt($Gamma, #scopeMark($"if"$)$, $s_1$, $Gamma'$), typeStmt($Gamma, #scopeMark($"if"$)$, $s_2$, $Gamma''$), typeContC($Gamma$, $K$))),
  proof-tree(rule(name: "KDecl", typeContE($Gamma$, $#declK (x : tau) dot.c K$), typeContC($Gamma, x : tau$, $K$))),
  proof-tree(rule(name: "KAssign", typeContE($Gamma$, $#assignK (x) dot.c K$), $Gamma(x) = tau$, typeContC($Gamma$, $K$))),

  proof-tree(rule(name: "KBinOpL", typeContE($Gamma$, $#binopLK (plus.o, e_2) dot.c K$), $plus.o : tau_1 times tau_2 -> tau_3$, typeExpr($Gamma$, $e_2$, $tau_2$), typeContE($Gamma$, $K$))),
  proof-tree(rule(name: "KBinOpR", typeContE($Gamma$, $#binopRK (plus.o, v_1) dot.c K$), $plus.o : tau_1 times tau_2 -> tau_3$, $tack.r v_1 : tau_1$, typeContE($Gamma$, $K$))),
  proof-tree(rule(name: "KUnOp", typeContE($Gamma$, $#unopK (plus.o) dot.c K$), typeContE($Gamma$, $K$))),
  proof-tree(rule(name: "KLoopE", typeContE($Gamma$, $#loopK (c, s) dot.c K$), typeExpr($Gamma$, $c$, $#Bool$), typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma$, $K$))),
)

KIfCond types both branches under $Gamma, #scopeMark($"if"$)$ (with a scope marker); the tail $K$ accepts $#Skip$ in $Gamma$ since the if-statement's output context is $Gamma$. KDecl extends the context with $x : tau$ for the tail. KAssign preserves the context since assignment does not change it. KBinOpL checks the pending right operand $e_2$ and requires the tail $K$ to accept the result. KBinOpR checks the saved left value $v_1$ against the operator's left domain. KUnOp simply requires the tail to accept the result. The operator signature premise $plus.o : tau_1 times tau_2 -> tau_3$ is determined by the fixed set of operators. KLoopE has the same premises as KLoop but appears as an expression continuation because $#loopK$ receives the condition value (a $#Bool$); the tail $K$ uses #typeContC because the loop ultimately produces $#Skip$.

=== Environment-Context Coherence

We define _coherence_ between an environment and a context, written $#coh($E$, $Gamma$)$, inductively:

#mathpar(
  proof-tree(rule(name: "CohEmp", $#coh($dot$, $dot$)$)),
  proof-tree(rule(name: "CohBind", $#coh($E, x := v$, $Gamma, x : tau$)$, $#coh($E$, $Gamma$)$, $tack.r v : tau$)),
  proof-tree(rule(name: "CohMark", $#coh($E, #scopeMark($ell$)$, $Gamma, #scopeMark($ell$)$)$, $#coh($E$, $Gamma$)$)),
)

Scope markers must match between $E$ and $Gamma$.

==== Well Typed States

A machine state is _well-typed_ when coherence bridges the environment to a context $Gamma$ that types both the control and the continuation:

#mathpar(
  proof-tree(rule(name: "WtExprE", $tack.r #cekE($e$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, typeExpr($Gamma$, $e$, $tau$), typeContE($Gamma$, $K$))),
  proof-tree(rule(name: "WtExprS", $tack.r #cekE($s$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma'$, $K$))),
  proof-tree(rule(name: "WtContV", $tack.r #cekC($v$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $tack.r v : tau$, typeContE($Gamma$, $K$))),
  proof-tree(rule(name: "WtContS", $tack.r #cekC($#Skip$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, typeContC($Gamma$, $K$))),
)

=== Properties

- *Progress:* if $tack.r S "ok"$ and $S$ is not terminal, then there exists $S'$ such that $S ~> S'$.

- *Preservation:* if $tack.r S "ok"$ and $S ~> S'$, then $tack.r S' "ok"$.

- *Statement Execution Preserves Coherence:* if $#coh($E$, $Gamma$)$, #typeStmt($Gamma$, $s$, $Gamma'$), and $#cekE($s$, $E$, $K$) #ms #cekC($#Skip$, $E'$, $K$)$, then $#coh($E'$, $Gamma'$)$.

- *Pop/Drop Preserves Coherence:* if $#coh($E$, $Gamma$)$, then $#coh($#pop($E$, $ell$)$, $#drop($Gamma$, $ell$)$)$.

- *Determinacy:* each machine state has at most one successor (the transition relation is deterministic). Consequently, if the machine terminates, the terminal state is unique.
