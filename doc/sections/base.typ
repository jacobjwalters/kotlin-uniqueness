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
// Continuation typing: Γ ⊢ K : τ̄ and Γ ⊢ K
#let typeContE(gin, k, t) = $#gin tack.r #k : overline(#t)$
#let typeContC(gin, k) = $#gin tack.r #k$

= #Lbase

#Lbase is a simple typed language with expressions and statements. Conditionals, loops, and breaks are expressions; local variable scoping is managed by scope blocks. There are no classes, methods, modes, or lambdas.

== Syntax

$
tau ::=& #Nat && "Naturals" \
  |& #Bool && "Booleans" \
  |& #Unit && "Unit" \
e ::=& x && "Variable Access" \
  |& #True \
  |& #False \
  |& n in bb(N) && "Natural Numbers" \
  |& #UnitVal && "Unit Value" \
  |& e_1 plus.o e_2 && "Binary Operator" \
  |& plus.o (e) && "Unary Operator" \
  |& #If e #Then e_1 #Else e_2 && "If/Then/Else" \
  |& #While c brace.l e brace.r && "While Loop" \
  |& #Break && "Loop Break" \
  |& #Scope brace.l s; e brace.r && "Scope Block" \
s ::=& #Var x : tau = e && "(Mutable) Variable Declaration" \
  |& x = e && "Variable Assignment/Mutation" \
  |& s_1; s_2 && "Statement Sequencing" \
  |& #Do e && "Expression Statement" \
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
Since expressions do not modify the typing context, we use the judgement form #typeExpr($Gamma$, $e$, $tau$) with no output context.

#mathpar(
  proof-tree(rule(name: "TrueConst", typeExpr($Gamma$, $#True$, $#Bool$))),
  proof-tree(rule(name: "FalseConst", typeExpr($Gamma$, $#False$, $#Bool$))),
  proof-tree(rule(name: "NatConst", typeExpr($Gamma$, $n$, $#Nat$), $n in bb(N)$)),
  proof-tree(rule(name: "UnitConst", typeExpr($Gamma$, $#UnitVal$, $#Unit$))),

  proof-tree(rule(name: "VarAccess", typeExpr($Gamma$, $x$, $tau$), $Gamma(x) = tau$)),

  proof-tree(rule(name: "BinOp", typeExpr($Gamma$, $e_1 plus.o e_2$, $tau_3$), typeExpr($Gamma$, $e_1$, $tau_1$), typeExpr($Gamma$, $e_2$, $tau_2$), $plus.o : tau_1 times tau_2 -> tau_3$)),
  proof-tree(rule(name: "UnOp", typeExpr($Gamma$, $plus.o (e)$, $tau_2$), typeExpr($Gamma$, $e$, $tau_1$), $plus.o : tau_1 -> tau_2$)),

  proof-tree(rule(name: "IfExpr", typeExpr($Gamma$, $#If e #Then e_1 #Else e_2$, $tau$), typeExpr($Gamma$, $e$, $#Bool$), typeExpr($Gamma$, $e_1$, $tau$), typeExpr($Gamma$, $e_2$, $tau$))),

  proof-tree(rule(name: "WhileExpr", typeExpr($Gamma$, $#While c brace.l e brace.r$, $#Unit$), typeExpr($Gamma$, $c$, $#Bool$), typeExpr($Gamma$, $e$, $#Unit$))),

  proof-tree(rule(name: "BreakExpr", typeExpr($Gamma$, $#Break$, $tau$))),

  proof-tree(rule(name: "ScopeExpr", typeExpr($Gamma$, $#Scope brace.l s; e brace.r$, $tau$), typeStmt($Gamma$, $s$, $Gamma'$), typeExpr($Gamma'$, $e$, $tau$))),
)

$#If$ expressions require both branches to have the same type $tau$; the condition must be $#Bool$. $#While$ expressions have type $#Unit$; the body must have type $#Unit$. $#Break$ has type $tau$ for any $tau$ since it never produces a value, and any code that consumes it is dead code as far as evaluation is concerned.

Note: BreakExpr places no restriction on $Gamma$, so $#Break$ is well-typed even outside a loop body; such programs get stuck at runtime (see Progress below). $#Scope$ expressions run a sequence of statements $s$ (which may extend the context from $Gamma$ to $Gamma'$), then evaluate a trailing expression $e$ in the extended context $Gamma'$. The overall type is the type of $e$; the scope's local declarations are not visible outside.

The operator signature premise $plus.o : tau_1 times tau_2 -> tau_3$ (or $plus.o : tau_1 -> tau_2$ for unary) is grounded by the operator typing rules below.

=== Operator Typing

The meta-level function $#delta$ is typed by the following rules, which define the operator signatures referenced in both the expression typing and the continuation typing:

#mathpar(
  proof-tree(rule(name: "DeltaAdd", $tack.r #delta (+, v_1, v_2) : #Nat$, $tack.r v_1 : #Nat$, $tack.r v_2 : #Nat$)),
  proof-tree(rule(name: "DeltaSub", $tack.r #delta (∸, v_1, v_2) : #Nat$, $tack.r v_1 : #Nat$, $tack.r v_2 : #Nat$)),
  proof-tree(rule(name: "DeltaEq", $tack.r #delta (==, v_1, v_2) : #Bool$, $tack.r v_1 : tau$, $tack.r v_2 : tau$, $tau in {#Nat, #Bool}$)),
  proof-tree(rule(name: "DeltaIsZero", $tack.r #delta (#IsZero, v) : #Bool$, $tack.r v : #Nat$)),
)

=== Statement Types
Since statements may update their context, we use a "small-step" typing judgement form #typeStmt($Gamma$, $s$, $Gamma'$), where $Gamma$ represents the context before the statement runs and $Gamma'$ represents the context after.

#mathpar(
  proof-tree(rule(name: "VarDecl", typeStmt($Gamma$, $#Var x : tau = e$, $Gamma, x : tau$), typeExpr($Gamma$, $e$, $tau$))),
  proof-tree(rule(name: "VarAssign", typeStmt($Gamma$, $x = e$, $Gamma$), $Gamma(x) = tau$, typeExpr($Gamma$, $e$, $tau$))),

  proof-tree(rule(name: "Seq", typeStmt($Gamma$, $s_1; s_2$, $Gamma''$), typeStmt($Gamma$, $s_1$, $Gamma'$), typeStmt($Gamma'$, $s_2$, $Gamma''$))),

  proof-tree(rule(name: "ExprStmt", typeStmt($Gamma$, $#Do e$, $Gamma$), typeExpr($Gamma$, $e$, $tau$))),
)

Variable declarations check the initialiser expression against the declared type, then extend the context, possibly shadowing an existing binding.

Variable assignment requires that $x : tau$ is present somewhere in the context via membership lookup. The expression $e$ is typed under the same context $Gamma$, which includes $x$; this allows self mutation (such as $x = x + 1$). The output context is unchanged.

Sequencing threads the context produced as the output of the first statement into the input of the second statement.

In order to admit $#If$, $#While$ and $#Break$ in statement positions, we use expression statements ($#Do e$) to evaluate an expression and discard the result. Since expressions do not modify the typing context, the output context is $Gamma$ (unchanged).

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
The CEK machine operates on a run-time language that extends the source syntax with run-time-only forms. This language is a strict extension of the source language; it has one additional syntactic construct $#Skip$, with a corresponding typing rule. We should show all of the properties of the source language's type system hold for the run-time language's type system too.

==== Values
Values are fully evaluated expressions:

$
v ::=& #True |& #False |& n in bb(N) |& #UnitVal
$

We write $tack.r v : tau$ for value typing: $tack.r #True : #Bool$, $tack.r #False : #Bool$, $tack.r n : #Nat$ for $n in bb(N)$, and $tack.r #UnitVal : #Unit$.

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
  |& E, x := v && "Variable binding"
$

The environment is an ordered, rightwards-growing list of variable-to-value bindings. Lookup and update scan right-to-left. Lookup finds the rightmost binding for a given variable name (permitting shadowing). Update ($E[x |-> v]$) modifies the rightmost binding of $x$ in place.

The environment is extended when variables are declared ($#Var x : tau = e$ adds $x := v$ to the rightmost position, where $v$ is the value of $e$) and individual bindings are updated on assignment ($x = v$ updates the rightmost $x$). We write $|E|$ for the length (number of bindings) of $E$. The operation $#truncate($E$, $n$)$ returns the first $n$ bindings of $E$, dropping everything from position $n + 1$ onward. Scoping constructs record $|E|$ at entry and truncate back to that size at exit.

The operation $#popLoopK ($K$)$ scans the continuation for the first $#loopK$ or $#loopContK$ frame and returns both the saved environment size $n$ and the tail after it:

$
#popLoopK (#loopK (c, e, n) dot.c K) &= (n, K) \
#popLoopK (#loopContK (c, e, n) dot.c K) &= (n, K) \
#popLoopK (F dot.c K) &= #popLoopK (K) && quad F "not a loop frame"
$

$#popLoopK ($#halt$)$ is undefined; a well-formedness precondition on source programs requires that $#Break$ appears only inside a $#While$ body (see Progress caveat).

==== Continuation ($K$)
The continuation is a stack of frames that describes what to do after the current control finishes:

$
K ::=& #halt && "Program complete" \
  |& #ifCondK (e_1, e_2) dot.c K && "After evaluating condition, branch to expression" \
  |& #declK (x : tau) dot.c K && "After evaluating initialiser of type" tau ", bind" x "in" E \
  |& #assignK (x) dot.c K && "After evaluating RHS, assign to" x "in" E \
  |& #seqK (s) dot.c K && "After first statement completes, continue with" s \
  |& #binopLK (plus.o, e_2) dot.c K && "After evaluating left operand of" plus.o", evaluate" e_2 \
  |& #binopRK (plus.o, v_1) dot.c K && "After evaluating right operand of" plus.o", apply to" v_1 \
  |& #unopK (plus.o) dot.c K && "After evaluating operand of unary" plus.o", apply" \
  |& #loopK (c, e, n) dot.c K && "While condition: body" e ", saved env size" n \
  |& #loopContK (c, e, n) dot.c K && "After loop body, re-evaluate condition" \
  |& #scopeBodyK (e, n) dot.c K && "After scope statements, evaluate trailing expr" e \
  |& #scopeExitK (n) dot.c K && "After trailing expr, truncate env to size" n \
  |& #exprStmtK dot.c K && "After expression evaluates, discard value"
$

- $#halt$ signals that the program is finished; a terminal state is $#cekC($#Skip$, $E$, $#halt$)$.
- $#ifCondK (e_1, e_2)$ waits for the condition to evaluate, then dispatches to the appropriate branch expression.
- $#declK (x : tau)$ waits for the initialiser expression to evaluate to a value $v$ of type $tau$, then extends the environment with $x := v$.
- $#assignK (x)$ waits for the RHS expression to evaluate to a value $v$, then updates the environment with $E[x |-> v]$.
- $#seqK (s)$ waits for the first statement to complete, then loads $s$ into the control.
- $#binopLK (plus.o, e_2)$ waits for the left operand to evaluate to $v_1$, then begins evaluating $e_2$ with $#binopRK (plus.o, v_1)$ on the stack.
- $#binopRK (plus.o, v_1)$ waits for the right operand to evaluate to $v_2$, then computes $#delta (plus.o, v_1, v_2)$.
- $#unopK (plus.o)$ waits for the operand to evaluate to $v$, then computes $#delta (plus.o, v)$.
- $#loopK (c, e, n)$ receives the condition value: $#True$ enters the body $e$ via $#loopContK$; $#False$ truncates the environment to size $n$ and produces $#UnitVal$. The saved size $n$ records $|E|$ at while entry.
- $#loopContK (c, e, n)$ receives $#UnitVal$ after the body completes, then re-evaluates $c$ with $#loopK$ on the continuation.
- $#scopeBodyK (e, n)$ waits for the scope's statements to complete ($#Skip$), then evaluates the trailing expression $e$. The saved size $n$ records $|E|$ at scope entry.
- $#scopeExitK (n)$ waits for the trailing expression to produce a value, then truncates the environment to size $n$, dropping scope-local bindings.
- $#exprStmtK$ waits for an expression to produce a value, discards it, and produces $#Skip$.

=== Transition Rules
We define a multi-step judgement $ms$ in the usual way.

==== Expr
$
#cekE($v$, $E$, $K$) &~> #cekC($v$, $E$, $K$) && "Val" \
#cekE($x$, $E$, $K$) &~> #cekC($E(x)$, $E$, $K$) && "Var" \
#cekE($#Var x : tau = e$, $E$, $K$) &~> #cekE($e$, $E$, $#declK (x : tau) dot.c K$) && "VarDecl" \
#cekE($x = e$, $E$, $K$) &~> #cekE($e$, $E$, $#assignK (x) dot.c K$) && "Assign" \
#cekE($s_1 ; s_2$, $E$, $K$) &~> #cekE($s_1$, $E$, $#seqK (s_2) dot.c K$) && "Seq" \
#cekE($#Do e$, $E$, $K$) &~> #cekE($e$, $E$, $#exprStmtK dot.c K$) && "ExprStmt" \
#cekE($e_1 plus.o e_2$, $E$, $K$) &~> #cekE($e_1$, $E$, $#binopLK (plus.o, e_2) dot.c K$) && "BinOp" \
#cekE($#IsZero (e)$, $E$, $K$) &~> #cekE($e$, $E$, $#unopK (#IsZero) dot.c K$) && "UnOp" \
#cekE($#If e #Then e_1 #Else e_2$, $E$, $K$) &~> #cekE($e$, $E$, $#ifCondK (e_1, e_2) dot.c K$) && "If" \
#cekE($#While c brace.l e brace.r$, $E$, $K$) &~> #cekE($c$, $E$, $#loopK (c, e, |E|) dot.c K$) && "While" \
#cekE($#Break$, $E$, $K$) &~> #cekC($#UnitVal$, $#truncate($E$, $n$)$, $K'$) && "Break" \
& quad "where" op("popLoopK") (K) = (n, K') \
#cekE($#Scope brace.l s ; e brace.r$, $E$, $K$) &~> #cekE($s$, $E$, $#scopeBodyK (e, |E|) dot.c K$) && "Scope"
$
Val transitions a source value expression ($#True$, $#False$, $n$, $#UnitVal$) into Cont mode. Var looks up the rightmost binding of $x$ in $E$.

The remaining rules decompose a compound form by pushing a continuation frame. BinOp evaluates the left operand first (left-to-right evaluation order). UnOp evaluates its single operand. If evaluates the condition; the branches are expressions, so no scope markers are needed. While records $|E|$ in $#loopK$ for later truncation. Break uses $#popLoopK$ to find the enclosing loop, truncates $E$ to the loop's saved size, and produces $#UnitVal$. Scope records $|E|$ and evaluates the statement body.

==== Cont
$
#cekC($#True$, $E$, $#ifCondK (e_1, e_2) dot.c K$) &~> #cekE($e_1$, $E$, $K$) && "IfTrue" \
#cekC($#False$, $E$, $#ifCondK (e_1, e_2) dot.c K$) &~> #cekE($e_2$, $E$, $K$) && "IfFalse" \
#cekC($v$, $E$, $#declK (x : tau) dot.c K$) &~> #cekC($#Skip$, $E, x := v$, $K$) && "VarDeclDone" \
#cekC($v$, $E$, $#assignK (x) dot.c K$) &~> #cekC($#Skip$, $E[x |-> v]$, $K$) && "AssignDone" \
#cekC($#Skip$, $E$, $#seqK (s_2) dot.c K$) &~> #cekE($s_2$, $E$, $K$) && "SeqDone" \
#cekC($v$, $E$, $#exprStmtK dot.c K$) &~> #cekC($#Skip$, $E$, $K$) && "ExprStmtDone" \
#cekC($v_1$, $E$, $#binopLK (plus.o, e_2) dot.c K$) &~> #cekE($e_2$, $E$, $#binopRK (plus.o, v_1) dot.c K$) && "BinOpL" \
#cekC($v_2$, $E$, $#binopRK (plus.o, v_1) dot.c K$) &~> #cekC($#delta (plus.o, v_1, v_2)$, $E$, $K$) && "BinOpR" \
#cekC($v$, $E$, $#unopK (plus.o) dot.c K$) &~> #cekC($#delta (plus.o, v)$, $E$, $K$) && "UnOpDone" \
#cekC($#True$, $E$, $#loopK (c, e, n) dot.c K$) &~> #cekE($e$, $E$, $#loopContK (c, e, n) dot.c K$) && "LoopTrue" \
#cekC($#False$, $E$, $#loopK (c, e, n) dot.c K$) &~> #cekC($#UnitVal$, $#truncate($E$, $n$)$, $K$) && "LoopFalse" \
#cekC($#UnitVal$, $E$, $#loopContK (c, e, n) dot.c K$) &~> #cekE($c$, $E$, $#loopK (c, e, n) dot.c K$) && "LoopCont" \
#cekC($#Skip$, $E$, $#scopeBodyK (e, n) dot.c K$) &~> #cekE($e$, $E$, $#scopeExitK (n) dot.c K$) && "ScopeBody" \
#cekC($v$, $E$, $#scopeExitK (n) dot.c K$) &~> #cekC($v$, $#truncate($E$, $n$)$, $K$) && "ScopeExit"
$
$E[x |-> v]$ updates the rightmost binding of $x$ in $E$. BinOpL/BinOpR implement left-to-right evaluation of binary operators. IfTrue/IfFalse dispatch directly to the branch expression.

LoopTrue enters the body expression via $#loopContK$. LoopFalse truncates $E$ to the saved size $n$ and produces $#UnitVal$. LoopCont re-evaluates the condition; no truncation is needed since any local variables were cleaned up by inner scope expressions.

ScopeBody loads the trailing expression after the scope's statements complete. ScopeExit truncates $E$ to the saved size $n$, dropping scope-local bindings, and passes the value through.

=== Initial and Terminal States

$
"Initial:" && #cekE($s$, $dot$, $#halt$) && "where" s "is the program" \
"Terminal:" && #cekC($#Skip$, $E$, $#halt$)
$

=== Continuation Typing

We write $#truncate($Gamma$, $n$)$ for the first $n$ bindings of $Gamma$, mirroring $#truncate($E$, $n$)$ on environments. We define well-typedness for continuations with two judgement forms mirroring the machine phases.

==== Expression Continuations

Expression continuations (#typeContE($Gamma$, $K$, $tau$)) _consume_ a value of type $tau$ in context $Gamma$; the overline denotes that $tau$ is in negative position.

#mathpar(
  proof-tree(rule(name: $#IfCondK$, typeContE($Gamma$, $#ifCondK (e_1, e_2) dot.c K$, $#Bool$), typeExpr($Gamma$, $e_1$, $tau$), typeExpr($Gamma$, $e_2$, $tau$), typeContE($Gamma$, $K$, $tau$))),

  proof-tree(rule(name: $#DeclK$, typeContE($Gamma$, $#declK (x : tau) dot.c K$, $tau$), typeContC($Gamma, x : tau$, $K$))),
  proof-tree(rule(name: $#AssignK$, typeContE($Gamma$, $#assignK (x) dot.c K$, $tau$), $Gamma(x) = tau$, typeContC($Gamma$, $K$))),

  proof-tree(rule(name: $#BinOpLK$, typeContE($Gamma$, $#binopLK (plus.o, e_2) dot.c K$, $tau_1$), $plus.o : tau_1 times tau_2 -> tau_3$, typeExpr($Gamma$, $e_2$, $tau_2$), typeContE($Gamma$, $K$, $tau_3$))),
  proof-tree(rule(name: $#BinOpRK$, typeContE($Gamma$, $#binopRK (plus.o, v_1) dot.c K$, $tau_2$), $plus.o : tau_1 times tau_2 -> tau_3$, $tack.r v_1 : tau_1$, typeContE($Gamma$, $K$, $tau_3$))),
  proof-tree(rule(name: $#UnOpK$, typeContE($Gamma$, $#unopK (plus.o) dot.c K$, $tau_1$), $plus.o : tau_1 -> tau_2$, typeContE($Gamma$, $K$, $tau_2$))),

  proof-tree(rule(name: $#LoopK$, typeContE($Gamma$, $#loopK (c, e, n) dot.c K$, $#Bool$), typeExpr($Gamma$, $c$, $#Bool$), typeExpr($Gamma$, $e$, $#Unit$), typeContE($#truncate($Gamma$, $n$)$, $K$, $#Unit$))),
  proof-tree(rule(name: $#LoopContK$, typeContE($Gamma$, $#loopContK (c, e, n) dot.c K$, $#Unit$), typeExpr($Gamma$, $c$, $#Bool$), typeExpr($Gamma$, $e$, $#Unit$), typeContE($#truncate($Gamma$, $n$)$, $K$, $#Unit$))),

  proof-tree(rule(name: $#ScopeExitK$, typeContE($Gamma$, $#scopeExitK (n) dot.c K$, $tau$), typeContE($#truncate($Gamma$, $n$)$, $K$, $tau$))),
  proof-tree(rule(name: $#ExprStmtK$, typeContE($Gamma$, $#exprStmtK dot.c K$, $tau$), typeContC($Gamma$, $K$))),
)

$#IfCondK$ accepts $#Bool$ and types both branches as expressions under $Gamma$.

$#DeclK$ accepts a value of the declared type $tau$.

$#AssignK$ accepts a value matching the variable's type.

For operators, the negative-position type threads through the evaluation chain: $#BinOpLK$ accepts $tau_1$, requires $e_2 : tau_2$, and the tail $K$ must accept $tau_3$. $#BinOpRK$ and $#UnOpK$ are similar.

$#LoopK$ and $#LoopContK$ share the same conditions, but differ in accepted type: $#LoopK$ accepts $#Bool$ (the condition result) while $#LoopContK$ accepts $#Unit$ (the body result).

$#ScopeExitK$ accepts a value of any type $tau$ and requires the tail $K$ to accept $tau$ at the truncated context.

$#ExprStmtK$ accepts any value type and requires the tail $K$ to be a statement continuation at $Gamma$.

==== Statement Continuations

Statement continuations (#typeContC($Gamma$, $K$)) accept $#Skip$ in context $Gamma$.

#mathpar(
  proof-tree(rule(name: $#HaltK$, typeContC($Gamma$, $#halt$))),
  proof-tree(rule(name: $#SeqK$, typeContC($Gamma$, $#seqK (s) dot.c K$), typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma'$, $K$))),
  proof-tree(rule(name: $#ScopeBodyK$, typeContC($Gamma$, $#scopeBodyK (e, n) dot.c K$), typeExpr($Gamma$, $e$, $tau$), typeContE($#truncate($Gamma$, $n$)$, $K$, $tau$))),
)

=== Environment-Context Coherence

We define _coherence_ between an environment and a context, written $#coh($E$, $Gamma$)$, inductively:

#mathpar(
  proof-tree(rule(name: "CohEmp", $#coh($dot$, $dot$)$)),
  proof-tree(rule(name: "CohBind", $#coh($E, x := v$, $Gamma, x : tau$)$, $#coh($E$, $Gamma$)$, $tack.r v : tau$)),
)

==== Well Typed States

A machine state is _well-typed_ when coherence bridges the environment to a context $Gamma$ that types both the control and the continuation:

#mathpar(
  proof-tree(rule(name: "WtExprE", $tack.r #cekE($e$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, typeExpr($Gamma$, $e$, $tau$), typeContE($Gamma$, $K$, $tau$))),
  proof-tree(rule(name: "WtExprS", $tack.r #cekE($s$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma'$, $K$))),
  proof-tree(rule(name: "WtContV", $tack.r #cekC($v$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $tack.r v : tau$, typeContE($Gamma$, $K$, $tau$))),
  proof-tree(rule(name: "WtContS", $tack.r #cekC($#Skip$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, typeContC($Gamma$, $K$))),
)

=== Properties

- *Progress:* if $tack.r S "ok"$ and $S$ is not terminal, then there exists $S'$ such that $S ~> S'$. *Caveat:* this currently requires a well-formedness precondition that $#Break$ appears only inside a $#While$ body. Until this is fixed, part of the $#Break$ case should be left as sorry.

- *Preservation:* if $tack.r S "ok"$ and $S ~> S'$, then $tack.r S' "ok"$.

- *Statement Execution Preserves Coherence:* if $#coh($E$, $Gamma$)$, #typeStmt($Gamma$, $s$, $Gamma'$), and $#cekE($s$, $E$, $K$) #ms #cekC($#Skip$, $E'$, $K$)$, then $#coh($E'$, $Gamma'$)$.

- *Truncation Preserves Coherence:* if $#coh($E$, $Gamma$)$ and $n <= |E|$, then $#coh($#truncate($E$, $n$)$, $#truncate($Gamma$, $n$)$)$. This follows by definition of coherence.

- *Update Preserves Coherence:* if $#coh($E$, $Gamma$)$, $Gamma(x) = tau$, and $tack.r v : tau$, then $#coh($E[x |-> v]$, $Gamma$)$.

- *Expression Evaluation Preserves Environment Size:* if $#coh($E$, $Gamma$)$, #typeExpr($Gamma$, $e$, $tau$), and $#cekE($e$, $E$, $K$) #ms #cekC($v$, $E'$, $K$)$, then $|E'| = |E|$.

- *PopLoopK Preserves Typing:* if $tack.r #cekE($#Break$, $E$, $K$) "ok"$ with $#coh($E$, $Gamma$)$ and $op("popLoopK")(K) = (n, K')$, then #typeContE($#truncate($Gamma$, $n$)$, $K'$, $#Unit$).

- *Determinacy:* each machine state has at most one successor (the transition relation is deterministic). Consequently, if the machine terminates, the terminal state is unique.
