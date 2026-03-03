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
// Continuation typing: Γ ⊢_e K : τ̄ and Γ ⊢_c K
#let typeContE(gin, k, t) = $#gin tack.r_e #k : overline(#t)$
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
  |& #Break && "Loop Break" \
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

  proof-tree(rule(name: "BinOp", typeExpr($Gamma$, $e_1 plus.o e_2$, $tau_3$), typeExpr($Gamma$, $e_1$, $tau_1$), typeExpr($Gamma$, $e_2$, $tau_2$), $plus.o : tau_1 times tau_2 -> tau_3$)),
  proof-tree(rule(name: "UnOp", typeExpr($Gamma$, $plus.o (e)$, $tau_2$), typeExpr($Gamma$, $e$, $tau_1$), $plus.o : tau_1 -> tau_2$)),
)

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

  proof-tree(rule(name: "IfStmt", typeStmt($Gamma$, $#If e #Then s_1 #Else s_2$, $Gamma$), typeExpr($Gamma$, $e$, $#Bool$), typeStmt($Gamma$, $s_1$, $Gamma'$), typeStmt($Gamma$, $s_2$, $Gamma''$))),

  proof-tree(rule(name: "WhileStmt", typeStmt($Gamma$, $#While c brace.l s brace.r$, $Gamma$), typeExpr($Gamma$, $c$, $#Bool$), typeStmt($Gamma$, $s$, $Gamma'$))),

  proof-tree(rule(name: "BreakStmt", typeStmt($Gamma$, $#Break$, $Gamma'$))),
)

Variable declarations check the initialiser expression against the declared type, then extend the context, possibly shadowing an existing binding.

Variable assignment requires that $x : tau$ is present somewhere in the context via membership lookup. The expression $e$ is typed under the same context $Gamma$, which includes $x$; this allows self mutation (such as $x = x + 1$). The output context is unchanged.

Sequencing threads the context produced as the output of the first statement into the input of the second statement.

The while loop checks its condition against $#Bool$ and types the body under $Gamma$. The body may extend the context to $Gamma'$, but the output context of the whole loop is $Gamma$ since the body is scoped per iteration.

The $#Break$ statement has an unconstrained output context $Gamma'$ because it never continues normally — it pops to the enclosing loop boundary. Code following $#Break$ in a sequence is unreachable but still type-checked via Seq threading $Gamma'$.

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

The analogous operation $#popK($K$, $ell$)$ scans the continuation for the first $#jumpK (ell)$ and returns the tail after it:

$
#popK($#jumpK (ell) dot.c K$, $ell$) &= K \
#popK($F dot.c K$, $ell$) &= #popK($K$, $ell$) && quad F != #jumpK (ell)
$

$#popK($#halt$, $ell$)$ is undefined; the type system ensures a matching $#jumpK$ is always present when $#Break$ executes.

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
- $#loopK (c, s)$ serves dual roles: as an expression continuation, it receives the condition value ($#True$ enters the body, $#False$ exits); as a statement continuation, it receives $#Skip$ after the body completes and resets the environment before re-evaluating $c$. The While rule places $#jumpK ("loop")$ after $#loopK$ on the continuation; $#Break$ uses $#popK$ to jump directly to this $#jumpK$, exiting the loop in a single step.

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

  proof-tree(rule(name: "While", $#cekE($#While c brace.l s brace.r$, $E$, $K$) ~> #cekE($c$, $E, #scopeMark($"loop"$)$, $#loopK (c, s) dot.c #jumpK ("loop") dot.c K$)$)),
  proof-tree(rule(name: "Break", $#cekE($#Break$, $E$, $K$) ~> #cekC($#Skip$, $#pop($E$, $"loop"$)$, $#popK($K$, $"loop"$)$)$)),
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

  proof-tree(rule(name: "LoopTrue", $#cekC($#True$, $E$, $#loopK (c, s) dot.c K$) ~> #cekE($s$, $E$, $#loopK (c, s) dot.c K$)$)),
  proof-tree(rule(name: "LoopFalse", $#cekC($#False$, $E$, $#loopK (c, s) dot.c K$) ~> #cekC($#Skip$, $E$, $K$)$)),
  proof-tree(rule(name: "LoopCont", $#cekC($#Skip$, $E$, $#loopK (c, s) dot.c K$) ~> #cekE($c$, $#pop($E$, $"loop"$), #scopeMark($"loop"$)$, $#loopK (c, s) dot.c K$)$)),
)
IfTrue/IfFalse push a scope marker $#scopeMark($"if"$)$ and $#jumpK ("if")$ before entering a branch. ScopeDone pops the environment to the rightmost $#scopeMark($ell$)$. $E[x |-> v]$ updates the rightmost binding of $x$ in $E$. BinOpL/BinOpR implement left-to-right evaluation of binary operators: BinOpL saves the left value and begins the right operand; BinOpR applies $#delta$ to both values. UnOpDone applies $#delta$ to the single operand value. LoopTrue enters the body directly. LoopFalse produces $#Skip$, which reaches $#jumpK ("loop")$ via the existing ScopeDone rule, popping $#scopeMark($"loop"$)$. LoopCont resets the environment between iterations by popping to $#scopeMark($"loop"$)$ and re-pushing it, discarding iteration-local variables while preserving outer mutations. Break pops both the environment and the continuation to the $"loop"$ label in a single step, fully exiting the loop.

The lifecycle of a while loop proceeds as follows. The While rule pushes $#scopeMark($"loop"$)$ onto the environment and places $#loopK (c, s) dot.c #jumpK ("loop")$ on the continuation, then evaluates the condition $c$. If the condition is $#False$, LoopFalse produces $#Skip$; this reaches $#jumpK ("loop")$ and ScopeDone pops $#scopeMark($"loop"$)$, cleaning up the loop scope. If the condition is $#True$, LoopTrue enters the body $s$ directly. Variables declared in the body accumulate in $E$ during the iteration. When the body completes with $#Skip$, LoopCont fires: it pops $E$ to $#scopeMark($"loop"$)$ (discarding iteration-local bindings) and re-pushes $#scopeMark($"loop"$)$ to begin the next iteration, then re-evaluates $c$. If $#Break$ is executed inside the body, it pops $E$ to $#scopeMark($"loop"$)$ via $#pop$ and pops $K$ to $#jumpK ("loop")$ via $#popK$, producing $#Skip$ in a clean state — the loop is fully exited in a single transition. For nested loops, $#pop$ finds the rightmost (innermost) $#scopeMark($"loop"$)$ and $#popK$ finds the topmost (innermost) $#jumpK ("loop")$, so $#Break$ exits the innermost enclosing loop.

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

We define well-typedness for continuations with two judgement forms mirroring the machine phases. _Expression continuations_ (#typeContE($Gamma$, $K$, $tau$)) accept a value of type $tau$ in context $Gamma$. The overline on $overline(tau)$ indicates the type is in negative position — consumed by the continuation, not produced. _Statement continuations_ (#typeContC($Gamma$, $K$)) accept $#Skip$ in context $Gamma$.

==== Expression Continuations

#mathpar(
  proof-tree(rule(name: "IfCondK", typeContE($Gamma$, $#ifCondK (s_1, s_2) dot.c K$, $#Bool$), typeStmt($Gamma, #scopeMark($"if"$)$, $s_1$, $Gamma'$), typeStmt($Gamma, #scopeMark($"if"$)$, $s_2$, $Gamma''$), typeContC($Gamma$, $K$))),
  proof-tree(rule(name: "DeclK", typeContE($Gamma$, $#declK (x : tau) dot.c K$, $tau$), typeContC($Gamma, x : tau$, $K$))),
  proof-tree(rule(name: "AssignK", typeContE($Gamma$, $#assignK (x) dot.c K$, $tau$), $Gamma(x) = tau$, typeContC($Gamma$, $K$))),

  proof-tree(rule(name: "BinOpLK", typeContE($Gamma$, $#binopLK (plus.o, e_2) dot.c K$, $tau_1$), $plus.o : tau_1 times tau_2 -> tau_3$, typeExpr($Gamma$, $e_2$, $tau_2$), typeContE($Gamma$, $K$, $tau_3$))),
  proof-tree(rule(name: "BinOpRK", typeContE($Gamma$, $#binopRK (plus.o, v_1) dot.c K$, $tau_2$), $plus.o : tau_1 times tau_2 -> tau_3$, $tack.r v_1 : tau_1$, typeContE($Gamma$, $K$, $tau_3$))),
  proof-tree(rule(name: "UnOpK", typeContE($Gamma$, $#unopK (plus.o) dot.c K$, $tau_1$), $plus.o : tau_1 -> tau_2$, typeContE($Gamma$, $K$, $tau_2$))),
  proof-tree(rule(name: "LoopEK", typeContE($Gamma$, $#loopK (c, s) dot.c K$, $#Bool$), typeExpr($Gamma$, $c$, $#Bool$), typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma$, $K$))),
)

IfCondK accepts $#Bool$ (the condition) and types both branches under $Gamma, #scopeMark($"if"$)$. DeclK accepts a value of the declared type $tau$. AssignK accepts a value matching the variable's type. For operators, the negative-position type threads through the evaluation chain: BinOpLK accepts $tau_1$ (the left operand type), requires $e_2 : tau_2$, and the tail $K$ must accept $tau_3$ (the result type). BinOpRK accepts $tau_2$ (the right operand type), checks $v_1 : tau_1$, and again the tail accepts $tau_3$. UnOpK accepts $tau_1$ and the tail accepts $tau_2$ per the unary signature $plus.o : tau_1 -> tau_2$. LoopEK accepts $#Bool$ (the condition); the tail $K$ uses #typeContC because the loop ultimately produces $#Skip$.

==== Statement Continuations

#mathpar(
  proof-tree(rule(name: "HaltK", typeContC($Gamma$, $#halt$))),
  proof-tree(rule(name: "JumpK", typeContC($Gamma$, $#jumpK (ell) dot.c K$), typeContC($#drop($Gamma$, $ell$)$, $K$))),
  proof-tree(rule(name: "SeqK", typeContC($Gamma$, $#seqK (s) dot.c K$), typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma'$, $K$))),
  proof-tree(rule(name: "LoopK", typeContC($Gamma$, $#loopK (c, s) dot.c K$), typeExpr($Gamma$, $c$, $#Bool$), typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma$, $K$))),
)

JumpK uses $#drop($Gamma$, $ell$)$ to strip the context to the matching scope marker, mirroring $#pop($E$, $ell$)$ on environments. The tail $K$ is typed at the resulting outer context. LoopK checks the condition and body under $Gamma$; the tail $K$ is typed at $Gamma$ since the loop preserves the context.

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
  proof-tree(rule(name: "WtExprE", $tack.r #cekE($e$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, typeExpr($Gamma$, $e$, $tau$), typeContE($Gamma$, $K$, $tau$))),
  proof-tree(rule(name: "WtExprS", $tack.r #cekE($s$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, typeStmt($Gamma$, $s$, $Gamma'$), typeContC($Gamma'$, $K$))),
  proof-tree(rule(name: "WtContV", $tack.r #cekC($v$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $tack.r v : tau$, typeContE($Gamma$, $K$, $tau$))),
  proof-tree(rule(name: "WtContS", $tack.r #cekC($#Skip$, $E$, $K$) "ok"$, $#coh($E$, $Gamma$)$, typeContC($Gamma$, $K$))),
)

=== Properties

- *Progress:* if $tack.r S "ok"$ and $S$ is not terminal, then there exists $S'$ such that $S ~> S'$.

- *Preservation:* if $tack.r S "ok"$ and $S ~> S'$, then $tack.r S' "ok"$.

- *Statement Execution Preserves Coherence:* if $#coh($E$, $Gamma$)$, #typeStmt($Gamma$, $s$, $Gamma'$), and $#cekE($s$, $E$, $K$) #ms #cekC($#Skip$, $E'$, $K$)$, then $#coh($E'$, $Gamma'$)$.

- *Pop/Drop Preserves Coherence:* if $#coh($E$, $Gamma$)$, then $#coh($#pop($E$, $ell$)$, $#drop($Gamma$, $ell$)$)$.

- *PopK/Drop Preserves Continuation Typing:* if #typeContC($Gamma$, $K$) and $K$ contains $#jumpK (ell)$, then #typeContC($#drop($Gamma$, $ell$)$, $#popK($K$, $ell$)$). Analogous to Pop/Drop Preserves Coherence but for continuations.

- *Determinacy:* each machine state has at most one successor (the transition relation is deterministic). Consequently, if the machine terminates, the terminal state is unique.
