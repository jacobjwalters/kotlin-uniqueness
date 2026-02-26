#import "../defs.typ": *

// Local definitions for simplified judgement forms (override defs.typ)
// Expression typing: Γ ⊢ e : τ (no heap Δ, no return type σ, no output context)
#let typeExpr(gin, e, t) = $#gin tack.r #e : #t$
// Statement typing: Γ ⊢ s ⊣ Γ' (no heap Δ, no return type σ)
#let typeStmt(gin, s, gout) = $#gin tack.r #s tack.l #gout$
// CEK machine state: ⟨C | E | K⟩ (no store S)
#let cek(c, e, k) = $chevron.l #c | #e | #k chevron.r$
// Local continuation frame for variable declaration
#let declK = math.op("declK")

= #Lbase

#Lbase is a simple typed language consisting of sequentially ordered statements with conditionals. There are no classes, methods, modes, or lambdas.

== Syntax

$
tau ::=& #Nat && "Naturals" \
  |& #Bool && "Booleans" \
e ::=& x && "Variable Access" \
  |& #True \
  |& #False \
  |& n in bb(N) && "Natural Numbers" \
s ::=& #Var x : tau = e && "(Mutable) Variable Declaration" \
  |& x = e && "Variable Assignment/Mutation" \
  |& s_1; s_2 && "Statement Sequencing" \
  |& #If e #Then s_1 #Else s_2 && "If/Then/Else" \
$

A program $P$ is a statement $s$. $x$ represents an infinite set of variable names.

We assume usual boolean/arithmetic operators are defined as primitive expressions.

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
)

=== Statement Types
Since statements may update their context, we use a "small-step" typing judgement form #typeStmt($Gamma$, $s$, $Gamma'$), where $Gamma$ represents the context before the statement runs and $Gamma'$ represents the context after.

#mathpar(
  proof-tree(rule(name: "VarDecl", typeStmt($Gamma$, $#Var x : tau = e$, $Gamma, x : tau$), typeExpr($Gamma$, $e$, $tau$))),
  proof-tree(rule(name: "VarAssign", typeStmt($Gamma$, $x = e$, $Gamma$), $Gamma(x) = tau$, typeExpr($Gamma$, $e$, $tau$))),

  proof-tree(rule(name: "Seq", typeStmt($Gamma$, $s_1; s_2$, $Gamma''$), typeStmt($Gamma$, $s_1$, $Gamma'$), typeStmt($Gamma'$, $s_2$, $Gamma''$))),

  proof-tree(rule(name: "IfStmt", typeStmt($Gamma$, $#If e #Then s_1 #Else s_2$, $Gamma$), typeExpr($Gamma$, $e$, $#Bool$), typeStmt($Gamma$, $s_1$, $Gamma'$), typeStmt($Gamma$, $s_2$, $Gamma''$))),
)

Variable declarations check the initialiser expression against the declared type, then extend the context, possibly shadowing an existing binding.

Variable assignment requires that $x : tau$ is present somewhere in the context via membership lookup. The expression $e$ is typed under the same context $Gamma$, which includes $x$; this allows self mutation (such as $x = x + 1$). The output context is unchanged.

Sequencing threads the context produced as the output of the first statement into the input of the second statement.

=== Properties

- *Output Context Determinacy:* if #typeStmt($Gamma$, $s$, $Gamma_1$) and #typeStmt($Gamma$, $s$, $Gamma_2$), then $Gamma_1 = Gamma_2$.

- *Expression Weakening (Extension):* if #typeExpr($Gamma$, $e$, $tau$) and $Gamma$ is a prefix of $Gamma'$, then #typeExpr($Gamma'$, $e$, $tau$).

- *Expression Weakening (Permutation):* if #typeExpr($Gamma$, $e$, $tau$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeExpr($Gamma'$, $e$, $tau$).

- *Statement Weakening (Extension):* if #typeStmt($Gamma$, $s$, $Gamma, Delta$) and $Gamma$ is a prefix of $Gamma'$, then #typeStmt($Gamma'$, $s$, $Gamma', Delta$).

- *Statement Weakening (Permutation):* if #typeStmt($Gamma$, $s$, $Gamma, Delta$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeStmt($Gamma'$, $s$, $Gamma', Delta$).

Note that in the statement weakening properties, $Gamma, Delta$ refers to $Gamma$ concatenated with another context $Delta$; $Delta$ is *not* a heap. We can't extend by a single variable as in the expression weakening rules since compound statements may extend $Gamma$ with any number of new variables.

== Evaluation
Evaluation of an #Lbase program begins with a program statement $s$. We define the operational semantics as a CEK machine; a state machine that makes evaluation order explicit via a continuation stack. We also introduce a run-time language.

=== Run-time Language
The CEK machine operates on a run-time language that extends the source syntax with run-time-only forms. This language is a strict extension of the source language; it has one additional syntactic construct, with a corresponding typing rule. We should show all of the properties of the source langauge's type system hold for the run-time language's type system.

==== Values
Values are fully evaluated expressions:

$
v ::=& #True |& #False |& n in bb(N)
$

==== Completion Marker
$#Skip$ is a run-time-only completion marker indicating that a statement has been fully executed. It does not appear in the source program. Since $#Skip$ can appear in the control during evaluation, it needs a typing rule:

#mathpar(
  proof-tree(rule(name: "Skip", typeStmt($Gamma$, $#Skip$, $Gamma$))),
)

$#Skip$ preserves the context unchanged.

=== Machine State
The machine state is a 3-tuple $#cek($C$, $E$, $K$)$:

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

The environment is an ordered, rightwards-growing list of variable-to-value bindings. Lookup finds the rightmost binding for a given variable name (permitting shadowing). Update ($E[x |-> v]$) modifies the rightmost binding of $x$ in place.

The environment is extended when variables are declared ($#Var x : tau = e$ adds $x := v$ to the rightmost position, where $v$ is the value of $e$) and individual bindings are updated on assignment ($x = v$ updates the rightmost $x$). We write $|E|$ for the number of bindings in $E$, and $#trunc($E$, $n$)$ for $E$ truncated to its first $n$ bindings.

==== Continuation ($K$)
The continuation is a stack of frames that describes what to do after the current control finishes:

$
K ::=& #halt && "Program complete" \
  |& #ifCondK (s_1, s_2) dot.c K && "After evaluating condition, branch" \
  |& #ifDoneK (n) dot.c K && "After branch completes, truncate" E "to" n "bindings" \
  |& #declK (x) dot.c K && "After evaluating initialiser, bind" x "in" E \
  |& #assignK (x) dot.c K && "After evaluating RHS, assign to" x "in" E \
  |& #seqK (s) dot.c K && "After first statement completes, continue with" s
$

- $#halt$ signals that the program is finished; a terminal state is $#cek($#Skip$, $E$, $#halt$)$.
- $#ifCondK (s_1, s_2)$ waits for the condition expression to evaluate to a value, then dispatches to the appropriate branch.
- $#ifDoneK (n)$ waits for the chosen branch to complete, then truncates the environment to its first $n$ bindings, dropping branch-local declarations while preserving mutations to outer-scope variables.
- $#declK (x)$ waits for the initialiser expression to evaluate to a value $v$, then extends the environment with $x := v$.
- $#assignK (x)$ waits for the RHS expression to evaluate to a value $v$, then updates the environment with $E[x |-> v]$.
- $#seqK (s)$ waits for the first statement to complete, then loads $s$ into the control.

=== Transition Rules
Our transition judgement is $#cek($C$, $E$, $K$) ~> #cek($C'$, $E'$, $K'$)$. We define a multi-step judgement $ms$ in the usual way.

==== Variable Access
#mathpar(
  proof-tree(rule(name: "Var", $#cek($x$, $E$, $K$) ~> #cek($E(x)$, $E$, $K$)$)),
)
Look up the rightmost binding of $x$ in $E$.

==== If Statement
#mathpar(
  proof-tree(rule(name: "If", $#cek($#If e #Then s_1 #Else s_2$, $E$, $K$) ~> #cek($e$, $E$, $#ifCondK (s_1, s_2) dot.c K$)$)),
  proof-tree(rule(name: "IfTrue", $#cek($#True$, $E$, $#ifCondK (s_1, s_2) dot.c K$) ~> #cek($s_1$, $E$, $#ifDoneK (|E|) dot.c K$)$)),
  proof-tree(rule(name: "IfFalse", $#cek($#False$, $E$, $#ifCondK (s_1, s_2) dot.c K$) ~> #cek($s_2$, $E$, $#ifDoneK (|E|) dot.c K$)$)),
)

When a branch completes, the environment is truncated to its pre-branch scope depth, dropping branch-local declarations while preserving mutations to existing variables:
#mathpar(
  proof-tree(rule(name: "IfDone", $#cek($#Skip$, $E$, $#ifDoneK (n) dot.c K$) ~> #cek($#Skip$, $#trunc($E$, $n$)$, $K$)$)),
)
This ensures branch-local declarations are truly local at run-time, while mutations to outer-scope variables remain visible, matching the typing discipline.

==== Variable Declaration
#mathpar(
  proof-tree(rule(name: "VarDecl", $#cek($#Var x : tau = e$, $E$, $K$) ~> #cek($e$, $E$, $#declK (x) dot.c K$)$)),
  proof-tree(rule(name: "VarDeclDone", $#cek($v$, $E$, $#declK (x) dot.c K$) ~> #cek($#Skip$, $E, x := v$, $K$)$)),
)
Evaluates the initialiser $e$ to a value $v$, then extends $E$ with $x := v$.

==== Variable Assignment
#mathpar(
  proof-tree(rule(name: "Assign", $#cek($x = e$, $E$, $K$) ~> #cek($e$, $E$, $#assignK (x) dot.c K$)$)),
  proof-tree(rule(name: "AssignDone", $#cek($v$, $E$, $#assignK (x) dot.c K$) ~> #cek($#Skip$, $E[x |-> v]$, $K$)$)),
)
$E[x |-> v]$ updates the rightmost binding of $x$ in $E$.

==== Sequencing
#mathpar(
  proof-tree(rule(name: "Seq", $#cek($s_1 ; s_2$, $E$, $K$) ~> #cek($s_1$, $E$, $#seqK (s_2) dot.c K$)$)),
  proof-tree(rule(name: "SeqDone", $#cek($#Skip$, $E$, $#seqK (s_2) dot.c K$) ~> #cek($s_2$, $E$, $K$)$)),
)

=== Initial and Terminal States

$
"Initial:" && #cek($s$, $dot$, $#halt$) && "where" s "is the program" \
"Terminal:" && #cek($#Skip$, $E$, $#halt$)
$

=== Properties

We say $E$ _models_ $Gamma$ when $E$ and $Gamma$ bind the same variables in the same order and for all $x in op("dom")(Gamma)$, $tack.r E(x) : Gamma(x)$.

Given a well-typed program $s$ and a state $#cek($C$, $E$, $K$)$ reachable from the initial state over $s$:

- *Progress:* either the state is terminal, or there exists a state $#cek($C'$, $E'$, $K'$)$ such that $#cek($C$, $E$, $K$) ~> #cek($C'$, $E'$, $K'$)$.

- *Preservation:* if the state is well-typed and can step, the resulting state is also well-typed (with the same type).

- *Statement Execution Preserves Modelling:* if $E$ models $Gamma$, #typeStmt($Gamma$, $s$, $Gamma'$), and $#cek($s$, $E$, $K$) #ms #cek($#Skip$, $E'$, $K$)$, then $E'$ models $Gamma'$.

- *Value Type Correctness:* if $E$ models $Gamma$ and $Gamma(x) = tau$, then $tack.r E(x) : tau$. (Immediate from the definition of modelling.)

- *Truncation Preserves Modelling:* if $E$ models $Gamma'$ where $Gamma$ is a prefix of $Gamma'$ and $n = |Gamma|$, then $#trunc($E$, $n$)$ models $Gamma$.

- *Strong Normalisation:* the machine starting at $#cek($s$, $dot$, $#halt$)$ reaches a terminal state in finitely many steps.

- *Determinacy of Normalisation:* the terminal state is unique: if $#cek($s$, $dot$, $#halt$) #ms #cek($#Skip$, $E_1$, $#halt$)$ and $#cek($s$, $dot$, $#halt$) #ms #cek($#Skip$, $E_2$, $#halt$)$, then $E_1 = E_2$.
