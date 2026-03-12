#import "../defs.typ": *

// Lclass uses the σ-annotated judgement forms
#let typeExpr = typeExprSig
#let typeStmt = typeStmtSig

= #Lclass

#Lclass is a simple typed language consisting of sequentially ordered statements with classes and method calls. There are no modes, and no lambdas.

== Syntax

$
P ::=& C^* times M^* && "Programs" \
C ::=& #Class C(f_i : tau_i) && "Classes" \
M ::=& m(x_i : tau_i) : sigma { s } && "Method Definitions" \
tau, sigma ::=& #Nat && "Naturals" \
  |& #Bool && "Booleans" \
  |& C && "Class Types" \
p ::=& x && "Variable Access" \
  |& p.f && "Subfield Access" \
e ::=& p && "Path Access" \
  |& #True \
  |& #False \
  |& n in bb(N) && "Natural Numbers" \
  |& #New C(e_1, ..., e_n) && "Object Construction" \
  |& #Return e && "(Early) Return" \
s ::=& #Var x : tau = e && "(Mutable) Variable Declaration" \
  |& x = e && "Variable Assignment/Mutation" \
  |& s_1; s_2 && "Statement Sequencing" \
  |& m(e_i) && "Method Call" \
  |& #If e #Then s_1 #Else s_2 && "If/Then/Else" \
  |& #While c brace.l s brace.r && "While Loop" \
  |& #Break && "Loop Break" \
$

$f$, $x$, and $m$ represent infinite and non-intersecting sets of field, variable, and method names respectively. Methods are all defined top-level, and may be (mutually) recursive.

Non-forgetful differences from the system described by @protopapa2024VerifyingKotlinCode are:
- Our system is typed (and has #Nat and #Bool as ground types).
- ITE tests an arbitrary boolean expression, rather than direct equality on patterns.

We assume usual boolean/arithmetic operators are defined as method call expressions.

== Typing Contexts
Typing contexts (hereafter contexts) in #Lclass are ordered, rightwards-growing lists of names and their associated types. In particular, we have a (global) list of methods and associated method types#footnote[Since we don't have object-level function types, a method type is a list of argument types, paired with a return type, writ $m : (tau_1, tau_2, ...): sigma$], paired with a list of variable names and their associated types.

Since method declarations are top level, we omit them from our treatment of contexts, and assume that the expression/statement theories are parameterised by a particular context of methods and method types. Methods are typed in empty contexts; the current return type is tracked as part of the statement typing judgement.

The grammar for contexts is as follows:

$
Gamma ::=& dot && "Empty" \
  |& Gamma, x : tau && "Variable Extension"
$

Lookup ($Gamma(x) = tau$) returns the type of $x$ in $Gamma$.

=== Well Formed Contexts
We introduce a judgement $Gamma #ctx$ to denote well formed contexts (WFCs). WFCs are defined inductively:

#mathpar(
  proof-tree(rule(name: "CtxEmp", $dot #ctx$)),
  proof-tree(rule(name: "CtxVarExt", $Gamma, x : tau #ctx$, $x in.not Gamma$, $Gamma #ctx$))
)

$x in.not Gamma$ is bookkeeping for ensuring all names are distinct, and isn't strictly needed. Membership checking and lookup are defined in the usual way.

== Type System
Herein we discuss the type system of #Lclass. Mostly it's a straightforward approach; the interesting parts surround control flow and calling methods.

The approach to type checking begins by adding all method declarations to a (global) context of methods, thereby assuming that method type declarations are always correct. Once this pass is done, the body of each method (if given) is checked according to the statement rules.

=== Expression Types
Since expressions may affect their context (via returns), we use the judgement form #typeExpr($Gamma$, $sigma$, $e$, $tau$, $Gamma'$), where $sigma$ is the current method's return type. For most expressions, the output context is identical to the input; $#Return$ is the exception, setting the output context to $dot$.

#mathpar(
  proof-tree(rule(name: "TrueConst", typeExpr($Gamma$, $sigma$, $#True$, $#Bool$, $Gamma$))),
  proof-tree(rule(name: "FalseConst", typeExpr($Gamma$, $sigma$, $#False$, $#Bool$, $Gamma$))),
  proof-tree(rule(name: "NatConst", typeExpr($Gamma$, $sigma$, $n$, $#Nat$, $Gamma$), $n in bb(N)$)),

  proof-tree(rule(name: "VarAccess", typeExpr($Gamma$, $sigma$, $x$, $tau$, $Gamma$), $Gamma(x) = tau$)),

  proof-tree(rule(name: "FieldAccess", typeExpr($Gamma$, $sigma$, $p.f$, $tau$, $Gamma$), typeExpr($Gamma$, $sigma$, $p$, $C$, $Gamma$), $f : tau in #fields (C)$)),

  proof-tree(rule(name: "New", typeExpr($Gamma$, $sigma$, $#New C(e_1, ..., e_n)$, $C$, $Gamma$), $#fields (C) = (f_1 : tau_1, ..., f_n : tau_n)$, typeExpr($Gamma$, $sigma$, $e_i$, $tau_i$, $Gamma$))),

  proof-tree(rule(name: "Return", typeExpr($Gamma$, $sigma$, $#Return e$, $tau$, $dot$), typeExpr($Gamma$, $sigma$, $e$, $sigma$, $Gamma$))),
)

$#New C(e_1, ..., e_n)$ checks each field initialiser $e_i$ against the declared field type $tau_i$; all must be pure (output context equals input). The expression has type $C$. $#Return$ has type $tau$ for any $tau$ since it never produces a value to its enclosing expression context.

=== Statement Types
Since statements may update their context, we use a "small-step" typing judgement form #typeStmt($Gamma$, $sigma$, $s$, $Gamma'$), where $Gamma$ represents the context before the statement runs, $Gamma'$ represents the context after the statement runs, and $sigma$ is the current method's return type.

#mathpar(
  proof-tree(rule(name: "VarDecl", typeStmt($Gamma$, $sigma$, $#Var x : tau = e$, $Gamma, x : tau$), typeExpr($Gamma$, $sigma$, $e$, $tau$, $Gamma$))),
  proof-tree(rule(name: "VarAssign", typeStmt($Gamma$, $sigma$, $x = e$, $Gamma'$), $Gamma(x) = tau$, typeExpr($Gamma$, $sigma$, $e$, $tau$, $Gamma'$))),

  proof-tree(rule(name: "Seq", typeStmt($Gamma$, $sigma$, $s_1; s_2$, $Gamma''$), typeStmt($Gamma$, $sigma$, $s_1$, $Gamma'$), typeStmt($Gamma'$, $sigma$, $s_2$, $Gamma''$))),

  proof-tree(rule(name: "CallStmt", typeStmt($Gamma$, $sigma$, $m(e_1, e_2, ...)$, $Gamma$), $m : (tau_1, tau_2, ...): \_$, typeExpr($Gamma$, $sigma$, $e_i$, $tau_i$, $Gamma$))),

  proof-tree(rule(name: "IfStmt", typeStmt($Gamma$, $sigma$, $#If e #Then s_1 #Else s_2$, $Gamma$), typeExpr($Gamma$, $sigma$, $e$, $#Bool$, $Gamma$), typeStmt($Gamma$, $sigma$, $s_1$, $Gamma'$), typeStmt($Gamma$, $sigma$, $s_2$, $Gamma''$))),

  proof-tree(rule(name: "WhileLoop", typeStmt($Gamma$, $sigma$, $#While c brace.l s brace.r$, $Gamma$), typeExpr($Gamma$, $sigma$, $c$, $#Bool$, $Gamma$), typeStmt($Gamma$, $sigma$, $s$, $Gamma'$))),

  proof-tree(rule(name: "BreakStmt", typeStmt($Gamma$, $sigma$, $#Break$, $Gamma'$))),
)

Variable declarations check the initialiser expression against the declared type, then extend the context.

Variable assignment requires that the variable we're assigning to is available in the context. The output context is determined by the expression: if $e$ is a simple expression, the context is preserved; if $e$ contains a return, the context drops to $dot$. Note that $e$ has access to $x$ in its context; this allows self mutation (such as $x = x + 1$).

Sequencing threads the context produced as the output of the first statement into the input of the second statement.

Method call statements have no effect on the context at compile time, so we merely have to check the argument types.

The while loop checks its condition against $#Bool$ and types the body under $Gamma$. The body may extend the context to $Gamma'$, but the output context of the whole loop is $Gamma$ since the body is scoped per iteration.

The $#Break$ statement has an unconstrained output context $Gamma'$ because it never continues normally — it pops to the enclosing loop boundary. Code following $#Break$ in a sequence is unreachable but still type-checked via Seq threading $Gamma'$.

#v(1em)

Consider carefully a method with the body $#Return 0 ; #Return 1$. We obviously shouldn't allow $#Return 1$ to execute in the parent call frame; in fact, it shouldn't execute at all, and should be seen as unreachable code.

=== Method Bodies
We introduce a final typing judgement $tack.r m(x_i : tau_i): sigma { s }$ to ascribe types for method definitions.

#mathpar(
  proof-tree(rule(name: "Method", $tack.r m(x_i : tau_i): sigma { s }$, typeStmt($x_i : tau_i$, $sigma$, $s$, $dot$)))
)

Since methods are typed in empty contexts, the body is checked with only the arguments in scope and the return type $sigma$ annotating the judgement. The output context must be $dot$, forcing all arguments and local definitions to be dropped, which in turn means that we can only exit a method via an explicit return statement.

=== Properties

- *Output Context Determinacy:* if #typeStmt($Gamma$, $sigma$, $s$, $Gamma_1$) and #typeStmt($Gamma$, $sigma$, $s$, $Gamma_2$), then $Gamma_1 = Gamma_2$, provided $s$ does not contain $#Break$ at a position where its output context is unconstrained. The output context of $#Break$ is chosen freely to allow typing of unreachable code in sequences.

- *Expression Weakening (Extension):* if #typeExpr($Gamma$, $sigma$, $e$, $tau$, $Gamma$) and $Gamma$ is a suffix of $Gamma'$, then #typeExpr($Gamma'$, $sigma$, $e$, $tau$, $Gamma'$).

- *Expression Weakening (Permutation):* if #typeExpr($Gamma$, $sigma$, $e$, $tau$, $Gamma$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeExpr($Gamma'$, $sigma$, $e$, $tau$, $Gamma'$).

- *Statement Weakening (Extension):* if #typeStmt($Gamma$, $sigma$, $s$, $Gamma, Delta$) and $Gamma$ is a suffix of $Gamma'$, then #typeStmt($Gamma'$, $sigma$, $s$, $Gamma', Delta$).

- *Statement Weakening (Permutation):* if #typeStmt($Gamma$, $sigma$, $s$, $Gamma, Delta$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeStmt($Gamma'$, $sigma$, $s$, $Gamma', Delta$).

Note that in the statement weakening properties, $Gamma, Delta$ refers to $Gamma$ concatenated with another context $Delta$; $Delta$ is *not* a heap. We can't extend by a single variable as in the expression weakening rules since compound statements may extend $Gamma$ with any number of new variables.

Note that we don't have strong normalisation, even for expressions; a method is able to call itself in an infinite loop.


// Local: two-phase CESK machine states
#let ceskE(c, e, s, k) = $chevron.l #c | #e | #s | #k chevron.r_e$
#let ceskC(c, e, s, k) = $chevron.l #c | #e | #s | #k chevron.r_c$
// Drop operation on contexts: drop(Γ, ℓ)
#let drop(g, l) = $op("drop") (#g, #l)$
// Coherence: E ~ Γ
#let coh(e, g) = $#e tilde #g$
// Continuation typing: Γ ⊢_e K : τ̄ and Γ ⊢_c K
#let typeContE(gin, k, t) = $#gin tack.r_e #k : overline(#t)$
#let typeContC(gin, k) = $#gin tack.r_c #k$

== Evaluation
Evaluation of an #Lclass program begins with a pre-specified method name. For the rest of this document, we'll use "main". We define the operational semantics as a two-phase CESK machine; a state machine that makes evaluation order explicit via a continuation stack. We also introduce a run-time language, which extends the source language with syntactic forms for address values and a completion marker.

=== Runtime Language
The CESK machine operates on a runtime language that extends the source syntax with runtime-only forms.

==== Values
Values are fully evaluated expressions. The source values $#True$, $#False$, and $n in bb(N)$ are joined by runtime-only addresses:

$
v ::=& a in cal(A) |& #True |& #False |& n in bb(N)
$

Addresses $a in cal(A)$ are opaque references to objects in the store. They do not appear in the source program; they arise only during execution when objects are allocated.

We write $tack.r v : tau$ for value typing: $tack.r #True : #Bool$, $tack.r #False : #Bool$, $tack.r n : #Nat$ for $n in bb(N)$, and $tack.r a : C$ when $S(a) = C(...)$ (the address points to an object of class $C$ in the store).

==== Completion Marker
$#Skip$ is a run-time-only completion marker indicating that a statement has been fully executed. It does not appear in the source program. Since $#Skip$ can appear in the control during evaluation, it needs a typing rule:

#mathpar(
  proof-tree(rule(name: "Skip", typeStmt($Gamma$, $sigma$, $#Skip$, $Gamma$))),
)

$#Skip$ preserves the context unchanged.

=== Machine State
The machine state is a 4-tuple $#cesk($C$, $E$, $S$, $K$)$. The machine operates in one of two phases, indicated by a subscript on the state. In _Expr_ mode ($#ceskE($C$, $E$, $S$, $K$)$), the control holds a source expression or statement to be decomposed. In _Cont_ mode ($#ceskC($C$, $E$, $S$, $K$)$), the control holds a value or completion marker and the machine dispatches on the continuation.

#table(
  columns: (auto, auto, 1fr),
  align: (center, left, left),
  table.header([*Component*], [*Name*], [*Description*]),
  [$C$], [Control], [The current expression, statement, value, or completion marker being processed],
  [$E$], [Environment], [Ordered map from variables to values, with scope markers],
  [$S$], [Store], [Unordered map from addresses to objects],
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

The operation $#popCallK($K$)$ scans the continuation for the first $#callK (E')$ and returns the saved environment and the tail:

$
#popCallK($#callK (E) dot.c K$) &= (E, K) \
#popCallK($F dot.c K$) &= #popCallK($K$) && quad F != #callK (...)
$

$#popCallK($#halt$)$ is undefined; the type system ensures $#returnK$ is only reachable inside a method body.

The environment is saved and restored across method calls: $#callK (E)$ preserves the caller's environment on the continuation, and restores it when the method returns (either explicitly via $#returnK$ and $#popCallK$, or implicitly when the body completes with $#Skip$).

The scope markers $#scopeMark($ell$)$ are notational devices for delineating scopes within a flat list. A formalisation may prefer to represent environments explicitly as a stack of frames (i.e. a list of lists), where push/pop correspond to cons/uncons on the outer list.

==== Store ($S$)
$
S ::=& dot && "Empty" \
  |& S, a -> C(... f_i := v_i ...) && "Object mapping"
$

The store maps addresses to objects. An object $C(... f_i := v_i ...)$ records its class $C$ and the values of its fields. A store is _well-typed_ when, for every $a -> C(... f_i := v_i ...)$ in $S$, each field value has its declared type: $tack.r v_i : tau_i$ where $f_i : tau_i in #fields (C)$.

==== Continuation ($K$)
The continuation is a stack of frames that describes what to do after the current control finishes:

$
K ::=& #halt && "Program complete" \
  |& #fieldK (f) dot.c K && "After evaluating path, look up field" f \
  |& #ifCondK (s_1, s_2) dot.c K && "After evaluating condition, branch" \
  |& #jumpK (ell) dot.c K && "After scoped block completes, pop to" #scopeMark($ell$) \
  |& #declK (x : tau) dot.c K && "After evaluating initialiser of type" tau ", bind" x "in" E \
  |& #returnK dot.c K && "After evaluating return expr, jump to most recent" #callK \
  |& #assignK (x) dot.c K && "After evaluating RHS, assign to" x "in" E \
  |& #seqK (s) dot.c K && "After first statement completes, continue with" s \
  |& #loopK (c, s) dot.c K && "After evaluating while condition, dispatch or re-enter" \
  |& #argK (m, overline(v), overline(e)) dot.c K && "Evaluating args: method, done, remaining" \
  |& #newK (C, overline(v), overline(e)) dot.c K && "Evaluating field initialisers: class" C", done, remaining" \
  |& #callK (E) dot.c K && "Call boundary: saved caller environment" E
$

Method bodies are tracked globally when defined. We define a function $#body (m)$, which returns the body of a method, and a function $#args (m)$, which returns the argument names taken by a method.

- $#halt$ signals that the program is finished; a terminal state is $#ceskC($#Skip$, $E$, $S$, $#halt$)$.
- $#ifCondK (s_1, s_2)$ waits for the condition expression to evaluate to a value, then dispatches to the appropriate branch.
- $#jumpK (ell)$ waits for a scoped block to complete, then pops the environment to the rightmost $#scopeMark($ell$)$, dropping scope-local declarations while preserving mutations to outer-scope variables.
- $#declK (x : tau)$ waits for the initialiser expression to evaluate to a value $v$ of type $tau$, then extends the environment with $x := v$.
- $#returnK$ waits for the return expression to evaluate to a value, then uses $#popCallK$ to jump directly to the most recent $#callK$, restoring the caller's environment and producing $#Skip$.
- $#assignK (x)$ waits for the RHS expression to evaluate to a value $v$, then updates the environment with $E[x |-> v]$.
- $#seqK (s)$ waits for the first statement to complete, then loads $s$ into the control.
- $#loopK (c, s)$ serves dual roles: as an expression continuation, it receives the condition value ($#True$ enters the body, $#False$ exits); as a statement continuation, it receives $#Skip$ after the body completes and resets the environment before re-evaluating $c$. The While rule places $#jumpK ("loop")$ after $#loopK$ on the continuation; $#Break$ uses $#popK$ to jump directly to this $#jumpK$, exiting the loop in a single step.
- $#argK (m, overline(v), overline(e))$ evaluates method arguments left-to-right, accumulating values in $overline(v)$. When $overline(e)$ is exhausted, the method body is entered.
- $#newK (C, overline(v), overline(e))$ evaluates field initialisers left-to-right, accumulating values in $overline(v)$. When $overline(e)$ is exhausted, a fresh address is allocated in the store and the new object is bound there.
- $#callK (E)$ preserves the caller's environment. When the method body completes (with $#Skip$), the caller's environment is restored. $#returnK$ also targets $#callK$ via $#popCallK$.

=== Transition Rules
We define a multi-step judgement $ms$ in the usual way.

==== Expr
#mathpar(
  proof-tree(rule(name: "Val", $#ceskE($v$, $E$, $S$, $K$) ~> #ceskC($v$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "Var", $#ceskE($x$, $E$, $S$, $K$) ~> #ceskC($E(x)$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "Field", $#ceskE($p.f$, $E$, $S$, $K$) ~> #ceskE($p$, $E$, $S$, $#fieldK (f) dot.c K$)$)),
  proof-tree(rule(name: "Return", $#ceskE($#Return e$, $E$, $S$, $K$) ~> #ceskE($e$, $E$, $S$, $#returnK dot.c K$)$)),
  proof-tree(rule(name: "VarDecl", $#ceskE($#Var x : tau = e$, $E$, $S$, $K$) ~> #ceskE($e$, $E$, $S$, $#declK (x : tau) dot.c K$)$)),
  proof-tree(rule(name: "Assign", $#ceskE($x = e$, $E$, $S$, $K$) ~> #ceskE($e$, $E$, $S$, $#assignK (x) dot.c K$)$)),
  proof-tree(rule(name: "Seq", $#ceskE($s_1 ; s_2$, $E$, $S$, $K$) ~> #ceskE($s_1$, $E$, $S$, $#seqK (s_2) dot.c K$)$)),
  proof-tree(rule(name: "If", $#ceskE($#If e #Then s_1 #Else s_2$, $E$, $S$, $K$) ~> #ceskE($e$, $E$, $S$, $#ifCondK (s_1, s_2) dot.c K$)$)),

  proof-tree(rule(name: "While", $#ceskE($#While c brace.l s brace.r$, $E$, $S$, $K$) ~> #ceskE($c$, $E, #scopeMark($"loop"$)$, $S$, $#loopK (c, s) dot.c #jumpK ("loop") dot.c K$)$)),
  proof-tree(rule(name: "Break", $#ceskE($#Break$, $E$, $S$, $K$) ~> #ceskC($#Skip$, $#pop($E$, $"loop"$)$, $S$, $#popK($K$, $"loop"$)$)$)),

  proof-tree(rule(name: [$"Call"_0$], $#ceskE($m()$, $E$, $S$, $K$) ~> #ceskE($#body (m)$, $dot$, $S$, $#callK (E) dot.c K$)$)),
  proof-tree(rule(name: [$"Call"_N$], $#ceskE($m(e_1, ..., e_n)$, $E$, $S$, $K$) ~> #ceskE($e_1$, $E$, $S$, $#argK (m, epsilon, (e_2, ..., e_n)) dot.c K$)$, $n >= 1$)),

  proof-tree(rule(name: [$"New"_0$], $#ceskE($#New C()$, $E$, $S$, $K$) ~> #ceskC($a$, $E$, $S, a -> C()$, $K$)$, $a in.not op("dom")(S)$)),
  proof-tree(rule(name: [$"New"_N$], $#ceskE($#New C(e_1, ..., e_n)$, $E$, $S$, $K$) ~> #ceskE($e_1$, $E$, $S$, $#newK (C, epsilon, (e_2, ..., e_n)) dot.c K$)$, $n >= 1$)),
)
Val transitions a source value expression ($#True$, $#False$, $n$, or address $a$) into Cont mode. Var looks up the rightmost binding of $x$ in $E$. The remaining rules decompose a compound form by pushing a continuation frame. Arguments are evaluated left-to-right in the caller's environment.

==== Cont
#mathpar(
  proof-tree(rule(name: "FieldDone", $#ceskC($a$, $E$, $S$, $#fieldK (f_i) dot.c K$) ~> #ceskC($v_i$, $E$, $S$, $K$)$, $S(a) = C(... f_i := v_i ...)$)),

  proof-tree(rule(name: "IfTrue", $#ceskC($#True$, $E$, $S$, $#ifCondK (s_1, s_2) dot.c K$) ~> #ceskE($s_1$, $E, #scopeMark($"if"$)$, $S$, $#jumpK ("if") dot.c K$)$)),
  proof-tree(rule(name: "IfFalse", $#ceskC($#False$, $E$, $S$, $#ifCondK (s_1, s_2) dot.c K$) ~> #ceskE($s_2$, $E, #scopeMark($"if"$)$, $S$, $#jumpK ("if") dot.c K$)$)),

  proof-tree(rule(name: "ScopeDone", $#ceskC($#Skip$, $E$, $S$, $#jumpK (ell) dot.c K$) ~> #ceskC($#Skip$, $#pop($E$, $ell$)$, $S$, $K$)$)),

  proof-tree(rule(name: "ReturnDone", $#ceskC($v$, $E$, $S$, $#returnK dot.c K$) ~> #ceskC($#Skip$, $E'$, $S$, $K'$)$, $#popCallK($K$) = (E', K')$)),

  proof-tree(rule(name: "VarDeclDone", $#ceskC($v$, $E$, $S$, $#declK (x : tau) dot.c K$) ~> #ceskC($#Skip$, $E, x := v$, $S$, $K$)$)),
  proof-tree(rule(name: "AssignDone", $#ceskC($v$, $E$, $S$, $#assignK (x) dot.c K$) ~> #ceskC($#Skip$, $E[x |-> v]$, $S$, $K$)$)),
  proof-tree(rule(name: "SeqDone", $#ceskC($#Skip$, $E$, $S$, $#seqK (s_2) dot.c K$) ~> #ceskE($s_2$, $E$, $S$, $K$)$)),

  proof-tree(rule(name: "LoopTrue", $#ceskC($#True$, $E$, $S$, $#loopK (c, s) dot.c K$) ~> #ceskE($s$, $E$, $S$, $#loopK (c, s) dot.c K$)$)),
  proof-tree(rule(name: "LoopFalse", $#ceskC($#False$, $E$, $S$, $#loopK (c, s) dot.c K$) ~> #ceskC($#Skip$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "LoopCont", $#ceskC($#Skip$, $E$, $S$, $#loopK (c, s) dot.c K$) ~> #ceskE($c$, $#pop($E$, $"loop"$), #scopeMark($"loop"$)$, $S$, $#loopK (c, s) dot.c K$)$)),

  proof-tree(rule(name: "ArgNext", $#ceskC($v$, $E$, $S$, $#argK (m, overline(v), (e, overline(e))) dot.c K$) ~> #ceskE($e$, $E$, $S$, $#argK (m, overline(v) dot.c v, overline(e)) dot.c K$)$)),
  proof-tree(rule(name: "ArgDone", $#ceskC($v$, $E$, $S$, $#argK (m, overline(v), epsilon) dot.c K$) ~> #ceskE($#body (m)$, $E_m$, $S$, $#callK (E) dot.c K$)$, $E_m = #args (m)_1 := overline(w)_1, ..., #args (m)_n := overline(w)_n$, $text("where") overline(w) = overline(v), v$)),

  proof-tree(rule(name: "NewNext", $#ceskC($v$, $E$, $S$, $#newK (C, overline(v), (e, overline(e))) dot.c K$) ~> #ceskE($e$, $E$, $S$, $#newK (C, overline(v) dot.c v, overline(e)) dot.c K$)$)),
  proof-tree(rule(name: "NewDone", $#ceskC($v$, $E$, $S$, $#newK (C, overline(v), epsilon) dot.c K$) ~> #ceskC($a$, $E$, $S, a -> C(f_1 := w_1, ..., f_n := w_n)$, $K$)$, $a in.not op("dom")(S)$, $#fields (C) = (f_1 : tau_1, ..., f_n : tau_n)$, $text("where") overline(w) = overline(v), v$)),

  proof-tree(rule(name: "ImplicitReturn", $#ceskC($#Skip$, $E$, $S$, $#callK (E') dot.c K$) ~> #ceskC($#Skip$, $E'$, $S$, $K$)$)),
)
IfTrue/IfFalse push a scope marker $#scopeMark($"if"$)$ and $#jumpK ("if")$ before entering a branch. $E[x |-> v]$ updates the rightmost binding of $x$ in $E$.

The lifecycle of a while loop proceeds as follows. The While rule pushes $#scopeMark($"loop"$)$ onto the environment and places $#loopK (c, s) dot.c #jumpK ("loop")$ on the continuation, then evaluates the condition $c$. If the condition is $#False$, LoopFalse produces $#Skip$; this reaches $#jumpK ("loop")$ and ScopeDone pops $#scopeMark($"loop"$)$, cleaning up the loop scope. If the condition is $#True$, LoopTrue enters the body $s$ directly. Variables declared in the body accumulate in $E$ during the iteration. When the body completes with $#Skip$, LoopCont fires: it pops $E$ to $#scopeMark($"loop"$)$ (discarding iteration-local bindings) and re-pushes $#scopeMark($"loop"$)$ to begin the next iteration, then re-evaluates $c$. If $#Break$ is executed inside the body, it pops $E$ to $#scopeMark($"loop"$)$ via $#pop$ and pops $K$ to $#jumpK ("loop")$ via $#popK$, producing $#Skip$ in a clean state — the loop is fully exited in a single transition. For nested loops, $#pop$ finds the rightmost (innermost) $#scopeMark($"loop"$)$ and $#popK$ finds the topmost (innermost) $#jumpK ("loop")$, so $#Break$ exits the innermost enclosing loop.

Return evaluates its expression via $#returnK$, then ReturnDone uses $#popCallK$ to scan the continuation for the most recent $#callK (E')$, restoring the caller's environment $E'$ and producing $#Skip$ in a single step. ImplicitReturn handles the case where a method body completes normally with $#Skip$, restoring the caller's environment.

=== Initial and Terminal States

$
"Initial:" && #ceskE($#body ("main")$, $dot$, $dot$, $#callK (dot) dot.c #halt$) \
"Terminal:" && #ceskC($#Skip$, $E$, $S$, $#halt$)
$

The initial state wraps main's body in a $#callK (dot)$ frame so that $#returnK$ and $#popCallK$ are always well-defined within a method body.

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
  proof-tree(rule(name: "IfCondK", typeContE($Gamma$, $#ifCondK (s_1, s_2) dot.c K$, $#Bool$), typeStmt($Gamma, #scopeMark($"if"$)$, $sigma$, $s_1$, $Gamma'$), typeStmt($Gamma, #scopeMark($"if"$)$, $sigma$, $s_2$, $Gamma''$), typeContC($Gamma$, $K$))),
  proof-tree(rule(name: "DeclK", typeContE($Gamma$, $#declK (x : tau) dot.c K$, $tau$), typeContC($Gamma, x : tau$, $K$))),
  proof-tree(rule(name: "AssignK", typeContE($Gamma$, $#assignK (x) dot.c K$, $tau$), $Gamma(x) = tau$, typeContC($Gamma$, $K$))),
  proof-tree(rule(name: "ReturnK", typeContE($Gamma$, $#returnK dot.c K$, $sigma$))),
  proof-tree(rule(name: "FieldK", typeContE($Gamma$, $#fieldK (f) dot.c K$, $C$), $f : tau in #fields (C)$, typeContE($Gamma$, $K$, $tau$))),
  proof-tree(rule(name: "ArgK", typeContE($Gamma$, $#argK (m, overline(v), overline(e)) dot.c K$, $tau_i$), typeContC($Gamma$, $K$))),
  proof-tree(rule(name: "NewK", typeContE($Gamma$, $#newK (C, overline(v), overline(e)) dot.c K$, $tau_i$), typeContE($Gamma$, $K$, $C$))),
  proof-tree(rule(name: "LoopCondK", typeContE($Gamma$, $#loopK (c, s) dot.c K$, $#Bool$), typeExpr($Gamma$, $sigma$, $c$, $#Bool$, $Gamma$), typeStmt($Gamma$, $sigma$, $s$, $Gamma'$), typeContC($Gamma$, $K$))),
)

IfCondK accepts $#Bool$ (the condition) and types both branches under $Gamma, #scopeMark($"if"$)$; the tail $K$ accepts $#Skip$ in $Gamma$ since the if-statement's output context is $Gamma$. DeclK accepts a value of the declared type $tau$. AssignK accepts a value matching the variable's type. ReturnK accepts a value of the method's return type $sigma$; it has no constraint on the tail $K$ since return jumps past it via $#popCallK$. FieldK accepts a class type $C$, looks up $f : tau in #fields (C)$, and requires the tail $K$ to accept $tau$. ArgK accepts the type of the current argument position; it carries the statement continuation typing for the tail $K$ (needed when ArgDone enters the method body via $#callK$). NewK accepts the type of the current field initialiser; the tail $K$ must accept $C$ (the result type of the allocation). LoopCondK accepts $#Bool$ (the while condition); the tail $K$ uses #typeContC because the loop ultimately produces $#Skip$.

==== Statement Continuations

#mathpar(
  proof-tree(rule(name: "HaltK", typeContC($Gamma$, $#halt$))),
  proof-tree(rule(name: "JumpK", typeContC($Gamma$, $#jumpK (ell) dot.c K$), typeContC($#drop($Gamma$, $ell$)$, $K$))),
  proof-tree(rule(name: "SeqK", typeContC($Gamma$, $#seqK (s) dot.c K$), typeStmt($Gamma$, $sigma$, $s$, $Gamma'$), typeContC($Gamma'$, $K$))),
  proof-tree(rule(name: "LoopBodyK", typeContC($Gamma$, $#loopK (c, s) dot.c K$), typeExpr($Gamma$, $sigma$, $c$, $#Bool$, $Gamma$), typeStmt($Gamma$, $sigma$, $s$, $Gamma'$), typeContC($Gamma$, $K$))),
  proof-tree(rule(name: "CallK", typeContC($Gamma$, $#callK (E) dot.c K$), $#coh($E$, $Gamma'$)$, typeContC($Gamma'$, $K$))),
)

JumpK uses $#drop($Gamma$, $ell$)$ to strip the context to the matching scope marker, mirroring $#pop($E$, $ell$)$ on environments. The tail $K$ is typed at the resulting outer context. SeqK types the pending statement and the tail. LoopBodyK checks the condition and body under $Gamma$; the tail $K$ is typed at $Gamma$ since the loop preserves the context. CallK types the tail $K$ under the caller's context $Gamma'$, recovered from the saved environment via coherence.

=== Environment-Context Coherence

We define _coherence_ between an environment and a context, written $#coh($E$, $Gamma$)$, inductively:

#mathpar(
  proof-tree(rule(name: "CohEmp", $#coh($dot$, $dot$)$)),
  proof-tree(rule(name: "CohBind", $#coh($E, x := v$, $Gamma, x : tau$)$, $#coh($E$, $Gamma$)$, $tack.r v : tau$)),
  proof-tree(rule(name: "CohMark", $#coh($E, #scopeMark($ell$)$, $Gamma, #scopeMark($ell$)$)$, $#coh($E$, $Gamma$)$)),
)

Scope markers must match between $E$ and $Gamma$.

==== Well Typed States

A machine state is _well-typed_ when coherence bridges the environment to a context $Gamma$ that types both the control and the continuation, and the store is well-typed:

#mathpar(
  proof-tree(rule(name: "WtExprE", $tack.r #ceskE($e$, $E$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $tack.r S "ok"$, typeExpr($Gamma$, $sigma$, $e$, $tau$, $Gamma'$), typeContE($Gamma$, $K$, $tau$))),
  proof-tree(rule(name: "WtExprS", $tack.r #ceskE($s$, $E$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $tack.r S "ok"$, typeStmt($Gamma$, $sigma$, $s$, $Gamma'$), typeContC($Gamma'$, $K$))),
  proof-tree(rule(name: "WtContV", $tack.r #ceskC($v$, $E$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $tack.r S "ok"$, $tack.r v : tau$, typeContE($Gamma$, $K$, $tau$))),
  proof-tree(rule(name: "WtContS", $tack.r #ceskC($#Skip$, $E$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $tack.r S "ok"$, typeContC($Gamma$, $K$))),
)

=== Properties

Given a well-typed program $P$ and a state reachable from the initial state:

- *Progress:* if $tack.r S "ok"$ and $S$ is not terminal, then there exists $S'$ such that $S ~> S'$.

- *Preservation:* if $tack.r S "ok"$ and $S ~> S'$, then $tack.r S' "ok"$.

- *Statement Execution Preserves Coherence:* if $#coh($E$, $Gamma$)$, #typeStmt($Gamma$, $sigma$, $s$, $Gamma'$), and $#ceskE($s$, $E$, $S$, $K$) #ms #ceskC($#Skip$, $E'$, $S'$, $K$)$, then $#coh($E'$, $Gamma'$)$.

- *Pop/Drop Preserves Coherence:* if $#coh($E$, $Gamma$)$, then $#coh($#pop($E$, $ell$)$, $#drop($Gamma$, $ell$)$)$.

- *PopK/Drop Preserves Continuation Typing:* if #typeContC($Gamma$, $K$) and $K$ contains $#jumpK (ell)$, then #typeContC($#drop($Gamma$, $ell$)$, $#popK($K$, $ell$)$).

- *Allocation Preserves Store Typing:* if $tack.r S "ok"$ and $S' = S, a -> C(f_1 := v_1, ..., f_n := v_n)$ where $tack.r v_i : tau_i$ and $f_i : tau_i in #fields (C)$, then $tack.r S' "ok"$.

- *PopCallK Preserves Typing:* if the continuation $K$ is well-typed and contains $#callK (E')$, then $#popCallK($K$) = (E', K')$ where $#coh($E'$, $Gamma'$)$ and #typeContC($Gamma'$, $K'$). This follows from the structural invariant that every $#callK$ on the stack was placed by a well-typed $"Call"$ transition, which saves a coherent environment and threads the caller's statement continuation.

- *Determinacy:* each machine state has at most one successor (the transition relation is deterministic). Consequently, if the machine terminates, the terminal state is unique.

=== Known Limitations

- *$sigma$ threading across calls:* the return type $sigma$ is existentially quantified in well-typed states. When $"Call"_0$/$"ArgDone"$ enter a method body, $sigma$ changes from the caller's return type to the callee's. Preservation relies on the fact that CallK's typing of the tail $K$ is independent of $sigma$; the caller's continuation was fully typed before the call.

- *Expression Weakening excludes $#Return$:* the weakening properties require the output context to equal the input context. $#Return$ has output $dot$, so the properties do not apply to expressions containing $#Return$.

- *$#popK$/$#popCallK$ totality:* the claims that these operations are always defined when needed rely on structural invariants; $#Break$ only executes inside a $#While$ body (so $#jumpK ("loop")$ is on $K$), and $#Return$ only executes inside a method body (so $#callK$ is on $K$). These invariants hold for well-typed reachable states but are not directly enforced by the typing rules; they follow by induction on the reachable state structure.

- *Well-typed state invariant for unreachable states:* if a loop body always diverges (e.g. via $#Return$), its output context may be $dot$. LoopTrue produces a state where the continuation must be typed at this output context, which may fail if the condition references variables. At runtime this state is unreachable (the return fires first), but the well-typed state invariant technically breaks. A formal proof would use a "reachably well-typed" notion.

Note that we do not have strong normalisation; a method may call itself in an infinite loop, or a while loop may have a condition that is always true..
