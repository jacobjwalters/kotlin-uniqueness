#import "../defs.typ": *

= #Lbase

#Lbase is a simple typed language consisting of sequentially ordered statements with classes and method calls. There are no modes, and no lambdas.

== Syntax

$
P ::=& C^* times M^* && "Programs" \
C ::=& #Class C(f_i : tau_i) && "Classes" \
M ::=& m(x_i : tau_i) : sigma { s } && "Method Definitions" \
  |& m(x_i : tau_i) : sigma && "Method Declarations" \
tau, sigma ::=& #Nat && "Naturals" \
  |& #Bool && "Booleans" \
  |& C && "Class Types" \
p ::=& x && "Variable Access" \
  |& p.f && "Subfield Access" \
e ::=& #Null \
  |& p && "Path Access" \
  |& #True \
  |& #False \
  |& n in bb(N) && "Natural Numbers" \
  |& #If e #Then s_1 #Else s_2 && "If/Then/Else" \
  |& #Return e && "(Early) Return" \
s ::=& #Var x : tau && "(Mutable) Variable Declaration" \
  |& x = e && "Variable Assignment/Mutation" \
  |& s_1; s_2 && "Statement Sequencing" \
  |& m(e_i) && "Method Call" \
  |& #While c  { s } && "While Loop" \
  |& #Break && "Loop Breaking" \
$

$f$, $x$, and $m$ represent infinite and non-intersecting sets of field, variable, and method names respectively. Methods are all defined top-level, and may be (mutually) recursive.

Non-forgetful differences from the system described by @protopapa2024VerifyingKotlinCode are:
- Our system is typed (and has #Nat and #Bool as ground types).
- ITE tests an arbitrary boolean expression, rather than direct equality on patterns.

For brevity's sake, we define $#Var x : tau = e$ as $#Var x : tau; x = e$. Additionally, we assume usual boolean/arithmetic operators are defined as method call expressions.

== Typing Contexts
Morally, typing contexts (hereafter contexts) in #Lbase are ordered, rightwards-growing lists of names and their associated types, split by a loop delimiter to denote the scopes in which variables are introduced. In particular, we have a (global) list of methods and associated method types#footnote[Since we don't have object-level function types, a method type is a list of argument types, paired with a return type, writ $m : (tau_1, tau_2, ...): sigma$], paired with a list of either variable names and their associated types, or a loop delimiter.

Since method declarations are top level, we omit them from our treatment of contexts, and assume that the expression/statement theories are parameterised by a particular context of methods and method types. Methods are typed in empty contexts; the current return type is tracked as part of the statement typing judgement.

The grammar for contexts is as follows:

$
Gamma ::=& dot && "Empty" \
  |& Gamma, x : tau && "Variable Extension" \
  |& Gamma, diamond_w && "Loop Delimiter"
$

The loop delimiter is introduced when entering the body of a while loop ($diamond_w$), and is removed either at the end of the body, or during early return.

=== Well Formed Contexts
We introduce a judgement $Gamma #ctx$ to denote well formed contexts (WFCs). WFCs are defined inductively:

#mathpar(
  proof-tree(rule(name: "CtxEmp", $dot #ctx$)),
  proof-tree(rule(name: "CtxVarExt", $Gamma, x : tau #ctx$, $x in.not Gamma$, $Gamma #ctx$)),
  proof-tree(rule(name: "CtxLoopDelimiter", $Gamma, diamond_w #ctx$, $Gamma #ctx$))
)

$x in.not Gamma$ is bookkeeping for ensuring all names are distinct, and isn't strictly needed. Membership checking and lookup are defined in the usual way.

#jq[Do we want to allow name reuse (and thus shadowing)? How will this interact with borrowing later on? A: we need to investigate what happens with shadowing in Viper]

=== Removal
When typing a $#Break$ statement, we need to strip all bindings introduced since the enclosing loop was entered. To do this, we define a recursive function $drop$ that walks backwards through the context, removing variable bindings until it reaches the nearest loop delimiter $diamond_w$:

$
  drop (Gamma, diamond_w)  &= Gamma, diamond_w \
  drop (Gamma, x : tau)    &= drop (Gamma) \
$

Note that $drop$ is undefined on $dot$, which ensures that $#Break$ is ill-typed outside of a loop body.

== Type System
Herein we discuss the type system of #Lbase. Mostly it's a straightforward approach; the interesting parts surround control flow and calling methods.

The approach to type checking begins by adding all method declarations to a (global) context of methods, thereby assuming that method type declarations are always correct. Once this pass is done, the body of each method (if given) is checked according to the statement rules.

=== Expression Types
Since expressions may affect their context (via conditionals and returns), we use the judgement form #typeExpr($Gamma$, $sigma$, $e$, $tau$, $Gamma'$), where $sigma$ is the current method's return type. For most expressions, the output context is identical to the input.

#mathpar(
  proof-tree(rule(name: "TrueConst", typeExpr($Gamma$, $sigma$, $#True$, $#Bool$, $Gamma$))),
  proof-tree(rule(name: "FalseConst", typeExpr($Gamma$, $sigma$, $#False$, $#Bool$, $Gamma$))),
  proof-tree(rule(name: "NatConst", typeExpr($Gamma$, $sigma$, $n$, $#Nat$, $Gamma$), $n in bb(N)$)),
  proof-tree(rule(name: "NullConst", typeExpr($Gamma$, $sigma$, $#Null$, $tau$, $Gamma$))),

  proof-tree(rule(name: "VarAccess", typeExpr($Gamma$, $sigma$, $x$, $tau$, $Gamma$), $Gamma(x) = tau$)),

  proof-tree(rule(name: "FieldAccess", typeExpr($Gamma$, $sigma$, $p.f$, $tau$, $Gamma$), typeExpr($Gamma$, $sigma$, $p$, $C$, $Gamma$), $f : tau in #fields (C)$)),

  proof-tree(rule(name: "IfExpr", typeExpr($Gamma$, $sigma$, $#If e #Then s_1 #Else s_2$, $tau$, $Gamma$), typeExpr($Gamma$, $sigma$, $e$, $#Bool$, $Gamma$), typeStmt($Gamma$, $sigma$, $s_1$, $Gamma'_1$), typeStmt($Gamma$, $sigma$, $s_2$, $Gamma'_2$))),

  proof-tree(rule(name: "Return", typeExpr($Gamma$, $sigma$, $#Return e$, $tau$, $dot$), typeExpr($Gamma$, $sigma$, $e$, $sigma$, $Gamma$))),
)

Note that $#Null$ is a member of all types in this system. $#Return$ has type $tau$ for any $tau$ since it never produces a value. $#If$ has type $tau$ for any $tau$ since its branches are statements.
#jq[Subtyping with null?]

=== Statement Types
Typing statements is more involved. Since statements may update their context, we use a "small-step" typing judgement form #typeStmt($Gamma$, $sigma$, $s$, $Gamma'$), where $Gamma$ represents the context before the statement runs, $Gamma'$ represents the context after the statement runs, and $sigma$ is the current method's return type.

#mathpar(
  proof-tree(rule(name: "VarDecl", typeStmt($Gamma$, $sigma$, $#Var x : tau$, $Gamma, x : tau$), $x in.not Gamma$)),
  proof-tree(rule(name: "VarAssign", typeStmt($Gamma$, $sigma$, $x = e$, $Gamma'$), $Gamma(x) = tau$, typeExpr($Gamma$, $sigma$, $e$, $tau$, $Gamma'$))),

  proof-tree(rule(name: "Seq", typeStmt($Gamma$, $sigma$, $s_1; s_2$, $Gamma''$), typeStmt($Gamma$, $sigma$, $s_1$, $Gamma'$), typeStmt($Gamma'$, $sigma$, $s_2$, $Gamma''$))),

  proof-tree(rule(name: "CallStmt", typeStmt($Gamma$, $sigma$, $m(e_1, e_2, ...)$, $Gamma$), $m : (tau_1, tau_2, ...): \_$, typeExpr($Gamma$, $sigma$, $e_i$, $tau_i$, $Gamma$))),

  proof-tree(rule(name: "WhileLoop", typeStmt($Gamma$, $sigma$, $#While c { s }$, $Gamma$), typeExpr($Gamma$, $sigma$, $c$, $#Bool$, $Gamma$), typeStmt($Gamma, diamond_w$, $sigma$, $s$, $Gamma'$), $drop(Gamma') = Gamma, diamond_w$)),

  proof-tree(rule(name: "Break", typeStmt($Gamma$, $sigma$, $#Break$, $drop(Gamma)$))),
)

#jc[IfExpr is very restrictive; we should check with Komi to see exactly what we want here, especially since classes will make things a lot more complicated. Likely we will need some type unification over contexts/heaps here for the branches.]

#jq[Is our treatment of method calling and returning sound?]

Variable declarations extend the context with a fresh variable.

Variable assigment requires that the variable we're assigning to is available in the context. The output context is determined by the expression: if $e$ is a simple expression, the context is preserved; if $e$ contains a return, the context drops to $dot$. Note that $e$ has access to $x$ in its context; this allows self mutation (such as $x = x + 1$).

Sequencing threads the context produced as the output of the first statement into the input of the second statement.

Method call statements have no effect on the context at compile time, so we merely have to check the argument types. Note that the preconditions for this rule are identical to the expression case; only the judgement form of the consequent differs.

#v(1em)

Consider carefully a method with the body $#Return #Null ; #Return 1$. We obviously shouldn't allow $#Return 1$ to execute in the parent call frame; in fact, it shouldn't execute at all, and should be seen as unreachable code.

#jtodo[Double check that this is sensible]

=== Method Bodies
We introduce a final typing judgement $tack.r m(x_i : tau_i): sigma { s }$ to ascribe types for method definitions.

#mathpar(
  proof-tree(rule(name: "Method", $tack.r m(x_i : tau_i): sigma { s }$, typeStmt($x_i : tau_i$, $sigma$, $s$, $dot$)))
)

Since methods are typed in empty contexts, the body is checked with only the arguments in scope and the return type $sigma$ annotating the judgement. The output context must be $dot$, forcing all arguments and local definitions to be dropped, which in turn means that we can only exit a method via an explicit return statement.

=== Theorems and Lemmata
We should be able to use standard techniques to prove progress and preservation for the typing system, since we don't really do anything fancy at the type level.

Our treatment of contexts, however, is non-standard. We should take care to show that it's not possible for values to escape their scopes, nor for control flow to leave its scope without destroying the corresponding delimiter.

Note that we don't have strong normalisation, even for expressions; a method is able to call itself in an infinite loop.


== Evaluation
Evaluation of an #Lbase program begins with a pre-specified method name. For the rest of this document, we'll use "main". We define the operational semantics as a CESK machine; a state machine that makes evaluation order explicit via a continuation stack. We also introduce a run-time language, which extends the source language with syntactic forms for modelling non-local control flow, and address values for heap access.

=== Runtime Language
The CESK machine operates on a runtime language that extends the source syntax with runtime-only forms.

==== Values
Values are fully evaluated expressions. The source values $#True$, $#False$, $#Null$, and $n in bb(N)$ are joined by runtime-only addresses:

$
v ::=& a in cal(A) |& #True |& #False |& #Null |& n in bb(N)
$

Addresses $a in cal(A)$ are opaque references to objects in the store. They do not appear in the source program; they arise only during execution when objects are allocated.

==== Signals
Signals are runtime-only control forms produced during evaluation. They do not appear in the source program. We distinguish two kinds:

A completion signal is consumed by the immediately next continuation frame:
$
#Skip &&& "Statement completed normally"
$

Unwinding signals propagate through transparent frames until caught by a matching frame:
$
#breaking &&& "Loop exit (caught by " #loopK ")" \
#returning (v) &&& "Method return carrying value " v " (caught by " #callK ")"
$

Together, these form the signal grammar:
$
#sig ::=& #Skip |& #breaking |& #returning (v)
$

$#Skip$ signals that a statement has been fully executed: when a continuation frame expecting a statement result sees $#Skip$, it proceeds to its next action. $#breaking$ is produced when the source statement $#Break$ is executed. $#returning (v)$ is produced when $#Return e$ finishes evaluating $e$ to value $v$.

=== Machine State
The machine state is a 4-tuple $#cesk($C$, $E$, $S$, $K$)$:

#table(
  columns: (auto, auto, 1fr),
  align: (center, left, left),
  table.header([*Component*], [*Name*], [*Description*]),
  [$C$], [Control], [The current expression, statement, value, or signal being processed],
  [$E$], [Environment], [Ordered map from variables to values],
  [$S$], [Store], [Unordered map from addresses to objects],
  [$K$], [Continuation], [Stack of continutations],
)

==== Control ($C$)
The control component holds whatever syntactic construct the machine is currently processing:

$
C ::=& e && "Source expression (to evaluate)" \
  |& s && "Source statement (to execute)" \
  |& v && "Value (expression result)" \
  |& #sig && "Signal"
$

Expression evaluation terminates with a value $v$ in the control. Statement execution terminates with $#Skip$. Unwinding signals ($#breaking$ and $#returning (v)$) propagate through the continuation until caught.

==== Environment ($E$)
$
E ::=& dot && "Empty" \
  |& E, x := v && "Variable binding"
$

The environment is an ordered, rightwards-growing list of variable-to-value bindings. Lookup finds the rightmost binding for a given variable name (permitting shadowing). Update ($E[x |-> v]$) modifies the rightmost binding of $x$ in place.

The environment is extended when variables are declared ($#Var x : tau$ adds $x := #Null$ to the rightmost position) and individual bindings are updated on assignment ($x = v$ updates the rightmost $x$). The environment is saved and restored across method calls: $#callK (E)$ preserves the caller's environment on the continuation, and restores it when the method returns.

==== Store ($S$)
$
S ::=& dot && "Empty" \
  |& S, a -> C(... f_i := v_i ...) && "Object mapping"
$

The store maps addresses to objects. An object $C(... f_i := v_i ...)$ records its class $C$ and the values of its fields.

==== Continuation ($K$)
The continuation is a stack of frames that describes what to do after the current control finishes:

$
K ::=& #halt && "Program complete" \
  |& #fieldK (f) dot.c K && "After evaluating path, look up field" f \
  |& #ifK (s_1, s_2) dot.c K && "After evaluating condition, branch" \
  |& #returnK dot.c K && "After evaluating return expr, begin unwinding to most recent" #callK \
  |& #assignK (x) dot.c K && "After evaluating RHS, assign to" x "in" E \
  |& #seqK (s) dot.c K && "After first statement completes, continue with" s \
  |& #loopK (c, s) dot.c K && "Loop boundary: condition" c ", original body" s \
  |& #argK (m, overline(v), overline(e)) dot.c K && "Evaluating args: method, done, remaining" \
  |& #callK (E) dot.c K && "Call boundary: saved caller environment" E
$

Method bodies are tracked globally when defined. We define a function $#body (m)$, which returns the body of a method, and a function $#args (m)$, which returns the argument names taken by a method.

Frames are classified by which unwinding signals they catch:
- $#loopK$ catches $#breaking$ $->$ produces $#Skip$
- $#callK$ catches $#returning (v)$ $->$ restores saved environment, produces $#Skip$
- All other frames are transparent to unwinding signals (signals pass through them)

=== Transition Rules
Our transition judgement is $#cesk($C$, $E$, $S$, $K$) ~> #cesk($C'$, $E'$, $S'$, $K'$)$. We define a multi-step judgement $ms$ in the usual way.

==== Variable Access
#mathpar(
  proof-tree(rule(name: "Var", $#cesk($x$, $E$, $S$, $K$) ~> #cesk($E(x)$, $E$, $S$, $K$)$)),
)
Look up the rightmost binding of $x$ in $E$.

==== Field Access
#mathpar(
  proof-tree(rule(name: "Field", $#cesk($p.f$, $E$, $S$, $K$) ~> #cesk($p$, $E$, $S$, $#fieldK (f) dot.c K$)$)),
  proof-tree(rule(name: "FieldDone", $#cesk($a$, $E$, $S$, $#fieldK (f_i) dot.c K$) ~> #cesk($v_i$, $E$, $S$, $K$)$, $S(a) = C(... f_i := v_i ...)$)),
)
Chains compose naturally: $x.f.g$ pushes $#fieldK (g)$ then $#fieldK (f)$.

==== If Expression
#mathpar(
  proof-tree(rule(name: "If", $#cesk($#If e #Then s_1 #Else s_2$, $E$, $S$, $K$) ~> #cesk($e$, $E$, $S$, $#ifK (s_1, s_2) dot.c K$)$)),
  proof-tree(rule(name: "IfTrue", $#cesk($#True$, $E$, $S$, $#ifK (s_1, s_2) dot.c K$) ~> #cesk($s_1$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "IfFalse", $#cesk($#False$, $E$, $S$, $#ifK (s_1, s_2) dot.c K$) ~> #cesk($s_2$, $E$, $S$, $K$)$)),
)

==== Return Expression
#mathpar(
  proof-tree(rule(name: "Return", $#cesk($#Return e$, $E$, $S$, $K$) ~> #cesk($e$, $E$, $S$, $#returnK dot.c K$)$)),
  proof-tree(rule(name: "ReturnDone", $#cesk($v$, $E$, $S$, $#returnK dot.c K$) ~> #cesk($#returning (v)$, $E$, $S$, $K$)$)),
)
Evaluates $e$ to a value, then emits the $#returning (v)$ signal.

==== Variable Declaration
#mathpar(
  proof-tree(rule(name: "VarDecl", $#cesk($#Var x : tau$, $E$, $S$, $K$) ~> #cesk($#Skip$, $E, x := #Null$, $S$, $K$)$)),
)
Extends $E$ with $x$ bound to $#Null$.

==== Variable Assignment
#mathpar(
  proof-tree(rule(name: "Assign", $#cesk($x = e$, $E$, $S$, $K$) ~> #cesk($e$, $E$, $S$, $#assignK (x) dot.c K$)$)),
  proof-tree(rule(name: "AssignDone", $#cesk($v$, $E$, $S$, $#assignK (x) dot.c K$) ~> #cesk($#Skip$, $E[x |-> v]$, $S$, $K$)$)),
)
$E[x |-> v]$ updates the rightmost binding of $x$ in $E$.

==== Sequencing
#mathpar(
  proof-tree(rule(name: "Seq", $#cesk($s_1 ; s_2$, $E$, $S$, $K$) ~> #cesk($s_1$, $E$, $S$, $#seqK (s_2) dot.c K$)$)),
  proof-tree(rule(name: "SeqDone", $#cesk($#Skip$, $E$, $S$, $#seqK (s_2) dot.c K$) ~> #cesk($s_2$, $E$, $S$, $K$)$)),
)

==== Break
#mathpar(
  proof-tree(rule(name: "Break", $#cesk($#Break$, $E$, $S$, $K$) ~> #cesk($#breaking$, $E$, $S$, $K$)$)),
)
The source statement $#Break$ immediately produces the $#breaking$ signal.

==== While Loop
#mathpar(
  proof-tree(rule(name: "While", $#cesk($#While c { s }$, $E$, $S$, $K$) ~> #cesk($c$, $E$, $S$, $#loopK (c, s) dot.c K$)$)),
  proof-tree(rule(name: "LoopTrue", $#cesk($#True$, $E$, $S$, $#loopK (c, s) dot.c K$) ~> #cesk($s$, $E$, $S$, $#loopK (c, s) dot.c K$)$)),
  proof-tree(rule(name: "LoopFalse", $#cesk($#False$, $E$, $S$, $#loopK (c, s) dot.c K$) ~> #cesk($#Skip$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "LoopCont", $#cesk($#Skip$, $E$, $S$, $#loopK (c, s) dot.c K$) ~> #cesk($c$, $E$, $S$, $#loopK (c, s) dot.c K$)$)),
)
LoopCont: when the body finishes ($#Skip$), the $#loopK$ frame re-evaluates the condition $c$ while keeping itself in place for the next iteration.

==== Method Call
#mathpar(
  proof-tree(rule(name: [$"Call"_0$], $#cesk($m()$, $E$, $S$, $K$) ~> #cesk($#body (m)$, $dot$, $S$, $#callK (E) dot.c K$)$)),

  proof-tree(rule(name: [$"Call"_N$], $#cesk($m(e_1, ..., e_n)$, $E$, $S$, $K$) ~> #cesk($e_1$, $E$, $S$, $#argK (m, epsilon, (e_2, ..., e_n)) dot.c K$)$, $n >= 1$)),

  proof-tree(rule(name: "ArgNext", $#cesk($v$, $E$, $S$, $#argK (m, overline(v), (e, overline(e))) dot.c K$) ~> #cesk($e$, $E$, $S$, $#argK (m, overline(v) dot.c v, overline(e)) dot.c K$)$)),

  proof-tree(rule(name: "ArgDone", $#cesk($v$, $E$, $S$, $#argK (m, overline(v), epsilon) dot.c K$) ~> #cesk($#body (m)$, $E_m$, $S$, $#callK (E) dot.c K$)$, $E_m = #args (m)_1 := overline(w)_1, ..., #args (m)_n := overline(w)_n$, $text("where") overline(w) = overline(v), v$)),
)
Arguments are evaluated left-to-right in the caller's environment. When all arguments are evaluated, the caller's environment is saved in $#callK (E)$, a fresh environment is created from the method parameters, and the body is entered.

==== Method Return
#mathpar(
  proof-tree(rule(name: "ReturnCall", $#cesk($#returning (v)$, $E$, $S$, $#callK (E') dot.c K$) ~> #cesk($#Skip$, $E'$, $S$, $K$)$)),
  proof-tree(rule(name: "ImplicitReturn", $#cesk($#Skip$, $E$, $S$, $#callK (E') dot.c K$) ~> #cesk($#Skip$, $E'$, $S$, $K$)$)),
)
ReturnCall: explicit return; restore caller environment, discard $v$ (method calls are statement-level). ImplicitReturn: method body completed without return; same effect.

=== Signal Unwinding
Unwinding signals ($#breaking$ and $#returning (v)$) propagate through the continuation by popping transparent frames until they reach a catching frame.

==== $#breaking$ propagation (caught by $#loopK$)
#mathpar(
  proof-tree(rule(name: "BreakSeq", $#cesk($#breaking$, $E$, $S$, $#seqK (s) dot.c K$) ~> #cesk($#breaking$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "BreakAssign", $#cesk($#breaking$, $E$, $S$, $#assignK (x) dot.c K$) ~> #cesk($#breaking$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "BreakReturn", $#cesk($#breaking$, $E$, $S$, $#returnK dot.c K$) ~> #cesk($#breaking$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "BreakArg", $#cesk($#breaking$, $E$, $S$, $#argK (m, overline(v), overline(e)) dot.c K$) ~> #cesk($#breaking$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "BreakLoop", $#cesk($#breaking$, $E$, $S$, $#loopK (c, s) dot.c K$) ~> #cesk($#Skip$, $E$, $S$, $K$)$)),
)
$#breaking$ at $#callK$ is stuck; the type system guarantees this cannot happen ($#Break$ is only well-typed inside a loop body). $#breaking$ at $#fieldK$ is unreachable; paths are syntactically restricted to variable/field chains and cannot contain statements.

==== $#returning (v)$ propagation (caught by $#callK$)
#mathpar(
  proof-tree(rule(name: "RetSeq", $#cesk($#returning (v)$, $E$, $S$, $#seqK (s) dot.c K$) ~> #cesk($#returning (v)$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "RetAssign", $#cesk($#returning (v)$, $E$, $S$, $#assignK (x) dot.c K$) ~> #cesk($#returning (v)$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "RetReturn", $#cesk($#returning (v)$, $E$, $S$, $#returnK dot.c K$) ~> #cesk($#returning (v)$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "RetArg", $#cesk($#returning (v)$, $E$, $S$, $#argK (m, overline(v), overline(e)) dot.c K$) ~> #cesk($#returning (v)$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "RetLoop", $#cesk($#returning (v)$, $E$, $S$, $#loopK (c, s) dot.c K$) ~> #cesk($#returning (v)$, $E$, $S$, $K$)$)),
  proof-tree(rule(name: "ReturnCall", $#cesk($#returning (v)$, $E$, $S$, $#callK (E') dot.c K$) ~> #cesk($#Skip$, $E'$, $S$, $K$)$)),
)
$#returning (v)$ at $#fieldK$ is unreachable for the same reason as $#breaking$; paths cannot contain expressions that produce signals.

Note: BreakAssign/RetAssign are reachable via $x = #If #True #Then #Break #Else #Skip$, and BreakReturn/RetReturn via $#Return (#If #True #Then #Break #Else 0)$; if-expressions have statement branches, so a signal in a branch propagates through the enclosing expression's frame.

=== Initial and Terminal States

$
"Initial:" && #cesk($#body ("main")$, $dot$, $dot$, $#halt$) \
"Terminal:" && #cesk($#Skip$, $E$, $S$, $#halt$) && "Normal completion" \
 && #cesk($#returning (v)$, $E$, $S$, $#halt$) && "Main returned a value"
$

=== Design Note: Environment Scoping
The environment $E$ grows monotonically; variables declared in inner scopes (loop bodies, if branches) remain in $E$ after scope exit. This is semantically safe because the type system prevents references to out-of-scope variables. However, for the eventual uniqueness/borrowing system, dangling bindings in $E$ to heap objects could interfere with aliasing analysis. If this becomes an issue, $#loopK$ and $#callK$ can be extended to save/restore $E$.

=== Theorems and Lemmata
Given a well-typed program $P$ and a state $#cesk($C$, $E$, $S$, $K$)$ reachable from the initial state:

*Progress:* either the state is terminal, or there exists a state $#cesk($C'$, $E'$, $S'$, $K'$)$ such that $#cesk($C$, $E$, $S$, $K$) ~> #cesk($C'$, $E'$, $S'$, $K'$)$.

It should be impossible for $P$ to:
- Have $#breaking$ reach a $#callK$ frame (guaranteed by the type system: $#Break$ is only well-typed inside a loop body)
- Have $#returning (v)$ reach $#halt$ outside of the main method (guaranteed by $#callK$ catching returns at method boundaries)
