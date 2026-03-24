#import "../defs.typ": *

= #Lclass

#Lclass is a typed language with expressions, statements, classes, and method calls. Conditionals, loops, breaks, and returns are expressions with labelled non-local jumps; local variable scoping is managed by scope blocks. There are no modes, and no lambdas.

== Syntax

$
P ::=& C^* times M^* && "Programs" \
C ::=& #Class C(f_i : tau_i) && "Classes" \
M ::=& m(x_i : tau_i) : sigma { s } && "Method Definitions" \
tau, sigma ::=& #Nat && "Naturals" \
  |& #Bool && "Booleans" \
  |& #Unit && "Unit" \
  |& C && "Class Types" \
p ::=& x && "Variable Access" \
  |& p.f && "Subfield Access" \
e ::=& p && "Path Access" \
  |& #True \
  |& #False \
  |& n in bb(N) && "Natural Numbers" \
  |& #UnitVal && "Unit Value" \
  |& e_1 plus.o e_2 && "Binary Operator" \
  |& plus.o (e) && "Unary Operator" \
  |& #New C(e_1, ..., e_n) && "Object Construction" \
  |& m(e_i) && "Method Call" \
  |& #Return ell thin e && "Return (labelled)" \
  |& #If e #Then e_1 #Else e_2 && "If/Then/Else" \
  |& #While c brace.l e brace.r && "While Loop" \
  |& #Break ell && "Loop Break (labelled)" \
  |& #Scope brace.l s; e brace.r && "Scope Block" \
s ::=& #Var x : tau = e && "(Mutable) Variable Declaration" \
  |& x = e && "Variable Assignment/Mutation" \
  |& s_1; s_2 && "Statement Sequencing" \
  |& #Do e && "Expression Statement" \
$

$f$, $x$, and $m$ represent infinite and non-intersecting sets of field, variable, and method names respectively. Methods are all defined top-level, and may be (mutually) recursive.

$ell$ represents an infinite set of jump labels. For the purpose of formalisation, it may be easier to use distinct sets for $#Break$ and $#Return$. We write $#Break$ as shorthand for $#Break ell$ where $ell$ is the most recently bound loop label, and $#Return e$ as shorthand for $#Return ell thin e$ where $ell$ is the current method's label.

We write $plus.o$ to range over binary operators ${+, ∸, ==}$ and unary operators ${#IsZero}$. The meta-level function $#delta$ maps an operator and its argument value(s) to the result:

$
#delta (+, n_1, n_2) &= n_1 + n_2 \
#delta (∸, n_1, n_2) &= max(n_1 - n_2, 0) \
#delta (==, v_1, v_2) &= cases(#True &"if" v_1 = v_2, #False &"otherwise") \
#delta (#IsZero, n) &= cases(#True &"if" n = 0, #False &"otherwise")
$

== Typing Contexts
Typing contexts (hereafter contexts) in #Lclass are ordered, rightwards-growing lists of names and their associated types. We have a (global) list of methods and associated method types#footnote[Since we don't have object-level function types, a method type is a list of argument types, paired with a return type, writ $m : (tau_1, tau_2, ...): sigma$], paired with a list of variable names and their associated types.

Since method declarations are top level, we omit them from our treatment of contexts, and assume that the expression/statement theories are parameterised by a particular context of methods and method types.

The grammar for contexts is as follows:

$
Gamma ::=& dot && "Empty" \
  |& Gamma, x : tau && "Variable Extension"
$

Lookup ($Gamma(x) = tau$) returns the type of $x$ in $Gamma$.

== Jump Contexts
A jump context $Delta$ is a stack tracking which non-local jump targets are lexically in scope. In #Lclass, jump targets include both loops (for $#Break$) and methods (for $#Return$):

$
Delta ::=& dot && "Empty" \
  |& Delta, #Loop (ell) && "Loop boundary (labelled" ell")" \
  |& Delta, #Method (ell, sigma) && "Method boundary (labelled" ell", return type" sigma")"
$

$#While$ extends $Delta$ with $#Loop (ell)$ for its body. Method bodies are typed with $Delta = #Method (ell, sigma)$.

Lookup $Delta(ell)$ scans $Delta$ right-to-left for the entry with label $ell$:

$
(Delta, #Loop (ell))(ell) &= #Loop (ell) \
(Delta, #Loop (ell'))(ell) &= Delta(ell) && quad ell' != ell \
(Delta, #Method (ell, sigma))(ell) &= #Method (ell, sigma) \
(Delta, #Method (ell', sigma))(ell) &= Delta(ell) && quad ell' != ell
$

$dot (ell)$ is undefined. $#Break ell$ requires $Delta(ell) = #Loop (ell)$; $#Return ell thin e$ requires $Delta(ell) = #Method (ell, sigma)$ and recovers the return type $sigma$ from the entry.

== Type System
Herein we discuss the type system of #Lclass.

The approach to type checking begins by adding all method declarations to a (global) context of methods, thereby assuming that method type declarations are always correct. Once this pass is done, the body of each method (if given) is checked according to the statement rules.

=== Expression Types
Since expressions do not modify the typing context, we use the judgement form #typeExpr($Gamma$, $Delta$, $e$, $tau$) with no output context. The jump context $Delta$ tracks which non-local jumps are available; the return type for $#Return$ is recovered from $Delta$ via lookup.

#mathpar(
  proof-tree(rule(name: "TrueConst", typeExpr($Gamma$, $Delta$, $#True$, $#Bool$))),
  proof-tree(rule(name: "FalseConst", typeExpr($Gamma$, $Delta$, $#False$, $#Bool$))),
  proof-tree(rule(name: "NatConst", typeExpr($Gamma$, $Delta$, $n$, $#Nat$), $n in bb(N)$)),
  proof-tree(rule(name: "UnitConst", typeExpr($Gamma$, $Delta$, $#UnitVal$, $#Unit$))),

  proof-tree(rule(name: "VarAccess", typeExpr($Gamma$, $Delta$, $x$, $tau$), $Gamma(x) = tau$)),

  proof-tree(rule(name: "FieldAccess", typeExpr($Gamma$, $Delta$, $p.f$, $tau$), typeExpr($Gamma$, $Delta$, $p$, $C$), $f : tau in #fields (C)$)),

  proof-tree(rule(name: "BinOp", typeExpr($Gamma$, $Delta$, $e_1 plus.o e_2$, $tau_3$), typeExpr($Gamma$, $Delta$, $e_1$, $tau_1$), typeExpr($Gamma$, $Delta$, $e_2$, $tau_2$), $plus.o : tau_1 times tau_2 -> tau_3$)),
  proof-tree(rule(name: "UnOp", typeExpr($Gamma$, $Delta$, $plus.o (e)$, $tau_2$), typeExpr($Gamma$, $Delta$, $e$, $tau_1$), $plus.o : tau_1 -> tau_2$)),

  proof-tree(rule(name: "New", typeExpr($Gamma$, $Delta$, $#New C(e_1, ..., e_n)$, $C$), $#fields (C) = (f_1 : tau_1, ..., f_n : tau_n)$, typeExpr($Gamma$, $Delta$, $e_i$, $tau_i$))),

  proof-tree(rule(name: "Call", typeExpr($Gamma$, $Delta$, $m(e_1, ..., e_n)$, $sigma_m$), $m : (tau_1, ..., tau_n) : sigma_m$, typeExpr($Gamma$, $Delta$, $e_i$, $tau_i$))),

  proof-tree(rule(name: "Return", typeExpr($Gamma$, $Delta$, $#Return ell thin e$, $tau$), $Delta(ell) = #Method (ell, sigma)$, typeExpr($Gamma$, $Delta$, $e$, $sigma$))),

  proof-tree(rule(name: "IfExpr", typeExpr($Gamma$, $Delta$, $#If e #Then e_1 #Else e_2$, $tau$), typeExpr($Gamma$, $Delta$, $e$, $#Bool$), typeExpr($Gamma$, $Delta$, $e_1$, $tau$), typeExpr($Gamma$, $Delta$, $e_2$, $tau$))),

  proof-tree(rule(name: "WhileExpr", typeExpr($Gamma$, $Delta$, $#While c brace.l e brace.r$, $#Unit$), typeExpr($Gamma$, $Delta$, $c$, $#Bool$), typeExpr($Gamma$, $Delta, #Loop (ell)$, $e$, $#Unit$))),

  proof-tree(rule(name: "BreakExpr", typeExpr($Gamma$, $Delta$, $#Break ell$, $tau$), $Delta(ell) = #Loop (ell)$)),

  proof-tree(rule(name: "ScopeExpr", typeExpr($Gamma$, $Delta$, $#Scope brace.l s; e brace.r$, $tau$), typeStmt($Delta$, $Gamma$, $s$, $Gamma'$), typeExpr($Gamma'$, $Delta$, $e$, $tau$))),
)

$#New C(e_1, ..., e_n)$ checks each field initialiser $e_i$ against the declared field type $tau_i$. Method calls $m(e_1, ..., e_n)$ check each argument against the method's parameter types and have the method's return type $sigma_m$.

$#Return ell thin e$ and $#Break ell$ both have type $tau$ for any $tau$ since they never produce a value. $#Return ell thin e$ requires $Delta(ell) = #Method (ell, sigma)$ and checks its sub-expression against the recovered return type $sigma$. $#Break ell$ requires $Delta(ell) = #Loop (ell)$. Both are ill-typed outside their respective scopes.

$#If$ expressions require both branches to have the same type $tau$; the condition must be $#Bool$. $#While$ expressions have type $#Unit$; the body is typed with $Delta$ extended by $#Loop (ell)$, making $#Break ell$ available inside the loop body. The condition is typed at $Delta$ (without $#Loop (ell)$), so $#Break$ in the condition targets an outer loop. $#Scope$ expressions run statements $s$ (extending $Gamma$ to $Gamma'$), then evaluate a trailing expression $e$ in $Gamma'$. The overall type is the type of $e$; the scope's local declarations are not visible outside.

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
Since statements may update their context, we use a "small-step" typing judgement form #typeStmt($Delta$, $Gamma$, $s$, $Gamma'$), where $Gamma$ is the context before the statement and $Gamma'$ after. $Delta$ is unchanged by all statements, and is threaded through for expressions.

#mathpar(
  proof-tree(rule(name: "VarDecl", typeStmt($Delta$, $Gamma$, $#Var x : tau = e$, $Gamma, x : tau$), typeExpr($Gamma$, $Delta$, $e$, $tau$))),
  proof-tree(rule(name: "VarAssign", typeStmt($Delta$, $Gamma$, $x = e$, $Gamma$), $Gamma(x) = tau$, typeExpr($Gamma$, $Delta$, $e$, $tau$))),

  proof-tree(rule(name: "Seq", typeStmt($Delta$, $Gamma$, $s_1; s_2$, $Gamma''$), typeStmt($Delta$, $Gamma$, $s_1$, $Gamma'$), typeStmt($Delta$, $Gamma'$, $s_2$, $Gamma''$))),

  proof-tree(rule(name: "ExprStmt", typeStmt($Delta$, $Gamma$, $#Do e$, $Gamma$), typeExpr($Gamma$, $Delta$, $e$, $tau$))),
)

Variable declarations check the initialiser expression against the declared type, then extend the context.

Variable assignment requires that $x : tau$ is present in the context. The output context is $Gamma$ (unchanged). $e$ has access to $x$; this allows self mutation (such as $x = x + 1$).

Sequencing threads $Gamma$ from the output of the first statement into the input of the second; $Delta$ is unchanged.

Expression statements ($#Do e$) evaluate an expression and discard the result. Since expressions do not modify the typing context, the output is $Gamma$ (unchanged). This is how $#If$, $#While$, $#Break$, $#Return$, and method calls appear in statement position.

=== Method Bodies
We introduce a final typing judgement $tack.r m(x_i : tau_i): sigma { s }$ to ascribe types for method definitions.

#mathpar(
  proof-tree(rule(name: "Method", $tack.r m(x_i : tau_i): sigma { s }$, typeStmt($#Method (ell, sigma)$, $x_i : tau_i$, $s$, $Gamma'$)))
)

The body is checked with only the arguments in scope and $Delta = #Method (ell, sigma)$: a fresh jump context containing just the method boundary. The return type $sigma$ is embedded in $Delta$ and recovered by $#Return ell thin e$ via lookup. The output context $Gamma'$ is unconstrained.

=== Properties

- *Output Context Determinacy:* if #typeStmt($Delta$, $Gamma$, $s$, $Gamma_1$) and #typeStmt($Delta$, $Gamma$, $s$, $Gamma_2$), then $Gamma_1 = Gamma_2$.

- *Expression Weakening (Extension):* if #typeExpr($Gamma$, $Delta$, $e$, $tau$) and $Gamma$ is a suffix of $Gamma'$, then #typeExpr($Gamma'$, $Delta$, $e$, $tau$).

- *Expression Weakening (Permutation):* if #typeExpr($Gamma$, $Delta$, $e$, $tau$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeExpr($Gamma'$, $Delta$, $e$, $tau$).

- *Statement Weakening (Extension):* if #typeStmt($Delta$, $Gamma$, $s$, $Gamma, Gamma'$) and $Gamma$ is a suffix of $Gamma'$, then #typeStmt($Delta$, $Gamma'$, $s$, $Gamma', Gamma'$).

- *Statement Weakening (Permutation):* if #typeStmt($Delta$, $Gamma$, $s$, $Gamma, Gamma'$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeStmt($Delta$, $Gamma'$, $s$, $Gamma', Gamma'$).

Note that in the statement weakening properties, $Gamma, Gamma'$ refers to $Gamma$ concatenated with another context $Gamma'$. We can't extend by a single variable as in the expression weakening rules since compound statements may extend $Gamma$ with any number of new variables.

- *Expression $Delta$-Weakening (Extension):* if #typeExpr($Gamma$, $Delta$, $e$, $tau$) and $Delta$ is a suffix of $Delta'$, then #typeExpr($Gamma$, $Delta'$, $e$, $tau$). Adding jump targets to $Delta$ does not invalidate existing typing: all rules either ignore $Delta$, thread it unchanged, or require $Delta(ell)$ to be defined (which is preserved by extension). This property is needed for preservation of WhileExpr (extending $Delta$ with $#Loop (ell)$ for the body).

- *Expression $Delta$-Weakening (Permutation):* if #typeExpr($Gamma$, $Delta$, $e$, $tau$) and for all $ell in op("dom")(Delta)$, $Delta(ell) = Delta'(ell)$, then #typeExpr($Gamma$, $Delta'$, $e$, $tau$). Typing rules access $Delta$ only via $Delta(ell)$ lookup, which is preserved by the permutation condition.

- *Statement $Delta$-Weakening (Extension):* if #typeStmt($Delta$, $Gamma$, $s$, $Gamma'$) and $Delta$ is a suffix of $Delta'$, then #typeStmt($Delta'$, $Gamma$, $s$, $Gamma'$). Follows from Expression $Delta$-Weakening since statements only interact with $Delta$ through their sub-expressions.

- *Statement $Delta$-Weakening (Permutation):* if #typeStmt($Delta$, $Gamma$, $s$, $Gamma'$) and for all $ell in op("dom")(Delta)$, $Delta(ell) = Delta'(ell)$, then #typeStmt($Delta'$, $Gamma$, $s$, $Gamma'$).


== Evaluation
Evaluation of an #Lclass program begins with a pre-specified method name. For the rest of this document, we'll use "main". We define the operational semantics as a two-phase CEJSK machine; a state machine that makes evaluation order explicit via a continuation stack and a jump stack. We also introduce a run-time language, which extends the source language with syntactic forms for address values and a completion marker.

=== Runtime Language
The CEJSK machine operates on a runtime language that extends the source syntax with runtime-only forms.

==== Values
Values are fully evaluated expressions. The source values $#True$, $#False$, and $n in bb(N)$ are joined by runtime-only addresses:

$
v ::=& a in cal(A) |& #True |& #False |& n in bb(N) |& #UnitVal
$

Addresses $a in cal(A)$ are opaque references to objects in the store. They do not appear in the source program; they arise only during execution when objects are allocated.

We write $tack.r v : tau$ for value typing: $tack.r #True : #Bool$, $tack.r #False : #Bool$, $tack.r n : #Nat$ for $n in bb(N)$, $tack.r #UnitVal : #Unit$, and $tack.r a : C$ when $S(a) = C(...)$ (the address points to an object of class $C$ in the store).

==== Completion Marker
$#Skip$ is a run-time-only completion marker indicating that a statement has been fully executed. It does not appear in the source program. Since $#Skip$ can appear in the control during evaluation, it needs a typing rule:

#mathpar(
  proof-tree(rule(name: "Skip", typeStmt($Delta$, $Gamma$, $#Skip$, $Gamma$))),
)

$#Skip$ preserves the context unchanged.

=== Machine State
The machine state is a 5-tuple $#cesk($C$, $E$, $J$, $S$, $K$)$. The machine operates in one of two phases, indicated by a subscript on the state. In _Expr_ mode ($#ceskE($C$, $E$, $J$, $S$, $K$)$), the control holds a source expression or statement to be decomposed. In _Cont_ mode ($#ceskC($C$, $E$, $J$, $S$, $K$)$), the control holds a value or completion marker and the machine dispatches on the continuation.

#table(
  columns: (auto, auto, 1fr),
  align: (center, left, left),
  table.header([*Component*], [*Name*], [*Description*]),
  [$C$], [Control], [The current expression, statement, value, or completion marker being processed],
  [$E$], [Environment], [Ordered map from variables to values],
  [$J$], [Jump stack], [Stack of jump targets mirroring $Delta$],
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
  |& E, x := v && "Variable binding"
$

The environment is an ordered, rightwards-growing list of variable-to-value bindings. Lookup and update scan right-to-left. Lookup finds the rightmost binding for a given variable name (permitting shadowing). Update ($E[x |-> v]$) modifies the rightmost binding of $x$ in place.

The environment is extended when variables are declared ($#Var x : tau = e$ adds $x := v$ to the rightmost position, where $v$ is the value of $e$) and individual bindings are updated on assignment ($x = v$ updates the rightmost $x$). We write $|E|$ for the length (number of bindings) of $E$. The operation $#truncate($E$, $n$)$ returns the first $n$ bindings of $E$, dropping everything from position $n + 1$ onward. Scoping constructs record $|E|$ at entry and truncate back to that size at exit.

==== Jump Stack ($J$)
The jump stack is the runtime mirror of the jump context $Delta$. Each entry stores a label, the data needed to restore the caller/loop state, and the continuation to resume after the jump:

$
J ::=& dot && "Empty" \
  |& J, #Loop (ell, n, K) && "Loop: label" ell", env size" n", exit continuation" K \
  |& J, #Method (ell, E, K) && "Method: label" ell", caller env" E", return continuation" K
$

Lookup $J(ell)$ scans $J$ right-to-left for the entry with label $ell$. For loop entries, it returns $(n, K)$; for method entries, it returns $(E, K)$. As with $Delta$, $dot (ell)$ is undefined; the type system ensures this case is unreachable.

$J$ is pushed at LoopTrue (entering a loop body) and at Call (entering a method body). It is popped at LoopCont (re-entering the condition), Break (exiting a loop), ReturnDone (explicit return), or ImplicitReturn (normal method completion).

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
  |& #ifCondK (e_1, e_2) dot.c K && "After evaluating condition, branch to expression" \
  |& #declK (x : tau) dot.c K && "After evaluating initialiser of type" tau ", bind" x "in" E \
  |& #returnK (ell) dot.c K && "After evaluating return expr, jump to method" ell \
  |& #assignK (x) dot.c K && "After evaluating RHS, assign to" x "in" E \
  |& #binopLK (plus.o, e_2) dot.c K && "After evaluating left operand of" plus.o", evaluate" e_2 \
  |& #binopRK (plus.o, v_1) dot.c K && "After evaluating right operand of" plus.o", apply to" v_1 \
  |& #unopK (plus.o) dot.c K && "After evaluating operand of unary" plus.o", apply" \
  |& #seqK (s) dot.c K && "After first statement completes, continue with" s \
  |& #loopK (c, e, n) dot.c K && "While condition: body" e ", saved env size" n \
  |& #loopContK (c, e) dot.c K && "After loop body, re-evaluate condition" \
  |& #scopeBodyK (e, n) dot.c K && "After scope statements, evaluate trailing expr" e \
  |& #scopeExitK (n) dot.c K && "After trailing expr, truncate env to size" n \
  |& #exprStmtK dot.c K && "After expression evaluates, discard value" \
  |& #argK (m, overline(v), overline(e)) dot.c K && "Evaluating args: method, done, remaining" \
  |& #newK (C, overline(v), overline(e)) dot.c K && "Evaluating field initialisers: class" C", done, remaining" \
  |& #callK (E) dot.c K && "Call boundary: saved caller environment" E
$

Method bodies are tracked globally when defined. We define a function $#body (m)$, which returns the body of a method, and a function $#args (m)$, which returns the argument names taken by a method.

- $#halt$ signals that the program is finished; a terminal state is $#ceskC($#Skip$, $E$, $J$, $S$, $#halt$)$.
- $#ifCondK (e_1, e_2)$ waits for the condition to evaluate, then dispatches to the appropriate branch expression.
- $#declK (x : tau)$ waits for the initialiser expression to evaluate to a value $v$ of type $tau$, then extends the environment with $x := v$.
- $#returnK (ell)$ waits for the return expression to evaluate to a value, then uses $J(ell)$ to jump to the method boundary, restoring the caller's environment and producing the return value.
- $#assignK (x)$ waits for the RHS expression to evaluate to a value $v$, then updates the environment with $E[x |-> v]$.
- $#binopLK (plus.o, e_2)$ waits for the left operand to evaluate to $v_1$, then begins evaluating $e_2$ with $#binopRK (plus.o, v_1)$ on the stack.
- $#binopRK (plus.o, v_1)$ waits for the right operand to evaluate to $v_2$, then computes $#delta (plus.o, v_1, v_2)$.
- $#unopK (plus.o)$ waits for the operand to evaluate to $v$, then computes $#delta (plus.o, v)$.
- $#seqK (s)$ waits for the first statement to complete, then loads $s$ into the control.
- $#loopK (c, e, n)$ receives the condition value: $#True$ enters the body $e$ via $#loopContK$; $#False$ truncates the environment to size $n$ and produces $#UnitVal$. The saved size $n$ records $|E|$ at while entry and is needed here because LoopFalse fires during condition evaluation, before $J$ has been pushed with this loop's entry.
- $#loopContK (c, e)$ receives $#UnitVal$ after the body completes, then re-evaluates $c$ with $#loopK$ on the continuation.
- $#scopeBodyK (e, n)$ waits for the scope's statements to complete ($#Skip$), then evaluates the trailing expression $e$. The saved size $n$ records $|E|$ at scope entry.
- $#scopeExitK (n)$ waits for the trailing expression to produce a value, then truncates the environment to size $n$, dropping scope-local bindings.
- $#exprStmtK$ waits for an expression to produce a value, discards it, and produces $#Skip$.
- $#argK (m, overline(v), overline(e))$ evaluates method arguments left-to-right, accumulating values in $overline(v)$. When $overline(e)$ is exhausted, the method body is entered.
- $#newK (C, overline(v), overline(e))$ evaluates field initialisers left-to-right, accumulating values in $overline(v)$. When $overline(e)$ is exhausted, a fresh address is allocated in the store and the new object is bound there.
- $#callK (E)$ preserves the caller's environment. When the method body completes (with $#Skip$), $#UnitVal$ is produced and the caller's environment is restored via ImplicitReturn.

=== Transition Rules
We define a multi-step judgement $ms$ in the usual way.

==== Expr
$
#ceskE($v$, $E$, $J$, $S$, $K$) &~> #ceskC($v$, $E$, $J$, $S$, $K$) && "Val" \
#ceskE($x$, $E$, $J$, $S$, $K$) &~> #ceskC($E(x)$, $E$, $J$, $S$, $K$) && "Var" \
#ceskE($p.f$, $E$, $J$, $S$, $K$) &~> #ceskE($p$, $E$, $J$, $S$, $#fieldK (f) dot.c K$) && "Field" \
#ceskE($#Return ell thin e$, $E$, $J$, $S$, $K$) &~> #ceskE($e$, $E$, $J$, $S$, $#returnK (ell) dot.c K$) && "Return" \
#ceskE($#Var x : tau = e$, $E$, $J$, $S$, $K$) &~> #ceskE($e$, $E$, $J$, $S$, $#declK (x : tau) dot.c K$) && "VarDecl" \
#ceskE($x = e$, $E$, $J$, $S$, $K$) &~> #ceskE($e$, $E$, $J$, $S$, $#assignK (x) dot.c K$) && "Assign" \
#ceskE($e_1 plus.o e_2$, $E$, $J$, $S$, $K$) &~> #ceskE($e_1$, $E$, $J$, $S$, $#binopLK (plus.o, e_2) dot.c K$) && "BinOp" \
#ceskE($#IsZero (e)$, $E$, $J$, $S$, $K$) &~> #ceskE($e$, $E$, $J$, $S$, $#unopK (#IsZero) dot.c K$) && "UnOp" \
#ceskE($s_1 ; s_2$, $E$, $J$, $S$, $K$) &~> #ceskE($s_1$, $E$, $J$, $S$, $#seqK (s_2) dot.c K$) && "Seq" \
#ceskE($#Do e$, $E$, $J$, $S$, $K$) &~> #ceskE($e$, $E$, $J$, $S$, $#exprStmtK dot.c K$) && "ExprStmt" \
#ceskE($#If e #Then e_1 #Else e_2$, $E$, $J$, $S$, $K$) &~> #ceskE($e$, $E$, $J$, $S$, $#ifCondK (e_1, e_2) dot.c K$) && "If" \
#ceskE($#While c brace.l e brace.r$, $E$, $J$, $S$, $K$) &~> #ceskE($c$, $E$, $J$, $S$, $#loopK (c, e, |E|) dot.c K$) && "While" \
#ceskE($#Break ell$, $E$, $J$, $S$, $K$) &~> #ceskC($#UnitVal$, $#truncate($E$, $n$)$, $J'$, $S$, $K'$) && "Break" \
& quad "where" J(ell) = (n, K') \
#ceskE($#Scope brace.l s ; e brace.r$, $E$, $J$, $S$, $K$) &~> #ceskE($s$, $E$, $J$, $S$, $#scopeBodyK (e, |E|) dot.c K$) && "Scope" \
#ceskE($m()$, $E$, $J$, $S$, $K$) &~> #ceskE($#body (m)$, $dot$, $J'$, $S$, $#callK (E) dot.c K$) && "Call"_0 \
& quad "where" J' = J, #Method (ell, E, K) \
#ceskE($m(e_1, ..., e_n)$, $E$, $J$, $S$, $K$) &~> #ceskE($e_1$, $E$, $J$, $S$, $#argK (m, epsilon, (e_2, ..., e_n)) dot.c K$) && "Call"_N \
& quad n >= 1 \
#ceskE($#New C()$, $E$, $J$, $S$, $K$) &~> #ceskC($a$, $E$, $J$, $S, a -> C()$, $K$) && "New"_0 \
& quad a in.not op("dom")(S) \
#ceskE($#New C(e_1, ..., e_n)$, $E$, $J$, $S$, $K$) &~> #ceskE($e_1$, $E$, $J$, $S$, $#newK (C, epsilon, (e_2, ..., e_n)) dot.c K$) && "New"_N \
& quad n >= 1
$
Val transitions a source value expression ($#True$, $#False$, $n$, $#UnitVal$, or address $a$) into Cont mode. Var looks up the rightmost binding of $x$ in $E$. The remaining rules decompose a compound form by pushing a continuation frame. BinOp evaluates the left operand first (left-to-right evaluation order). UnOp evaluates its single operand. If evaluates the condition; the branches are expressions. While records $|E|$ in $#loopK$ for use by LoopFalse. Break looks up $J(ell)$ to find the target loop's saved environment size $n$ and exit continuation $K'$, truncates $E$ to $n$, and produces $#UnitVal$. $J'$ is $J$ with the entry for $ell$ and all entries above it removed. $"Call"_0$ pushes $#Method (ell, E, K)$ onto $J$ and $#callK (E)$ onto $K$, then enters the method body with an empty environment. Arguments are evaluated left-to-right in the caller's environment.

==== Cont
$
#ceskC($a$, $E$, $J$, $S$, $#fieldK (f_i) dot.c K$) &~> #ceskC($v_i$, $E$, $J$, $S$, $K$) && "FieldDone" \
& quad S(a) = C(... f_i := v_i ...) \
#ceskC($#True$, $E$, $J$, $S$, $#ifCondK (e_1, e_2) dot.c K$) &~> #ceskE($e_1$, $E$, $J$, $S$, $K$) && "IfTrue" \
#ceskC($#False$, $E$, $J$, $S$, $#ifCondK (e_1, e_2) dot.c K$) &~> #ceskE($e_2$, $E$, $J$, $S$, $K$) && "IfFalse" \
#ceskC($v$, $E$, $J$, $S$, $#returnK (ell) dot.c K$) &~> #ceskC($v$, $E'$, $J'$, $S$, $K'$) && "ReturnDone" \
& quad "where" J(ell) = (E', K') \
#ceskC($v$, $E$, $J$, $S$, $#declK (x : tau) dot.c K$) &~> #ceskC($#Skip$, $E, x := v$, $J$, $S$, $K$) && "VarDeclDone" \
#ceskC($v$, $E$, $J$, $S$, $#assignK (x) dot.c K$) &~> #ceskC($#Skip$, $E[x |-> v]$, $J$, $S$, $K$) && "AssignDone" \
#ceskC($v_1$, $E$, $J$, $S$, $#binopLK (plus.o, e_2) dot.c K$) &~> #ceskE($e_2$, $E$, $J$, $S$, $#binopRK (plus.o, v_1) dot.c K$) && "BinOpL" \
#ceskC($v_2$, $E$, $J$, $S$, $#binopRK (plus.o, v_1) dot.c K$) &~> #ceskC($#delta (plus.o, v_1, v_2)$, $E$, $J$, $S$, $K$) && "BinOpR" \
#ceskC($v$, $E$, $J$, $S$, $#unopK (plus.o) dot.c K$) &~> #ceskC($#delta (plus.o, v)$, $E$, $J$, $S$, $K$) && "UnOpDone" \
#ceskC($#Skip$, $E$, $J$, $S$, $#seqK (s_2) dot.c K$) &~> #ceskE($s_2$, $E$, $J$, $S$, $K$) && "SeqDone" \
#ceskC($v$, $E$, $J$, $S$, $#exprStmtK dot.c K$) &~> #ceskC($#Skip$, $E$, $J$, $S$, $K$) && "ExprStmtDone" \
#ceskC($#True$, $E$, $J$, $S$, $#loopK (c, e, n) dot.c K$) &~> #ceskE($e$, $E$, $J'$, $S$, $#loopContK (c, e) dot.c K$) && "LoopTrue" \
& quad "where" J' = J, #Loop (ell, n, K) \
#ceskC($#False$, $E$, $J$, $S$, $#loopK (c, e, n) dot.c K$) &~> #ceskC($#UnitVal$, $#truncate($E$, $n$)$, $J$, $S$, $K$) && "LoopFalse" \
#ceskC($#UnitVal$, $E$, $J_0$, $S$, $#loopContK (c, e) dot.c K'$) &~> #ceskE($c$, $E$, $J$, $S$, $#loopK (c, e, n) dot.c K'$) && "LoopCont" \
& quad "where" J_0 = J, #Loop (ell, n, K') \
#ceskC($#Skip$, $E$, $J$, $S$, $#scopeBodyK (e, n) dot.c K$) &~> #ceskE($e$, $E$, $J$, $S$, $#scopeExitK (n) dot.c K$) && "ScopeBody" \
#ceskC($v$, $E$, $J$, $S$, $#scopeExitK (n) dot.c K$) &~> #ceskC($v$, $#truncate($E$, $n$)$, $J$, $S$, $K$) && "ScopeExit" \
#ceskC($v$, $E$, $J$, $S$, $#argK (m, overline(v), (e, overline(e))) dot.c K$) &~> #ceskE($e$, $E$, $J$, $S$, $#argK (m, overline(v) dot.c v, overline(e)) dot.c K$) && "ArgNext" \
#ceskC($v$, $E$, $J$, $S$, $#argK (m, overline(v), epsilon) dot.c K$) &~> #ceskE($#body (m)$, $E_m$, $J'$, $S$, $#callK (E) dot.c K$) && "ArgDone" \
& quad "where" J' = J, #Method (ell, E, K) \
& quad E_m = #args (m)_1 := overline(w)_1, ..., #args (m)_n := overline(w)_n \
& quad overline(w) = overline(v), v \
#ceskC($v$, $E$, $J$, $S$, $#newK (C, overline(v), (e, overline(e))) dot.c K$) &~> #ceskE($e$, $E$, $J$, $S$, $#newK (C, overline(v) dot.c v, overline(e)) dot.c K$) && "NewNext" \
#ceskC($v$, $E$, $J$, $S$, $#newK (C, overline(v), epsilon) dot.c K$) &~> #ceskC($a$, $E$, $J$, $S'$, $K$) && "NewDone" \
& quad "where" S' = S, a -> C(f_1 := w_1, ..., f_n := w_n) \
& quad a in.not op("dom")(S) quad #fields (C) = (f_1 : tau_1, ..., f_n : tau_n) \
& quad overline(w) = overline(v), v \
#ceskC($#Skip$, $E$, $J_0$, $S$, $#callK (E') dot.c K'$) &~> #ceskC($#UnitVal$, $E'$, $J$, $S$, $K'$) && "ImplicitReturn" \
& quad "where" J_0 = J, #Method (ell, E', K')
$
$E[x |-> v]$ updates the rightmost binding of $x$ in $E$. BinOpL/BinOpR implement left-to-right evaluation of binary operators. IfTrue/IfFalse dispatch directly to the branch expression.

LoopTrue enters the body and pushes $#Loop (ell, n, K)$ onto $J$. LoopFalse truncates $E$ to the saved size $n$ and produces $#UnitVal$; $J$ is unchanged since it was never pushed for this iteration. LoopCont pops the loop entry from $J$ and re-evaluates the condition.

Return evaluates its expression via $#returnK (ell)$, then ReturnDone uses $J(ell)$ to find the method boundary directly, restoring the caller's environment $E'$ and producing the return value $v$ to the caller's continuation $K'$. $J'$ is $J$ with the method entry and everything above it removed. ImplicitReturn handles the case where a method body completes normally with $#Skip$: it pops the method entry from $J$, restores the caller's environment, and produces $#UnitVal$.

ScopeBody loads the trailing expression after the scope's statements complete. ScopeExit truncates $E$ to the saved size $n$, dropping scope-local bindings. $J$ is unaffected by scope blocks.

=== Initial and Terminal States

$
"Initial:" && #ceskE($#body ("main")$, $dot$, $#Method (ell_"main", dot, #halt)$, $dot$, $#callK (dot) dot.c #halt$) \
"Terminal:" && #ceskC($#Skip$, $E$, $J$, $S$, $#halt$)
$

The initial state pushes $#Method (ell_"main", dot, #halt)$ onto $J$ and wraps main's body in a $#callK (dot)$ frame so that both $#Return$ (via $J$) and ImplicitReturn (via $#callK$) are well-defined.

=== Continuation Typing

We write $#truncate($Gamma$, $n$)$ for the first $n$ bindings of $Gamma$, mirroring $#truncate($E$, $n$)$ on environments. We define well-typedness for continuations with two judgement forms mirroring the machine phases.

==== Expression Continuations

Expression continuations (#typeContE($Gamma$, $Delta$, $K$, $tau$)) _consume_ a value of type $tau$ in context $Gamma$ with jump context $Delta$.

#mathpar(
  proof-tree(rule(name: $#IfCondK$, typeContE($Gamma$, $Delta$, $#ifCondK (e_1, e_2) dot.c K$, $#Bool$), typeExpr($Gamma$, $Delta$, $e_1$, $tau$), typeExpr($Gamma$, $Delta$, $e_2$, $tau$), typeContE($Gamma$, $Delta$, $K$, $tau$))),
  proof-tree(rule(name: $#DeclK$, typeContE($Gamma$, $Delta$, $#declK (x : tau) dot.c K$, $tau$), typeContC($Gamma, x : tau$, $Delta$, $K$))),
  proof-tree(rule(name: $#AssignK$, typeContE($Gamma$, $Delta$, $#assignK (x) dot.c K$, $tau$), $Gamma(x) = tau$, typeContC($Gamma$, $Delta$, $K$))),

  proof-tree(rule(name: $#BinOpLK$, typeContE($Gamma$, $Delta$, $#binopLK (plus.o, e_2) dot.c K$, $tau_1$), $plus.o : tau_1 times tau_2 -> tau_3$, typeExpr($Gamma$, $Delta$, $e_2$, $tau_2$), typeContE($Gamma$, $Delta$, $K$, $tau_3$))),
  proof-tree(rule(name: $#BinOpRK$, typeContE($Gamma$, $Delta$, $#binopRK (plus.o, v_1) dot.c K$, $tau_2$), $plus.o : tau_1 times tau_2 -> tau_3$, $tack.r v_1 : tau_1$, typeContE($Gamma$, $Delta$, $K$, $tau_3$))),
  proof-tree(rule(name: $#UnOpK$, typeContE($Gamma$, $Delta$, $#unopK (plus.o) dot.c K$, $tau_1$), $plus.o : tau_1 -> tau_2$, typeContE($Gamma$, $Delta$, $K$, $tau_2$))),

  proof-tree(rule(name: "ReturnK", typeContE($Gamma$, $Delta$, $#returnK (ell) dot.c K$, $sigma$), $Delta(ell) = #Method (ell, sigma)$)),
  proof-tree(rule(name: "FieldK", typeContE($Gamma$, $Delta$, $#fieldK (f) dot.c K$, $C$), $f : tau in #fields (C)$, typeContE($Gamma$, $Delta$, $K$, $tau$))),
  proof-tree(rule(name: "ArgK", typeContE($Gamma$, $Delta$, $#argK (m, overline(v), overline(e)) dot.c K$, $tau_i$), $m : (tau_1, ..., tau_n) : sigma_m$, $tack.r overline(v)_j : tau_j "for" j < i$, typeExpr($Gamma$, $Delta$, $overline(e)_k$, $tau_(i+k)$), typeContE($Gamma$, $Delta$, $K$, $sigma_m$))),
  proof-tree(rule(name: "NewK", typeContE($Gamma$, $Delta$, $#newK (C, overline(v), overline(e)) dot.c K$, $tau_i$), $#fields (C) = (f_1 : tau_1, ..., f_n : tau_n)$, $tack.r overline(v)_j : tau_j "for" j < i$, typeExpr($Gamma$, $Delta$, $overline(e)_k$, $tau_(i+k)$), typeContE($Gamma$, $Delta$, $K$, $C$))),

  proof-tree(rule(name: $#LoopK$, typeContE($Gamma$, $Delta$, $#loopK (c, e, n) dot.c K$, $#Bool$), typeExpr($Gamma$, $Delta$, $c$, $#Bool$), typeExpr($Gamma$, $Delta, #Loop (ell)$, $e$, $#Unit$), typeContE($#truncate($Gamma$, $n$)$, $Delta$, $K$, $#Unit$))),
  proof-tree(rule(name: $#LoopContK$, typeContE($Gamma$, $Delta, #Loop (ell)$, $#loopContK (c, e) dot.c K$, $#Unit$), typeExpr($Gamma$, $Delta$, $c$, $#Bool$), typeExpr($Gamma$, $Delta, #Loop (ell)$, $e$, $#Unit$), typeContE($#truncate($Gamma$, $n$)$, $Delta$, $K$, $#Unit$))),

  proof-tree(rule(name: $#ScopeExitK$, typeContE($Gamma$, $Delta$, $#scopeExitK (n) dot.c K$, $tau$), typeContE($#truncate($Gamma$, $n$)$, $Delta$, $K$, $tau$))),
  proof-tree(rule(name: $#ExprStmtK$, typeContE($Gamma$, $Delta$, $#exprStmtK dot.c K$, $tau$), typeContC($Gamma$, $Delta$, $K$))),
)

$#IfCondK$ accepts $#Bool$ and types both branches as expressions under $Gamma | Delta$.

$#DeclK$ accepts a value of the declared type $tau$. $#AssignK$ accepts a value matching the variable's type.

For operators, the negative-position type threads through the evaluation chain: $#BinOpLK$ accepts $tau_1$, requires $e_2 : tau_2$, and the tail $K$ must accept $tau_3$. $#BinOpRK$ and $#UnOpK$ are similar.

ReturnK accepts $sigma$ and requires $Delta(ell) = #Method (ell, sigma)$. It has no premises about the tail $K$ since return jumps past it via $J(ell)$. FieldK accepts a class type $C$, looks up $f : tau in #fields (C)$, and requires the tail $K$ to accept $tau$.

ArgK accepts the type $tau_i$ of the current argument being evaluated and carries: the method signature, value typing for accumulated arguments, expression typing for remaining arguments, and an expression continuation for the tail accepting $sigma_m$ (the method's return type). The tail is an expression continuation because the method call is an expression producing $sigma_m$; ArgDone needs this to establish both JCohMethod and CallK. NewK is analogous for field initialisers.

$#LoopK$ is typed at $Delta$ (the condition's jump context, without the current loop). $#LoopContK$ is typed at $Delta, #Loop (ell)$ (the body's jump context). Both type the condition at $Delta$ and the body at $Delta, #Loop (ell)$. The tail $K$ is typed at $Delta$.

$#ScopeExitK$ accepts any type $tau$ and requires the tail at the truncated context. $#ExprStmtK$ accepts any value type and requires a statement continuation at $Gamma$.

==== Statement Continuations

Statement continuations (#typeContC($Gamma$, $Delta$, $K$)) accept $#Skip$ in context $Gamma$ with jump context $Delta$.

#mathpar(
  proof-tree(rule(name: $#HaltK$, typeContC($Gamma$, $Delta$, $#halt$))),
  proof-tree(rule(name: $#SeqK$, typeContC($Gamma$, $Delta$, $#seqK (s) dot.c K$), typeStmt($Delta$, $Gamma$, $s$, $Gamma'$), typeContC($Gamma'$, $Delta$, $K$))),
  proof-tree(rule(name: $#ScopeBodyK$, typeContC($Gamma$, $Delta$, $#scopeBodyK (e, n) dot.c K$), typeExpr($Gamma$, $Delta$, $e$, $tau$), typeContE($#truncate($Gamma$, $n$)$, $Delta$, $K$, $tau$))),
  proof-tree(rule(name: "CallK", typeContC($Gamma$, $Delta$, $#callK (E) dot.c K$), $#coh($E$, $Gamma'$)$, typeContE($Gamma'$, $Delta'$, $K$, $sigma_m$))),
)

CallK types the tail $K$ as an expression continuation accepting $sigma_m$ under the caller's context $Gamma'$ and the caller's jump context $Delta'$, recovered from the saved environment via coherence.

=== Environment-Context Coherence

We define _coherence_ between an environment and a context, written $#coh($E$, $Gamma$)$, inductively:

#mathpar(
  proof-tree(rule(name: "CohEmp", $#coh($dot$, $dot$)$)),
  proof-tree(rule(name: "CohBind", $#coh($E, x := v$, $Gamma, x : tau$)$, $#coh($E$, $Gamma$)$, $tack.r v : tau$)),
)

=== Jump Stack Coherence

We define _jump stack coherence_ between a jump stack and a jump context, written $#jcoh($J$, $Gamma$, $Delta$)$, inductively:

#mathpar(
  proof-tree(rule(name: "JCohEmp", $#jcoh($dot$, $Gamma$, $dot$)$)),
  proof-tree(rule(name: "JCohLoop", $#jcoh($J, #Loop (ell, n, K)$, $Gamma$, $Delta, #Loop (ell)$)$, $#jcoh($J$, $#truncate($Gamma$, $n$)$, $Delta$)$, typeContE($#truncate($Gamma$, $n$)$, $Delta$, $K$, $#Unit$))),
  proof-tree(rule(name: "JCohMethod", $#jcoh($J, #Method (ell, E', K')$, $Gamma$, $Delta, #Method (ell, sigma)$)$, $#jcoh($J$, $Gamma_"caller"$, $Delta_"caller"$)$, $#coh($E'$, $Gamma_"caller"$)$, typeContE($Gamma_"caller"$, $Delta_"caller"$, $K'$, $sigma$))),
)

Each loop entry in $J$ records a label, saved environment size, and exit continuation. The exit continuation is well-typed at the context and jump context from _after_ the loop exits. Each method entry records a label, the caller's saved environment, and the return continuation. The return continuation is well-typed at the caller's context and jump context with the method's return type $sigma$. This is what makes Break's and Return's preservation proofs direct: the target is already known to be well-typed.

==== Well Typed States

A machine state is _well-typed_ when coherence and jump stack coherence bridge the runtime state to a context $Gamma$ and jump context $Delta$ that type both the control and the continuation, and the store is well-typed:

#mathpar(
  proof-tree(rule(name: "WtExprE", $tack.r #ceskE($e$, $E$, $J$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $#jcoh($J$, $Gamma$, $Delta$)$, $tack.r S "ok"$, typeExpr($Gamma$, $Delta$, $e$, $tau$), typeContE($Gamma$, $Delta$, $K$, $tau$))),
  proof-tree(rule(name: "WtExprS", $tack.r #ceskE($s$, $E$, $J$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $#jcoh($J$, $Gamma$, $Delta$)$, $tack.r S "ok"$, typeStmt($Delta$, $Gamma$, $s$, $Gamma'$), typeContC($Gamma'$, $Delta$, $K$))),
  proof-tree(rule(name: "WtContV", $tack.r #ceskC($v$, $E$, $J$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $#jcoh($J$, $Gamma$, $Delta$)$, $tack.r S "ok"$, $tack.r v : tau$, typeContE($Gamma$, $Delta$, $K$, $tau$))),
  proof-tree(rule(name: "WtContS", $tack.r #ceskC($#Skip$, $E$, $J$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $#jcoh($J$, $Gamma$, $Delta$)$, $tack.r S "ok"$, typeContC($Gamma$, $Delta$, $K$))),
)

=== Properties

Given a well-typed program $P$ and a state reachable from the initial state:

- *Progress:* if $tack.r S "ok"$ and $S$ is not terminal, then there exists $S'$ such that $S ~> S'$. In particular, $#Break ell$ and $#Return ell thin e$ are sound: their typing rules require $Delta(ell)$ to be defined, which via jump stack coherence guarantees $J(ell)$ is defined.

- *Preservation:* if $tack.r S "ok"$ and $S ~> S'$, then $tack.r S' "ok"$.

- *Statement Execution Preserves Coherence:* if $#coh($E$, $Gamma$)$, #typeStmt($Delta$, $Gamma$, $s$, $Gamma'$), and $#ceskE($s$, $E$, $J$, $S$, $K$) #ms #ceskC($#Skip$, $E'$, $J$, $S'$, $K$)$, then $#coh($E'$, $Gamma'$)$.

- *Truncation Preserves Coherence:* if $#coh($E$, $Gamma$)$ and $n <= |E|$, then $#coh($#truncate($E$, $n$)$, $#truncate($Gamma$, $n$)$)$. This follows by definition of coherence.

- *Update Preserves Coherence:* if $#coh($E$, $Gamma$)$, $Gamma(x) = tau$, and $tack.r v : tau$, then $#coh($E[x |-> v]$, $Gamma$)$.

- *Jump Stack Coherence Monotonicity (Extension):* if $#jcoh($J$, $Gamma$, $Delta$)$, then $#jcoh($J$, $Gamma, x : tau$, $Delta$)$. By induction on jcoh: each JCohLoop premise references $#truncate($Gamma$, $n$)$ where $n <= |Gamma|$, and $#truncate($Gamma, x : tau$, $n$) = #truncate($Gamma$, $n$)$; similarly for JCohMethod. Needed for VarDeclDone.

- *Jump Stack Coherence under Truncation:* if $#jcoh($J$, $Gamma$, $Delta$)$ and all saved sizes in $J$ satisfy $n_i <= n$, then $#jcoh($J$, $#truncate($Gamma$, $n$)$, $Delta$)$. At ScopeExit, all $J$ entries predate the scope (loops and methods entered inside the scope have already exited), so their saved sizes are $<= n$. By induction on jcoh, truncating a truncation ($#truncate($#truncate($Gamma$, $n$)$, $n_i$) = #truncate($Gamma$, $n_i$)$ when $n_i <= n$) preserves each entry's premises.

- *Break Preserves Typing (via jcoh):* if $J(ell) = (n, K')$ with $#jcoh($J$, $Gamma$, $Delta$)$, then JCohLoop provides #typeContE($#truncate($Gamma$, $n$)$, $Delta'$, $K'$, $#Unit$) directly.

- *Return Preserves Typing (via jcoh):* if $J(ell) = (E', K')$ with $#jcoh($J$, $Gamma$, $Delta$)$, then JCohMethod provides $#coh($E'$, $Gamma_"caller"$)$ and #typeContE($Gamma_"caller"$, $Delta_"caller"$, $K'$, $sigma$) directly.

- *Allocation Preserves Store Typing:* if $tack.r S "ok"$ and $S' = S, a -> C(f_1 := v_1, ..., f_n := v_n)$ where $tack.r v_i : tau_i$ and $f_i : tau_i in #fields (C)$, then $tack.r S' "ok"$.

- *Determinacy:* each machine state has at most one successor (the transition relation is deterministic). Consequently, if the machine terminates, the terminal state is unique.
