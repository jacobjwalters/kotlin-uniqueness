#import "../defs.typ": *

= #Lbase

#Lbase is a simple typed language with expressions and statements. Conditionals, loops, and breaks are expressions; local variable scoping is managed by scope blocks. There are no classes, methods, modes, or lambdas.

== Syntax

$
  tau ::= & #Nat                        && "Naturals" \
        | & #Bool                       && "Booleans" \
        | & #Unit                       && "Unit" \
    e ::= & x                           && "Variable Access" \
        | & #True \
        | & #False \
        | & n in bb(N)                  && "Natural Numbers" \
        | & #UnitVal                    && "Unit Value" \
        | & e_1 plus.o e_2              && "Binary Operator" \
        | & plus.o (e)                  && "Unary Operator" \
        | & #If e #Then e_1 #Else e_2   && "If/Then/Else" \
        | & #While c brace.l e brace.r  && "While Loop" \
        | & #Break ell                  && "Loop Break (labelled)" \
        | & #Scope brace.l s; e brace.r && "Scope Block" \
    s ::= & #Var x : tau = e            && "(Mutable) Variable Declaration" \
        | & x = e                       && "Variable Assignment/Mutation" \
        | & s_1; s_2                    && "Statement Sequencing" \
        | & #Do e                       && "Expression Statement" \
$

A program $P$ is a statement $s$. $x$ represents an infinite set of variable names. While we write names as strings in this document, for formalisation purposes, we use de Bruijn indices. We write $#Break$ as shorthand for $#Break ell$ where $ell$ is the most recently bound loop label.

We write $plus.o$ to range over binary operators ${+, ∸, ==}$ and unary operators ${#IsZero}$. The meta-level function $#delta$ maps an operator and its argument value(s) to the result:

$
   #delta (+, n_1, n_2) & = n_1 + n_2 \
   #delta (∸, n_1, n_2) & = max(n_1 - n_2, 0) \
  #delta (==, v_1, v_2) & = cases(#True &"if" v_1 = v_2, #False &"otherwise") \
    #delta (#IsZero, n) & = cases(#True &"if" n = 0, #False &"otherwise")
$

== Typing Contexts
Typing contexts (hereafter contexts) in #Lbase are ordered, rightwards-growing lists of names and their associated types.

The grammar for contexts is as follows:

$
  Gamma ::= & dot            && "Empty" \
          | & Gamma, x : tau && "Variable Extension"
$

Lookup ($Gamma(x) = tau$) returns the type from the rightmost binding of $x$ in $Gamma$, permitting shadowing.

== Jump Contexts
A jump context $Delta$ is a stack tracking which non-local jump targets are lexically in scope. In #Lbase, the only jump targets are loops:

$
  Delta ::= & dot                && "Empty" \
          | & Delta, #Loop (ell) && "Loop boundary (labelled" ell")"
$

$#While$ extends $Delta$ with $#Loop (ell)$ for its body; $#Break ell$ requires that $ell$ is in $Delta$.

Lookup $Delta(ell)$ scans $Delta$ right-to-left for the entry with label $ell$:

$
   (Delta, #Loop (ell))(ell) & = #Loop (ell) \
  (Delta, #Loop (ell'))(ell) & = Delta(ell)  && quad ell' != ell
$

Lookup is partial; in particular, $dot (ell)$ is undefined. This allows us to enforce that $#Break$ is only well typed when inside a loop.

== Type System
Herein we discuss the type system of #Lbase.

=== Expression Types
Since expressions do not modify the typing context, we use the judgement form #typeExpr($Gamma$, $Delta$, $e$, $tau$) with no output context. The jump context $Delta$ tracks which non-local jumps are available.

#mathpar(
  proof-tree(rule(name: "TrueConst", typeExpr($Gamma$, $Delta$, $#True$, $#Bool$))),
  proof-tree(rule(name: "FalseConst", typeExpr($Gamma$, $Delta$, $#False$, $#Bool$))),
  proof-tree(rule(name: "NatConst", typeExpr($Gamma$, $Delta$, $n$, $#Nat$), $n in bb(N)$)),
  proof-tree(rule(name: "UnitConst", typeExpr($Gamma$, $Delta$, $#UnitVal$, $#Unit$))),

  proof-tree(rule(name: "VarAccess", typeExpr($Gamma$, $Delta$, $x$, $tau$), $Gamma(x) = tau$)),

  proof-tree(rule(
    name: "BinOp",
    typeExpr($Gamma$, $Delta$, $e_1 plus.o e_2$, $tau_3$),
    typeExpr($Gamma$, $Delta$, $e_1$, $tau_1$),
    typeExpr($Gamma$, $Delta$, $e_2$, $tau_2$),
    $plus.o : tau_1 times tau_2 -> tau_3$,
  )),
  proof-tree(rule(
    name: "UnOp",
    typeExpr($Gamma$, $Delta$, $plus.o (e)$, $tau_2$),
    typeExpr($Gamma$, $Delta$, $e$, $tau_1$),
    $plus.o : tau_1 -> tau_2$,
  )),

  proof-tree(rule(
    name: "IfExpr",
    typeExpr($Gamma$, $Delta$, $#If e #Then e_1 #Else e_2$, $tau$),
    typeExpr($Gamma$, $Delta$, $e$, $#Bool$),
    typeExpr($Gamma$, $Delta$, $e_1$, $tau$),
    typeExpr($Gamma$, $Delta$, $e_2$, $tau$),
  )),

  proof-tree(rule(
    name: "WhileExpr",
    typeExpr($Gamma$, $Delta$, $#While c brace.l e brace.r$, $#Unit$),
    typeExpr($Gamma$, $Delta$, $c$, $#Bool$),
    typeExpr($Gamma$, $Delta, #Loop (ell)$, $e$, $#Unit$),
  )),

  proof-tree(rule(name: "BreakExpr", typeExpr($Gamma$, $Delta$, $#Break ell$, $tau$), $Delta(ell) = #Loop (ell)$)),

  proof-tree(rule(
    name: "ScopeExpr",
    typeExpr($Gamma$, $Delta$, $#Scope brace.l s; e brace.r$, $tau$),
    typeStmt($Gamma$, $Delta$, $s$, $Gamma'$, $Delta$),
    typeExpr($Gamma'$, $Delta$, $e$, $tau$),
  )),
)

$#If$ expressions require both branches to have the same type $tau$; the condition must be $#Bool$. $#While$ expressions have type $#Unit$; the body is typed with $Delta$ extended by $#Loop (ell)$, making $#Break ell$ available inside the loop body. The condition is typed at $Delta$ (without $#Loop (ell)$), so $#Break$ in the condition targets an outer loop. $#Break ell$ has type $tau$ for any $tau$ since it never produces a value; the premise $Delta(ell) = #Loop (ell)$ ensures Break is only well typed when $ell$ is a valid loop label in $Delta$. $#Scope$ expressions run a sequence of statements $s$ (which may extend the context from $Gamma$ to $Gamma'$), then evaluate a trailing expression $e$ in the extended context $Gamma'$. The overall type is the type of $e$; the scope's local declarations are not visible outside.

The operator signature premise $plus.o : tau_1 times tau_2 -> tau_3$ (or $plus.o : tau_1 -> tau_2$ for unary) is grounded by the operator typing rules below.

=== Operator Typing

The meta-level function $#delta$ is typed by the following rules, which define the operator signatures referenced in both the expression typing and the continuation typing:

#mathpar(
  proof-tree(rule(name: "DeltaAdd", $tack.r #delta (+, v_1, v_2) : #Nat$, $tack.r v_1 : #Nat$, $tack.r v_2 : #Nat$)),
  proof-tree(rule(name: "DeltaSub", $tack.r #delta (∸, v_1, v_2) : #Nat$, $tack.r v_1 : #Nat$, $tack.r v_2 : #Nat$)),
  proof-tree(rule(
    name: "DeltaEq",
    $tack.r #delta (==, v_1, v_2) : #Bool$,
    $tack.r v_1 : tau$,
    $tack.r v_2 : tau$,
    $tau in {#Nat, #Bool}$,
  )),
  proof-tree(rule(name: "DeltaIsZero", $tack.r #delta (#IsZero, v) : #Bool$, $tack.r v : #Nat$)),
)

=== Statement Types
Since statements may update their context, we use a "small-step" typing judgement form #typeStmt($Gamma$, $Delta$, $s$, $Gamma'$, $Delta'$), where $Gamma$ and $Delta$ are the contexts before the statement and $Gamma'$ and $Delta'$ after. Statements never introduce new jump labels, so we merely thread $Delta$ through until we reach an expression.

#mathpar(
  proof-tree(rule(name: "VarDecl", typeStmt($Gamma$, $Delta$, $#Var x : tau = e$, $Gamma, x : tau$, $Delta$), typeExpr(
    $Gamma$,
    $Delta$,
    $e$,
    $tau$,
  ))),
  proof-tree(rule(name: "VarAssign", typeStmt($Gamma$, $Delta$, $x = e$, $Gamma$, $Delta$), $Gamma(x) = tau$, typeExpr(
    $Gamma$,
    $Delta$,
    $e$,
    $tau$,
  ))),

  proof-tree(rule(
    name: "Seq",
    typeStmt($Gamma$, $Delta$, $s_1; s_2$, $Gamma''$, $Delta''$),
    typeStmt($Gamma$, $Delta$, $s_1$, $Gamma'$, $Delta'$),
    typeStmt($Gamma'$, $Delta'$, $s_2$, $Gamma''$, $Delta''$),
  )),

  proof-tree(rule(name: "ExprStmt", typeStmt($Gamma$, $Delta$, $#Do e$, $Gamma$, $Delta$), typeExpr(
    $Gamma$,
    $Delta$,
    $e$,
    $tau$,
  ))),
)

Variable declarations check the initialiser expression against the declared type, then extend the context, possibly shadowing an existing binding.

Variable assignment requires that $x : tau$ is present somewhere in the context via membership lookup. The expression $e$ is typed under the same context $Gamma$, which includes $x$; this allows self mutation (such as $x = x + 1$). The output context is unchanged.

Sequencing threads the context produced as the output of the first statement into the input of the second statement.

In order to admit $#If$, $#While$ and $#Break$ in statement positions, we use expression statements ($#Do e$) to evaluate an expression and discard the result. Since expressions do not modify the typing context, the output context is $Gamma$ (unchanged).

=== Properties

- *Output Context Determinacy:* if #typeStmt($Gamma$, $Delta$, $s$, $Gamma_1$, $Delta_1$) and #typeStmt($Gamma$, $Delta$, $s$, $Gamma_2$, $Delta_2$), then $Gamma_1 = Gamma_2$ and $Delta_1 = Delta_2$.

- *Expression Weakening (Extension):* if #typeExpr($Gamma$, $Delta$, $e$, $tau$) and $Gamma$ is a suffix of $Gamma'$, then #typeExpr($Gamma'$, $Delta$, $e$, $tau$).

- *Expression Weakening (Permutation):* if #typeExpr($Gamma$, $Delta$, $e$, $tau$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeExpr($Gamma'$, $Delta$, $e$, $tau$).

- *Statement Weakening (Extension):* if #typeStmt($Gamma$, $Delta$, $s$, $Gamma, Gamma'$, $Delta'$) and $Gamma$ is a suffix of $Gamma'$, then #typeStmt($Gamma'$, $Delta$, $s$, $Gamma', Gamma'$, $Delta'$).

- *Statement Weakening (Permutation):* if #typeStmt($Gamma$, $Delta$, $s$, $Gamma, Gamma'$, $Delta'$) and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then #typeStmt($Gamma'$, $Delta$, $s$, $Gamma', Gamma'$, $Delta'$).

Note that in the statement weakening properties, $Gamma, Gamma'$ refers to $Gamma$ concatenated with another context $Gamma'$. We can't extend by a single variable as in the expression weakening rules since compound statements may extend $Gamma$ with any number of new variables.

- *Expression $Delta$-Weakening (Extension):* if #typeExpr($Gamma$, $Delta$, $e$, $tau$) and $Delta$ is a suffix of $Delta'$, then #typeExpr($Gamma$, $Delta'$, $e$, $tau$). Adding jump targets to $Delta$ does not invalidate existing typing.

- *Expression $Delta$-Weakening (Permutation):* if #typeExpr($Gamma$, $Delta$, $e$, $tau$) and for all $ell in op("dom")(Delta)$, $Delta(ell) = Delta'(ell)$, then #typeExpr($Gamma$, $Delta'$, $e$, $tau$). Typing rules access $Delta$ only via $Delta(ell)$ lookup, which is preserved by the permutation condition.

- *Statement $Delta$-Weakening (Extension):* if #typeStmt($Gamma$, $Delta$, $s$, $Gamma'$, $Delta'$) and $Delta$ is a suffix of $Delta''$, then #typeStmt($Gamma$, $Delta''$, $s$, $Gamma'$, $Delta''$).

- *Statement $Delta$-Weakening (Permutation):* if #typeStmt($Gamma$, $Delta$, $s$, $Gamma'$, $Delta'$) and for all $ell in op("dom")(Delta)$, $Delta(ell) = Delta''(ell)$, then #typeStmt($Gamma$, $Delta''$, $s$, $Gamma'$, $Delta''$).


== Evaluation
Evaluation of an #Lbase program begins with a program statement $s$. We define the operational semantics as a CEK machine; a state machine that makes evaluation order explicit via a continuation stack. We also introduce a run-time language.

=== Run-time Language
The CEK machine operates on a run-time language that extends the source syntax with run-time-only forms. This language is a strict extension of the source language; it has one additional syntactic construct $#Skip$, with a corresponding typing rule. We should show all of the properties of the source language's type system hold for the run-time language's type system too.

==== Values
Values are fully evaluated expressions:

$
  v ::= & #True | & #False | & n in bb(N) | & #UnitVal
$

We write $tack.r v : tau$ for value typing: $tack.r #True : #Bool$, $tack.r #False : #Bool$, $tack.r n : #Nat$ for $n in bb(N)$, and $tack.r #UnitVal : #Unit$.

==== Completion Marker
$#Skip$ is a run-time-only completion marker indicating that a statement has been fully executed. It does not appear in the source program. Since $#Skip$ can appear in the control during evaluation, it needs a typing rule:

#mathpar(
  proof-tree(rule(name: "Skip", typeStmt($Gamma$, $Delta$, $#Skip$, $Gamma$, $Delta$))),
)

$#Skip$ preserves the context unchanged.

=== Machine State
The machine state is a 4-tuple $#cek($C$, $E$, $J$, $K$)$. The machine operates in one of two phases, indicated by a subscript on the state. In _Expr_ mode ($#cekE($C$, $E$, $J$, $K$)$), the control holds a source expression or statement to be decomposed. In _Cont_ mode ($#cekC($C$, $E$, $J$, $K$)$), the control holds a value or completion marker and the machine dispatches on the continuation.

#table(
  columns: (auto, auto, 1fr),
  align: (center, left, left),
  table.header([*Component*], [*Name*], [*Description*]),
  [$C$], [Control], [The current expression, statement, value, or completion marker being processed],
  [$E$], [Environment], [Ordered map from variables to values],
  [$J$], [Jump stack], [Stack of jump targets mirroring $Delta$],
  [$K$], [Continuation], [Stack of continuations],
)

==== Control ($C$)
The control component holds whatever syntactic construct the machine is currently processing:

$
  C ::= & e     && "Source expression (to evaluate)" \
      | & s     && "Source statement (to execute)" \
      | & v     && "Value (expression result)" \
      | & #Skip && "Statement completed"
$

Expression evaluation terminates with a value $v$ in the control. Statement execution terminates with $#Skip$.

==== Environment ($E$)
$
  E ::= & dot       && "Empty" \
      | & E, x := v && "Variable binding"
$

The environment is an ordered, rightwards-growing list of variable-to-value bindings interspersed with labelled scope markers. Lookup and update scan right-to-left, skipping scope markers. Lookup finds the rightmost binding for a given variable name (permitting shadowing). Update ($E[x |-> v]$) modifies the rightmost binding of $x$ in place.

The environment is extended when variables are declared ($#Var x : tau = e$ adds $x := v$ to the rightmost position, where $v$ is the value of $e$) and individual bindings are updated on assignment ($x = v$ updates the rightmost $x$). We write $|E|$ for the length (number of bindings) of $E$. The operation $#truncate($E$, $n$)$ returns the first $n$ bindings of $E$, dropping everything from position $n + 1$ onward. Scoping constructs record $|E|$ at entry and truncate back to that size at exit.

==== Jump Stack ($J$)
The jump stack is the runtime mirror of the jump context $Delta$. Each entry stores a loop label, the saved environment size, and the continuation to restore on break:

$
  J ::= & dot                  && "Empty" \
      | & J, #Loop (ell, n, K) && "Loop: label" ell", env size" n", exit continuation" K
$

Lookup $J(ell) = (n, K)$ scans $J$ right-to-left for the entry with label $ell$, returning the saved environment size and exit continuation. As with lookup for $Delta$, $dot (ell)$ is undefined.

$J$ is pushed at LoopTrue (entering a loop body) and popped at LoopCont (re-entering the condition) or Break (exiting the loop). During condition evaluation, $J$ does not contain the current loop's entry.

==== Continuation ($K$)
The continuation is a stack of frames that describes what to do after the current control finishes:

$
  K ::= & #halt                          && "Program complete" \
      | & #ifCondK (e_1, e_2) dot.c K    && "After evaluating condition, branch to expression" \
      | & #declK (x : tau) dot.c K       && "After evaluating initialiser of type" tau ", bind" x "in" E \
      | & #assignK (x) dot.c K           && "After evaluating RHS, assign to" x "in" E \
      | & #seqK (s) dot.c K              && "After first statement completes, continue with" s \
      | & #binopLK (plus.o, e_2) dot.c K && "After evaluating left operand of" plus.o", evaluate" e_2 \
      | & #binopRK (plus.o, v_1) dot.c K && "After evaluating right operand of" plus.o", apply to" v_1 \
      | & #unopK (plus.o) dot.c K        && "After evaluating operand of unary" plus.o", apply" \
      | & #loopK (c, e, n) dot.c K       && "While condition: body" e ", saved env size" n \
      | & #loopContK (c, e) dot.c K      && "After loop body, re-evaluate condition" \
      | & #scopeBodyK (e, n) dot.c K     && "After scope statements, evaluate trailing expr" e \
      | & #scopeExitK (n) dot.c K        && "After trailing expr, truncate env to size" n \
      | & #exprStmtK dot.c K             && "After expression evaluates, discard value"
$

- $#halt$ signals that the program is finished; a terminal state is $#cekC($#Skip$, $E$, $J$, $#halt$)$.
- $#ifCondK (e_1, e_2)$ waits for the condition to evaluate, then dispatches to the appropriate branch expression.
- $#declK (x : tau)$ waits for the initialiser expression to evaluate to a value $v$ of type $tau$, then extends the environment with $x := v$.
- $#assignK (x)$ waits for the RHS expression to evaluate to a value $v$, then updates the environment with $E[x |-> v]$.
- $#seqK (s)$ waits for the first statement to complete, then loads $s$ into the control.
- $#binopLK (plus.o, e_2)$ waits for the left operand to evaluate to $v_1$, then begins evaluating $e_2$ with $#binopRK (plus.o, v_1)$ on the stack.
- $#binopRK (plus.o, v_1)$ waits for the right operand to evaluate to $v_2$, then computes $#delta (plus.o, v_1, v_2)$.
- $#unopK (plus.o)$ waits for the operand to evaluate to $v$, then computes $#delta (plus.o, v)$.
- $#loopK (c, e, n)$ receives the condition value: $#True$ enters the body $e$ via $#loopContK$; $#False$ truncates the environment to size $n$ and produces $#UnitVal$. The saved size $n$ records $|E|$ at while entry and is needed here because LoopFalse fires during condition evaluation, before $J$ has been pushed with this loop's entry.
- $#loopContK (c, e)$ receives $#UnitVal$ after the body completes, then re-evaluates $c$ with $#loopK$ on the continuation.
- $#scopeBodyK (e, n)$ waits for the scope's statements to complete ($#Skip$), then evaluates the trailing expression $e$. The saved size $n$ records $|E|$ at scope entry.
- $#scopeExitK (n)$ waits for the trailing expression to produce a value, then truncates the environment to size $n$, dropping scope-local bindings.
- $#exprStmtK$ waits for an expression to produce a value, discards it, and produces $#Skip$.

=== Transition Rules
We define a multi-step judgement $ms$ in the usual way.

==== Expr
$
  #cekE($v$, $E$, $J$, $K$) &~> #cekC($v$, $E$, $J$, $K$) && "Val" \
  #cekE($x$, $E$, $J$, $K$) &~> #cekC($E(x)$, $E$, $J$, $K$) && "Var" \
  #cekE($#Var x : tau = e$, $E$, $J$, $K$) &~> #cekE($e$, $E$, $J$, $#declK (x : tau) dot.c K$) && "VarDecl" \
  #cekE($x = e$, $E$, $J$, $K$) &~> #cekE($e$, $E$, $J$, $#assignK (x) dot.c K$) && "Assign" \
  #cekE($s_1 ; s_2$, $E$, $J$, $K$) &~> #cekE($s_1$, $E$, $J$, $#seqK (s_2) dot.c K$) && "Seq" \
  #cekE($#Do e$, $E$, $J$, $K$) &~> #cekE($e$, $E$, $J$, $#exprStmtK dot.c K$) && "ExprStmt" \
  #cekE($e_1 plus.o e_2$, $E$, $J$, $K$) &~> #cekE($e_1$, $E$, $J$, $#binopLK (plus.o, e_2) dot.c K$) && "BinOp" \
  #cekE($#IsZero (e)$, $E$, $J$, $K$) &~> #cekE($e$, $E$, $J$, $#unopK (#IsZero) dot.c K$) && "UnOp" \
  #cekE($#If e #Then e_1 #Else e_2$, $E$, $J$, $K$) &~> #cekE($e$, $E$, $J$, $#ifCondK (e_1, e_2) dot.c K$) && "If" \
  #cekE($#While c brace.l e brace.r$, $E$, $J$, $K$) &~> #cekE($c$, $E$, $J$, $#loopK (c, e, |E|) dot.c K$) && "While" \
  #cekE($#Break ell$, $E$, $J$, $K$) &~> #cekC($#UnitVal$, $#truncate($E$, $n$)$, $J'$, $K'$) && "Break" \
  & quad "where" J(ell) = (n, K') \
  #cekE($#Scope brace.l s ; e brace.r$, $E$, $J$, $K$) &~> #cekE($s$, $E$, $J$, $#scopeBodyK (e, |E|) dot.c K$) && "Scope"
$
Val transitions a source value expression ($#True$, $#False$, $n$, $#UnitVal$) into Cont mode. Var looks up the rightmost binding of $x$ in $E$.

The remaining rules decompose a compound form by pushing a continuation frame. BinOp evaluates the left operand first (left-to-right evaluation order). UnOp evaluates its single operand. If evaluates the condition; the branches are expressions. While records $|E|$ in $#loopK$ for use by LoopFalse. Break looks up $J(ell)$ to find the target loop's saved environment size $n$ and exit continuation $K'$, truncates $E$ to $n$, and produces $#UnitVal$. $J'$ is $J$ with the entry for $ell$ and all entries above it removed. Scope records $|E|$ and evaluates the statement body.

==== Cont
$
  #cekC($#True$, $E$, $J$, $#ifCondK (e_1, e_2) dot.c K$) &~> #cekE($e_1$, $E$, $J$, $K$) && "IfTrue" \
  #cekC($#False$, $E$, $J$, $#ifCondK (e_1, e_2) dot.c K$) &~> #cekE($e_2$, $E$, $J$, $K$) && "IfFalse" \
  #cekC($v$, $E$, $J$, $#declK (x : tau) dot.c K$) &~> #cekC($#Skip$, $E, x := v$, $J$, $K$) && "VarDeclDone" \
  #cekC($v$, $E$, $J$, $#assignK (x) dot.c K$) &~> #cekC($#Skip$, $E[x |-> v]$, $J$, $K$) && "AssignDone" \
  #cekC($#Skip$, $E$, $J$, $#seqK (s_2) dot.c K$) &~> #cekE($s_2$, $E$, $J$, $K$) && "SeqDone" \
  #cekC($v$, $E$, $J$, $#exprStmtK dot.c K$) &~> #cekC($#Skip$, $E$, $J$, $K$) && "ExprStmtDone" \
  #cekC($v_1$, $E$, $J$, $#binopLK (plus.o, e_2) dot.c K$) &~> #cekE($e_2$, $E$, $J$, $#binopRK (plus.o, v_1) dot.c K$) && "BinOpL" \
  #cekC($v_2$, $E$, $J$, $#binopRK (plus.o, v_1) dot.c K$) &~> #cekC($#delta (plus.o, v_1, v_2)$, $E$, $J$, $K$) && "BinOpR" \
  #cekC($v$, $E$, $J$, $#unopK (plus.o) dot.c K$) &~> #cekC($#delta (plus.o, v)$, $E$, $J$, $K$) && "UnOpDone" \
  #cekC($#True$, $E$, $J$, $#loopK (c, e, n) dot.c K$) &~> #cekE($e$, $E$, $J, #Loop (ell, n, K)$, $#loopContK (c, e) dot.c K$) && "LoopTrue" \
  #cekC($#False$, $E$, $J$, $#loopK (c, e, n) dot.c K$) &~> #cekC($#UnitVal$, $#truncate($E$, $n$)$, $J$, $K$) && "LoopFalse" \
  #cekC($#UnitVal$, $E$, $J, #Loop (ell, n, K')$, $#loopContK (c, e) dot.c K'$) &~> #cekE($c$, $E$, $J$, $#loopK (c, e, n) dot.c K'$) && "LoopCont" \
  #cekC($#Skip$, $E$, $J$, $#scopeBodyK (e, n) dot.c K$) &~> #cekE($e$, $E$, $J$, $#scopeExitK (n) dot.c K$) && "ScopeBody" \
  #cekC($v$, $E$, $J$, $#scopeExitK (n) dot.c K$) &~> #cekC($v$, $#truncate($E$, $n$)$, $J$, $K$) && "ScopeExit"
$
$E[x |-> v]$ updates the rightmost binding of $x$ in $E$. BinOpL/BinOpR implement left-to-right evaluation of binary operators. IfTrue/IfFalse dispatch directly to the branch expression.

LoopTrue enters the body and pushes $#Loop (ell, n, K)$ onto $J$, recording the loop's label, the saved environment size, and the exit continuation $K$. During body evaluation, $J$ contains this loop's entry so that $#Break ell$ can look it up directly. LoopFalse truncates $E$ to the saved size $n$ and produces $#UnitVal$; $J$ is unchanged since it was never pushed for this iteration. LoopCont pops the loop entry from $J$ and re-evaluates the condition; at this point $J$ no longer contains the current loop, matching the typing where the condition is at $Delta$ (not $Delta, #Loop (ell)$).

ScopeBody loads the trailing expression after the scope's statements complete. ScopeExit truncates $E$ to the saved size $n$, dropping scope-local bindings, and passes the value through. $J$ is unaffected by scope blocks.

=== Initial and Terminal States

$
   "Initial:" && #cekE($s$, $dot$, $dot$, $#halt$) && "where" s "is the program" \
  "Terminal:" && #cekC($#Skip$, $E$, $J$, $#halt$)
$

=== Continuation Typing

We write $#truncate($Gamma$, $n$)$ for the first $n$ bindings of $Gamma$, mirroring $#truncate($E$, $n$)$ on environments. We define well typedness for continuations with two judgement forms mirroring the machine phases.

==== Expression Continuations

Expression continuations (#typeContE($Gamma$, $Delta$, $K$, $tau$)) _consume_ a value of type $tau$ in context $Gamma$ with jump context $Delta$.

#mathpar(
  proof-tree(rule(
    name: $#IfCondK$,
    typeContE($Gamma$, $Delta$, $#ifCondK (e_1, e_2) dot.c K$, $#Bool$),
    typeExpr($Gamma$, $Delta$, $e_1$, $tau$),
    typeExpr($Gamma$, $Delta$, $e_2$, $tau$),
    typeContE($Gamma$, $Delta$, $K$, $tau$),
  )),

  proof-tree(rule(name: $#DeclK$, typeContE($Gamma$, $Delta$, $#declK (x : tau) dot.c K$, $tau$), typeContC(
    $Gamma, x : tau$,
    $Delta$,
    $K$,
  ))),
  proof-tree(rule(
    name: $#AssignK$,
    typeContE($Gamma$, $Delta$, $#assignK (x) dot.c K$, $tau$),
    $Gamma(x) = tau$,
    typeContC($Gamma$, $Delta$, $K$),
  )),

  proof-tree(rule(
    name: $#BinOpLK$,
    typeContE($Gamma$, $Delta$, $#binopLK (plus.o, e_2) dot.c K$, $tau_1$),
    $plus.o : tau_1 times tau_2 -> tau_3$,
    typeExpr($Gamma$, $Delta$, $e_2$, $tau_2$),
    typeContE($Gamma$, $Delta$, $K$, $tau_3$),
  )),
  proof-tree(rule(
    name: $#BinOpRK$,
    typeContE($Gamma$, $Delta$, $#binopRK (plus.o, v_1) dot.c K$, $tau_2$),
    $plus.o : tau_1 times tau_2 -> tau_3$,
    $tack.r v_1 : tau_1$,
    typeContE($Gamma$, $Delta$, $K$, $tau_3$),
  )),
  proof-tree(rule(
    name: $#UnOpK$,
    typeContE($Gamma$, $Delta$, $#unopK (plus.o) dot.c K$, $tau_1$),
    $plus.o : tau_1 -> tau_2$,
    typeContE($Gamma$, $Delta$, $K$, $tau_2$),
  )),

  proof-tree(rule(
    name: $#LoopK$,
    typeContE($Gamma$, $Delta$, $#loopK (c, e, n) dot.c K$, $#Bool$),
    typeExpr($Gamma$, $Delta$, $c$, $#Bool$),
    typeExpr($Gamma$, $Delta, #Loop (ell)$, $e$, $#Unit$),
    typeContE($#truncate($Gamma$, $n$)$, $Delta$, $K$, $#Unit$),
  )),
  proof-tree(rule(
    name: $#LoopContK$,
    typeContE($Gamma$, $Delta, #Loop (ell)$, $#loopContK (c, e) dot.c K$, $#Unit$),
    typeExpr($Gamma$, $Delta$, $c$, $#Bool$),
    typeExpr($Gamma$, $Delta, #Loop (ell)$, $e$, $#Unit$),
    typeContE($#truncate($Gamma$, $n$)$, $Delta$, $K$, $#Unit$),
  )),

  proof-tree(rule(name: $#ScopeExitK$, typeContE($Gamma$, $Delta$, $#scopeExitK (n) dot.c K$, $tau$), typeContE(
    $#truncate($Gamma$, $n$)$,
    $Delta$,
    $K$,
    $tau$,
  ))),
  proof-tree(rule(name: $#ExprStmtK$, typeContE($Gamma$, $Delta$, $#exprStmtK dot.c K$, $tau$), typeContC(
    $Gamma$,
    $Delta$,
    $K$,
  ))),
)

$#IfCondK$ accepts $#Bool$ and types both branches as expressions under $Gamma | Delta$.

$#DeclK$ accepts a value of the declared type $tau$. $#AssignK$ accepts a value matching the variable's type.

For operators, the negative-position type threads through the evaluation chain: $#BinOpLK$ accepts $tau_1$, requires $e_2 : tau_2$, and the tail $K$ must accept $tau_3$. $#BinOpRK$ and $#UnOpK$ are similar.

$#LoopK$ is typed at $Delta$ (the condition's jump context, without the current loop). $#LoopContK$ is typed at $Delta, #Loop (ell)$ (the body's jump context, with the current loop). Both type the condition at $Delta$ and the body at $Delta, #Loop (ell)$. The tail $K$ after the loop exits is typed at $Delta$.

$#ScopeExitK$ accepts a value of any type $tau$ and requires the tail $K$ to accept $tau$ at the truncated context. $#ExprStmtK$ accepts any value type and requires the tail $K$ to be a statement continuation at $Gamma$.

==== Statement Continuations

Statement continuations (#typeContC($Gamma$, $Delta$, $K$)) accept $#Skip$ in context $Gamma$ with jump context $Delta$.

#mathpar(
  proof-tree(rule(name: $#HaltK$, typeContC($Gamma$, $Delta$, $#halt$))),
  proof-tree(rule(
    name: $#SeqK$,
    typeContC($Gamma$, $Delta$, $#seqK (s) dot.c K$),
    typeStmt($Gamma$, $Delta$, $s$, $Gamma'$, $Delta$),
    typeContC($Gamma'$, $Delta$, $K$),
  )),
  proof-tree(rule(
    name: $#ScopeBodyK$,
    typeContC($Gamma$, $Delta$, $#scopeBodyK (e, n) dot.c K$),
    typeExpr($Gamma$, $Delta$, $e$, $tau$),
    typeContE($#truncate($Gamma$, $n$)$, $Delta$, $K$, $tau$),
  )),
)

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
  proof-tree(rule(
    name: "JCohLoop",
    $#jcoh($J, #Loop (ell, n, K)$, $Gamma$, $Delta, #Loop (ell)$)$,
    $#jcoh($J$, $#truncate($Gamma$, $n$)$, $Delta$)$,
    typeContE($#truncate($Gamma$, $n$)$, $Delta$, $K$, $#Unit$),
  )),
)

Each loop entry in $J$ records a label $ell$, a saved environment size $n$, and an exit continuation $K$. The exit continuation is well typed at the context and jump context from _after_ the loop exits (i.e. $#truncate($Gamma$, $n$)$ and $Delta$ without $#Loop (ell)$). This is what makes Break's preservation proof direct: the target $K$ is already known to be well typed.

==== Well Typed States

A machine state is _well typed_ when coherence and jump stack coherence bridge the runtime state to a context $Gamma$ and jump context $Delta$ that type both the control and the continuation:

#mathpar(
  proof-tree(rule(
    name: "WtExprE",
    $tack.r #cekE($e$, $E$, $J$, $K$) "ok"$,
    $#coh($E$, $Gamma$)$,
    $#jcoh($J$, $Gamma$, $Delta$)$,
    typeExpr($Gamma$, $Delta$, $e$, $tau$),
    typeContE($Gamma$, $Delta$, $K$, $tau$),
  )),
  proof-tree(rule(
    name: "WtExprS",
    $tack.r #cekE($s$, $E$, $J$, $K$) "ok"$,
    $#coh($E$, $Gamma$)$,
    $#jcoh($J$, $Gamma$, $Delta$)$,
    typeStmt($Gamma$, $Delta$, $s$, $Gamma'$, $Delta$),
    typeContC($Gamma'$, $Delta$, $K$),
  )),
  proof-tree(rule(
    name: "WtContV",
    $tack.r #cekC($v$, $E$, $J$, $K$) "ok"$,
    $#coh($E$, $Gamma$)$,
    $#jcoh($J$, $Gamma$, $Delta$)$,
    $tack.r v : tau$,
    typeContE($Gamma$, $Delta$, $K$, $tau$),
  )),
  proof-tree(rule(
    name: "WtContS",
    $tack.r #cekC($#Skip$, $E$, $J$, $K$) "ok"$,
    $#coh($E$, $Gamma$)$,
    $#jcoh($J$, $Gamma$, $Delta$)$,
    typeContC($Gamma$, $Delta$, $K$),
  )),
)

=== Properties

- *Progress:* if $tack.r S "ok"$ and $S$ is not terminal, then there exists $S'$ such that $S ~> S'$. In particular, the $#Break ell$ case is sound: BreakExpr requires $Delta(ell) = #Loop (ell)$, which via jump stack coherence guarantees $J(ell)$ is defined.

- *Preservation:* if $tack.r S "ok"$ and $S ~> S'$, then $tack.r S' "ok"$.

- *Statement Execution Preserves Coherence:* if $#coh($E$, $Gamma$)$, #typeStmt($Gamma$, $Delta$, $s$, $Gamma'$, $Delta$), and $#cekE($s$, $E$, $J$, $K$) #ms #cekC($#Skip$, $E'$, $J$, $K$)$, then $#coh($E'$, $Gamma'$)$.

- *Truncation Preserves Coherence:* if $#coh($E$, $Gamma$)$ and $n <= |E|$, then $#coh($#truncate($E$, $n$)$, $#truncate($Gamma$, $n$)$)$. This follows by definition of coherence.

- *Update Preserves Coherence:* if $#coh($E$, $Gamma$)$, $Gamma(x) = tau$, and $tack.r v : tau$, then $#coh($E[x |-> v]$, $Gamma$)$.

- *Jump Stack Coherence Monotonicity (Extension):* if $#jcoh($J$, $Gamma$, $Delta$)$, then $#jcoh($J$, $Gamma, x : tau$, $Delta$)$. By induction on jcoh: each JCohLoop premise references $#truncate($Gamma$, $n$)$ where $n <= |Gamma|$, and $#truncate($Gamma, x : tau$, $n$) = #truncate($Gamma$, $n$)$. Needed for VarDeclDone.

- *Jump Stack Coherence under Truncation:* if $#jcoh($J$, $Gamma$, $Delta$)$ and all saved sizes in $J$ satisfy $n_i <= n$, then $#jcoh($J$, $#truncate($Gamma$, $n$)$, $Delta$)$. At ScopeExit, all $J$ entries predate the scope (loops entered inside the scope have already exited), so their saved sizes are $<= n$. By induction on jcoh, truncating a truncation preserves each entry's premises.

- *Expression Evaluation Preserves Environment Size:* if $#coh($E$, $Gamma$)$, #typeExpr($Gamma$, $Delta$, $e$, $tau$), and $#cekE($e$, $E$, $J$, $K$) #ms #cekC($v$, $E'$, $J'$, $K$)$, then $|E'| = |E|$.

- *Break Preserves Typing (via jcoh):* if $tack.r #cek($#Break ell$, $E$, $J$, $K$) "ok"$ with $#jcoh($J$, $Gamma$, $Delta$)$ and $J(ell) = (n, K')$, then $#coh($#truncate($E$, $n$)$, $#truncate($Gamma$, $n$)$)$, $#jcoh($J'$, $#truncate($Gamma$, $n$)$, $Delta'$)$, and #typeContE($#truncate($Gamma$, $n$)$, $Delta'$, $K'$, $#Unit$). This follows directly from JCohLoop.

- *Determinacy:* each machine state has at most one successor (the transition relation is deterministic). Consequently, if the machine terminates, the terminal state is unique.
