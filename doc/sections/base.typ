#import "../defs.typ": *

= #Lbase

#Lbase is a simple typed language consisting of sequentially ordered statements with classes and method calls. There are no modes, and no lambdas

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
Morally, typing contexts (hereafter contexts) in #Lbase are ordered, rightwards-growing lists of names and their associated types, split by control flow delimiters to denote the scopes in which variables are introduced. In particular, we have a (global) list of methods and associated method types#footnote[Since we don't have object-level function types, a method type is a list of argument types, paired with a return type, writ $m : (tau_1, tau_2, ...): sigma$], paired with a list of either variable names and their associated types, or control flow delimiters.

Since method declarations are top level, we omit them from our treatment of contexts, and assume that the expression/statement theories are parameterised by a particular context of methods and method types. Methods are typed in empty contexts; the current return type is tracked as part of the statement typing judgement.

The grammar for contexts is as follows:

$
Gamma ::=& dot && "Empty" \
  |& Gamma, x : tau && "Variable Extension" \
  |& Gamma, diamond_i && "If Delimiter" \
  |& Gamma, diamond_w && "Loop Delimiter"
$

Control flow delimiters are introduced when entering the branches of an if statement ($diamond_i$) or the body of a while loop ($diamond_w$), and are removed either at the end of the branch/body, or during early return.

In order to model heap allocations, we have a second typing context $Delta$ for things on the heap:
$
Delta ::=& dot |& Delta, a : tau
$

=== Well Formed Contexts
We introduce a judgement $Gamma #ctx$, and $Delta #ctx$ to denote well formed contexts (WFCs) and heaps (WFHs). WFCs/WFHs are defined inductively:

#mathpar(
  proof-tree(rule(name: "CtxEmp", $dot #ctx$)),
  proof-tree(rule(name: "CtxVarExt", $Gamma, x : tau #ctx$, $x in.not Gamma$, $Gamma #ctx$)),
  proof-tree(rule(name: "CtxIfDelimiter", $Gamma, diamond_i #ctx$, $Gamma #ctx$)),
  proof-tree(rule(name: "CtxLoopDelimiter", $Gamma, diamond_w #ctx$, $Gamma #ctx$))
)

#mathpar(
  proof-tree(rule(name: "HeapCtxEmp", $dot #ctx$)),
  proof-tree(rule(name: "HeapCtxExt", $Delta, a : tau #ctx$, $a in.not Delta$, $Delta #ctx$)),
)

$x in.not Gamma$ is bookkeeping for ensuring all names are distinct, and isn't strictly needed. Membership checking and lookup are defined in the usual way.

#jq[Do we want to allow name reuse (and thus shadowing)? How will this interact with borrowing later on? A: we need to investigate what happens with shadowing in Viper]

=== Removal
When typing a $#Break$ statement, we need to strip all bindings introduced since the enclosing loop was entered. To do this, we define a recursive function $drop$ that walks backwards through the context, removing variable bindings and if-delimiters until it reaches the nearest loop delimiter $diamond_w$:

$
  drop (Gamma, diamond_w)  &= Gamma, diamond_w \
  drop (Gamma, x : tau)    &= drop (Gamma) \
  drop (Gamma, diamond_i)  &= drop (Gamma) \
$

Note that $drop$ is undefined on $dot$, which ensures that $#Break$ is ill-typed outside of a loop body. Since $drop$ passes through if-delimiters $diamond_i$, a $#Break$ nested inside an if within a loop correctly reaches the enclosing loop's $diamond_w$.

== Type System
Herein we discuss the type system of #Lbase. Mostly it's a straightforward approach; the interesting parts surround control flow and calling methods.

The approach to type checking begins by adding all method declarations to a (global) context of methods, thereby assuming that method type declarations are always correct. Once this pass is done, the body of each method (if given) is checked according to the statement rules.

=== Expression Types
Since expressions may affect their context (via conditionals and returns), we use the judgement form $Gamma | Delta tack.r_sigma e : tau tack.l Gamma' | Delta'$, where $sigma$ is the current method's return type. For most expressions, the output context is identical to the input.

#mathpar(
  proof-tree(rule(name: "TrueConst", $Gamma | Delta tack.r_sigma #True : #Bool tack.l Gamma | Delta$)),
  proof-tree(rule(name: "FalseConst", $Gamma | Delta tack.r_sigma #False : #Bool tack.l Gamma | Delta$)),
  proof-tree(rule(name: "NatConst", $Gamma | Delta tack.r_sigma n : #Nat tack.l Gamma | Delta$, $n in bb(N)$)),
  proof-tree(rule(name: "NullConst", $Gamma | Delta tack.r_sigma #Null : tau tack.l Gamma | Delta$)),

  proof-tree(rule(name: "VarAccess", $Gamma, x : tau | Delta tack.r_sigma x : tau tack.l Gamma, x : tau | Delta$)),

  proof-tree(rule(name: "FieldAccess", $Gamma | Delta tack.r_sigma p.f : tau tack.l Gamma | Delta$, $Gamma | Delta tack.r_sigma p : C tack.l Gamma | Delta$, $f : tau in #fields (C)$)),

  proof-tree(rule(name: "IfExpr", $Gamma | Delta tack.r_sigma #If e #Then s_1 #Else s_2 : tau tack.l Gamma' | Delta'$, $Gamma | Delta tack.r_sigma e : #Bool tack.l Gamma | Delta$, $Gamma, diamond_i | Delta tack.r_sigma s_1 tack.l Gamma', diamond_i | Delta'$, $Gamma, diamond_i | Delta tack.r_sigma s_2 tack.l Gamma', diamond_i | Delta'$)),

  proof-tree(rule(name: "Return", $Gamma | Delta tack.r_sigma #Return e : tau tack.l dot | Delta$, $Gamma | Delta tack.r_sigma e : sigma tack.l Gamma | Delta$)),
)

Note that $#Null$ is a member of all types in this system. $#Return$ has type $tau$ for any $tau$ since it never produces a value. $#If$ has type $tau$ for any $tau$ since its branches are statements.
#jq[Subtyping with null?]

=== Statement Types
Typing statements is more involved. Since statements may update their context, we use a "small-step" typing judgement form $Gamma | Delta tack.r_sigma s tack.l Gamma' | Delta'$, where $Gamma$ represents the context before the statement runs, $Gamma'$ represents the context after the statement runs (likewise for the heap $Delta$), and $sigma$ is the current method's return type.

#mathpar(
  proof-tree(rule(name: "VarDecl", $Gamma | Delta tack.r_sigma #Var x : tau tack.l Gamma, x : tau | Delta$, $x in.not Gamma$)),
  proof-tree(rule(name: "VarAssign", $Gamma, x : tau | Delta tack.r_sigma x = e tack.l Gamma' | Delta'$, $Gamma, x : tau | Delta tack.r_sigma e : tau tack.l Gamma' | Delta'$)),

  proof-tree(rule(name: "Seq", $Gamma | Delta tack.r_sigma s_1; s_2 tack.l Gamma'' | Delta''$, $Gamma | Delta tack.r_sigma s_1 tack.l Gamma' | Delta'$, $Gamma' | Delta' tack.r_sigma s_2 tack.l Gamma'' | Delta''$)),

  proof-tree(rule(name: "CallStmt", $Gamma | Delta tack.r_sigma m(e_1, e_2, ...) tack.l Gamma | Delta$, $m : (tau_1, tau_2, ...): \_$, $Gamma | Delta tack.r_sigma e_i : tau_i tack.l Gamma | Delta$)),

  proof-tree(rule(name: "WhileLoop", $Gamma | Delta tack.r_sigma #While c { s } tack.l Gamma | Delta$, $Gamma | Delta tack.r_sigma c : #Bool tack.l Gamma | Delta$, $Gamma, diamond_w | Delta tack.r_sigma s tack.l Gamma' | Delta'$, $drop(Gamma') = Gamma, diamond_w$)),

  proof-tree(rule(name: "Break", $Gamma | Delta tack.r_sigma #Break tack.l drop(Gamma) | Delta$)),
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
  proof-tree(rule(name: "Method", $tack.r m(x_i : tau_i): sigma { s }$, $x_i : tau_i | Delta tack.r_sigma s tack.l dot | Delta'$))
)

Since methods are typed in empty contexts, the body is checked with only the arguments in scope and the return type $sigma$ annotating the judgement. The output context must be $dot$, forcing all arguments and local definitions to be dropped, which in turn means that we can only exit a method via an explicit return statement.

=== Theorems and Lemmata
We should be able to use standard techniques to prove progress and preservation for the typing system, since we don't really do anything fancy at the type level.

Our treatment of contexts, however, is non-standard. We should take care to show that it's not possible for values to escape their scopes, nor for control flow to leave its scope without destroying the corresponding delimiter.

Note that we don't have strong normalisation, even for expressions; a method is able to call itself in an infinite loop.


== Evaluation
Evaluation of an #Lbase program begins with a pre-specified method name. For the rest of this document, we'll use "main". We define a small step store semantics.

=== Stack and Heap
We model two stores in our judgements; a stack $S$, which maps variables to values; and a heap $H$, which maps addresses to values. The stack is ordered so as to permit shadowing, and the heap is unordered.

$
S ::=& dot && "Empty" \
  |& S, x := v && "Variable Extension" \

H ::=& dot && "Empty" \
  |& H, a -> v && "Heap Extension" \
$

#jtodo[Early return?]

Our small step evaluation judgement for a term $t$ is $chevron.l S | H | t chevron.r ~> chevron.l S' | H' | t' chevron.r$. We define a multi step judgement $ms$ in the usual way.

Once again, method bodies are tracked globally when defined. We define a function $body(m)$, which returns the body of a method, and a function $args(m)$, which returns the argument names taken by a method.

=== Values
Values are terms that are fully evaluated. A value $v$ satisfies $chevron.l S | H | v chevron.r ~> chevron.l S | H | v chevron.r$. Addresses $a in cal(A)$ are runtime-only values that do not appear in the source language. $#True$, $#False$, $#Null$, $n in bb(N)$, and $a in cal(A)$ are values in #Lbase.

$
v ::=& a in cal(A) |& #True |& #False |& #Null |& n in bb(N)
$

=== Expression Evaluation
#mathpar(
  proof-tree(rule(name: "VarAccess", $chevron.l S, x := v | H | x chevron.r ~> chevron.l S, x := v | H | v chevron.r$)),

  proof-tree(rule(name: "FieldAccessE", $chevron.l S | H | p.f chevron.r ~> chevron.l S' | H' | p'.f chevron.r$, $chevron.l S | H | p chevron.r ~> chevron.l S' | H' | p' chevron.r$)),
  proof-tree(rule(name: "FieldAccessV", $chevron.l S | H, a -> C(... f_i := v_i ...) | a.f_i chevron.r ~> chevron.l S | H, a -> C(... f_i := v_i ...) | v_i chevron.r$)),

  proof-tree(rule(name: "IfCond", $chevron.l S | H | #If e #Then s_1 #Else s_2 chevron.r ~> chevron.l S' | H' | #If e' #Then s_1 #Else s_2 chevron.r$, $chevron.l S | H | e chevron.r ~> chevron.l S' | H' | e' chevron.r$)),
  proof-tree(rule(name: "IfThen", $chevron.l S | H | #If #True #Then s_1 #Else s_2 chevron.r ~> chevron.l S | H | s_1 chevron.r$)),
  proof-tree(rule(name: "IfElse", $chevron.l S | H | #If #False #Then s_1 #Else s_2 chevron.r ~> chevron.l S | H | s_2 chevron.r$)),

  proof-tree(rule(name: "Return", $chevron.l S | H | #Return e tack.l S'$, $drop_square(S) = S'$, $square_tau$, $chevron.l S | H | e : tau chevron.r$)),
)
#jtodo[Double check stack contents on method return is correct here]

Note the rules for call expressions. #Lbase passes by value, and evaluates arguments left-to-right.

=== Statement Evaluation
With small step operational semantics for expressions, we always know exactly which next step we can perform, even if we're looking at a value. Conversely, for rules such as VarDecl, VarAssign, and CallStmt, we don't know exactly what expression comes next, as it's presumably part of a sequencing operation higher up in the syntax tree.

To deal with this, we introduce a new statement form called $#Skip$, which denotes a fully evaluated statement. Operationally, it is a stuck state, but we're able to eliminate it and progress evaluation via Seq.

We also introduce a runtime-only statement form $#InLoop (s, c, s_0)$, which wraps the body of a loop during evaluation: $s$ is the current (partially evaluated) body, $c$ is the loop condition, and $s_0$ is the original body for re-entry.

The naive unrolling $#While c { s } -> #If c #Then (s; #While c { s }) #Else #Skip$ places the body and the loop continuation in a flat sequence. This fails with $#Break$: BreakSeq discards the rest of the body, yielding $#Break ; #While c { s }$, which in turn reduces to $#Break$. $#Break$ has escaped the loop with nothing to catch it! If instead we made $#Break$ reduce to $#Skip$, then $#Skip; #While c { s }$ would restart the loop via Seq2, which is equally wrong.

$#InLoop$ solves this by acting as a boundary between the iteration body and the loop itself. When the body finishes ($s = #Skip$), InLoopDone re-enters the loop via $#While c { s_0 }$. When the body breaks ($s = #Break$), InLoopBreak exits the loop by producing $#Skip$. $#Break$ never propagates past $#InLoop$.

#mathpar(
  proof-tree(rule(name: "VarDecl", $chevron.l S | H | #Var x : tau chevron.r ~> chevron.l S | H | #Skip chevron.r$)),

  proof-tree(rule(name: "VarAssign1", $chevron.l S, x := \_ | H | x = e chevron.r ~> chevron.l S | H | x = e' chevron.r$, $chevron.l S, x := \_ | H | e chevron.r ~> chevron.l S, x := \_ | H | e' chevron.r$)),
  proof-tree(rule(name: "VarAssign2", $chevron.l S, x := \_ | H | x = v chevron.r ~> chevron.l S, x := v | H | #Skip chevron.r$)),

  proof-tree(rule(name: "Seq1", $chevron.l S | H | s_1; s_2 chevron.r ~> chevron.l S' | H' | s'_1; s_2 chevron.r$, $chevron.l S | H | s_1 chevron.r ~> chevron.l S' | H' | s'_1 chevron.r$)),
  proof-tree(rule(name: "Seq2", $chevron.l S | H | #Skip ; s_2 chevron.r ~> chevron.l S | H | s_2 chevron.r$)),

  proof-tree(rule(name: "CallStmt", $chevron.l S | H | m(e_1, e_2, ...) chevron.r ~> chevron.l S | H | m(e_1)$, $m : (tau_1, tau_2, ...): sigma$, $chevron.l S | H | e_i : tau_i chevron.r$)),

  proof-tree(rule(name: "While", $chevron.l S | H | #While c { s } chevron.r ~> chevron.l S | H | #If c #Then #InLoop (s, c, s) #Else #Skip chevron.r$)),

  proof-tree(rule(name: "InLoopStep", $chevron.l S | H | #InLoop (s, c, s_0) chevron.r ~> chevron.l S' | H' | #InLoop (s', c, s_0) chevron.r$, $chevron.l S | H | s chevron.r ~> chevron.l S' | H' | s' chevron.r$)),
  proof-tree(rule(name: "InLoopDone", $chevron.l S | H | #InLoop (#Skip, c, s_0) chevron.r ~> chevron.l S | H | #While c { s_0 } chevron.r$)),
  proof-tree(rule(name: "InLoopBreak", $chevron.l S | H | #InLoop (#Break, c, s_0) chevron.r ~> chevron.l S | H | #Skip chevron.r$)),

  proof-tree(rule(name: "BreakSeq", $chevron.l S | H | #Break; s_2 chevron.r ~> chevron.l S | H | #Break chevron.r$)),

)

#jtodo[CallStmt]

Variable declaration has no effect during evaluation. Indeed, type checking already ensures that all variables we refer to have already been declared.

The underscore in the LHS of VarAssign is a wildcard, and represents a value we don't care about.

=== Theorems and Lemmata
Given a well-typed program $P$:

$P$ should always have an evaluation step to perform, or otherwise have finished executing (return from the main method)

It should be impossible for $P$ to:
- Escape from a method via return and retain locals on the stack
