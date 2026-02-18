#import "../defs.typ": *

= #Lbase

#Lbase is a simple typed language consisting of sequentially ordered statements with method calls. There are no modes, no classes, and no lambdas (or other methods of capturing).

== Syntax

$
P ::=& overline(M) && "Programs" \
M ::=& m(overline(x : tau)) : sigma { s } && "Method Definitions" \
  |& m(overline(x : tau)) : sigma && "Method Declarations" \
tau, sigma ::=& #Nat && "Naturals" \
  |& #Bool && "Booleans" \
  |& #Addr && "Addresses" \
e ::=& #Null \
  |& x && "Variable Access" \
  |& m(overline(e)) && "Method Call" \
  |& #True \
  |& #False \
  |& n in bb(N) && "Natural Numbers" \
  |& a in A && "Address" \
  |& @a && "Heap Access" \
s ::=& #Var x : tau && "(Mutable) Variable Declaration" \
  |& x = e && "Variable Assignment/Mutation" \
  |& s_1; s_2 && "Statement Sequencing" \
  |& #If e #Then s_1 #Else s_2 && "If/Then/Else" \
  |& #Return e && "(Early) Return" \
  |& m(overline(e)) && "Method Call" \
  |& #Alloc && "Heap Allocation" \
  |& #Free && "Heap Deallocation" \
  |& a = e && "Heap Store" \
$

#jq[Do we want loops?]

Overlined elements denote n-ary lists of such elements. $x$ and $m$ represent infinite sets of variable and method names respectively. Methods are all defined top-level, and may be (mutually) recursive.

#jtodo[Confirm with Komi: do we want (mutual) recursion?]

Non-forgetful differences from the system described by @protopapa2024VerifyingKotlinCode are:
- Our system is typed (and has #Nat and #Bool as ground types).
- ITE tests an arbitrary boolean expression, rather than direct equality on patterns.
- We have explicit heap manipulation, in lieu of making all objects heap allocated.

For brevity's sake, we define $#Var x : tau = e$ as $#Var x : tau; x = e$. Additionally, we assume usual boolean/arithmetic operators are defined as method call expressions.

== Typing Contexts
Morally, typing contexts (hereafter contexts) in #Lbase are ordered, rightwards-growing lists of names and their associated types, split into "stack frames" to denote the scopes in which variables are introduced. In particular, we have a (global) list of methods and associated method types#footnote[Since we don't have object-level function types, a method type is a list of argument types, paired with a return type, writ $m : (tau_1, tau_2, ...): sigma$], paired with a list of either variables names and their associated types, or stack frame delimiters.

In this working note, stack frame delimiters will be displayed as $square$, and if associated with a method, are annotated by that method's return type. Additionally, since method declarations are top level, we omit them from our treatment of contexts, and assume that the expression/statement theories are parameterised by a particular context of methods and method types.

The grammar for contexts is as follows:

$
Gamma ::=& dot && "Empty" \
  |& Gamma, x : tau && "Variable Extension" \
  |& Gamma, square_tau && "Method Stack Frame Delimiter" \
  |& Gamma, diamond && "Control Flow Stack Frame Delimiter"
$

Method stack frames are typed with the return type of the method, are introduced when entering the body of a method, and are removed upon returning. Control flow stack frames are untyped, are introduced when entering the branches of an if statement, and are removed either at the end of the branch, or during early return.
#jtodo[Loops? Break/continue statements?]

=== Well Formed Contexts
We introduce a judgement $Gamma #ctx$ to denote well formed contexts (WFCs). WFCs are defined inductively:

#mathpar(
  proof-tree(rule(name: "CtxEmp", $dot #ctx$)),
  proof-tree(rule(name: "CtxVarExt", $Gamma, x : tau #ctx$, $x in.not Gamma$, $Gamma #ctx$)),
  proof-tree(rule(name: "CtxMethodFrame", $Gamma, square_tau #ctx$, $Gamma #ctx$)),
  proof-tree(rule(name: "CtxControlFrame", $Gamma, diamond #ctx$, $Gamma #ctx$))
)

$x in.not Gamma$ is bookkeeping for ensuring all names are distinct, and isn't strictly needed. Membership checking and lookup are defined in the usual way.

#jq[Do we want to allow name reuse (and thus shadowing)? How will this interact with borrowing later on?]

=== Removal
When leaving a scope, we drop all bindings introduced after the current stack frame. To do this, we define two recursive functions called $drop_square$ and $drop_diamond$, used when exiting method frames and control flow frames respectively:

$
  drop_square (dot)               &= dot \
  drop_square (Gamma, square_tau) &= Gamma, square_tau \
  drop_square (Gamma, diamond)    &= drop_square (Gamma) \
  drop_square (Gamma, x : tau)    &= drop_square (Gamma)
$

$
  drop_diamond (dot)               &= dot \
  drop_diamond (Gamma, diamond)    &= Gamma, diamond \
  drop_diamond (Gamma, x : tau)    &= drop_diamond (Gamma)
$

Note the $Gamma, diamond$ case: in $drop_square$, we recurse past the control flow delimiter; in $drop_diamond$, we stop. Addtionally, $drop_diamond$ is undefined on $Gamma, square_tau$. This is to preclude us from writing a break statement outside of a loop.

#jq[Is this going to get weird if we add exceptions?]

== Type System
Herein we discuss the type system of #Lbase. Mostly it's a straightforward approach; the interesting parts surround stack frames and calling methods.

The approach to type checking begins by adding all method declarations to a (global) context of methods, thereby assuming that method type declarations are always correct. Once this pass is done, the body of each method (if given) is checked according to the statement rules.

=== Expression Types
Typing expressions is straightforward. We use the standard $Gamma tack.r e : tau$ judgement form.

#mathpar(
  proof-tree(rule(name: "TrueConst", $Gamma tack.r #True : #Bool$)),
  proof-tree(rule(name: "FalseConst", $Gamma tack.r #False : #Bool$)),
  proof-tree(rule(name: "NatConst", $Gamma tack.r n : #Nat$, $n in bb(N)$)),
  proof-tree(rule(name: "NullConst", $Gamma tack.r #Null : tau$)),
  proof-tree(rule(name: "CallExpr", $Gamma tack.r m(e_1, e_2, ...) : sigma$, $m : (tau_1, tau_2, ...): sigma$, $Gamma tack.r e_i : tau_i$))
  proof-tree(rule(name: "VarAccess", $Gamma, x : tau tack.r x : tau$)),
)

Note that $#Null$ is a member of all types in this system.
#jq[Subtyping with null?]

=== Statement Types
Typing statements is more involved. Since statments may update their context, we use a "small-step" typing judgement form $Gamma tack.r s tack.l Gamma'$, where $Gamma$ represents the context before the statement runs, and $Gamma'$ represents the context after the statement runs.

#mathpar(
  proof-tree(rule(name: "VarDecl", $Gamma tack.r #Var x : tau tack.l Gamma, x : tau$, $x in.not Gamma$)),
  proof-tree(rule(name: "VarAssign", $Gamma, x : tau tack.r x = e tack.l Gamma, x : tau$, $Gamma, x : tau tack.r e : tau$)),
  proof-tree(rule(name: "Seq", $Gamma tack.r s_1; s_2 tack.l Gamma''$, $Gamma tack.r s_1 tack.l Gamma'$, $Gamma' tack.r s_2 tack.l Gamma''$)),
  proof-tree(rule(name: "IfStmt", $Gamma tack.r #If e #Then s_1 #Else s_2 tack.l Gamma'$, $Gamma tack.r e : #Bool$, $Gamma, diamond tack.r s_1 tack.l Gamma', diamond$, $Gamma, diamond tack.r s_2 tack.l Gamma', diamond$)),
  proof-tree(rule(name: "Return", $Gamma tack.r #Return e tack.l Gamma', square_tau$, $drop_square (Gamma) = Gamma', square_tau$, $Gamma tack.r e : tau$)),
  proof-tree(rule(name: "CallStmt", $Gamma tack.r m(e_1, e_2, ...) tack.l Gamma$, $m : (tau_1, tau_2, ...): sigma$, $Gamma tack.r e_i : tau_i$))
)

#jc[IfStmt is very restrictive; we should check with Komi to see exactly what we want here, especially since classes will make things a lot more complicated. Likely we will need some unification over contexts here for the branches.]

#jq[Is our treatment of method calling and returning sound?]

Variable declarations extend the context with a fresh variable.

Variable assigment requires that the variable we're assigning to is available in the context. Note that $e$ has access to $x$ in its context; this allows self mutation (such as $x = x + 1$).

Sequencing threads the context produced as the output of the first statement into the input of the second statement.

If statements require that both branches produce the same resultant context. This may be subject to change.

Return drops the current stack frame, checks the expression matches the expected type, then produces the context in which the method was originally called.

Method call statements may have an effect on the heap at run time, but at compile time they have no effect on the context, so in this case we merely have to check the argument types. Note that the preconditions for this rule are identical to the expression case; only the judgement form of the consequent differs.

#v(1em)

Consider carefully a method with the body $#Return #Null ; #Return 1$. We obviously shouldn't allow $#Return 1$ to execute in the parent call frame; in fact, it shouldn't execute at all, and should be seen as unreachable code.

#jtodo[Double check that this is sensible]

=== Method Bodies
We introduce a final typing judgement $Gamma tack.r m(x_i : tau_i): sigma { s }$ to ascribe types for method definitions.

#mathpar(
  proof-tree(rule(name: "Method", $Gamma tack.r m(x_i : tau_i): sigma { s }$, $Gamma, square_sigma, x_i : tau_i tack.r s tack.l Gamma, square_sigma$))
)

Note the assymmetry in the contexts when checking the method body. Effectively we're forcing the introduced arguments (and any local defs) to be dropped, which in turn means that we only can exit a method via an explicit return statement.

== Evaluation
Evaluation of an #Lbase program begins with a pre-specified method name. For the rest of this document, we'll use "main". We define a small step store semantics.

=== Environment and the Heap
We model two stores in our judgements; an environment $S$, which maps variables to addresses or values; and a heap $H$, which maps addresses to values. Effectively, $S$ is the stack, and $D$ is the heap. We model lookup as partial functions $S(x) = a$ and $H(a) = v$, for a variable $x$, an address $a$ and a value $v$. The environment is ordered so as to permit shadowing, and the heap is unordered.

#jq[Should addresses just be normal values? Is allowing that sound?]

Our environment and heap syntax is as follows:
$
S ::=& dot && "Empty" \
  |& S, x := v && "Variable Extension" \

H ::=& dot && "Empty" \
  |& H, a -> v && "Heap Extension" \
$

Each address $a$ is a distinct label from an infinite set $A$, and refers to a location on the heap. Addresses are treated as values.

#jtodo[Early return? We need stack frames again for sure this time.]

Our small step evaluation judgement for a term $t$ is $chevron.l S | H | t chevron.r ~> chevron.l S', H', t' chevron.r$. We define a multi step judgement $ms$ in the usual way.

Once again, method bodies are tracked globally when defined. We define a function $body(m)$, which returns the body of a method, and a function $args(m)$, which returns the argument names taken by a method.

=== Values
Our notion of values is given by the standard small step definition $chevron.l S | H | v chevron.r ~> chevron.l S | H | v chevron.r$. Only $#True$, $#False$, $#Null$, and $n in bb(N)$ are values in #Lbase.

$
v ::=& a in A |& #True |& #False |& #Null |& n in bb(N)
$

=== Expression Evaluation
#mathpar(
  proof-tree(rule(name: "TrueConst", $chevron.l S | H | #True chevron.r ~> chevron.l S | H | #True chevron.r$)),
  proof-tree(rule(name: "FalseConst", $chevron.l S | H | #False chevron.r ~> chevron.l S | H | #False chevron.r$)),
  proof-tree(rule(name: "NatConst", $chevron.l S | H | n chevron.r ~> chevron.l S | H | n chevron.r$, $n in bb(N)$)),
  proof-tree(rule(name: "NullConst", $chevron.l S | H | #Null chevron.r ~> chevron.l S | H | #Null chevron.r$)),
  proof-tree(rule(name: "VarAccess", $chevron.l S, x := a | H, a -> v | x chevron.r ~> chevron.l S, x := a | H, a -> v | v chevron.r$)),
  proof-tree(rule(name: "CallExprE", $chevron.l S | H | m(e_1, e_2, ...) chevron.r ~> chevron.l S | H | m(e'_1, e_2, ...) chevron.r$, $chevron.l S | H | e_1 chevron.r ~> chevron.l S | H | e'_1 chevron.r$)),
  proof-tree(rule(name: "CallExprV", $chevron.l S | H | m(v_1, v_2, ...) chevron.r ~> chevron.l S, x_1 := v_1, x_2 := v_2, ... | H | s chevron.r$, $args(m) = x_1, x_2, ...$, $body(m) = s$)),
)
#jtodo[Double check stack contents on method return is correct here]

The only expression rule which directly interacts with the heap is the one for variable access. We enforce in this rule that the corresponding label is actually defined on the heap.

Note the rules for call expressions. #Lbase passes by value, and evaluates arguments left-to-right.

=== Statement Evaluation
With small step operational semantics for expressions, we always know exactly which next step we can perform, even if we're looking at a value. Conversely, for rules such as VarDecl, VarAssign, and CallStmt, we don't know exactly what expression comes next, as it's presumably part of a sequencing operation higher up in the syntax tree.

To deal with this, we introduce a new statement form called $#Skip$, which denotes a fully evaluated statement. Operationally, it is a stuck state, but we're able to eliminate it and progress evaluation via Seq.

#mathpar(
  proof-tree(rule(name: "Skip", $chevron.l S | H | #Skip chevron.r ~> chevron.l S | H | #Skip chevron.r$)),
  proof-tree(rule(name: "VarDecl", $chevron.l S | H | #Var x : tau chevron.r ~> chevron.l S | H | #Skip chevron.r$)),
  proof-tree(rule(name: "VarAssign1", $chevron.l S, x := \_ | H | x = e chevron.r ~> chevron.l S | H | x = e' chevron.r$, $chevron.l S, x := \_ | H | e chevron.r ~> chevron.l S, x := \_ | H | e' chevron.r$)),
  proof-tree(rule(name: "VarAssign2", $chevron.l S, x := \_ | H | x = v chevron.r ~> chevron.l S, x := v | H | #Skip chevron.r$)),
  proof-tree(rule(name: "Seq1", $chevron.l S | H | s_1; s_2 chevron.r ~> chevron.l S' | H' | s'_1; s_2 chevron.r$, $chevron.l S | H | s_1 chevron.r ~> chevron.l S' | H' | s'_1 chevron.r$)),
  proof-tree(rule(name: "Seq2", $chevron.l S | H | #Skip ; s_2 chevron.r ~> chevron.l S | H | s_2 chevron.r$)),
  proof-tree(rule(name: "IfCond", $chevron.l S | H | #If e #Then s_1 #Else s_2 chevron.r ~> chevron.l S' | H' | #If e' #Then s_1 #Else s_2 chevron.r$, $chevron.l S | H | e chevron.r ~> chevron.l S' | H' | e' chevron.r$)),
  proof-tree(rule(name: "IfThen", $chevron.l S | H | #If #True #Then s_1 #Else s_2 chevron.r ~> chevron.l S | H | s_1 chevron.r$)),
  proof-tree(rule(name: "IfElse", $chevron.l S | H | #If #False #Then s_1 #Else s_2 chevron.r ~> chevron.l S | H | s_2 chevron.r$)),
  proof-tree(rule(name: "Return", $chevron.l S | H | #Return e tack.l S'$, $drop_square(S) = S'$, $square_tau$, $chevron.l S | H | e : tau chevron.r$)),
  proof-tree(rule(name: "CallStmt", $chevron.l S | H | m(e_1, e_2, ...) chevron.r ~> chevron.l S | H | m(e_1)$, $m : (tau_1, tau_2, ...): sigma$, $chevron.l S | H | e_i : tau_i chevron.r$))
)

#jtodo[Return, CallStmt]
#jtodo[What judgement should we use for statements? They don't always produce another statement to execute]

Variable declaration has no effect during evaluation. Indeed, type checking already ensures that all variables we refer to have already been declared.

The underscore in the LHS of VarAssign is a wildcard, and represents a value we don't care about.

The If rule assumes that expressions do not modify the stack or heap. This is currently true,