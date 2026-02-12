#import "../defs.typ": *

= #Lbase

#Lbase is a simple typed language consisting of sequentially ordered statements with method calls. There are no modes, no classes, and no lambdas (or other methods of capturing).

== Syntax

$
P ::=& overline(M) && "Programs" \
M ::=& m(overline(x : tau)) : sigma { #Begin ; s ; #Return thin e } && "Method Definitions" \
  |& m(overline(x : tau)) : sigma && "Method Declarations" \
tau, sigma ::=& #Nat && "Naturals" \
  |& #Bool && "Booleans" \
e ::=& #Null \
  |& x && "Variable Access" \
  |& m(overline(e)) && "Method Call" \
  |& #True \
  |& #False \
  |& n in bb(N) && "Natural Numbers" \
s ::=& #Var x : tau && "(Mutable) Variable Declaration" \
  |& x = e && "Variable Assignment/Mutation" \
  |& s_1 ; s_2 && "Statement Sequencing" \
  |& #If e #Then s_1 #Else s_2 \
  |& #Return e && "Early Return" \
  |& m(overline(e)) && "Method Call"
$

#jq[Do we want loops?]

Overlined elements denote n-ary lists of such elements. $x$ and $m$ represent infinite sets of variable and method names respectively. Methods are all defined top-level, and may be (mutually) recursive.

#jtodo[Confirm with Komi: do we want (mutual) recursion?]

Non-forgetful differences from the system described by @protopapa2024VerifyingKotlinCode are:
- Our system is typed (and has #Nat and #Bool as ground types)
- ITE tests an arbitrary boolean expression, rather than direct equality on patterns.

For brevity's sake, we define $#Var x : tau = e$ as $#Var x : tau ; x = e$. Additionally, we assume usual boolean/arithmetic operators are defined as method call expressions.

== Typing Contexts
Morally, typing contexts (hereafter contexts) in #Lbase are (rightwards-growing) lists of names and their associated types, split into "stack frames" to denote the scopes in which variables are introduced. In particular, we have a (global) list of methods and associated method types#footnote[Since we don't have object-level function types, a method type is a list of argument types, paired with a return type, writ $m : (tau_1, tau_2, ...): sigma$], paired with a list of either variables names and their associated types, or stack frame delimiters.

In this working note, stack frame delimiters will be displayed as $square$, and if associated with a method, are annotated by that method's return type. Additionally, since method declarations are top level, we omit them from our treatment of contexts, and assume that the expression/statement theories are parameterised by a particular context of methods and method types.

The grammar for contexts is as follows:

$
Gamma ::=& dot && "Empty" \
  |& Gamma, x : tau && "Variable Extension" \
  |& Gamma, square_tau && "Stack Frame Delimiter"
$

New stack frames are introduced when calling a method, and when entering a branch of an if statement.

=== Well Formed Contexts
We introduce a judgement $Gamma #ctx$ to denote well formed contexts (WFCs). WFCs are defined inductively:

#mathpar(
  proof-tree(rule(name: "CtxEmp", $dot #ctx$)),
  proof-tree(rule(name: "CtxVarExt", $Gamma #ctx$, $x in.not Gamma$, $Gamma, x : tau #ctx$))
)
#mathpar(proof-tree(rule(name: "CtxStackFrame", $Gamma #ctx$, $Gamma, square #ctx$)))

$x in.not Gamma$ is bookkeeping for ensuring all names are distinct, and isn't strictly needed. Membership checking and lookup are defined in the usual way.

#jq[Do we want to allow name reuse (and thus shadowing)? How will this interact with borrowing later on?]

=== Removal
#jc[This part until the next question is likely irrelevant]
We need a removal operator acting on the context, to remove local variables when leaving a scope. We define removal inductively:

#mathpar(
  proof-tree(rule(name: "RemoveEmp", $dot backslash x = dot$)),
  proof-tree(rule(name: "RemoveVar", $Gamma, x : tau backslash x = Gamma$))
)
#mathpar(proof-tree(rule(name: "RemoveRec", $Gamma backslash x = Gamma'$, $x != y$, $Gamma, y : tau backslash x = Gamma', y : tau$)))

#jq[If we want shadowing, how should we deal with removal? With the above approach, we have no way of knowing which variables are declared in the local scope, and which are needed outside of the scope. My gut feeling is that we need a notion of stack frame in the context.]

When leaving a scope, we drop all bindings introduced after the current stack frame. To do this, we define a recursive function drop:

$
  drop(dot)                 &= dot \
  drop(Gamma, square_tau)  &= Gamma, square_tau \
  drop(Gamma, x : tau)      &= drop(Gamma)
$

#jq[Is this going to get weird if we add exceptions?]

== Type System
Typing expressions is straightforward. We use the standard $Gamma tack.r e : tau$ judgement form.

#jtodo[Expression types]

Typing statements is more involved. Since statments may update their context, we use a "small-step" typing judgement form $Gamma tack.r s tack.l Gamma'$, where $Gamma$ represents the context before the statement runs, and $Gamma'$ represents the context after the statement runs.

#mathpar(
  proof-tree(rule(name: "VarDecl", $x in.not Gamma$, $Gamma tack.r #Var x : tau tack.l Gamma, x : tau$)),
  proof-tree(rule(name: "VarAssign", $Gamma, x : tau tack.r e : tau$, $Gamma, x : tau tack.r x = e tack.l Gamma, x : tau$))
)

#mathpar(proof-tree(rule(name: "Seq", $Gamma tack.r s_1 tack.l Gamma'$, $Gamma' tack.r s_2 tack.l Gamma''$, $Gamma tack.r s_1 ; s_2 tack.l Gamma''$)))

#mathpar(proof-tree(rule(name: "IfStmt", $Gamma tack.r e : #Bool$, $Gamma tack.r s_1 tack.l Gamma'$, $Gamma tack.r s_2 tack.l Gamma'$, $Gamma tack.r #If e #Then s_1 #Else s_2 tack.l Gamma'$)))

#mathpar(
  proof-tree(rule(name: "Return", $drop(Gamma) = Gamma'$, $square_tau$, $Gamma tack.r e : tau$, $Gamma tack.r #Return e tack.l Gamma'$)),
  proof-tree(rule(name: "CallStmt", $m : (tau_1, tau_2, ...): sigma$, $Gamma tack.r e_1 : tau_1$, $Gamma tack.r e_2 : tau_2$, $dots$, $Gamma tack.r m(e_1, e_2, ...) tack.l Gamma$))
)

#jc[IfStmt is very restrictive; we should check with Komi to see exactly what we want here, especially since classes will make things a lot more complicated. Likely we will need some unification over contexts here for the branches.]

Variable declarations extend the context with a fresh variable.

Variable assigment requires that the variable we're assigning to is available in the context. Note that $e$ has access to $x$ in its context; this allows self mutation (such as $x = x + 1$).

Sequencing threads the context produced as the output of the first statement into the input of the second statement.

If statements require that both branches produce the same resultant context. This may be subject to change.

Return drops the current stack frame, checks the expression matches the expected type, then produces the context in which the method was originally called.

Method call statements may have an effect on the heap at run time, but at compile time they have no effect on the context, so in this case we merely have to check the argument types.

#v(1em)

Consider carefully a method with the body $#Return #Null ; #Return 1$. We obviously shouldn't allow $#Return 1$ to execute in the parent call frame; in fact, it shouldn't execute at all, and should be seen as unreachable code.
