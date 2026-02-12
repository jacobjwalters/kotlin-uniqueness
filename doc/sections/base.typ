#import "../defs.typ": *

= #Lbase

#Lbase is a simple typed language consisting of sequentially ordered statements with method calls. There are no modes, no classes, and no lambdas (or other methods of capturing).

== Syntax

$
P ::=& overline(M) && "Programs" \
M ::=& m(overline(x #Colon tau)) #Colon sigma { #Begin #Semi s #Semi #Return thin e } && "Method Definitions" \
  |& m(overline(x #Colon tau)) #Colon sigma && "Method Declarations" \
tau, sigma ::=& #Nat && "Naturals" \
  |& #Bool && "Booleans" \
e ::=& #Null \
  |& x && "Variable Access" \
  |& m(overline(e)) && "Method Call" \
  |& #True \
  |& #False \
  |& n in NN && "Natural Numbers" \
s ::=& #Var x #Colon tau && "(Mutable) Variable Declaration" \
  |& x = e && "Variable Assignment/Mutation" \
  |& s_1 #Semi s_2 && "Statement Sequencing" \
  |& #If e #Then s_1 #Else s_2 \
  |& #Return e && "Early Return" \
  |& m(overline(e)) && "Method Call"
$

Overlined elements denote n-ary lists of such elements. $x$ and $m$ represent infinite sets of variable and method names respectively.

Non-forgetful differences from the system described by @protopapa2024VerifyingKotlinCode are:
- Our system is typed (and has #Nat and #Bool as ground types)
- ITE tests an arbitrary boolean expression, rather than direct equality on patterns.

For brevity's sake, we define $#Var x : tau = e$ as $#Var x : tau #Semi x = e$. Additionally, we assume usual boolean/arithmetic operators are defined as method call expressions.

== Typing Contexts

Typing contexts (hereafter contexts) in #Lbase are (rightwards-growing) lists of variable names and their associated types. The grammar for contexts is as follows:

$
Gamma ::=& dot && "Empty" \
  |& Gamma, x #Colon tau && "Extension"
$

Statements in #Lbase may alter their context, particular for variable declaration and (early) return statements. To model this, we take a small-step semantics like approach to dealing with contexts, with judgements of the form $Gamma tack.r s tack.l Gamma'$.

=== Well Formed Contexts

We introduce a judgement $Gamma #ctx$, to denote well formed contexts (WFCs). WFCs are defined inductively:

#align(center)[
  #columns(2)[
    #proof-tree(rule(name: "CtxEmp", $dot #ctx$)),
    #colbreak()
    #proof-tree(rule(name: "CtxExt", $Gamma #ctx$, $x in.not Gamma$, $Gamma, x : tau #ctx$)),
  ]
]

$x in.not Gamma$ is bookkeeping for ensuring all names are distinct, and isn't strictly needed. Membership checking and lookup are defined in the usual way.

#jq[Do we want to allow name reuse (and thus shadowing)? How will this interact with borrowing later on?]

We need a removal operator acting on the context, to remove local variables when leaving a scope. We define removal inductively:

#align(center)[
  #columns(2)[
    #proof-tree(rule(name: "RemoveEmp", $dot without x = dot$))
    #colbreak()

    #proof-tree(rule(name: "RemoveVar", $Gamma, x : tau without x = Gamma$))
  ]

  #proof-tree(rule(name: "RemoveRec", $Gamma, y : tau without x = Gamma without x, y : tau$))
]

#jq[If we want shadowing, how should we deal with removal? With the above approach, we have no way of knowing which variables are declared in the local scope, and which are needed outside of the scope. My gut feeling is that we need a notion of stack frame in the context.]

=== Type System

Typing expressions is straightforward. We use the standard $Gamma tack.r e : tau$ judgement form.

#jtodo[Expression types]

Typing statements is more involved. Since statements may update their context, we use a "small-step" typing judgement form $Gamma tack.r s tack.l Gamma'$, where $Gamma$ represents the context before the statement runs, and $Gamma'$ represents the context after the statement runs.

#align(center)[
  #columns(2)[
    #proof-tree(rule(
      name: "VarDecl",
      $x in.not Gamma$,
      $Gamma tack.r #Var x : tau tack.l Gamma, x : tau$
    ))
    #colbreak()

    #proof-tree(rule(
      name: "VarAssign",
      $Gamma, x : tau tack.r e : tau$,
      $Gamma, x : tau tack.r x = e tack.l Gamma, x : tau$
    ))
  ]

  #columns(2)[
    #proof-tree(rule(
      name: "Seq",
      $Gamma tack.r s_1 tack.l Gamma'$,
      $Gamma' tack.r s_2 tack.l Gamma''$,
      $Gamma tack.r s_1 #Semi s_2 tack.l Gamma''$
    ))
    #colbreak()

    #proof-tree(rule(
      name: "IfStmt",
      $Gamma tack.r s_1 tack.l Gamma'$,
      $Gamma tack.r s_2 tack.l Gamma'$,
      $Gamma tack.r #If e #Then s_1 #Else s_2 tack.l Gamma'$
    ))
  ]

  #proof-tree(rule(
    name: "CallStmt",
    $space$
  ))
]

#jtodo[Return and method call]

#jc[IfStmt is very restrictive; we should check with Komi to see exactly what we want here, especially since classes will make things a lot more complicated. Likely we will need some unification over contexts here for the branches.]
