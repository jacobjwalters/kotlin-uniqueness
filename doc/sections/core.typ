#import "../defs.typ": *

= #Lcore

#Lcore is the core call-by-value system used as a small operational baseline for later uniqueness systems. It is a simply typed lambda calculus with spined functions and spined ML-style references. There are no classes, statements, loops, modes, or lifetime annotations.

The word _spined_ means that function application and reference allocation evaluate an explicit list of subexpressions left-to-right. A reference stores a fixed-length vector of values, and $#get($i$, $e$)$ and $#Set($i$, $e$, $e'$)$ operate on the $i$th cell of that vector.

== Syntax

$
tau, sigma ::=& #Unit && "Unit" \
  |& tau_0, ..., tau_n arrow.r sigma && "Spined Function" \
  |& #Ref [tau_0, ..., tau_n] && "Reference to a fixed spine" \
e ::=& x && "Variable Access" \
  |& lambda [y_0, ..., y_m] (x_0 : tau_0, ..., x_n : tau_n) thin e && "Lambda Abstraction" \
  |& e med e_0 med ... med e_n && "Spined Application" \
  |& #ref($e_0 med ... med e_n$) && "Reference Allocation" \
  |& #get($i$, $e$) && "Reference Access" \
  |& #Set($i$, $e$, $e'$) && "Reference Mutation" \
  |& #UnitVal && "Unit Value"
$

Variables range over an infinite set of names. The forms $#ref($e_0 med ... med e_n$)$, $#get($i$, $e$)$, and $#Set($i$, $e$, $e'$)$ use zero-based indices, so a reference of type $#Ref [tau_0, ..., tau_n]$ has valid cells $0, ..., n$.

Function/application and reference-allocation spines are non-empty in this presentation. Nullary functions and zero-cell references would require separate direct rules.

Lambdas include an explicit capture list $[y_0, ..., y_m]$. Only the variables named in this list are copied into the closure at runtime. The empty capture list $[]$ denotes a closed lambda. We require capture names to be distinct from each other and from parameter names.

As in the other systems, the informal syntax uses named variables while the formalisation may use de Bruijn indices. The core system does not include general products: the spine inside $#Ref [tau_0, ..., tau_n]$ is part of the reference type, not an independent tuple type.

#text(fill: red)[*How do we represent n-ary break in Lcore?*]

== Typing Contexts

Typing contexts are ordered, rightwards-growing lists of names and types:

$
Gamma ::=& dot && "Empty" \
  |& Gamma, x : tau && "Variable Extension"
$

Lookup $Gamma(x) = tau$ returns the rightmost binding of $x$ in $Gamma$, permitting shadowing.

== Type System

The source typing judgement is $Gamma tack.r e : tau$. Source programs do not contain addresses or closures; those runtime-only values are typed in the evaluation section.

#mathpar(
  proof-tree(rule(name: "UnitConst", $Gamma tack.r #UnitVal : #Unit$)),
  proof-tree(rule(name: "VarAccess", $Gamma tack.r x : tau$, $Gamma(x) = tau$)),

  proof-tree(rule(
    name: "Lambda",
    $Gamma tack.r lambda [y_0, ..., y_m] (x_0 : tau_0, ..., x_n : tau_n) thin e : tau_0, ..., tau_n arrow.r sigma$,
    $Gamma(y_j) = rho_j$,
    $op("distinct")(y_0, ..., y_m, x_0, ..., x_n)$,
    $y_0 : rho_0, ..., y_m : rho_m, x_0 : tau_0, ..., x_n : tau_n tack.r e : sigma$,
  )),

  proof-tree(rule(
    name: "App",
    $Gamma tack.r e med e_0 med ... med e_n : sigma$,
    $Gamma tack.r e : tau_0, ..., tau_n arrow.r sigma$,
    $Gamma tack.r e_i : tau_i$,
    $0 <= i <= n$,
  )),

  proof-tree(rule(
    name: "Ref",
    $Gamma tack.r #ref($e_0 med ... med e_n$) : #Ref [tau_0, ..., tau_n]$,
    $Gamma tack.r e_i : tau_i$,
    $0 <= i <= n$,
  )),

  proof-tree(rule(
    name: "Get",
    $Gamma tack.r #get($i$, $e$) : tau_i$,
    $Gamma tack.r e : #Ref [tau_0, ..., tau_n]$,
    $0 <= i <= n$,
  )),

  proof-tree(rule(
    name: "Set",
    $Gamma tack.r #Set($i$, $e$, $e'$) : #Unit$,
    $Gamma tack.r e : #Ref [tau_0, ..., tau_n]$,
    $Gamma tack.r e' : tau_i$,
    $0 <= i <= n$,
  )),
)

Application is arity-exact: the number of supplied arguments must match the function type's spine. Reference allocation is also arity-exact: $#ref($e_0 med ... med e_n$)$ allocates exactly $n + 1$ cells, whose types become the reference payload type. $#Set($i$, $e$, $e'$)$ mutates the selected cell and returns $#Unit$.

This formulation does not admit recursive heap structures. Creating a self-cycle would require a finite type equation such as $tau = #Ref [tau_0, ..., tau, ..., tau_n]$; mutually recursive heap structures would require a mutually recursive family of such equations. Since #Lcore types are finite syntax trees and there is no recursive type former, no such type can be written.

=== Properties

- *Type Uniqueness:* if $Gamma tack.r e : tau_1$ and $Gamma tack.r e : tau_2$, then $tau_1 = tau_2$.

- *Weakening (Extension):* if $Gamma tack.r e : tau$ and $Gamma$ is a suffix of $Gamma'$, then $Gamma' tack.r e : tau$.

- *Weakening (Permutation):* if $Gamma tack.r e : tau$ and for all $x in op("dom")(Gamma)$, $Gamma(x) = Gamma'(x)$, then $Gamma' tack.r e : tau$.

- *Substitution:* if $Gamma, x : tau tack.r e : sigma$ and $Gamma tack.r v : tau$ for a source value $v$, then $Gamma tack.r e[x := v] : sigma$.

== Evaluation

Evaluation is a two-phase CEK-style machine with an explicit store. We use the same CESK notation as #Lclass, with the jump component fixed to $dot$ because #Lcore has no non-local jumps. The continuation stack makes left-to-right evaluation order explicit.

=== Runtime Language

The runtime language extends the source language with closures and addresses.

==== Values

$
v ::=& #UnitVal && "Unit value" \
  |& a in cal(A) && "Store address" \
  |& chevron.l lambda [y_0, ..., y_m] (x_0 : tau_0, ..., x_n : tau_n) thin e ; E chevron.r && "Closure"
$

Addresses and closures do not appear in source programs. A closure pairs a lambda with the environment formed from its explicit capture list when the lambda is evaluated.

==== Runtime Typing

#mathpar(
  proof-tree(rule(name: "VUnit", $tack.r #UnitVal : #Unit$)),
  proof-tree(rule(name: "VAddr", $tack.r a : #Ref [tau_0, ..., tau_n]$, $S(a) = [v_0, ..., v_n]$, $tack.r v_i : tau_i$, $0 <= i <= n$)),
  proof-tree(rule(
    name: "VClosure",
    $tack.r chevron.l lambda [y_0, ..., y_m] (x_0 : tau_0, ..., x_n : tau_n) thin e ; E chevron.r : tau_0, ..., tau_n arrow.r sigma$,
    $#coh($E$, $Gamma_c$)$,
    $Gamma_c, x_0 : tau_0, ..., x_n : tau_n tack.r e : sigma$,
  )),
)

Address typing follows the same convention as #Lclass: the premise refers to the current store $S$. An address has reference type $#Ref [tau_0, ..., tau_n]$ when the store maps it to a cell vector whose values have the corresponding payload types.

=== Environment-Context Coherence

We define _coherence_ between an environment and a context, written $#coh($E$, $Gamma$)$, inductively:

#mathpar(
  proof-tree(rule(name: "CohEmp", $#coh($dot$, $dot$)$)),
  proof-tree(rule(name: "CohBind", $#coh($E, x := v$, $Gamma, x : tau$)$, $#coh($E$, $Gamma$)$, $tack.r v : tau$)),
)

=== Store Typing

A store $S$ is well typed, written $tack.r S "ok"$, when every mapping $a -> [v_0, ..., v_n]$ in $S$ has some payload type $#Ref [tau_0, ..., tau_n]$ such that $tack.r v_i : tau_i$ for all $0 <= i <= n$.

=== Machine State

The machine state is a 5-tuple $#cesk($C$, $E$, $J$, $S$, $K$)$ with $J = dot$ in all reachable #Lcore states. In _Expr_ mode ($#ceskE($C$, $E$, $dot$, $S$, $K$)$), the control holds an expression to decompose. In _Cont_ mode ($#ceskC($C$, $E$, $dot$, $S$, $K$)$), the control holds a value and the machine dispatches on the continuation.

#table(
  columns: (auto, auto, 1fr),
  align: (center, left, left),
  table.header([*Component*], [*Name*], [*Description*]),
  [$C$], [Control], [The current expression or value being processed],
  [$E$], [Environment], [Ordered map from variables to runtime values],
  [$J$], [Jump stack], [Always $dot$ in #Lcore],
  [$S$], [Store], [Unordered map from addresses to reference cells],
  [$K$], [Continuation], [Stack of continuations],
)

==== Control ($C$)

$
C ::=& e && "Source expression" \
  |& v && "Runtime value"
$

Expression evaluation terminates with a value $v$ in the control.

==== Environment ($E$)

$
E ::=& dot && "Empty" \
  |& E, x := v && "Variable binding"
$

Lookup scans right-to-left, so later bindings shadow earlier ones. Function application evaluates the body under the closure's captured environment extended with the argument values.

The operation $op("capture")(E; y_0, ..., y_m)$ builds a new environment containing exactly the listed variables in capture-list order:

$
op("capture")(E; y_0, ..., y_m) = y_0 := E(y_0), ..., y_m := E(y_m)
$

Since lambda typing requires $Gamma(y_j) = rho_j$ and runtime coherence relates $E$ to $Gamma$, each captured value has the type recorded for that capture in the lambda typing rule.

==== Store ($S$)

$
S ::=& dot && "Empty" \
  |& S, a -> [v_0, ..., v_n] && "Reference cell vector"
$

The update $S[a[i] |-> v]$ modifies only the $i$th cell at address $a$.

==== Continuation ($K$)

$
K ::=& #halt && "Program complete" \
  |& #appFunK (e_0, ..., e_n) dot.c K && "After evaluating function, evaluate argument spine" \
  |& #appArgK (v_f, overline(v), overline(e)) dot.c K && "Evaluating function arguments" \
  |& #refK (overline(v), overline(e)) dot.c K && "Evaluating allocation spine" \
  |& #getK (i) dot.c K && "After evaluating reference, read cell" i \
  |& #setRefK (i, e') dot.c K && "After evaluating reference, evaluate value to write" \
  |& #setValK (i, a) dot.c K && "After evaluating value, write cell" i "at address" a
$

- $#halt$ accepts the final value.
- $#appFunK (e_0, ..., e_n)$ waits for the function expression to evaluate, then starts evaluating the argument spine.
- $#appArgK (v_f, overline(v), overline(e))$ accumulates evaluated arguments for function value $v_f$.
- $#refK (overline(v), overline(e))$ accumulates evaluated cell values for allocation.
- $#getK (i)$ waits for an address and reads its $i$th cell.
- $#setRefK (i, e')$ waits for an address, then evaluates the new cell value $e'$.
- $#setValK (i, a)$ waits for the new value and performs the store update.

=== Transition Rules

We define a multi-step judgement $ms$ in the usual way.

==== Expr

$
#ceskE($#UnitVal$, $E$, $dot$, $S$, $K$) &~> #ceskC($#UnitVal$, $E$, $dot$, $S$, $K$) && "Val" \
#ceskE($x$, $E$, $dot$, $S$, $K$) &~> #ceskC($E(x)$, $E$, $dot$, $S$, $K$) && "Var" \
#ceskE($L$, $E$, $dot$, $S$, $K$) &~> #ceskC($v_L$, $E$, $dot$, $S$, $K$) && "Lam" \
& quad "where" L = lambda [overline(y)] (overline(x : tau)) thin e \
& quad "and" E_c = op("capture")(E; overline(y)) quad "and" v_L = chevron.l L ; E_c chevron.r \
#ceskE($e med e_0 med ... med e_n$, $E$, $dot$, $S$, $K$) &~> #ceskE($e$, $E$, $dot$, $S$, $#appFunK (e_0, ..., e_n) dot.c K$) && "App" \
#ceskE($#ref($e_0 med ... med e_n$)$, $E$, $dot$, $S$, $K$) &~> #ceskE($e_0$, $E$, $dot$, $S$, $#refK (epsilon, (e_1, ..., e_n)) dot.c K$) && "Ref" \
#ceskE($#get($i$, $e$)$, $E$, $dot$, $S$, $K$) &~> #ceskE($e$, $E$, $dot$, $S$, $#getK (i) dot.c K$) && "Get" \
#ceskE($#Set($i$, $e$, $e'$)$, $E$, $dot$, $S$, $K$) &~> #ceskE($e$, $E$, $dot$, $S$, $#setRefK (i, e') dot.c K$) && "Set"
$

The Ref rule assumes the allocation spine is non-empty, as written in the syntax.

==== Cont

$
#ceskC($v_f$, $E$, $dot$, $S$, $#appFunK (e, overline(e)) dot.c K$) &~> \
& #ceskE($e$, $E$, $dot$, $S$, $#appArgK (v_f, epsilon, overline(e)) dot.c K$) && "AppFun" \
#ceskC($v$, $E$, $dot$, $S$, $#appArgK (v_f, overline(v), (e, overline(e))) dot.c K$) &~> \
& #ceskE($e$, $E$, $dot$, $S$, $#appArgK (v_f, overline(v) dot.c v, overline(e)) dot.c K$) && "AppArgNext" \
#ceskC($v$, $E$, $dot$, $S$, $#appArgK (v_L, overline(v), epsilon) dot.c K$) &~> #ceskE($e$, $E_c, overline(x := w)$, $dot$, $S$, $K$) && "AppArgDone" \
& quad "where" v_L = chevron.l lambda [overline(y)] (overline(x : tau)) thin e ; E_c chevron.r \
& quad "and" overline(w) = overline(v), v \
#ceskC($v$, $E$, $dot$, $S$, $#refK (overline(v), (e, overline(e))) dot.c K$) &~> #ceskE($e$, $E$, $dot$, $S$, $#refK (overline(v) dot.c v, overline(e)) dot.c K$) && "RefNext" \
#ceskC($v$, $E$, $dot$, $S$, $#refK (overline(v), epsilon) dot.c K$) &~> #ceskC($a$, $E$, $dot$, $S, a -> [overline(w)]$, $K$) && "RefDone" \
& quad "where" a in.not op("dom")(S) quad "and" overline(w) = overline(v), v \
#ceskC($a$, $E$, $dot$, $S$, $#getK (i) dot.c K$) &~> #ceskC($v_i$, $E$, $dot$, $S$, $K$) && "GetDone" \
& quad "where" S(a) = [v_0, ..., v_i, ..., v_n] \
#ceskC($a$, $E$, $dot$, $S$, $#setRefK (i, e') dot.c K$) &~> #ceskE($e'$, $E$, $dot$, $S$, $#setValK (i, a) dot.c K$) && "SetRefDone" \
#ceskC($v$, $E$, $dot$, $S$, $#setValK (i, a) dot.c K$) &~> #ceskC($#UnitVal$, $E$, $dot$, $S[a[i] |-> v]$, $K$) && "SetValDone"
$

Applications, allocation spines, and mutation are left-to-right. Function arguments are evaluated in the caller's environment $E$; after all arguments are available, the body runs in the captured closure environment $E_c$ extended with the parameter bindings. References store already-evaluated runtime values.

=== Initial and Terminal States

$
"Initial:" && #ceskE($e$, $dot$, $dot$, $dot$, $#halt$) && "where" e "is the program expression" \
"Terminal:" && #ceskC($v$, $E$, $dot$, $S$, $#halt$)
$

=== Continuation Typing

Expression continuations (#typeContE($Gamma$, $dot$, $K$, $tau$)) consume a value of type $tau$ in context $Gamma$. The jump context position is always $dot$ because #Lcore has no non-local jumps.

#mathpar(
  proof-tree(rule(name: "HaltK", typeContE($Gamma$, $dot$, $#halt$, $tau$))),

  proof-tree(rule(
    name: "AppFunK",
    typeContE($Gamma$, $dot$, $#appFunK (e_0, ..., e_n) dot.c K$, $tau_0, ..., tau_n arrow.r sigma$),
    $Gamma tack.r e_i : tau_i$,
    $0 <= i <= n$,
    typeContE($Gamma$, $dot$, $K$, $sigma$),
  )),

  proof-tree(rule(
    name: "AppArgK",
    typeContE($Gamma$, $dot$, $#appArgK (v_f, overline(v), overline(e)) dot.c K$, $tau_i$),
    $tack.r v_f : tau_0, ..., tau_n arrow.r sigma$,
    $tack.r overline(v)_j : tau_j "for" j < i$,
    $Gamma tack.r overline(e)_k : tau_(i + 1 + k)$,
    typeContE($Gamma$, $dot$, $K$, $sigma$),
  )),

  proof-tree(rule(
    name: "RefK",
    typeContE($Gamma$, $dot$, $#refK (overline(v), overline(e)) dot.c K$, $tau_i$),
    $tack.r overline(v)_j : tau_j "for" j < i$,
    $Gamma tack.r overline(e)_k : tau_(i + 1 + k)$,
    typeContE($Gamma$, $dot$, $K$, $#Ref [tau_0, ..., tau_n]$),
  )),

  proof-tree(rule(
    name: "GetK",
    typeContE($Gamma$, $dot$, $#getK (i) dot.c K$, $#Ref [tau_0, ..., tau_n]$),
    $0 <= i <= n$,
    typeContE($Gamma$, $dot$, $K$, $tau_i$),
  )),

  proof-tree(rule(
    name: "SetRefK",
    typeContE($Gamma$, $dot$, $#setRefK (i, e') dot.c K$, $#Ref [tau_0, ..., tau_n]$),
    $Gamma tack.r e' : tau_i$,
    $0 <= i <= n$,
    typeContE($Gamma$, $dot$, $K$, $#Unit$),
  )),

  proof-tree(rule(
    name: "SetValK",
    typeContE($Gamma$, $dot$, $#setValK (i, a) dot.c K$, $tau_i$),
    $tack.r a : #Ref [tau_0, ..., tau_n]$,
    $0 <= i <= n$,
    typeContE($Gamma$, $dot$, $K$, $#Unit$),
  )),
)

For AppArgK and RefK, the index $i$ is the position currently being evaluated. The accumulated values cover positions before $i$, and the remaining expressions cover positions after $i$.

==== Well Typed States

A machine state is _well typed_ when coherence and store typing bridge the runtime state to a context $Gamma$ that types both the control and the continuation:

#mathpar(
  proof-tree(rule(name: "WtExpr", $tack.r #ceskE($e$, $E$, $dot$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $tack.r S "ok"$, $Gamma tack.r e : tau$, typeContE($Gamma$, $dot$, $K$, $tau$))),
  proof-tree(rule(name: "WtCont", $tack.r #ceskC($v$, $E$, $dot$, $S$, $K$) "ok"$, $#coh($E$, $Gamma$)$, $tack.r S "ok"$, $tack.r v : tau$, typeContE($Gamma$, $dot$, $K$, $tau$))),
)

=== Properties

- *Progress:* if $tack.r S "ok"$ and $S$ is not terminal, then there exists $S'$ such that $S ~> S'$. In particular, Get and Set cannot get stuck on missing cells because the source typing index premise and address typing agree on the reference payload length.

- *Preservation:* if $tack.r S "ok"$ and $S ~> S'$, then $tack.r S' "ok"$.

- *Environment-Context Coherence:* if $#coh($E$, $Gamma$)$, then every binding in $E$ has the type recorded at the corresponding position in $Gamma$.

- *Capture Preserves Coherence:* if $#coh($E$, $Gamma$)$, $Gamma(y_j) = rho_j$, the captures are distinct, and $E_c = op("capture")(E; y_0, ..., y_m)$, then $#coh($E_c$, $y_0 : rho_0, ..., y_m : rho_m$)$.

- *Allocation Preserves Store Typing:* if $tack.r S "ok"$, $a in.not op("dom")(S)$, and $tack.r v_i : tau_i$ for each cell, then $tack.r S, a -> [v_0, ..., v_n] "ok"$.

- *Update Preserves Store Typing:* if $tack.r S "ok"$, $tack.r a : #Ref [tau_0, ..., tau_n]$, $0 <= i <= n$, and $tack.r v : tau_i$, then $tack.r S[a[i] |-> v] "ok"$.

- *Determinacy:* each machine state has at most one successor. Consequently, if evaluation terminates, the terminal value and final store are unique.
