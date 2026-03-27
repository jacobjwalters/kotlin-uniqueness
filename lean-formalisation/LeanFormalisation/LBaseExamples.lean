import LeanFormalisation.LBaseElab
import LeanFormalisation.LBaseEval

/-! # Example LBase programs

Each example is written using the elaborator (named variables),
then executed with the evaluator to show the final result and
full stepping trace.
-/

/-! ## Example 1: Simple arithmetic

```pseudo
var x : nat := 5
var y : nat := 3
x := x + y
```

Final environment: `[Nat 3, Nat 8]` (y=3, x=8; newest-declared first)
-/

def ex1 : Lang .Stmt := elaborate do
  eStmts [
    eDecl "x" .nat (eNat 5),
    eDecl "y" .nat (eNat 3),
    eAssign "x" (eAdd (eVar "x") (eVar "y"))
  ]

#eval! runProgram ex1
-- [Value.Nat 3, Value.Nat 8]  (y=3, x=8)

#eval! traceProgram ex1


/-! ## Example 2: If-then-else

```pseudo
var x : nat := 10
var y : nat := 10
do (if x == y then
      { x := 1; unit }
    else
      { y := 2; unit })
```

Since x == y (both 10), the true branch runs: x becomes 1.
Final environment: `[Nat 10, Nat 1]` (y=10, x=1)
-/

def ex2 : Lang .Stmt := elaborate do
  eStmts [
    eDecl "x" .nat (eNat 10),
    eDecl "y" .nat (eNat 10),
    eDo (eIf (eNatEq (eVar "x") (eVar "y"))
      (eScope (eAssign "x" (eNat 1)) eUnit)
      (eScope (eAssign "y" (eNat 2)) eUnit))
  ]

#eval! runProgram ex2
-- [Value.Nat 10, Value.Nat 1]  (y=10, x=1)

#eval! traceProgram ex2


/-! ## Example 3: While loop (summation)

```pseudo
var counter : nat := 5
var acc : nat := 0
do while (not (isZero counter)) {
  acc := acc + counter
  counter := counter - 1
  unit
}
```

Computes 5 + 4 + 3 + 2 + 1 = 15.
Final environment: `[Nat 15, Nat 0]` (acc=15, counter=0)

We encode `not (isZero x)` as `if isZero(x) then false else true`
since the language has no boolean-not primitive.
-/

def ex3 : Lang .Stmt := elaborate do
  eStmts [
    eDecl "counter" .nat (eNat 5),
    eDecl "acc" .nat (eNat 0),
    eDo (eWhile
      (eIf (eIsZero (eVar "counter")) eFalse eTrue)
      (eScope
        (eStmts [
          eAssign "acc" (eAdd (eVar "acc") (eVar "counter")),
          eAssign "counter" (eSub (eVar "counter") (eNat 1))
        ])
        eUnit))
  ]

#eval! runProgram ex3
-- [Value.Nat 15, Value.Nat 0]  (acc=15, counter=0)

#eval! traceProgram ex3


/-! ## Example 4: Nested scopes

```pseudo
var x : nat := 1
do {
  var y : nat := 10
  x := x + y
  ; x
}
x := x + x
```

x starts at 1, becomes 11 inside the scope, then 22 after doubling.
The scope-local variable y is cleaned up when the scope exits.
Final environment: `[Nat 22]`
-/

def ex4 : Lang .Stmt := elaborate do
  eStmts [
    eDecl "x" .nat (eNat 1),
    eDo (eScope
      (eStmts [
        eDecl "y" .nat (eNat 10),
        eAssign "x" (eAdd (eVar "x") (eVar "y"))
      ])
      (eVar "x")),
    eAssign "x" (eAdd (eVar "x") (eVar "x"))
  ]

#eval! runProgram ex4
-- [Value.Nat 22]  (x=22)

#eval! traceProgram ex4


/-! ## Example 5: Break from loop

```pseudo
var x : nat := 0
do while true {
  x := x + 1
  do (if x == 3 then { break } else { unit })
  unit
}
```

The loop increments x until it reaches 3, then breaks.
Break restores the environment to the loop entry point.
Final environment: `[Nat 3]`
-/

def ex5 : Lang .Stmt := elaborate do
  eStmts [
    eDecl "x" .nat (eNat 0),
    eDo (eWhile eTrue
      (eScope
        (eStmts [
          eAssign "x" (eAdd (eVar "x") (eNat 1)),
          eDo (eIf (eNatEq (eVar "x") (eNat 3))
            (eScope (pure (.Do (.Break 0))) eUnit)
            eUnit)
        ])
        eUnit))
  ]

#eval! runProgram ex5
-- [Value.Nat 3]  (x=3)

#eval! traceProgram ex5


/-! ## Example 6: Fibonacci (iterative)

```pseudo
var a : nat := 0
var b : nat := 1
var n : nat := 10
do while (not (isZero n)) {
  var temp : nat := b
  b := a + b
  a := temp
  n := n - 1
  unit
}
```

After 10 iterations: a = fib(10) = 55, b = fib(11) = 89, n = 0.
Final environment: `[Nat 0, Nat 89, Nat 55]` (n=0, b=89, a=55)
-/

def ex6_fib : Lang .Stmt := elaborate do
  eStmts [
    eDecl "a" .nat (eNat 0),
    eDecl "b" .nat (eNat 1),
    eDecl "n" .nat (eNat 10),
    eDo (eWhile
      (eIf (eIsZero (eVar "n")) eFalse eTrue)
      (eScope
        (eStmts [
          eDecl "temp" .nat (eVar "b"),
          eAssign "b" (eAdd (eVar "a") (eVar "b")),
          eAssign "a" (eVar "temp"),
          eAssign "n" (eSub (eVar "n") (eNat 1))
        ])
        eUnit))
  ]

#eval! runProgram ex6_fib
-- [Value.Nat 0, Value.Nat 89, Value.Nat 55]  (n=0, b=89, a=55)

#eval! traceProgram ex6_fib
