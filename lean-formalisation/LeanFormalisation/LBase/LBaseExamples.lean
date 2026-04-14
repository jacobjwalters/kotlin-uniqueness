import LeanFormalisation.LBase.Eval.LBaseElab
import LeanFormalisation.LBase.Eval.LBaseEval

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
    var_ "x" .nat 5,
    var_ "y" .nat 3,
    set_ "x" (v "x" + v "y")
  ]

#eval! runProgram ex1
-- [Value.Nat 3, Value.Nat 8]  (y=3, x=8)

#eval! traceProgram ex1


/-! ## Example 2: If-then-else

```pseudo
var x : nat := 10
var y : nat := 10
if x == y then x := 1 else y := 2
```

Since x == y (both 10), the true branch runs: x becomes 1.
Final environment: `[Nat 10, Nat 1]` (y=10, x=1)
-/

def ex2 : Lang .Stmt := elaborate do
  eStmts [
    var_ "x" .nat 10,
    var_ "y" .nat 10,
    if_ (v "x" .==. v "y")
      [set_ "x" 1]
      [set_ "y" 2]
  ]

#eval! runProgram ex2
-- [Value.Nat 10, Value.Nat 1]  (y=10, x=1)

#eval! traceProgram ex2


/-! ## Example 3: While loop (summation)

```pseudo
var counter : nat := 5
var acc : nat := 0
while counter != 0 {
  acc := acc + counter
  counter := counter - 1
}
```

Computes 5 + 4 + 3 + 2 + 1 = 15.
Final environment: `[Nat 15, Nat 0]` (acc=15, counter=0)
-/

def ex3 : Lang .Stmt := elaborate do
  eStmts [
    var_ "counter" .nat 5,
    var_ "acc" .nat 0,
    while_ (eNotZero (v "counter")) [
      set_ "acc" (v "acc" + v "counter"),
      set_ "counter" (v "counter" - 1)
    ]
  ]

#eval! runProgram ex3
-- [Value.Nat 15, Value.Nat 0]  (acc=15, counter=0)

#eval! traceProgram ex3


/-! ## Example 4: Nested scopes

```pseudo
var x : nat := 1
do { var y : nat := 10; x := x + y; return x }
x := x + x
```

x starts at 1, becomes 11 inside the scope, then 22 after doubling.
The scope-local variable y is cleaned up when the scope exits.
Final environment: `[Nat 22]`
-/

def ex4 : Lang .Stmt := elaborate do
  eStmts [
    var_ "x" .nat 1,
    eDo (scopeReturn
      [var_ "y" .nat 10,
       set_ "x" (v "x" + v "y")]
      (v "x")),
    set_ "x" (v "x" + v "x")
  ]

#eval! runProgram ex4
-- [Value.Nat 22]  (x=22)

#eval! traceProgram ex4


/-! ## Example 5: Break from loop

```pseudo
var x : nat := 0
while true {
  x := x + 1
  if x == 3 then break else skip
}
```

The loop increments x until it reaches 3, then breaks.
Break restores the environment to the loop entry point.
Final environment: `[Nat 3]`
-/

def ex5 : Lang .Stmt := elaborate do
  eStmts [
    var_ "x" .nat 0,
    while_ eTrue [
      set_ "x" (v "x" + 1),
      if_ (v "x" .==. 3)
        [break_]
        []
    ]
  ]

#eval! runProgram ex5
-- [Value.Nat 3]  (x=3)

#eval! traceProgram ex5


/-! ## Example 6: Fibonacci (iterative)

```pseudo
var a : nat := 0
var b : nat := 1
var n : nat := 10
while n != 0 {
  var temp : nat := b
  b := a + b
  a := temp
  n := n - 1
}
```

After 10 iterations: a = fib(10) = 55, b = fib(11) = 89, n = 0.
Final environment: `[Nat 0, Nat 89, Nat 55]` (n=0, b=89, a=55)
-/

def ex6_fib : Lang .Stmt := elaborate do
  eStmts [
    var_ "a" .nat 0,
    var_ "b" .nat 1,
    var_ "n" .nat 10,
    while_ (eNotZero (v "n")) [
      var_ "temp" .nat (v "b"),
      set_ "b" (v "a" + v "b"),
      set_ "a" (v "temp"),
      set_ "n" (v "n" - 1)
    ]
  ]

#eval! runProgram ex6_fib
-- [Value.Nat 0, Value.Nat 89, Value.Nat 55]  (n=0, b=89, a=55)

#eval! traceProgram ex6_fib
