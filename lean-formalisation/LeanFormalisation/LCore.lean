import LeanFormalisation.LBase

/-!
# LCore: CPS-style core language for Lbase

LCore is a continuation-passing style (CPS) intermediate language that makes all control
flow explicit. It is designed as a lowering target for Lbase, with the goal of eventually
proving a simulation theorem between the two.

## Key design decisions

- **Atoms** are trivially-evaluable expressions (variables, constants).
- **All intermediate results are named** via `letVal`, `letPrim`, `letUnPrim`.
- **Control flow is explicit** via `letCont`/`jump`/`ite`.
- **Mutable state** is retained via `assign` to match Lbase's mutable variables.
- **Continuations are recursive** (`letCont` binds a continuation visible in its own body),
  which is needed to encode `while` loops.
- **Environment restoration on jump**: when jumping to a continuation, the environment is
  restored to the state at the point of definition (dropping locally-declared variables),
  then the continuation argument is pushed.
-/

namespace LCore

/-! ## Syntax -/

/-- Atoms: trivially-evaluable terms that require no computation. -/
inductive Atom
| var (x : VarName)
| true
| false
| nat (n : Nat)
| unit
deriving Repr, Inhabited

/-- Continuation names, de Bruijn indexed into the continuation store.
    Index 0 refers to the most recently bound continuation. -/
abbrev ContName := Nat

/-- CPS terms. Every non-tail operation binds its result and continues with a body. -/
inductive Term
| letVal (a : Atom) (body : Term)
    -- ^ Bind the value of atom `a` as a new variable; continue with `body`.
| letPrim (op : BinOp) (a₁ a₂ : Atom) (body : Term)
    -- ^ Compute `op(a₁, a₂)`, bind the result; continue with `body`.
| letUnPrim (op : UnOp) (a : Atom) (body : Term)
    -- ^ Compute `op(a)`, bind the result; continue with `body`.
| letCont (contBody : Term) (rest : Term)
    -- ^ Bind a (recursive) continuation whose body is `contBody` (with one argument
    --   at de Bruijn index 0).  The continuation is in scope in both `contBody`
    --   (for recursion) and `rest`.
| ite (cond : Atom) (thenBranch elseBranch : Term)
    -- ^ Branch on a boolean atom.
| jump (k : ContName) (a : Atom)
    -- ^ Jump to continuation `k` with argument `a`.
    --   Restores the environment to the state when `k` was defined, then pushes `a`.
| assign (x : VarName) (a : Atom) (body : Term)
    -- ^ Mutate variable `x` to the value of `a`; continue with `body`.
| halt (a : Atom)
    -- ^ Terminate, producing the value of `a`.
deriving Inhabited

/-! ## Operational Semantics -/

/-- Evaluate an atom in an environment. -/
def Atom.eval (E : Environment) : Atom → Value
| .var x => E[x]!
| .true => .True
| .false => .False
| .nat n => .Nat n
| .unit => .Unit

/-- A continuation closure pairs a body term with the environment size at definition. -/
structure ContClosure where
  body : Term
  envSize : Nat
deriving Inhabited

/-- Continuation store: a list of closures, de Bruijn indexed (head = most recent). -/
abbrev ContStore := List ContClosure

/-- Machine state: current term, value environment, and continuation store. -/
abbrev State := Term × Environment × ContStore

/-- Restore the environment to its bottom `n` entries by dropping recent bindings.
    E.g., if `E = [z, y, x, w]` (length 4) and `n = 2`, the result is `[x, w]`. -/
def restoreEnv (E : Environment) (n : Nat) : Environment :=
  E.drop (E.length - n)

/-- Small-step operational semantics for LCore. -/
inductive Step : State → State → Prop
| letVal (a : Atom) (body : Term) (E : Environment) (S : ContStore) :
    Step
      ⟨.letVal a body, E, S⟩
      ⟨body, a.eval E :: E, S⟩
| letPrim (op : BinOp) (a₁ a₂ : Atom) (body : Term)
    (E : Environment) (S : ContStore) (result : Value) :
    op.step (a₁.eval E) (a₂.eval E) result →
    Step
      ⟨.letPrim op a₁ a₂ body, E, S⟩
      ⟨body, result :: E, S⟩
| letUnPrim (op : UnOp) (a : Atom) (body : Term)
    (E : Environment) (S : ContStore) (result : Value) :
    op.step (a.eval E) result →
    Step
      ⟨.letUnPrim op a body, E, S⟩
      ⟨body, result :: E, S⟩
| letCont (contBody rest : Term) (E : Environment) (S : ContStore) :
    Step
      ⟨.letCont contBody rest, E, S⟩
      ⟨rest, E, ⟨contBody, E.length⟩ :: S⟩
| iteTrue (cond : Atom) (e₁ e₂ : Term) (E : Environment) (S : ContStore) :
    cond.eval E = .True →
    Step
      ⟨.ite cond e₁ e₂, E, S⟩
      ⟨e₁, E, S⟩
| iteFalse (cond : Atom) (e₁ e₂ : Term) (E : Environment) (S : ContStore) :
    cond.eval E = .False →
    Step
      ⟨.ite cond e₁ e₂, E, S⟩
      ⟨e₂, E, S⟩
| jump (k : ContName) (a : Atom) (E : Environment) (S : ContStore) :
    Step
      ⟨.jump k a, E, S⟩
      ⟨(S[k]!).body, a.eval E :: restoreEnv E (S[k]!).envSize, S⟩
| assign (x : VarName) (a : Atom) (body : Term) (E : Environment) (S : ContStore) :
    Step
      ⟨.assign x a body, E, S⟩
      ⟨body, E.set x (a.eval E), S⟩

/-- A state is terminal when the current term is `halt`. -/
def State.isTerminal : State → Prop
| ⟨.halt _, _, _⟩ => True
| _ => False

/-- Initial state for a term. -/
def initState (t : Term) : State := ⟨t, [], []⟩

/-- Extract the result value from a halted state. -/
def State.result : State → Option Value
| ⟨.halt a, E, _⟩ => some (a.eval E)
| _ => none

/-- Reflexive-transitive closure of the step relation. -/
inductive MultiStep : State → State → Prop
| refl (s : State) : MultiStep s s
| step (s₁ s₂ s₃ : State) : Step s₁ s₂ → MultiStep s₂ s₃ → MultiStep s₁ s₃

/-! ## Type System -/

/-- Atom typing: `AtomTyp Γ a τ` means atom `a` has type `τ` in context `Γ`. -/
inductive AtomTyp : Ctx → Atom → Ty → Prop
| var (x : VarName) (type : Ty) (Γ : Ctx) :
    (Γ(x) = type) →
    AtomTyp Γ (.var x) type
| true :
    AtomTyp Γ .true .bool
| false :
    AtomTyp Γ .false .bool
| nat (n : Nat) :
    AtomTyp Γ (.nat n) .nat
| unit :
    AtomTyp Γ .unit .unit

/-- Continuation type: the argument type and the saved variable context. -/
structure ContTy where
  argType : Ty
  savedCtx : Ctx
deriving Repr

/-- Continuation context: a list of continuation types, de Bruijn indexed. -/
abbrev ContCtx := List ContTy

/-- Term well-formedness: `TermTyp Γ Δ t` means term `t` is well-typed
    in variable context `Γ` and continuation context `Δ`. -/
inductive TermTyp : Ctx → ContCtx → Term → Prop
| letVal (Γ : Ctx) (Δ : ContCtx) (a : Atom) (body : Term) (τ : Ty) :
    AtomTyp Γ a τ →
    TermTyp (τ :: Γ) Δ body →
    TermTyp Γ Δ (.letVal a body)
| letPrim (Γ : Ctx) (Δ : ContCtx) (op : BinOp) (a₁ a₂ : Atom) (body : Term) :
    AtomTyp Γ a₁ op.args.1 →
    AtomTyp Γ a₂ op.args.2 →
    TermTyp (op.args.3 :: Γ) Δ body →
    TermTyp Γ Δ (.letPrim op a₁ a₂ body)
| letUnPrim (Γ : Ctx) (Δ : ContCtx) (op : UnOp) (a : Atom) (body : Term) :
    AtomTyp Γ a op.args.1 →
    TermTyp (op.args.2 :: Γ) Δ body →
    TermTyp Γ Δ (.letUnPrim op a body)
| letCont (Γ : Ctx) (Δ : ContCtx) (contBody rest : Term) (argTy : Ty) :
    -- The continuation body is typed with the argument pushed onto the current context.
    -- The continuation itself is in scope (recursive), with savedCtx = Γ.
    TermTyp (argTy :: Γ) (⟨argTy, Γ⟩ :: Δ) contBody →
    -- The rest is typed in the original context with the continuation in scope.
    TermTyp Γ (⟨argTy, Γ⟩ :: Δ) rest →
    TermTyp Γ Δ (.letCont contBody rest)
| ite (Γ : Ctx) (Δ : ContCtx) (cond : Atom) (e₁ e₂ : Term) :
    AtomTyp Γ cond .bool →
    TermTyp Γ Δ e₁ →
    TermTyp Γ Δ e₂ →
    TermTyp Γ Δ (.ite cond e₁ e₂)
| jump (Γ : Ctx) (Δ : ContCtx) (k : ContName) (a : Atom) (ct : ContTy) :
    k < Δ.length →
    Δ[k]? = some ct →
    AtomTyp Γ a ct.argType →
    TermTyp Γ Δ (.jump k a)
| assign (Γ : Ctx) (Δ : ContCtx) (x : VarName) (a : Atom) (body : Term) (τ : Ty) :
    (Γ(x) = τ) →
    AtomTyp Γ a τ →
    TermTyp Γ Δ body →
    TermTyp Γ Δ (.assign x a body)
| halt (Γ : Ctx) (Δ : ContCtx) (a : Atom) (τ : Ty) :
    AtomTyp Γ a τ →
    TermTyp Γ Δ (.halt a)

/-! ## Examples

Encoding of Lbase constructs in LCore:

### Sequence `s₁; s₂`
Simply concatenate the CPS translations of s₁ and s₂.

### `var x : τ = e`
Translate `e` to atoms/let-bindings, then the final value is bound with `letVal`.

### `if c then e₁ else e₂` (as expression producing a value)
```
  <translate c to atom ac>
  letcont k(result) = <rest of program using result> in
  ite ac
    (<translate e₁ to atom a₁>; jump k a₁)
    (<translate e₂ to atom a₂>; jump k a₂)
```

### `while c body`
```
  letcont exit(result) = <rest of program> in
  letcont loop(dummy) =
    <translate c to atom ac>
    ite ac
      (<translate body>; jump loop unit)
      (jump exit unit)
  in
  jump loop unit
```

### `break`
```
  jump exit unit
```
where `exit` is the continuation bound by the enclosing while.

### `scope { s; e }`
```
  letcont k(result) = <rest of program using result> in
  <translate s>
  <translate e to atom a>
  jump k a
```
The jump to `k` restores the environment to the point before the scope,
effectively discarding locally-declared variables.
-/

end LCore
