import Mathlib.Data.Nat.Notation

inductive Expr where
| nat (n : ℕ)
| var (ix : ℕ)
| add (lhs rhs : Expr)
| bind (binding body : Expr)

@[grind]
inductive TyExpr : ℕ → Expr → Prop where
| nat {ctx n} : TyExpr ctx (.nat n)
| var {ctx ix} : ix < ctx → TyExpr ctx (.var ix)
| add {ctx lhs rhs} : TyExpr ctx lhs → TyExpr ctx rhs → TyExpr ctx (.add lhs rhs)
| bind {ctx binding body}
  : TyExpr ctx binding → TyExpr (ctx + 1) body
  → TyExpr ctx (.bind binding body)

-- bind (nat 3) $ bind (nat 5) (var 0) ~> 5

-- CEK states:
-- <e, E, K>
-- <K, E, v>

abbrev Env := List ℕ

inductive Cont where
| done
| add1 (rhs : Expr) (env : Env) (next : Cont)
| add2 (lhsv : ℕ) (next : Cont)
| bind1 (body : Expr) (env : Env) (next : Cont)
| bind2 (env : Env) (next : Cont)

inductive CEKState where
| expr (e : Expr) (env : Env) (next : Cont)
| cont (next : Cont) (result : ℕ)

@[grind]
inductive TyCont : ℕ → Cont → Prop where
| done {ctx} : TyCont ctx .done
| add1 {ctx rhs env next}
  : env.length = ctx → TyExpr ctx rhs → TyCont ctx next → TyCont ctx (.add1 rhs env next)
| add2 {ctx lhsv next}
  : TyCont ctx next → TyCont ctx (.add2 lhsv next)
| bind1 {ctx body env next}
  : env.length = ctx → TyExpr (ctx + 1) body → TyCont ctx next → TyCont ctx (.bind1 body env next)
| bind2 {ctx env next}
  : env.length = ctx → TyCont ctx next → TyCont ctx (.bind2 env next)

@[grind]
inductive TyState (ctx : ℕ) : CEKState → Prop where
| expr {e env next}
  : TyExpr ctx e → env.length = ctx → TyCont ctx next
  → TyState ctx (.expr e env next)
| cont {next n}
  : TyCont ctx next → TyState ctx (.cont next n)

inductive CEKStep : CEKState → CEKState → Prop where
| expr_nat {n env next}
  : CEKStep (.expr (.nat n) env next) (.cont next n)
| expr_var {ix n env next}
  : env[ix]? = some n
  → CEKStep (.expr (.var ix) env next) (.cont next n)
| expr_add {lhs rhs env next}
  : CEKStep (.expr (.add lhs rhs) env next) (.expr lhs env (.add1 rhs env next))
| expr_cont {binding body env next}
  : CEKStep (.expr (.bind binding body) env next)
            (.expr binding env (.bind1 body env next))
| cont_add1 {rhs n env next}
  : CEKStep (.cont (.add1 rhs env next) n) (.expr rhs env (.add2 n next))
| cont_add2 {lhsv rhsv next}
  : CEKStep (.cont (.add2 lhsv next) rhsv) (.cont next (lhsv + rhsv))
| cont_bind1 {n body env next}
  : CEKStep (.cont (.bind1 body env next) n)
            (.expr body (n :: env) next)

theorem preservation {ctx st st'}
    : CEKStep st st' → TyState ctx st
    → ∃ ctx', TyState ctx' st' := by
  intro step tyst
  cases step <;> try (exists ctx; grind)
  cases tyst
  rename_i tycont
  cases tycont
  exists (ctx + 1)
  repeat (first | constructor | assumption)
  simpa
  
