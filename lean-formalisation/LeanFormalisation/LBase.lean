import Mathlib.Data.Finmap
import Mathlib.Tactic.Basic

abbrev VarName := Nat
inductive Ty
| nat
| bool
| unit
deriving Repr, Inhabited, DecidableEq --! qtz: added DecidableEq


inductive Value
| True
| False
| Nat (n : Nat)
| Unit
deriving Inhabited, Repr, DecidableEq --! qtz: added DecidableEq

inductive BinOp
| Add
| Sub
| NatEq
| BoolEq
deriving Repr, DecidableEq --! qtz: added this line

structure BinOpArgs where
  arg₁ : Ty
  arg₂ : Ty
  out : Ty

inductive UnOp
| IsZero
deriving Repr, DecidableEq --! qtz: added this line

structure UnOpArgs where
  arg : Ty
  out : Ty

def BinOp.args : BinOp → BinOpArgs
| .Add => ⟨.nat, .nat, .nat⟩
| .Sub => ⟨.nat, .nat, .nat⟩
| .NatEq => ⟨.nat, .nat, .bool⟩
| .BoolEq => ⟨.bool, .bool, .bool⟩

inductive BinOp.step : BinOp → Value → Value → Value → Prop
| add (n m : Nat) : BinOp.step .Add (.Nat n) (.Nat m) (.Nat (n + m))
| sub (n m : Nat) : BinOp.step .Sub (.Nat n) (.Nat m) (.Nat (n - m))
| natEqTrue (n : Nat) : BinOp.step .NatEq (.Nat n) (.Nat n) .True
| natEqFalse (n m : Nat) : n ≠ m → BinOp.step .NatEq (.Nat n) (.Nat m) .False
| boolEqTT : BinOp.step .BoolEq .True .True .True
| boolEqFF : BinOp.step .BoolEq .False .False .True
| boolEqTF : BinOp.step .BoolEq .True .False .False
| boolEqFT : BinOp.step .BoolEq .False .True .False

def UnOp.args : UnOp → UnOpArgs
| .IsZero => ⟨.nat, .bool⟩

inductive UnOp.step : UnOp → Value → Value → Prop
| isZeroTrue : UnOp.step .IsZero (.Nat 0) .True
| isZeroFalse (n : Nat) : n ≠ 0 → UnOp.step .IsZero (.Nat n) .False

inductive Tag
| Expr
| Stmt
deriving Repr, DecidableEq --! qtz: added this line

inductive Lang : Tag → Type
-- # Expr
| Var (x : VarName) : Lang .Expr
| True : Lang .Expr
| False : Lang .Expr
| Nat (n : Nat) : Lang .Expr
| Unit : Lang .Expr
| BinOp (arg₁ : Lang .Expr) (arg₂ : Lang .Expr) (op : BinOp) : Lang .Expr
| UnOp (arg : Lang .Expr) (op : UnOp) : Lang .Expr
| If (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) : Lang .Expr
| While (cond : Lang .Expr) (body : Lang .Expr) : Lang .Expr
| Break (l : Nat) : Lang .Expr
| Scope (s : Lang .Stmt) (res : Lang .Expr) : Lang .Expr
-- # Stmt
| Decl (type : Ty) (e : Lang .Expr) : Lang .Stmt
| Assign (x : VarName) (e : Lang .Expr) : Lang .Stmt
| Seq (s₁ : Lang .Stmt) (s₂ : Lang .Stmt) : Lang .Stmt
| Do (e : Lang .Expr) : Lang .Stmt
deriving Repr, DecidableEq --! qtz: added this line

notation:100 s₁:100 ";" s₂:101 => Lang.Seq s₁ s₂
notation x "::=" exp => Lang.Assign x exp
abbrev Ctx := List Ty
abbrev JCtx := List Nat
notation Γ₁ "("x")" "=" type => x < List.length Γ₁ ∧ Γ₁[x]? = Option.some type

def langShift {tg : Tag} (l : Nat) : Lang tg → Lang tg
-- # Expr
| .Var (x : VarName) =>
  .Var (x + l)
| .True =>
  .True
| .False =>
  .False
| .Nat (n : Nat) =>
  .Nat n
| .Unit =>
  .Unit
| .BinOp (arg₁ : Lang .Expr) (arg₂ : Lang .Expr) (op : BinOp) =>
  .BinOp (langShift l arg₁) (langShift l arg₂) op
| .UnOp (arg : Lang .Expr) (op : UnOp) =>
  .UnOp (langShift l arg) op
| .If (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) =>
  .If (langShift l cond) (langShift l e₁) (langShift l e₂)
| .While (cond : Lang .Expr) (body : Lang .Expr) =>
  .While (langShift l cond) (langShift l body)
| .Break l =>
  .Break l
| .Scope (s : Lang .Stmt) (res : Lang .Expr) =>
  .Scope (langShift l s) (langShift l res)
-- # Stmt
| .Decl (type : Ty) (e : Lang .Expr) =>
  .Decl type (langShift l e)
| .Assign (x : VarName) (e : Lang .Expr) =>
  .Assign (x + l) (langShift l e)
| .Seq (s₁ : Lang .Stmt) (s₂ : Lang .Stmt) =>
  .Seq (langShift l s₁) (langShift l s₂)
| .Do (e : Lang .Expr) =>
  .Do (langShift l e)

section Types

inductive TypR : Tag → Type
| Stmt (Γ₁ : Ctx) : TypR .Stmt
| Expr (type : Ty) : TypR .Expr

inductive Typ : (tg : Tag) → JCtx → Ctx → Lang tg → TypR tg → Prop
-- # Expr
| TrueConst :
  Typ .Expr Δ₁ Γ₁ .True (.Expr .bool)
| FalseConst :
  Typ .Expr Δ₁ Γ₁ .False (.Expr .bool)
| NatConst (n : Nat) :
  Typ .Expr Δ₁ Γ₁ (.Nat n) (.Expr .nat)
| UnitConst :
  Typ .Expr Δ₁ Γ₁ .Unit (.Expr .unit)
| VarAccess (x : VarName) (type : Ty) :
  (Γ₁(x) = type) →
  Typ .Expr Δ₁ Γ₁ (.Var x) (.Expr type)
| UnOp (arg : Lang .Expr) (op : UnOp) :
  Typ .Expr Δ₁ Γ₁ arg (.Expr op.args.1) →
  Typ .Expr Δ₁ Γ₁ (.UnOp arg op) (.Expr op.args.2)
| BinOp (arg₁ arg₂ : Lang .Expr) (op : BinOp) :
  Typ .Expr Δ₁ Γ₁ arg₁ (.Expr op.args.1) →
  Typ .Expr Δ₁ Γ₁ arg₂ (.Expr op.args.2) →
  Typ .Expr Δ₁ Γ₁ (.BinOp arg₁ arg₂ op) (.Expr op.args.3)
| IfExpr (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ cond (.Expr .bool) →
  Typ .Expr Δ₁ Γ₁ e₁ (.Expr type) →
  Typ .Expr Δ₁ Γ₁ e₂ (.Expr type) →
  Typ .Expr Δ₁ Γ₁ (.If cond e₁ e₂) (.Expr type)
| WhileExpr (cond : Lang .Expr) (body : Lang .Expr) :
  Typ .Expr Δ₁ Γ₁ cond (.Expr .bool) →
  Typ .Expr (Γ₁.length :: Δ₁) Γ₁ body (.Expr .unit) →
  Typ .Expr Δ₁ Γ₁ (.While cond body) (.Expr .unit)
| BreakExpr (type : Ty) (l : Nat) :
  l < Δ₁.length →
  Typ .Expr Δ₁ Γ₁ (.Break l) (.Expr .unit)
| ScopeExpr (s : Lang .Stmt) (e : Lang .Expr) (type : Ty) :
  Typ .Stmt Δ₁ Γ₁ s (.Stmt Γ₂) →
  Typ .Expr Δ₁ Γ₂ e (.Expr type) →
  Typ .Expr Δ₁ Γ₁ (.Scope s e) (.Expr type)
-- # Stmt
| VarDecl (e : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) →
  Typ .Stmt Δ₁ Γ₁ (.Decl type e) (.Stmt (type :: Γ₁))
| VarAssign (x : VarName) (e : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) → (Γ₁(x) = type) →
  Typ .Stmt Δ₁ Γ₁ (.Assign x e) (.Stmt Γ₁)
| Seq (s₁ s₂ : Lang .Stmt) :
  Typ .Stmt Δ₁ Γ₁ s₁ (.Stmt Γ₂) →
  Typ .Stmt Δ₁ Γ₂ s₂ Γ₃ →
  Typ .Stmt Δ₁ Γ₁ (s₁; s₂) Γ₃
| Do (e : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) →
  Typ .Stmt Δ₁ Γ₁ (.Do e) (.Stmt Γ₁)

end Types

section TypeProperties

theorem lang_det (Γ₁ : Ctx) (tg : Tag) (Γ₂ Γ₃ : TypR tg) (s : Lang tg) :
  Typ tg Δ₁ Γ₁ s Γ₂ → Typ tg Δ₁ Γ₁ s Γ₃ → Γ₂ = Γ₃ := by
    intro h1 h2
    unhygienic induction h1 <;> try grind
    all_goals
    { cases h2
      grind }

theorem typ_permutation (Γ₁ Γ₂ : Ctx) (tg : Tag) (Γ₃ : TypR tg) (e : Lang tg) :
  (∀ tp x, (Γ₁(x) = tp) ↔ Γ₂(x) = tp) →
  Typ tg Δ₁ Γ₁ e Γ₃ → Typ tg Δ₁ Γ₂ e Γ₃ := by
    intro hg
    have leq : Γ₁.length = Γ₂.length := by
      by_cases h1: Γ₂.length < Γ₁.length
      { have hi := hg Γ₁[Γ₁.length - 1] (Γ₁.length - 1)
        clear hg
        grind }
      by_cases h2: Γ₁.length < Γ₂.length
      { have hi := hg Γ₂[Γ₂.length - 1] (Γ₂.length - 1)
        clear hg
        grind }
      grind
    have : Γ₁ = Γ₂ := by
      ext
      clear e
      rename_i idx el
      have hi := hg el idx
      by_cases hid: idx < Γ₁.length
      { clear hg
        grind }
      grind
    rw [this]
    grind

def TypR.extL (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₁ ++ Γ₂)

def TypR.extR (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₂ ++ Γ₁)

lemma stmt_mono (Γ₁ : Ctx) (tg : Tag) (Γ₂ : TypR tg) (s : Lang tg) :
  Typ tg Δ₁ Γ₁ s Γ₂ → ∃ Γ₃ : TypR tg, Γ₃.extR Γ₁ = Γ₂ := by
    intro hs
    unhygienic induction hs <;> try grind
    all_goals try
    { eapply Exists.intro
      rw [TypR.extR] }
    { eapply Exists.intro
      rw [TypR.extR]
      rotate_left
      { exact [type] }
      grind }
    { eapply Exists.intro
      rw [TypR.extR]
      rotate_left
      { exact [] }
      grind }
    { have ⟨g, hg⟩:= a_ih
      unhygienic cases g
      have ⟨g1, hg1⟩:= a_ih_1
      unhygienic cases g1
      simp only [TypR.extR] at *
      exists TypR.Stmt (Γ₁_3 ++ Γ₁_2)
      grind }
    eapply Exists.intro
    rw [TypR.extR]
    rotate_left
    { exact [] }
    grind


lemma stmt_decl (type : Ty) : Typ .Stmt Δ₁ Γ₁ (.Decl type e) (.Stmt Γ₂) → Γ₂ = type :: Γ₁ := by
  intro h
  cases h
  rfl

lemma p_index_r (Γ₁ Γ₂ : Ctx) (i : Nat) :
  i < Γ₁.length →
  (Γ₂ ++ Γ₁)[i + Γ₂.length]? = Γ₁[i]? := by
    intro hlt
    induction Γ₂ with
    | nil => simp
    | cons _ _ => grind


theorem lang_extension (tg : Tag) (e : Lang tg) (res : TypR tg)
    (Γ₁ Γ₂ : Ctx) :
    Typ tg Δ₁ Γ₁ e res →
    Typ tg (Δ₁.map (fun x => x + Γ₂.length)) (Γ₁ ++ Γ₂) (e)
      (res.extR Γ₂) := by
    intro h
    unhygienic induction h generalizing Γ₂ <;>try solve_by_elim
    { rw [TypR.extR]
      apply Typ.VarAccess
      grind }
    { apply Typ.WhileExpr
      { solve_by_elim }
      { -- map distributes over cons: map f (n :: Δ) = f n :: map f Δ
        -- and f n = n + len = (Γ₁ ++ Γ₂).length
        have h := a_ih_1 Γ₂
        simp only [List.map_cons, List.length_append,
          TypR.extR] at h ⊢
        exact h } }
    { exact Typ.BreakExpr .unit _
        (by rw [List.length_map]; exact a) }
    { solve_by_elim [Typ.ScopeExpr] }
    { rw [TypR.extR]
      apply Typ.VarAssign _ _ _ (a_ih Γ₂)
      grind }
    solve_by_elim [Typ.Seq]

theorem typ_ext (e : Lang .Expr) (type : Ty) (Γ₁ Γ₂ : Ctx) :
    Typ .Expr Δ₁ Γ₁ e (.Expr type) →
    Typ .Expr (Δ₁.map (fun x => x + Γ₂.length)) (Γ₁ ++ Γ₂) e
      (.Expr type) := by
    intro h
    have lm := lang_extension _ _ _ _ Γ₂ h
    rw [TypR.extR] at lm
    apply lm

end TypeProperties

def liftValue : Value → Lang .Expr
| .True => .True
| .False => .False
| .Nat (n : Nat) => .Nat n
| .Unit => .Unit

def value_type : Value → Ty → Prop
| .True, .bool => True
| .False, .bool => True
| .Nat _, .nat => True
| .Unit, .unit => True
| _, _ => False

inductive Control
| sourceExpr (e : Lang .Expr)
| sourceStmt (s : Lang .Stmt)
| value (v : Value)
| skip

abbrev Environment := List Value

inductive Cont
| ifCondK (e₁ e₂ : Lang .Expr)
| declK (type : Ty)
| assignK (x : VarName)
| seqK (s : Lang .Stmt)
| binopLK (op : BinOp) (e₂ : Lang .Expr)
| binopRK (op : BinOp) (v : Value)
| unopK (op : UnOp)
| loopK (c : Lang .Expr) (body : Lang .Expr) (n : Nat)
| loopContK (c : Lang .Expr) (body : Lang .Expr) (n : Nat)
| scopeBodyK (e : Lang .Expr) (n : Nat)
| scopeExitK (n : Nat)
| exprStmtK

abbrev JStackCtx := List (Nat × List Cont)

structure CEK where
  C : Control
  E : Environment
  J : JStackCtx
  K : List Cont

-- Do we need this relation in the current Jump Context implementation?
/-
inductive PopLoopK : List Cont → List Cont → Nat → Prop
| loopK (c body : Lang .Expr) (n : Nat) (rest : List Cont) :
  PopLoopK (.loopK c body n :: rest) rest n
| loopContK (c body : Lang .Expr) (n : Nat) (rest : List Cont) :
  PopLoopK (.loopContK c body n :: rest) rest n
| skip (k : Cont) (rest result : List Cont) (n : Nat) :
  PopLoopK rest result n →
  PopLoopK (k :: rest) result n
-/

inductive Eval : CEK → CEK → Prop
-- # Expr
| Val (v : Value) :
  Eval
    ⟨.sourceExpr (liftValue v), E, J, K⟩
    ⟨.value v, E, J, K⟩
| Var (v : Value) (x : VarName) :
  Eval
    ⟨.sourceExpr (.Var x), E, J, K⟩
    ⟨.value (E[x]!), E, J, K⟩
| VarDecl (type : Ty) (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Decl type e), E, J, K⟩
    ⟨.sourceExpr e, E, J, (.declK type) :: K⟩
| Assign (x : VarName) (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Assign x e), E, J, K⟩
    ⟨.sourceExpr e, E, J, (.assignK x) :: K⟩
| Seq (s₁ s₂ : Lang .Stmt) :
  Eval
    ⟨.sourceStmt (.Seq s₁ s₂), E, J, K⟩
    ⟨.sourceStmt s₁, E, J, (.seqK s₂) :: K⟩
| ExprStmt (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Do e), E, J, K⟩
    ⟨.sourceExpr e, E, J, .exprStmtK :: K⟩
| BinOp (e₁ e₂ : Lang .Expr) (op : BinOp) :
  Eval
    ⟨.sourceExpr (.BinOp e₁ e₂ op), E, J, K⟩
    ⟨.sourceExpr e₁, E, J, (.binopLK op e₂) :: K⟩
| UnOp (e : Lang .Expr) (op : UnOp) :
  Eval
    ⟨.sourceExpr (.UnOp e op), E, J, K⟩
    ⟨.sourceExpr e, E, J, (.unopK op) :: K⟩
| If (e : Lang .Expr) (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.If e s₁ s₂), E, J, K⟩
    ⟨.sourceExpr e, E, J, (.ifCondK s₁ s₂) :: K⟩
| While (c : Lang .Expr) (body : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.While c body), E, J, K⟩
    ⟨.sourceExpr c, E, J, (.loopK c body E.length) :: K⟩
| Break (K' : List Cont) (l : Nat):
    J[l]? = some j ->
  Eval
    ⟨.sourceExpr (.Break l), E, J, K⟩
    -- was skip before, should it be .skip?
    ⟨.value .Unit, E.drop (E.length - j.1), J.drop (l + 1), j.2⟩
| Scope (s : Lang .Stmt) (e : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.Scope s e), E, J, K⟩
    ⟨.sourceStmt s, E, J, .scopeBodyK e E.length :: K⟩
-- # Cont
| IfTrue (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.value .True, E, J, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceExpr s₁, E, J, K⟩
| IfFalse (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.value .False, E, J, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceExpr s₂, E, J, K⟩
| VarDeclDone (type : Ty) (v : Value) :
  Eval
    ⟨.value v, E, J, .declK type :: K⟩
    ⟨.skip, v :: E, J, K⟩
| AssignDone (x : VarName) (v : Value) :
  Eval
    ⟨.value v, E, J, .assignK x :: K⟩
    ⟨.skip, E.set x v, J, K⟩
| SeqDone (s₂ : Lang .Stmt) :
  Eval
    ⟨.skip, E, J, .seqK s₂ :: K⟩
    ⟨.sourceStmt s₂, E, J, K⟩
| BinOpL (op : BinOp) (v₁ : Value) (e₂ : Lang .Expr) :
  Eval
    ⟨.value v₁, E, J, .binopLK op e₂ :: K⟩
    ⟨.sourceExpr e₂, E, J, .binopRK op v₁ :: K⟩
| BinOpR (op : BinOp) (v₁ v₂ result : Value) :
  op.step v₁ v₂ result →
  Eval
    ⟨.value v₂, E, J, .binopRK op v₁ :: K⟩
    ⟨.value result, E, J, K⟩
| UnOpDone (op : UnOp) (v result : Value) :
  op.step v result →
  Eval
    ⟨.value v, E, J, .unopK op :: K⟩
    ⟨.value result, E, J, K⟩
| LoopTrue (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .True, E, J, .loopK c body n :: K⟩
    ⟨.sourceExpr body, E, ⟨n, K⟩ :: J, .loopContK c body n :: K⟩
| LoopFalse (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .False, E, J, .loopK c body n :: K⟩
    ⟨.value .Unit, E.drop (E.length - n), J, K⟩
| LoopCont (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .Unit, E, ⟨n, K⟩ :: J, .loopContK c body n :: K⟩
    ⟨.sourceExpr c, E, J, .loopK c body n :: K⟩
| ScopeBody (body : Lang .Expr) (n : Nat) :
  Eval
    ⟨.skip, E, J, .scopeBodyK body n :: K⟩
    ⟨.sourceExpr body, E, J, .scopeExitK n :: K⟩
| ScopeExit (body : Lang .Expr) (n : Nat) (v : Value) :
  Eval
    ⟨.value v, E, J, .scopeExitK n :: K⟩
    ⟨.value v, E.drop (E.length - n), J, K⟩
| ExprStmtDone (v : Value) :
  Eval
    ⟨.value v, E, J, .exprStmtK :: K⟩
    ⟨.skip, E, J, K⟩

def initState (s : Lang .Stmt) : CEK := ⟨.sourceStmt s, [], [], []⟩

def terminalState (E : Environment) : CEK := ⟨.skip, E, [], []⟩

inductive ContTypeRes : Tag → Type
| Expr (type : Ty) : ContTypeRes .Expr
| Stmt : ContTypeRes .Stmt

def ctx_limit (n : Nat) : JCtx → Prop
| [] => True
| x :: _ => x ≤ n

-- # Expression Continuations
inductive ContType : (tg : Tag) → JCtx → Ctx → List Cont → ContTypeRes tg → Prop
| IfCondK (s₁ : Lang .Expr) (s₂ : Lang .Expr) (Γ₁ : Ctx) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ s₁ (.Expr type) →
  Typ .Expr Δ₁ Γ₁ s₂ (.Expr type) →
  ContType .Expr Δ₁ Γ₁ K (.Expr type) →
  ContType .Expr Δ₁ Γ₁ (.ifCondK s₁ s₂ :: K) (.Expr .bool)
| DeclK (type : Ty) (Γ₁ : Ctx) :
  ContType .Stmt Δ₁ (type :: Γ₁) K .Stmt →
  ContType .Expr Δ₁ Γ₁ (.declK type :: K) (.Expr type)
| AssignK (x : VarName) (type : Ty) (Γ₁ : Ctx) :
  (Γ₁(x) = type) →
  ContType .Stmt Δ₁ Γ₁ K .Stmt →
  ContType .Expr Δ₁ Γ₁ (.assignK x :: K) (.Expr type)
| BinOpLK (Γ₁ : Ctx) (op : BinOp) (e₂ : Lang .Expr) :
  Typ .Expr Δ₁ Γ₁ e₂ (.Expr op.args.2) →
  ContType .Expr Δ₁ Γ₁ K (.Expr op.args.out) →
  ContType .Expr Δ₁ Γ₁ (.binopLK op e₂ :: K) (.Expr op.args.1)
| BinOpRK (Γ₁ : Ctx) (op : BinOp) (v₁ : Value) :
  value_type v₁ op.args.1 →
  ContType .Expr Δ₁ Γ₁ K (.Expr op.args.out) →
  ContType .Expr Δ₁ Γ₁ (.binopRK op v₁ :: K) (.Expr op.args.2)
| UnOpK (Γ₁ : Ctx) (op : UnOp) :
  ContType .Expr Δ₁ Γ₁ K (.Expr op.args.out) →
  ContType .Expr Δ₁ Γ₁ (.unopK op :: K) (.Expr op.args.1)
-- is this rule too strong now?
| LoopK (Γ₁ : Ctx) (e : Lang .Expr) (c : Lang .Expr) :
  Typ .Expr Δ₁ Γ₁ c (.Expr .bool) →
  Typ .Expr (Γ₁.length :: Δ₁) Γ₁ e (.Expr .unit) →
  ContType .Expr Δ₁ Γ₁ K (.Expr .unit) →
  ContType .Expr Δ₁ Γ₁ (.loopK c e Γ₁.length :: K) (.Expr .bool)
| LoopContK (Γ₁ : Ctx) (e : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Typ .Expr Δ₁ Γ₁ c (.Expr .bool) →
  Typ .Expr (Γ₁.length :: Δ₁) Γ₁ e (.Expr .unit) →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr .unit) →
  ContType .Expr (Γ₁.length :: Δ₁) Γ₁ (.loopContK c e n :: K) (.Expr .unit)
| ScopeExitK (Γ₁ : Ctx) (n : Nat) (type : Ty) :
  ctx_limit n Δ₁ →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr type) →
  ContType .Expr Δ₁ Γ₁ (.scopeExitK n :: K) (.Expr type)
| ExprStmtK (Γ₁ : Ctx) (type : Ty) :
  ContType .Stmt Δ₁ Γ₁ K .Stmt →
  ContType .Expr Δ₁ Γ₁ (.exprStmtK :: K) (.Expr type)
-- # Statement Continuations
| HaltK (Γ₁ : Ctx) :
  ContType .Stmt Δ₁ Γ₁ [] .Stmt
| SeqK (Γ₁ : Ctx) (Γ₂ : Ctx) (s : Lang .Stmt) :
  Typ .Stmt Δ₁ Γ₁ s (.Stmt Γ₂) →
  ContType .Stmt Δ₁ Γ₂ K .Stmt →
  ContType .Stmt Δ₁ Γ₁ (.seqK s :: K) .Stmt
| ScopeBodyK (Γ₁ : Ctx) (e : Lang .Expr) (type : Ty) (n : Nat) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) →
  ctx_limit n Δ₁ →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr type) →
  ContType .Stmt Δ₁ Γ₁ (.scopeBodyK e n :: K) .Stmt

inductive Coh : Environment → Ctx → Prop
| CohEmp :
  Coh [] []
| CohBind (v : Value) (type : Ty) :
  Coh E Γ →
  value_type v type →
  Coh (v :: E) (type :: Γ)

inductive JCoh : JStackCtx → Ctx → JCtx → Prop
| JCohEmp :
  JCoh [] Γ []
| JCohLoop (n : Nat) (Γ₁ : Ctx) (Δ₁ : JCtx) :
  n ≤ Γ₁.length →
  JCoh J (Γ₁.drop (Γ₁.length - n)) Δ₁ →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr .unit) →
  JCoh (⟨n, K⟩ :: J) Γ₁ (n :: Δ₁)

inductive Wt : CEK → Prop
| WtExprE (e : Lang .Expr) (type : Ty) :
  Coh E Γ →
  JCoh J Γ Δ →
  Typ .Expr Δ Γ e (.Expr type) →
  ContType .Expr Δ Γ K (.Expr type) →
  Wt ⟨.sourceExpr e, E, J, K⟩
| WtExprS (s : Lang .Stmt) :
  Coh E Γ →
  JCoh J Γ Δ →
  Typ .Stmt Δ Γ s (.Stmt Γ₁) →
  ContType .Stmt Δ Γ₁ K .Stmt →
  Wt ⟨.sourceStmt s, E, J, K⟩
| WtContV (v : Value) (type : Ty) :
  Coh E Γ →
  JCoh J Γ Δ →
  value_type v type →
  ContType .Expr Δ Γ K (.Expr type) →
  Wt ⟨.value v, E, J, K⟩
| WtContS :
  Coh E Γ →
  JCoh J Γ Δ →
  ContType .Stmt Δ Γ K .Stmt →
  Wt ⟨.skip, E, J, K⟩

-- do casing on Continuation
theorem progress (s : CEK) :
  Wt s →
  (∃ E, terminalState E = s) ∨ ∃ s', Eval s s' := by
    intro hwt
    unhygienic induction s
    by_cases ht : ∃ E1, terminalState E1 = ⟨C, E, J, K⟩
    { grind }
    simp [terminalState] at ht
    right
    unhygienic cases hwt
    stop sorry

lemma lift_value_type (v : Value) (type : Ty) :
  Typ .Expr Γ Δ (liftValue v) (.Expr type) → value_type v type := by
    intro ht
    cases v <;> cases ht <;> grind [value_type]

lemma coh_len (E : Environment) (Γ : Ctx) :
  Coh E Γ → E.length = Γ.length := by
    intro h
    induction h <;> grind

lemma coh_get (E : Environment) (Γ : Ctx) (idx : Nat) :
  Coh E Γ → idx < E.length →
  value_type E[idx]! Γ[idx]! := by
    intro h
    induction h generalizing idx <;> grind

lemma coh_set (E : Environment) (Γ : Ctx) (idx : Nat) (v : Value) :
  Coh E Γ → idx < E.length →
  value_type v Γ[idx]! →
  Coh (E.set idx v) Γ := by
    intro h
    induction h generalizing idx
    { grind }
    by_cases h0 : ∃ idx₁, idx = idx₁ + 1
    { grind [Coh] }
    simp only [Nat.exists_eq_add_one, not_lt, Nat.le_zero_eq] at h0
    rw [h0, List.set_cons_zero]
    grind [Coh]


lemma coh_mono (E : Environment) (Γ : Ctx) :
  Coh E Γ → Coh (E.drop n) (Γ.drop n) := by
    intro h
    induction h generalizing n
    { grind [Coh] }
    have cons_append (α : Type) (li : List α) (x : α) :
      [x] ++ li = x :: li := by grind
    have (α : Type) (li : List α) (x : α) : n > 0 → ([x] ++ li).drop n = li.drop (n - 1) := by
      rw [List.drop_append]
      intro hn
      rw [List.drop_cons]
      { grind [List.take] }
      grind
    by_cases n = 0
    { grind [Coh] }
    rw [←cons_append, this]
    { grind [Coh] }
    grind
/-
-- Not used in the current development; right-extension of context does not
-- interact well with List.drop when n ≤ Γ.length.  The prepend variant
-- (used via jcoh_ext) is what preservation actually needs.
lemma cont_type_ext (tg : Tag) (Γ₁ : ContTypeRes tg) (n : Nat) :
    ContType tg Δ Γ K Γ₁ →
    ctx_limit n Δ →
    ContType tg Δ (Γ.drop (Γ.length - n)) K Γ₁ := by
    intro hx hc
    induction hx generalizing n
    { sorry }
    stop sorry -- right-extension form not needed; see jcoh_ext
-/
lemma drop_suffix_prepend {α : Type} (Γ₁ Γ₂ : List α) (n : Nat)
    (hn : n ≤ Γ₂.length) :
    List.drop (List.length (Γ₁ ++ Γ₂) - n) (Γ₁ ++ Γ₂) =
    List.drop (List.length Γ₂ - n) Γ₂ := by
  rw [List.drop_append]
  have h1 : List.drop (List.length (Γ₁ ++ Γ₂) - n) Γ₁ = [] := by
    rw [List.drop_eq_nil_iff]; simp; omega
  rw [h1, List.nil_append]
  congr 1; simp; omega

lemma jcoh_ext (J : JStackCtx) (Γ Γ₁ : Ctx) :
    JCoh J Γ Δ → JCoh J (Γ₁ ++ Γ) Δ := by
    intro h
    unhygienic induction h generalizing Γ₁
    { exact JCoh.JCohEmp }
    rename_i Γ₂
    have hdrop := drop_suffix_prepend Γ₁ Γ₂ n a
    apply JCoh.JCohLoop
    { simp; omega }
    { rw [hdrop]; assumption }
    { rw [hdrop]; assumption }

lemma jcoh_sub (J : JStackCtx) (Γ : Ctx) :
    JCoh J Γ Δ → ctx_limit n Δ →
    JCoh J (Γ.drop (Γ.length - n)) Δ := by
    intro h hc
    unhygienic induction h generalizing n
    { exact JCoh.JCohEmp }
    apply JCoh.JCohLoop
    { grind [ctx_limit] }
    { simp at *
      grind [ctx_limit] }
    simp
    grind [ctx_limit]

lemma List.eq_take_drop (Γ : List α) (n : Nat) :
  Γ = Γ.take n ++ Γ.drop n := by
    induction Γ generalizing n
    { grind }
    by_cases ∃ k, n = k + 1
    { grind }
    simp at *

lemma jcoh_drop (J : JStackCtx) (Γ : Ctx) (l : Nat) :
    JCoh J Γ Δ →
    J[l]? = some j ->
    JCoh (J.drop (l + 1))
      (Γ.drop (Γ.length - j.1)) (Δ.drop (l + 1)) := by
    intro hj
    unhygienic induction l generalizing J Δ Γ
    { cases hj
      { grind [JCoh] }
      grind }
    unhygienic cases hj
    { grind [JCoh] }
    simp only [List.drop_succ_cons]
    apply a
    have : Γ = Γ.take (Γ.length - n_1) ++ (Γ.drop (Γ.length - n_1)) := by
      clear a a_2
      exact List.eq_take_drop Γ _
    rw [this]
    apply jcoh_ext
    apply a_2

lemma jcoh_cont_type_drop (J : JStackCtx) (Γ : Ctx) (l : Nat) :
    l < Δ.length →
    JCoh J Γ Δ →
    J[l]? = some j ->
    ContType Tag.Expr
      (List.drop (l + 1) Δ)
      (List.drop (List.length Γ - j.1) Γ)
      j.2
      (ContTypeRes.Expr Ty.unit) := by
    intro hl hj
    unhygienic induction l generalizing J Δ Γ
    { cases hj <;> grind }
    unhygienic cases hj
    { grind }
    simp only [List.drop_succ_cons]
    apply a
    { grind }
    have : Γ = Γ.take (Γ.length - n_1) ++ (Γ.drop (Γ.length - n_1)) := by
      clear a a_2
      exact List.eq_take_drop Γ _
    rw [this]
    apply jcoh_ext
    apply a_2

lemma jcoh_ctx :
  JCoh J Γ Δ → ctx_limit Γ.length Δ := by
    intro hj
    induction hj
    { grind [ctx_limit] }
    rw [ctx_limit]
    grind

theorem preservation (s s' : CEK) :
  Wt s → Eval s s' → Wt s' := by
    intro hw he
    unhygienic induction he <;> unhygienic cases hw
    -- Batch: simple cases handled by solve_by_elim
    all_goals try
    { unhygienic cases a_2
      try (apply Wt.WtExprE <;> solve_by_elim)
      try (apply Wt.WtExprS <;> solve_by_elim) }
    all_goals try
    { unhygienic cases a_3
      try (apply Wt.WtExprE <;> solve_by_elim)
      try (apply Wt.WtExprS <;> solve_by_elim) }
    -- ExprStmtDone: discard value, become skip
    all_goals try
    { unhygienic cases a_3
      apply Wt.WtContS
      { apply a }
      { apply a_1 }
      apply a_4 }
    -- Val: liftValue preserves type
    { apply Wt.WtContV (type := type)
      { apply a }
      { apply a_1 }
      { apply lift_value_type v type a_2 }
      apply a_3 }
    -- Var: environment lookup
    { cases a_2
      apply Wt.WtContV
      { apply a }
      { apply a_1 }
      { apply coh_get
        { apply a }
        grind [coh_len] }
      grind }
    -- While: push LoopK continuation
    { unhygienic cases a_2
      apply Wt.WtExprE
      { apply a }
      { apply a_1 }
      { apply a_4 }
      rw [coh_len _ _ a]
      apply ContType.LoopK
      { apply a_4 }
      { grind [coh_len] }
      { grind [jcoh_ctx] }
    /-apply a_3-/ }
    -- Break: jump to saved context
    { unhygienic cases a_3
      -- { cases a }
      apply Wt.WtContV (type := Ty.unit)
        (Δ := Δ.drop (l + 1))
      { apply coh_mono
        apply a_1 }
      { rw [coh_len E Γ a_1]
        refine jcoh_drop _ _ _ ?_ a
        { apply a_2 } }
      { simp [value_type] }
      rw [coh_len _ _ a_1]
      apply jcoh_cont_type_drop <;> solve_by_elim
      }
    -- Scope: push ScopeBodyK continuation
    { unhygienic cases a_2
      apply Wt.WtExprS
      { apply a }
      { apply a_1 }
      { apply a_4 }
      apply ContType.ScopeBodyK
      { apply a_5 }
      { rw [ctx_limit.eq_def]
        grind [coh_len, JCoh] }
      { rcases stmt_mono _ _ _ _ a_4 with ⟨g, hg⟩
        cases g
        rw [TypR.extR] at hg
        rw [coh_len _ _ a]
        simp at hg
        simp [←hg]
        grind } }
    -- VarDeclDone: extend environment
    { unhygienic cases a_3
      apply Wt.WtContS (Δ := Δ)
      { apply Coh.CohBind
        { apply a }
        apply a_2 }
      { exact jcoh_ext J Γ [type] a_1 }
      apply a_4 }
    -- AssignDone: update environment
    { unhygienic cases a_3
      apply Wt.WtContS
      { apply coh_set
        { apply a }
        { grind [coh_len] }
        grind }
      { apply a_1 }
      apply a_5 }
    -- BinOpR: step produces result
    { cases a_4
      apply Wt.WtContV (type := op.args.out)
      { apply a_1 }
      { apply a_2 }
      { cases a <;> grind [BinOp.args, value_type] }
      solve_by_elim }
    -- UnOpDone: step produces result
    { cases a_4
      apply Wt.WtContV
      { apply a_1 }
      { apply a_2 }
      { cases a
        { rw [value_type.eq_1]; trivial }
        rw [value_type.eq_2]; trivial }
      { solve_by_elim } }
    -- LoopTrue: enter loop body, push JStackCtx
    { unhygienic cases a_3
      apply Wt.WtExprE
      { apply a }
      { apply JCoh.JCohLoop
        { grind }
        { apply jcoh_sub
          { apply a_1 }
          grind [jcoh_ctx] }
        grind }
      -- need n = Γ.length (holds via Coh at loop entry)
      -- then JCtx becomes Γ.length :: Δ matching body typing
      { apply a_5 }
      apply ContType.LoopContK
      { apply a_4 }
      { apply a_5 }
      grind }
    -- LoopFalse: exit loop, drop environment
    { unhygienic cases a_3
      -- need JCoh after dropping env to loop entry length
      apply Wt.WtContV
      { apply coh_mono
        apply a }
      { rw [coh_len _ _ a]
        apply jcoh_sub
        { apply a_1 }
        grind [jcoh_ctx] }
      { rw [value_type.eq_4]
        simp }
      rw [coh_len _ _ a]
      grind }
    -- LoopCont: pop JStackCtx, re-enter condition
    { unhygienic cases a_3
      unhygienic cases a_1
      apply Wt.WtExprE
      { apply a }
      { simp only [Nat.sub_self, List.drop_zero] at a_7
        apply a_7 }
      { apply a_4 }
      apply ContType.LoopK
      { apply a_4 }
      { apply a_5 }
      grind }
    -- ScopeExit: drop environment, restore context
    unhygienic cases Δ
    { unhygienic cases a_3
      apply Wt.WtContV
      { apply coh_mono
        apply a }
      { cases a_1
        apply JCoh.JCohEmp }
      { apply a_2 }
      grind [coh_len] }
    unhygienic cases a_3
    apply Wt.WtContV
    { apply coh_mono
      apply a }
    { unhygienic cases a_1
      rw [ctx_limit] at a_4
      have : (List.length E - n + (List.length Γ - (List.length E - n) - head)) =
        (Γ.length - head) := by grind [coh_len]
      apply JCoh.JCohLoop
      { grind [coh_len] }
      { simp only [List.length_drop, List.drop_drop, this]
        apply a_6 }
      simp only [List.length_drop, List.drop_drop, this]
      apply a_7 }
    { apply a_2 }
    grind [coh_len]
