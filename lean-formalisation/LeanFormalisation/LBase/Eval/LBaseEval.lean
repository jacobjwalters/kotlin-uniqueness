import LeanFormalisation.LBase.LBaseDefs
import Mathlib.Tactic.Convert

/-! # Computable evaluator for LBase

A computable single-step function `CEK.step` that mirrors the `Eval`
relation from `LBase.lean`, together with multi-step runners and
correspondence proofs.
-/

section OperatorEval

/-- Computable version of `BinOp.step`. -/
def BinOp.eval : BinOp → Value → Value → Option Value
  | .Add, .Nat n, .Nat m => some (.Nat (n + m))
  | .Sub, .Nat n, .Nat m => some (.Nat (n - m))
  | .NatEq, .Nat n, .Nat m => some (if n == m then .True else .False)
  | .BoolEq, .True, .True => some .True
  | .BoolEq, .False, .False => some .True
  | .BoolEq, .True, .False => some .False
  | .BoolEq, .False, .True => some .False
  | _, _, _ => none

/-- Computable version of `UnOp.step`. -/
def UnOp.eval : UnOp → Value → Option Value
  | .IsZero, .Nat 0 => some .True
  | .IsZero, .Nat (_ + 1) => some .False
  | _, _ => none

/-- Recognise literal-value expressions (inverse of `liftValue`). -/
def isLiftValue : Lang .Expr → Option Value
  | .True => some .True
  | .False => some .False
  | .Nat n => some (.Nat n)
  | .Unit => some .Unit
  | _ => none

end OperatorEval

section Repr

def Control.show : Control → String
  | .sourceExpr e => s!"expr({repr e})"
  | .sourceStmt s => s!"stmt({repr s})"
  | .value v => s!"val({repr v})"
  | .skip => "skip"

instance : Repr Control where
  reprPrec c _ := Control.show c

def Cont.show : Cont → String
  | .ifCondK _ _ => "ifCondK"
  | .declK ty => s!"declK({repr ty})"
  | .assignK x => s!"assignK({x})"
  | .seqK _ => "seqK"
  | .binopLK op _ => s!"binopLK({repr op})"
  | .binopRK op v => s!"binopRK({repr op},{repr v})"
  | .unopK op => s!"unopK({repr op})"
  | .loopK _ _ n => s!"loopK@{n}"
  | .loopContK _ _ n => s!"loopContK@{n}"
  | .scopeBodyK _ n => s!"scopeBodyK@{n}"
  | .scopeExitK n => s!"scopeExitK@{n}"
  | .exprStmtK => "exprStmtK"

instance : Repr Cont where
  reprPrec c _ := Cont.show c

instance : Repr CEK where
  reprPrec cek _ :=
    s!"⟨{Control.show cek.C}, E={repr cek.E}, K=[{",".intercalate (cek.K.map Cont.show)}]⟩"

end Repr

section Step

/-- Single-step the CEK machine. Returns `none` if stuck or terminal. -/
def CEK.step (s : CEK) : Option CEK :=
  match s.C, s.K with
  -- Expression source forms
  | .sourceExpr e, K =>
    match e with
    | .Var x => some ⟨.value (s.E[x]!), s.E, s.J, K⟩
    | .BinOp e₁ e₂ op => some ⟨.sourceExpr e₁, s.E, s.J, .binopLK op e₂ :: K⟩
    | .UnOp e₁ op => some ⟨.sourceExpr e₁, s.E, s.J, .unopK op :: K⟩
    | .If c e₁ e₂ => some ⟨.sourceExpr c, s.E, s.J, .ifCondK e₁ e₂ :: K⟩
    | .While c body => some ⟨.sourceExpr c, s.E, s.J, .loopK c body s.E.length :: K⟩
    | .Break l => some ⟨.value .Unit,
        s.E.drop (s.E.length - s.J[l]!.1),
        s.J.drop (l + 1),
        s.J[l]!.2⟩
    | .Scope st res => some ⟨.sourceStmt st, s.E, s.J, .scopeBodyK res s.E.length :: K⟩
    | other =>
      match isLiftValue other with
      | some v => some ⟨.value v, s.E, s.J, K⟩
      | none => none
  -- Statement source forms
  | .sourceStmt st, K =>
    match st with
    | .Decl ty e => some ⟨.sourceExpr e, s.E, s.J, .declK ty :: K⟩
    | .Assign x e => some ⟨.sourceExpr e, s.E, s.J, .assignK x :: K⟩
    | .Seq s₁ s₂ => some ⟨.sourceStmt s₁, s.E, s.J, .seqK s₂ :: K⟩
    | .Do e => some ⟨.sourceExpr e, s.E, s.J, .exprStmtK :: K⟩
  -- Continuation pops: value on top
  | .value v, k :: K =>
    match k with
    | .ifCondK e₁ e₂ =>
      match v with
      | .True => some ⟨.sourceExpr e₁, s.E, s.J, K⟩
      | .False => some ⟨.sourceExpr e₂, s.E, s.J, K⟩
      | _ => none
    | .declK _ty => some ⟨.skip, v :: s.E, s.J, K⟩
    | .assignK x => some ⟨.skip, s.E.set x v, s.J, K⟩
    | .binopLK op e₂ => some ⟨.sourceExpr e₂, s.E, s.J, .binopRK op v :: K⟩
    | .binopRK op v₁ =>
      match op.eval v₁ v with
      | some result => some ⟨.value result, s.E, s.J, K⟩
      | none => none
    | .unopK op =>
      match op.eval v with
      | some result => some ⟨.value result, s.E, s.J, K⟩
      | none => none
    | .loopK c body n =>
      match v with
      | .True => some ⟨.sourceExpr body, s.E, ⟨n, K⟩ :: s.J, .loopContK c body n :: K⟩
      | .False => some ⟨.value .Unit, s.E.drop (s.E.length - n), s.J, K⟩
      | _ => none
    | .loopContK c body n =>
      match v, s.J with
      | .Unit, ⟨n', savedK⟩ :: J' =>
        if n' == n then
          some ⟨.sourceExpr c, s.E, J', .loopK c body n :: savedK⟩
        else none
      | _, _ => none
    | .scopeExitK n => some ⟨.value v, s.E.drop (s.E.length - n), s.J, K⟩
    | .exprStmtK => some ⟨.skip, s.E, s.J, K⟩
    | _ => none
  -- Continuation pops: skip on top
  | .skip, k :: K =>
    match k with
    | .seqK s₂ => some ⟨.sourceStmt s₂, s.E, s.J, K⟩
    | .scopeBodyK body n => some ⟨.sourceExpr body, s.E, s.J, .scopeExitK n :: K⟩
    | _ => none
  -- Terminal or stuck
  | _, _ => none

/-- Is this a terminal state (skip with empty continuation)? -/
def CEK.isTerminal (s : CEK) : Bool :=
  match s.C, s.K with
  | .skip, [] => true
  | _, _ => false

end Step

section Runners

/-- Run the CEK machine for up to `fuel` steps, collecting all states. -/
def CEK.trace (s : CEK) (fuel : Nat := 200) : List CEK :=
  match fuel with
  | 0 => [s]
  | fuel + 1 =>
    match s.step with
    | some s' => s :: s'.trace fuel
    | none => [s]

/-- Run the CEK machine to completion, returning the final state. -/
def CEK.run (s : CEK) (fuel : Nat := 1000) : CEK :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    match s.step with
    | some s' => s'.run fuel
    | none => s

/-- Pretty-print a trace with step numbers. -/
def showTrace (states : List CEK) : String :=
  go states 0 ""
where
  go : List CEK → Nat → String → String
  | [], _, acc => acc
  | s :: rest, i, acc => go rest (i + 1) (acc ++ s!"Step {i}: {repr s}\n")

/-- Run a program statement and show the full trace. -/
def traceProgram (prog : Lang .Stmt) (fuel : Nat := 200) : String :=
  showTrace ((initState prog).trace fuel)

/-- Run a program and return its final environment. -/
def runProgram (prog : Lang .Stmt) (fuel : Nat := 1000) : List Value :=
  ((initState prog).run fuel).E

end Runners

section Correspondence

/-! ### Operator correspondence -/

lemma BinOp.eval_complete {op : BinOp} {v₁ v₂ r : Value} :
    op.step v₁ v₂ r → op.eval v₁ v₂ = some r := by
  intro h; cases h <;> simp [BinOp.eval, beq_self_eq_true, beq_iff_eq, *]

lemma BinOp.eval_sound {op : BinOp} {v₁ v₂ r : Value} :
    (op.eval v₁ v₂ = some r) → op.step v₁ v₂ r := by
  intro h
  match op, v₁, v₂ with
  | .Add, .Nat n, .Nat m => simp [BinOp.eval] at h; subst h; exact .add n m
  | .Sub, .Nat n, .Nat m => simp [BinOp.eval] at h; subst h; exact .sub n m
  | .NatEq, .Nat n, .Nat m =>
    simp only [BinOp.eval] at h
    by_cases heq : n = m
    · subst heq; simp [beq_self_eq_true] at h; subst h; exact .natEqTrue n
    · have hbne : (n == m) = false := by rw [beq_eq_false_iff_ne]; exact heq
      simp [hbne] at h; subst h; exact .natEqFalse n m heq
  | .BoolEq, .True, .True => simp [BinOp.eval] at h; subst h; exact .boolEqTT
  | .BoolEq, .True, .False => simp [BinOp.eval] at h; subst h; exact .boolEqTF
  | .BoolEq, .False, .True => simp [BinOp.eval] at h; subst h; exact .boolEqFT
  | .BoolEq, .False, .False => simp [BinOp.eval] at h; subst h; exact .boolEqFF

lemma UnOp.eval_complete {op : UnOp} {v r : Value} :
    op.step v r → op.eval v = some r := by
  intro h; cases h
  · rfl
  · rename_i n hne; cases n
    · exact absurd rfl hne
    · rfl

lemma UnOp.eval_sound {op : UnOp} {v r : Value} :
    op.eval v = some r → op.step v r := by
  intro h
  cases op <;> cases v <;> simp [UnOp.eval] at h
  case IsZero.Nat n =>
    cases n with
    | zero => simp [UnOp.eval] at h; subst h; exact .isZeroTrue
    | succ n => simp [UnOp.eval] at h; subst h; exact .isZeroFalse (n + 1) (by omega)

lemma isLiftValue_complete (v : Value) :
    (isLiftValue (liftValue v)) = some v := by
  cases v <;> rfl

lemma isLiftValue_sound (e : Lang .Expr) (v : Value) :
    (isLiftValue e) = some v → e = liftValue v := by
  intro h
  cases e <;> simp [isLiftValue] at h
  case True => subst h; rfl
  case False => subst h; rfl
  case Nat n => subst h; rfl
  case Unit => subst h; rfl

/-! ### Soundness: `CEK.step s = some s' → Eval s s'`

Every step of the computable evaluator is justified by `Eval`.
Proof by case-splitting on the nested match inside `CEK.step`;
each of the ~25 branches directly applies an `Eval` constructor. -/

lemma CEK.step_sound {s s' : CEK} :
    s.step = some s' → Eval s s' := by
  intro h
  obtain ⟨C, E, J, K⟩ := s
  -- We use dsimp (not simp) to unfold CEK.step without rewriting getElem!/getElem?
  cases C with
  | sourceExpr e =>
    cases e with
    | Var x =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .Var x
    | BinOp e₁ e₂ op =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .BinOp e₁ e₂ op
    | UnOp e₁ op =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .UnOp e₁ op
    | If c e₁ e₂ =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .If c e₁ e₂
    | While c body =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .While c body
    | Break l =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .Break K l
    | Scope st res =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .Scope st res
    | True =>
      dsimp [CEK.step, isLiftValue] at h; injection h with h; subst h; exact .Val .True
    | False =>
      dsimp [CEK.step, isLiftValue] at h; injection h with h; subst h; exact .Val .False
    | Nat n =>
      dsimp [CEK.step, isLiftValue] at h; injection h with h; subst h; exact .Val (.Nat n)
    | Unit =>
      dsimp [CEK.step, isLiftValue] at h; injection h with h; subst h; exact .Val .Unit
  | sourceStmt st =>
    cases st with
    | Decl ty e =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .VarDecl ty e
    | Assign x e =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .Assign x e
    | Seq s₁ s₂ =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .Seq s₁ s₂
    | Do e =>
      dsimp [CEK.step] at h; injection h with h; subst h; exact .ExprStmt e
  | value v =>
    cases K with
    | nil => simp [CEK.step] at h
    | cons k K =>
      cases k with
      | ifCondK e₁ e₂ =>
        dsimp [CEK.step] at h
        cases v with
        | True => injection h with h; subst h; exact .IfTrue e₁ e₂
        | False => injection h with h; subst h; exact .IfFalse e₁ e₂
        | _ => simp at h
      | declK ty =>
        dsimp [CEK.step] at h; injection h with h; subst h; exact .VarDeclDone ty v
      | assignK x =>
        dsimp [CEK.step] at h; injection h with h; subst h; exact .AssignDone x v
      | binopLK op e₂ =>
        dsimp [CEK.step] at h; injection h with h; subst h; exact .BinOpL op v e₂
      | binopRK op v₁ =>
        dsimp only [CEK.step] at h
        generalize heval : op.eval v₁ v = res at h
        cases res with
        | none => simp at h
        | some result =>
          injection h with h; subst h
          exact .BinOpR op v₁ v result (BinOp.eval_sound heval)
      | unopK op =>
        dsimp only [CEK.step] at h
        generalize heval : op.eval v = res at h
        cases res with
        | none => simp at h
        | some result =>
          injection h with h; subst h
          exact .UnOpDone op v result (UnOp.eval_sound heval)
      | loopK c body n =>
        dsimp [CEK.step] at h
        cases v with
        | True => injection h with h; subst h; exact .LoopTrue body c n
        | False => injection h with h; subst h; exact .LoopFalse body c n
        | _ => simp at h
      | loopContK c body n =>
        dsimp only [CEK.step] at h
        cases v with
        | Unit =>
          cases J with
          | nil => simp at h
          | cons p J' =>
            obtain ⟨n', savedK⟩ := p
            dsimp at h
            by_cases heq : n' = n
            · subst heq; simp at h; subst h
              exact Eval.LoopCont (K := savedK) body c n' K
            · have : (n' == n) = false := beq_eq_false_iff_ne.mpr heq
              simp [this] at h
        | _ => simp at h
      | scopeExitK n =>
        dsimp [CEK.step] at h; injection h with h; subst h; exact .ScopeExit .Unit n v
      | exprStmtK =>
        dsimp [CEK.step] at h; injection h with h; subst h; exact .ExprStmtDone v
      | scopeBodyK _ _ => simp [CEK.step] at h
      | seqK _ => simp [CEK.step] at h
  | skip =>
    cases K with
    | nil => simp [CEK.step] at h
    | cons k K =>
      cases k with
      | seqK s₂ =>
        dsimp [CEK.step] at h; injection h with h; subst h; exact .SeqDone s₂
      | scopeBodyK body n =>
        dsimp [CEK.step] at h; injection h with h; subst h; exact .ScopeBody body n
      | _ => simp [CEK.step] at h

/-! ### Completeness: `Eval s s' → CEK.step s = some s'`

Every `Eval` step is computed by the evaluator. Proof by cases on
the `Eval` derivation: each constructor fixes the input shape so
`CEK.step` reduces (modulo operator completeness lemmas). -/

lemma CEK.step_complete {s s' : CEK} :
    Eval s s' → s.step = some s' := by
  intro h
  cases h with
  | Val v => cases v <;> simp [CEK.step, liftValue, isLiftValue]
  | Var x => simp [CEK.step]
  | VarDecl type e => simp [CEK.step]
  | Assign x e => simp [CEK.step]
  | Seq s₁ s₂ => simp [CEK.step]
  | ExprStmt e => simp [CEK.step]
  | BinOp e₁ e₂ op => simp [CEK.step]
  | UnOp e op => simp [CEK.step]
  | If e s₁ s₂ => simp [CEK.step]
  | While c body => simp [CEK.step]
  | Break K' l => simp [CEK.step]
  | Scope s e => simp [CEK.step]
  | IfTrue s₁ s₂ => simp [CEK.step]
  | IfFalse s₁ s₂ => simp [CEK.step]
  | VarDeclDone type v => simp [CEK.step]
  | AssignDone x v => simp [CEK.step]
  | SeqDone s₂ => simp [CEK.step]
  | ExprStmtDone v => simp [CEK.step]
  | BinOpL op v₁ e₂ => simp [CEK.step]
  | @BinOpR E J K op v₁ v₂ result hstep =>
    simp [CEK.step, BinOp.eval_complete hstep]
  | @UnOpDone E J K op v result hstep =>
    simp [CEK.step, UnOp.eval_complete hstep]
  | LoopTrue body c n => simp [CEK.step]
  | LoopFalse body c n => simp [CEK.step]
  | LoopCont body c n K' => simp [CEK.step]
  | ScopeBody body n => simp [CEK.step]
  | ScopeExit body n v => simp [CEK.step]

/-- The evaluator and the small-step relation agree exactly. -/
theorem CEK.step_iff_eval {s s' : CEK} :
    s.step = some s' ↔ Eval s s' :=
  ⟨CEK.step_sound, CEK.step_complete⟩

end Correspondence
