import LeanFormalisation.LClass.Theorems.TypeProperties
import LeanFormalisation.LClass.Theorems.ContextProperties

variable (cCnt : Nat) (defs : Defs cCnt)

/-- Progress: any well-typed CEK state is either terminal or can step. -/
theorem progress (s : CEK cCnt defs m) (hwt : Wt cCnt defs m s) :
    terminalState cCnt defs s ∨ ∃ m' s', Eval cCnt defs m m' s s' := by
  cases hwt with
  | @WtExprE _ S _ _ _ _ e _ _ _ _ _ hTyp _ _ _ _ _ _ _ =>
    right
    cases e with
    | Var x => exact ⟨_, _, .Var x⟩
    | Field f p => exact ⟨_, _, .Field f p⟩
    | True => exact ⟨_, _, .Val .True .True .True⟩
    | False => exact ⟨_, _, .Val .False .False .False⟩
    | Nat n => exact ⟨_, _, .Val (.Nat n) (.Nat n) (.Nat n)⟩
    | Unit => exact ⟨_, _, .Val .Unit .Unit .Unit⟩
    | BinOp e₁ e₂ op => exact ⟨_, _, .BinOp e₁ e₂ op⟩
    | UnOp e op => exact ⟨_, _, .UnOp e op⟩
    | New cls args =>
      cases hTyp with | New _ hc _ harg _ _ =>
      subst harg
      by_cases hs : 0 = defs.fieldsCnt ⟨cls, hc⟩
      · rcases map_fresh_addr S with ⟨a, ha⟩
        exact ⟨_, _, .New₀ ⟨cls, hc⟩ a args hs ha⟩
      · exact ⟨_, _, .New ⟨cls, hc⟩ args (by omega)⟩
    | Call m cls args =>
      cases hTyp with | Call _ hcls _ hm _ harg _ _ _ _ =>
      subst harg
      by_cases hs : 0 = (defs.methods ⟨cls, hcls⟩ ⟨m, hm⟩).nArg
      · exact ⟨_, _, .Call₀ ⟨cls, hcls⟩ ⟨m, hm⟩ args hs⟩
      · exact ⟨_, _, .Call ⟨cls, hcls⟩ ⟨m, hm⟩ args (by omega)⟩
    | Return e l => exact ⟨_, _, .Return e⟩
    | If c e₁ e₂ => exact ⟨_, _, .If c e₁ e₂⟩
    | While c body => exact ⟨_, _, .While c body⟩
    | Break l => exact ⟨_, _, .Break l⟩
    | Scope s e => exact ⟨_, _, .Scope s e⟩
  | WtExprS s _ _ _ _ _ _ _ _ _ _ _ _ =>
    right
    cases s with
    | Decl t e => exact ⟨_, _, .VarDecl t e⟩
    | Assign x e => exact ⟨_, _, .Assign x e⟩
    | Seq s₁ s₂ => exact ⟨_, _, .Seq s₁ s₂⟩
    | Do e => exact ⟨_, _, .ExprStmt e⟩
  | @WtContV E S _ _ _ K v _ _ _ _ _ hVT _ _ _ _ _ _ hK =>
    cases K with
    | nil => exact .inl trivial
    | cons head K' =>
      right
      cases head with
      | fieldK f =>
        cases hK
        rename_i cls _ hf _ _
        cases hVT
        rename_i cls' addr vls _ hlk _
        have hcls : cls' = cls := by ext; omega
        subst hcls
        exact ⟨_, _, .FieldDone addr _ ⟨f, hf⟩ vls hlk⟩
      | ifCondK _ _ =>
        cases hVT <;> cases hK
        · exact ⟨_, _, .IfTrue _ _⟩
        · exact ⟨_, _, .IfFalse _ _⟩
      | declK t => exact ⟨_, _, .VarDeclDone t v⟩
      | assignK x => exact ⟨_, _, .AssignDone x v⟩
      | seqK _ => cases hK
      | exprStmtK => exact ⟨_, _, .ExprStmtDone v⟩
      | binopLK op e₂ => exact ⟨_, _, .BinOpL op v e₂⟩
      | binopRK op v₁ =>
        cases hK
        rename_i hsimp _
        cases op
        · cases hsimp
          cases hVT
          exact ⟨_, _, .BinOpR _ _ _ _ (.add _ _)⟩
        · cases hsimp
          cases hVT
          exact ⟨_, _, .BinOpR _ _ _ _ (.sub _ _)⟩
        · cases hsimp
          cases hVT
          rename_i n m
          by_cases heq : m = n
          · subst heq
            exact ⟨_, _, .BinOpR _ _ _ _ (.natEqTrue _)⟩
          · exact ⟨_, _, .BinOpR _ _ _ _ (.natEqFalse _ _ (fun h => heq h.symm))⟩
        · cases hsimp <;> cases hVT
          · exact ⟨_, _, .BinOpR _ _ _ _ .boolEqTT⟩
          · exact ⟨_, _, .BinOpR _ _ _ _ .boolEqTF⟩
          · exact ⟨_, _, .BinOpR _ _ _ _ .boolEqFT⟩
          · exact ⟨_, _, .BinOpR _ _ _ _ .boolEqFF⟩
      | unopK op =>
        cases hK
        cases op
        cases hVT
        rename_i n
        match n with
        | 0 => exact ⟨_, _, .UnOpDone _ _ _ .isZeroTrue⟩
        | k + 1 => exact ⟨_, _, .UnOpDone _ _ _ (.isZeroFalse _ (by omega))⟩
      | loopK c body =>
        cases hK
        cases hVT
        · exact ⟨_, _, .LoopTrue body c⟩
        · exact ⟨_, _, .LoopFalse body c E.length⟩
      | loopContK c body n J₀ =>
        cases hK
        cases hVT
        exact ⟨_, _, .LoopCont body c n⟩
      | returnJumpK l => exact ⟨_, _, .ReturnJump v l rfl⟩
      | argK cls m sep vals exprs =>
        cases hK
        by_cases hsep : sep + 1 = (defs.methods cls m).nArg
        · exact ⟨_, _, .ArgDone v cls m sep vals exprs hsep⟩
        · exact ⟨_, _, .ArgNext v cls m sep vals exprs (by omega)⟩
      | newK cls sep vals exprs =>
        cases hK
        by_cases hsep : sep + 1 = defs.fieldsCnt cls
        · rcases map_fresh_addr S with ⟨addr, haddr⟩
          exact ⟨_, _, .NewDone v cls sep vals exprs hsep addr haddr⟩
        · exact ⟨_, _, .NewNext v cls sep vals exprs (by omega)⟩
      | breakRestoreK n J₀ =>
        cases hK
        cases hVT
        exact ⟨_, _, .BreakRestore⟩
      | scopeExitK n J₀ => exact ⟨_, _, .ScopeExit n v⟩
      | returnRestoreK E₀ J₀ => exact ⟨_, _, .ReturnRestore v⟩
      | callRestoreK E₀ J₀ => exact ⟨_, _, .CallRestore v⟩
      | scopeBodyK _ _ _ => cases hK
  | @WtContS _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ hK =>
    cases K with
    | nil => cases hK
    | cons head _ =>
      right
      cases head with
      | seqK s => exact ⟨_, _, .SeqDone s⟩
      | scopeBodyK e n _ => exact ⟨_, _, .ScopeBody e n⟩
      | fieldK _ | ifCondK _ _ | declK _ | assignK _ | exprStmtK
      | binopLK _ _ | binopRK _ _ | unopK _ | loopK _ _
      | loopContK _ _ _ _ | returnJumpK _ | argK _ _ _ _ _
      | newK _ _ _ _ | breakRestoreK _ _ | scopeExitK _ _
      | returnRestoreK _ _ | callRestoreK _ _ => cases hK

/-! ## Preservation, split per `Eval` rule

Each helper lemma proves preservation for a single `Eval` constructor.
`preservation` itself becomes a `cases he` dispatch over these helpers.
This keeps the per-case heartbeat budget small and makes failures local
to the offending rule.
-/

namespace Preservation

private lemma preservation_Val {E J S K} (v : Value) (e : Lang .Expr)
    (hlv : liftValue v e)
    (hw : Wt cCnt defs .Eval (.Eval .Expr e E J S K)) :
    Wt cCnt defs .Cont (.Cont (.value v) E J S K) := by
  unhygienic cases hw
  cases hlv <;>
  { cases a_3
    apply Wt.WtContV <;> solve_by_elim }

private lemma preservation_Var {E J S K} (x : VarName)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.Var x) E J S K)) :
    Wt cCnt defs .Cont (.Cont (.value E[x]!) E J S K) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtContV (cnts := cnts)
  · exact a
  · exact a_1
  · exact a_2
  · apply coh_get cCnt defs E
    · exact a
    grind [coh_len]
  · solve_by_elim
  · assumption
  · assumption
  · assumption
  · grind
  · grind
  have : Γ[x]! = type := by grind
  rw [this]
  exact a_10

private lemma preservation_Field {E J S K} (f : Nat) (p : Lang .Expr)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.Field f p) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Expr p E J S (.fieldK f :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprE <;> try solve_by_elim
  rename_i cls hcls hf _ _
  apply ContType.FieldK (cCnt := cCnt) (defs := defs) ⟨cls, hcls⟩ <;> solve_by_elim

private lemma preservation_VarDecl {E J S K} (type : Ty) (e : Lang .Expr)
    (hw : Wt cCnt defs .Eval (.Eval .Stmt (.Decl type e) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Expr e E J S (.declK type :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprE <;> solve_by_elim

private lemma preservation_Assign {E J S K} (x : VarName) (e : Lang .Expr)
    (hw : Wt cCnt defs .Eval (.Eval .Stmt (.Assign x e) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Expr e E J S (.assignK x :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprE <;> solve_by_elim

private lemma preservation_Seq {E J S K} (s₁ s₂ : Lang .Stmt)
    (hw : Wt cCnt defs .Eval (.Eval .Stmt (.Seq s₁ s₂) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Stmt s₁ E J S (.seqK s₂ :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprS <;> solve_by_elim

private lemma preservation_ExprStmt {E J S K} (e : Lang .Expr)
    (hw : Wt cCnt defs .Eval (.Eval .Stmt (.Do e) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Expr e E J S (.exprStmtK :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprE <;> solve_by_elim

private lemma preservation_BinOp {E J S K} (e₁ e₂ : Lang .Expr) (op : BinOp)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.BinOp e₁ e₂ op) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Expr e₁ E J S (.binopLK op e₂ :: K)) := by
  unhygienic cases hw
  cases a_3
  eapply Wt.WtExprE <;> try solve_by_elim
  apply ContType.BinOpLK <;> try solve_by_elim
  rename_i eq
  subst eq
  solve_by_elim

private lemma preservation_UnOp {E J S K} (e : Lang .Expr) (op : UnOp)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.UnOp e op) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Expr e E J S (.unopK op :: K)) := by
  unhygienic cases hw
  cases a_3
  eapply Wt.WtExprE <;> try solve_by_elim
  apply ContType.UnOpK <;> try solve_by_elim
  rename_i eq
  subst eq
  solve_by_elim

private lemma preservation_If {E J S K} (e s₁ s₂ : Lang .Expr)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.If e s₁ s₂) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Expr e E J S (.ifCondK s₁ s₂ :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprE <;> solve_by_elim

private lemma preservation_While {E J S K} (c body : Lang .Expr)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.While c body) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Expr c E J S (.loopK c body :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprE <;> solve_by_elim

private lemma preservation_Break {E J S K} (l : Nat)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.Break l) E J S K)) :
    Wt cCnt defs .Cont (.Cont (.value .Unit) E J S J[l]!) := by
  unhygienic cases hw
  cases a_3
  rename_i lj
  rw [loop_jump_ext] at lj
  apply Wt.WtContV _ _ cnts
  · exact a
  · exact a_1
  · exact a_2
  · exact .Unit
  · exact a_4
  · exact a_5
  · assumption
  · assumption
  · grind
  · grind
  rcases lj.2 l (by omega) with ⟨r, hr⟩
  rcases a_7 l (by grind) r hr with ⟨J₁, hj⟩
  have lm := a_6 l (by grind) r hr
  rw [hj] at lm
  cases lm
  rw [hj]
  apply ContType.BreakRestoreK <;> solve_by_elim

private lemma preservation_Scope {E J S K} (s : Lang .Stmt) (e : Lang .Expr)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.Scope s e) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Stmt s E J S (.scopeBodyK e E.length J :: K)) := by
  unhygienic cases hw
  unhygienic cases a_3
  apply Wt.WtExprS (cnts := cnts)
  · exact a
  · exact a_1
  · exact a_2
  · exact a_11
  · solve_by_elim
  iterate 5 { assumption }
  have typ_lemma := stmt_mono _ _ _ _ _ _ a_11
  rcases typ_lemma with ⟨g1, hg1⟩
  cases g1
  simp only [TypR.extR, TypR.Stmt.injEq] at hg1
  have hElen : E.length = Γ.length := by grind [coh_len]
  rename_i Γ₁
  have drop_lem : (List.drop (List.length Γ₂ - List.length E) Γ₂) = Γ := by
    rw [hElen, ← hg1]
    simp
  apply ContType.ScopeBodyK (cnts := cnts)
  · exact a_12
  · grind
  · solve_by_elim
  · solve_by_elim
  · intro l hl n1 hd
    rcases a_7 l hl n1 hd with ⟨k, hk⟩
    have := a_6 l hl n1 hd
    rw [drop_lem]
    apply this
  · solve_by_elim
  · intros
    apply cont_gen_method <;> solve_by_elim
  · solve_by_elim
  rw [hElen, ← hg1]
  simp only [List.length_append, Nat.add_sub_cancel, List.drop_left']
  exact a_10

private lemma preservation_Return {E J S K} (e : Lang .Expr) (l : Nat)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.Return e l) E J S K)) :
    Wt cCnt defs .Eval (.Eval .Expr e E J S (.returnJumpK l :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprE <;> solve_by_elim

private lemma preservation_Call₀ {E J S K} (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
    (args : Fin (defs.methods cls m).nArg → Lang .Expr)
    (h0 : 0 = (defs.methods cls m).nArg)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.Call m cls args) E J S K)) :
    Wt cCnt defs .Eval
      (.Eval .Expr (defs.methods cls m).body [] [.returnRestoreK E J :: K] S
        (.callRestoreK E J :: K)) := by
  unhygienic cases hw
  unhygienic cases a_3
  apply Wt.WtExprE (Δ := [.Method cls m]) (type := type) (cnts := [K])
  · exact .CohEmp
  · exact a_1
  · exact a_2
  · rw [defs_ok] at a_2
    have def_ok := a_2 cls m
    grind
  · solve_by_elim
  · solve_by_elim
  · grind
  · grind
  · intro l hl cls1_1 m1 hm
    have : cls = cls1_1 := by grind
    subst this
    have : m1 = m := by grind
    subst this
    have heq : [Cont.returnRestoreK E J :: K][l]! = Cont.returnRestoreK E J :: K := by grind
    rw [heq]
    apply ContType.ReturnRestoreK <;> try solve_by_elim
    grind
  · intro l hl cls' m' hlf
    grind
  apply ContType.CallRestoreK <;> try solve_by_elim

private lemma preservation_Call {E J S K} (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
    (args : Fin (defs.methods cls m).nArg → Lang .Expr)
    (hn : 0 < (defs.methods cls m).nArg)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.Call m cls args) E J S K)) :
    Wt cCnt defs .Eval
      (.Eval .Expr (args ⟨0, hn⟩) E J S
        (.argK cls m ⟨0, hn⟩ (fun x => by grind [Fin]) (fun i => args ⟨i + 1, by grind⟩) :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprE <;> try solve_by_elim
  apply ContType.ArgK
  · solve_by_elim
  · simp
  · grind
  · grind
  solve_by_elim

private lemma preservation_New₀ {E J S K} (cls : Fin cCnt) (a : Addr)
    (args : Fin (defs.fieldsCnt cls) → Lang .Expr)
    (h0 : 0 = defs.fieldsCnt cls) (ha : a ∉ S)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.New cls args) E J S K)) :
    Wt cCnt defs .Cont
      (.Cont (.value (.Addr a)) E J (S.insert a ⟨cls, fun _ => by grind [Fin]⟩) K) := by
  unhygienic cases hw
  cases a_4
  apply Wt.WtContV (.Addr a) _ cnts
  · apply coh_ext <;> solve_by_elim
  · apply store_ext
    · exact a_2
    · exact ha
    grind [Fin]
  · exact a_3
  · apply ValueTyp.Cls cls cls a _ (fun _ => .Unit) <;>
    · try rw [Finmap.lookup_insert]
      grind [Fin]
  · solve_by_elim
  · solve_by_elim
  · intros
    apply cont_type_ext <;> solve_by_elim
  · grind
  · intros
    apply cont_type_ext <;> solve_by_elim
  · grind
  apply cont_type_ext <;> solve_by_elim

private lemma preservation_New {E J S K} (cls : Fin cCnt)
    (args : Fin (defs.fieldsCnt cls) → Lang .Expr)
    (hn : 0 < defs.fieldsCnt cls)
    (hw : Wt cCnt defs .Eval (.Eval .Expr (.New cls args) E J S K)) :
    Wt cCnt defs .Eval
      (.Eval .Expr (args ⟨0, hn⟩) E J S
        (.newK cls ⟨0, hn⟩ (fun x => by grind [Fin]) (fun i => args ⟨i + 1, by grind⟩) :: K)) := by
  unhygienic cases hw
  cases a_3
  apply Wt.WtExprE <;> try solve_by_elim
  apply ContType.NewK (retTy := Ty.cls cls) <;> try solve_by_elim
  grind

private lemma preservation_FieldDone {E J S K} (a : Addr) (cls : Fin cCnt)
    (k : Fin (defs.fieldsCnt cls)) (values : Fin (defs.fieldsCnt cls) → Value)
    (hlk : S.lookup a = some ⟨cls, values⟩)
    (hw : Wt cCnt defs .Cont (.Cont (.value (.Addr a)) E J S (.fieldK k :: K))) :
    Wt cCnt defs .Cont (.Cont (.value (values k)) E J S K) := by
  unhygienic cases hw
  cases a_11
  apply Wt.WtContV <;> try solve_by_elim
  cases a_4
  rename_i ceq hv gt
  have ceq1 := Fin.eq_of_val_eq ceq
  subst ceq1
  clear ceq
  rename_i cls1 _ _ _ _ _
  have : cls = cls1 := by grind
  subst this
  simp only [hlk, Option.some.injEq, Object.mk.injEq, heq_eq_eq, true_and] at gt
  subst gt
  grind

private lemma preservation_VarDeclDone {E J S K} (type : Ty) (v : Value)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.declK type :: K))) :
    Wt cCnt defs .Cont (.Cont .skip (v :: E) J S K) := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtContS
  · apply Coh.CohBind <;> solve_by_elim
  · solve_by_elim
  · solve_by_elim
  · solve_by_elim
  · solve_by_elim
  · intro l hl n1 hd
    rcases a_7 l hl n1 hd with ⟨j, hj⟩
    rw [hj]
    have := a_6 l hl n1 hd
    rw [hj] at this
    cases this
    have : type :: Γ = [type] ++ Γ := by grind
    apply cont_gen_loop <;> try solve_by_elim
    · rw [this]
      apply suffix_eq <;> solve_by_elim
    grind
  · solve_by_elim
  · intros
    apply cont_gen_method <;> solve_by_elim
  · solve_by_elim
  solve_by_elim

private lemma preservation_AssignDone {E J S K} (x : VarName) (v : Value)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.assignK x :: K))) :
    Wt cCnt defs .Cont (.Cont .skip (E.set x v) J S K) := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtContS (cnts := cnts)
  · apply coh_set
    · exact a
    · grind [coh_len]
    grind
  · exact a_1
  · solve_by_elim
  · solve_by_elim
  iterate 6 { assumption }

private lemma preservation_SeqDone {E J S K} (s₂ : Lang .Stmt)
    (hw : Wt cCnt defs .Cont (.Cont .skip E J S (.seqK s₂ :: K))) :
    Wt cCnt defs .Eval (.Eval .Stmt s₂ E J S K) := by
  unhygienic cases hw
  cases a_9
  apply Wt.WtExprS <;> solve_by_elim

private lemma preservation_ExprStmtDone {E J S K} (v : Value)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.exprStmtK :: K))) :
    Wt cCnt defs .Cont (.Cont .skip E J S K) := by
  unhygienic cases hw
  cases a_10
  apply Wt.WtContS <;> solve_by_elim

private lemma preservation_BinOpL {E J S K} (op : BinOp) (v₁ : Value) (e₂ : Lang .Expr)
    (hw : Wt cCnt defs .Cont (.Cont (.value v₁) E J S (.binopLK op e₂ :: K))) :
    Wt cCnt defs .Eval (.Eval .Expr e₂ E J S (.binopRK op v₁ :: K)) := by
  unhygienic cases hw
  cases a_10
  apply Wt.WtExprE <;> try solve_by_elim
  apply ContType.BinOpRK
  · -- The ValueTyp `a_3` constrains `v₁` to the shape demanded by `op.args.1`;
    -- pick the matching `simpleType` witness per operator.
    cases op
    · cases a_3
      exact .Nat _
    · cases a_3
      exact .Nat _
    · cases a_3
      exact .Nat _
    · cases a_3
      · exact .True
      · exact .False
  solve_by_elim

private lemma preservation_BinOpR {E J S K} (op : BinOp) (v₁ v₂ result : Value)
    (hstep : op.step v₁ v₂ result)
    (hw : Wt cCnt defs .Cont (.Cont (.value v₂) E J S (.binopRK op v₁ :: K))) :
    Wt cCnt defs .Cont (.Cont (.value result) E J S K) := by
  unhygienic cases hw
  cases a_10
  apply Wt.WtContV <;> try solve_by_elim
  -- The `hstep : op.step v₁ v₂ result` constrains `result`'s shape;
  -- pick the matching ValueTyp witness per `op.step` constructor.
  cases hstep
  · exact .Nat _
  · exact .Nat _
  · exact .True
  · exact .False
  · exact .True
  · exact .True
  · exact .False
  · exact .False

private lemma preservation_UnOpDone {E J S K} (op : UnOp) (v result : Value)
    (hstep : op.step v result)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.unopK op :: K))) :
    Wt cCnt defs .Cont (.Cont (.value result) E J S K) := by
  unhygienic cases hw
  cases a_10
  apply Wt.WtContV (cnts := cnts)
  · exact a
  · exact a_1
  · solve_by_elim
  · cases hstep <;> solve_by_elim
  · solve_by_elim
  · solve_by_elim
  iterate 5 { assumption }

private lemma preservation_IfTrue {E J S K} (s₁ s₂ : Lang .Expr)
    (hw : Wt cCnt defs .Cont (.Cont (.value .True) E J S (.ifCondK s₁ s₂ :: K))) :
    Wt cCnt defs .Eval (.Eval .Expr s₁ E J S K) := by
  unhygienic cases hw
  cases a_10
  apply Wt.WtExprE <;> solve_by_elim

private lemma preservation_IfFalse {E J S K} (s₁ s₂ : Lang .Expr)
    (hw : Wt cCnt defs .Cont (.Cont (.value .False) E J S (.ifCondK s₁ s₂ :: K))) :
    Wt cCnt defs .Eval (.Eval .Expr s₂ E J S K) := by
  unhygienic cases hw
  cases a_10
  apply Wt.WtExprE <;> solve_by_elim

-- Loop entry: pushes the breakRestoreK frame onto J and adds a new
-- `.Loop |E|` jump frame on Δ; re-typing the existing J entries under the
-- extended Δ is the most expensive case in preservation.
private lemma preservation_LoopTrue {E J S K} (body c : Lang .Expr)
    (hw : Wt cCnt defs .Cont (.Cont (.value .True) E J S (.loopK c body :: K))) :
    Wt cCnt defs .Eval
      (.Eval .Expr body E ((.breakRestoreK E.length J :: K) :: J) S
        (.loopContK c body E.length J :: K)) := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtExprE _ _ (cnts := K :: cnts)
  · exact a
  · solve_by_elim
  · solve_by_elim
  · exact a_12
  · grind
  · grind
  · intro l hl n1 hlj
    simp at hl
    by_cases hl1 : ∃ l1, l1 + 1 = l
    · rcases hl1 with ⟨l1, hl1⟩
      subst hl1
      have hidx : ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l1 + 1]! = J[l1]! := by grind
      rw [hidx]
      have prev := a_6 l1 (by omega) n1 hlj
      rcases a_7 l1 (by omega) n1 hlj with ⟨j1, hj1⟩
      rw [hj1]
      rw [hj1] at prev
      cases prev
      apply ContType.BreakRestoreK <;> solve_by_elim
    have heq :
      ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l]! =
      .breakRestoreK (List.length E) J :: K := by
        simp at hl1
        grind
    rw [heq]
    have hdrop : (List.drop (List.length Γ - List.length E) Γ) = Γ := by
      rw [coh_len _ _ _ _ _ a]
      grind
    apply ContType.BreakRestoreK <;> try solve_by_elim
    · grind [coh_len]
    · grind
    · grind
    rw [hdrop]
    grind
  · intro l hl n1 hlj
    simp at hl
    by_cases hl1 : ∃ l1, l1 + 1 = l
    · rcases hl1 with ⟨l1, hl1⟩
      subst hl1
      grind
    have heq :
      ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l]! =
      .breakRestoreK (List.length E) J :: K := by
        simp at hl1
        grind
    grind [coh_len]
  · intro l hl cls m hlj
    simp at hl
    by_cases hl1 : ∃ l1, l1 + 1 = l
    · rcases hl1 with ⟨l1, hl1⟩
      subst hl1
      have hidx : ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l1 + 1]! = J[l1]! := by grind
      rw [hidx]
      apply cont_gen_method (K' := cnts[l1]!) <;> try solve_by_elim
      · grind
      grind
    have hidx2 :
      ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l]! =
      Cont.breakRestoreK (List.length E) J :: K := by
        simp at hl1
        grind
    grind
  · grind
  rw [coh_len _ _ _ _ _ a]
  apply ContType.LoopContK _ _ _ cnts
  · simp
  · simp only [Nat.sub_self, List.drop_zero]
    exact a_11
  · grind [coh_len]
  · solve_by_elim
  · grind
  · grind
  · grind
  · grind
  · grind
  grind

private lemma preservation_LoopFalse {E J S K} (body c : Lang .Expr) (n : Nat)
    (hw : Wt cCnt defs .Cont (.Cont (.value .False) E J S (.loopK c body :: K))) :
    Wt cCnt defs .Cont (.Cont (.value .Unit) E J S K) := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtContV (cnts := cnts)
  · exact a
  · exact a_1
  · exact a_2
  · exact .Unit
  · exact a_4
  · exact a_5
  · assumption
  · assumption
  · assumption
  · assumption
  · assumption

private lemma preservation_LoopCont {E J S K J₀} (body c : Lang .Expr) (n : Nat)
    (hw : Wt cCnt defs .Cont (.Cont (.value .Unit) E J S (.loopContK c body n J₀ :: K))) :
    Wt cCnt defs .Eval
      (.Eval .Expr c (E.drop (E.length - n)) J₀ S (.loopK c body :: K)) := by
  unhygienic cases hw
  unhygienic cases a_10
  rw [coh_len _ _ _ _ _ a]
  apply Wt.WtExprE _ _ cnts_1
  · apply coh_mono
    exact a
  · solve_by_elim
  · solve_by_elim
  · exact a_12
  · solve_by_elim
  · assumption
  · assumption
  · assumption
  · intros
    apply cont_gen_method <;> solve_by_elim
  · assumption
  apply ContType.LoopK <;> grind

private lemma preservation_BreakRestore {E J S K n J₀}
    (hw : Wt cCnt defs .Cont (.Cont (.value .Unit) E J S (.breakRestoreK n J₀ :: K))) :
    Wt cCnt defs .Cont (.Cont (.value .Unit) (E.drop (E.length - n)) J₀ S K) := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtContV (Δ := Δ₁) (cnts := cnts_1)
  · apply coh_mono
    exact a
  · exact a_1
  · solve_by_elim
  · solve_by_elim
  · solve_by_elim
  · solve_by_elim
  · grind [coh_len]
  · solve_by_elim
  · intros
    apply cont_gen_method <;> solve_by_elim
  · solve_by_elim
  grind [coh_len]

private lemma preservation_ScopeBody {E J S K J₀} (body : Lang .Expr) (n : Nat)
    (hw : Wt cCnt defs .Cont (.Cont .skip E J S (.scopeBodyK body n J₀ :: K))) :
    Wt cCnt defs .Eval (.Eval .Expr body E J S (.scopeExitK n J₀ :: K)) := by
  unhygienic cases hw
  unhygienic cases a_9
  apply Wt.WtExprE _ _ cnts
  · exact a
  · exact a_1
  · exact a_2
  · solve_by_elim
  · solve_by_elim
  · assumption
  · assumption
  · assumption
  · assumption
  · assumption
  apply ContType.ScopeExitK _ _ _ cnts_1 <;> try solve_by_elim

private lemma preservation_ScopeExit {E J S K J₀} (n : Nat) (v : Value)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.scopeExitK n J₀ :: K))) :
    Wt cCnt defs .Cont (.Cont (.value v) (E.drop (E.length - n)) J₀ S K) := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtContV (Δ := Δ₂) (cnts := cnts_1)
  · apply coh_mono
    exact a
  · exact a_1
  · solve_by_elim
  · solve_by_elim
  · solve_by_elim
  · solve_by_elim
  · grind [coh_len]
  · solve_by_elim
  · intros
    apply cont_gen_method <;> solve_by_elim
  · solve_by_elim
  grind [coh_len]

private lemma preservation_ReturnJump {E J S K K'} (v : Value) (l : Nat)
    (hjl : J[l]! = K')
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.returnJumpK l :: K))) :
    Wt cCnt defs .Cont (.Cont (.value v) E J S K') := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtContV (cnts := cnts)
  · exact a
  · exact a_1
  · exact a_2
  · exact a_3
  · solve_by_elim
  · assumption
  · assumption
  · assumption
  · assumption
  · assumption
  have ⟨hl, hΔl⟩ := method_jump_lookup cCnt defs cls m a_11
  rcases a_9 l (by grind) cls m hΔl with ⟨E₀, J₀, hk⟩
  subst hjl
  rw [hk]
  have lm := a_8 l (by grind) cls m hΔl
  rw [hk] at lm
  cases lm
  apply ContType.ReturnRestoreK <;> try solve_by_elim
  grind

private lemma preservation_ReturnRestore {E J S K E₀ J₀} (v : Value)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.returnRestoreK E₀ J₀ :: K))) :
    Wt cCnt defs .Cont (.Cont (.value v) E₀ J₀ S K) := by
  unhygienic cases hw
  cases a_10
  apply Wt.WtContV <;> solve_by_elim

private lemma preservation_ArgNext {E J S K} (v : Value)
    (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
    (sep : Fin (defs.methods cls m).nArg)
    (vals : Fin sep → Value)
    (exprs : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
    (hn : sep + 1 < (defs.methods cls m).nArg)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.argK cls m sep vals exprs :: K))) :
    Wt cCnt defs .Eval
      (.Eval .Expr (exprs ⟨0, by omega⟩) E J S
        (.argK cls m ⟨sep + 1, hn⟩
          (fun i => if hs : i.val = sep.val then v else vals ⟨i, by grind⟩)
          (fun i => exprs ⟨i + 1, by grind⟩) :: K)) := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtExprE <;> try solve_by_elim
  apply ContType.ArgK <;> try solve_by_elim
  · simp
  · grind
  grind

private lemma preservation_ArgDone {E J S K} (v : Value)
    (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
    (sep : Fin (defs.methods cls m).nArg)
    (vals : Fin sep → Value)
    (exprs : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
    (hn : sep + 1 = (defs.methods cls m).nArg)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.argK cls m sep vals exprs :: K))) :
    Wt cCnt defs .Eval
      (.Eval .Expr (defs.methods cls m).body
        (List.ofFn (fun i => if hs : i = sep then v else vals ⟨i, by grind⟩))
        ([.returnRestoreK E J :: K]) S (.callRestoreK E J :: K)) := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtExprE (Γ := List.ofFn (defs.methods cls m).argTy) (cnts := [K])
  · rw [coh_iff]
    grind
  · exact a_1
  · exact a_2
  · rw [defs_ok] at a_2
    exact a_2 _ _
  · solve_by_elim
  · grind
  · grind
  · grind
  · unhygienic intros
    have : [Cont.returnRestoreK E J :: K][l]! = Cont.returnRestoreK E J :: K := by grind
    rw [this]
    apply ContType.ReturnRestoreK <;> try solve_by_elim
    grind
  · grind
  apply ContType.CallRestoreK <;> try solve_by_elim
  grind

private lemma preservation_CallRestore {E J S K E₀ J₀} (v : Value)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.callRestoreK E₀ J₀ :: K))) :
    Wt cCnt defs .Cont (.Cont (.value v) E₀ J₀ S K) := by
  unhygienic cases hw
  cases a_10
  apply Wt.WtContV <;> solve_by_elim

private lemma preservation_NewNext {E J S K} (v : Value)
    (cls : Fin cCnt)
    (sep : Fin (defs.fieldsCnt cls))
    (vals : Fin sep → Value)
    (exprs : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
    (hn : sep + 1 < defs.fieldsCnt cls)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.newK cls sep vals exprs :: K))) :
    Wt cCnt defs .Eval
      (.Eval .Expr (exprs ⟨0, by omega⟩) E J S
        (.newK cls ⟨sep + 1, hn⟩
          (fun i => if hs : i.val = sep.val then v else vals ⟨i, by grind⟩)
          (fun i => exprs ⟨i + 1, by grind⟩) :: K)) := by
  unhygienic cases hw
  unhygienic cases a_10
  apply Wt.WtExprE <;> try solve_by_elim
  apply ContType.NewK <;> try solve_by_elim
  · simp
  · grind
  grind

-- NewDone allocates a fresh address and extends the store; the
-- store-extension lemma chain (`coh_ext`, `store_ext`, `cont_type_ext`,
-- `value_typ_ext`) is the bookkeeping that dominates this case.
private lemma preservation_NewDone {E J S K} (v : Value)
    (cls : Fin cCnt)
    (sep : Fin (defs.fieldsCnt cls))
    (vals : Fin sep → Value)
    (exprs : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
    (hn : sep + 1 = defs.fieldsCnt cls) (a : Addr) (ha : a ∉ S)
    (hw : Wt cCnt defs .Cont (.Cont (.value v) E J S (.newK cls sep vals exprs :: K))) :
    Wt cCnt defs .Cont
      (.Cont (.value (.Addr a)) E J
        (S.insert a ⟨cls,
          fun i => if hs : i.val = sep.val then v else vals ⟨i, by grind⟩⟩) K) := by
  unhygienic cases hw
  cases a_11
  apply Wt.WtContV (Δ := Δ) _ _ cnts
  · apply coh_ext <;> solve_by_elim
  · apply store_ext <;> grind
  · exact a_3
  · apply ValueTyp.Cls cls cls a
    · rw [Finmap.lookup_insert]
    · intro i
      apply value_typ_ext <;> grind
    rfl
  · solve_by_elim
  · solve_by_elim
  · intros
    apply cont_type_ext <;> grind
  · solve_by_elim
  · intros
    apply cont_type_ext <;> grind
  · grind
  apply cont_type_ext <;> grind

end Preservation

theorem preservation (s : CEK cCnt defs m) (s' : CEK cCnt defs m') :
    Wt cCnt defs m s → Eval cCnt defs m m' s s' → Wt cCnt defs m' s' := by
  intro hw he
  cases he with
  | Val v e hlv => exact Preservation.preservation_Val cCnt defs v e hlv hw
  | Var x => exact Preservation.preservation_Var cCnt defs x hw
  | Field f p => exact Preservation.preservation_Field cCnt defs f p hw
  | VarDecl type e => exact Preservation.preservation_VarDecl cCnt defs type e hw
  | Assign x e => exact Preservation.preservation_Assign cCnt defs x e hw
  | Seq s₁ s₂ => exact Preservation.preservation_Seq cCnt defs s₁ s₂ hw
  | ExprStmt e => exact Preservation.preservation_ExprStmt cCnt defs e hw
  | BinOp e₁ e₂ op => exact Preservation.preservation_BinOp cCnt defs e₁ e₂ op hw
  | UnOp e op => exact Preservation.preservation_UnOp cCnt defs e op hw
  | If e s₁ s₂ => exact Preservation.preservation_If cCnt defs e s₁ s₂ hw
  | While c body => exact Preservation.preservation_While cCnt defs c body hw
  | Break l => exact Preservation.preservation_Break cCnt defs l hw
  | Scope s e => exact Preservation.preservation_Scope cCnt defs s e hw
  | Return e => exact Preservation.preservation_Return cCnt defs e _ hw
  | Call₀ cls m args h0 => exact Preservation.preservation_Call₀ cCnt defs cls m args h0 hw
  | Call cls m args hn => exact Preservation.preservation_Call cCnt defs cls m args hn hw
  | New₀ cls a args h0 ha => exact Preservation.preservation_New₀ cCnt defs cls a args h0 ha hw
  | New cls args hn => exact Preservation.preservation_New cCnt defs cls args hn hw
  | FieldDone a cls k values hlk =>
    exact Preservation.preservation_FieldDone cCnt defs a cls k values hlk hw
  | VarDeclDone type v => exact Preservation.preservation_VarDeclDone cCnt defs type v hw
  | AssignDone x v => exact Preservation.preservation_AssignDone cCnt defs x v hw
  | SeqDone s₂ => exact Preservation.preservation_SeqDone cCnt defs s₂ hw
  | ExprStmtDone v => exact Preservation.preservation_ExprStmtDone cCnt defs v hw
  | BinOpL op v₁ e₂ => exact Preservation.preservation_BinOpL cCnt defs op v₁ e₂ hw
  | BinOpR op v₁ v₂ result hstep =>
    exact Preservation.preservation_BinOpR cCnt defs op v₁ v₂ result hstep hw
  | UnOpDone op v result hstep =>
    exact Preservation.preservation_UnOpDone cCnt defs op v result hstep hw
  | IfTrue s₁ s₂ => exact Preservation.preservation_IfTrue cCnt defs s₁ s₂ hw
  | IfFalse s₁ s₂ => exact Preservation.preservation_IfFalse cCnt defs s₁ s₂ hw
  | LoopTrue body c => exact Preservation.preservation_LoopTrue cCnt defs body c hw
  | LoopFalse body c n => exact Preservation.preservation_LoopFalse cCnt defs body c n hw
  | LoopCont body c n => exact Preservation.preservation_LoopCont cCnt defs body c n hw
  | BreakRestore => exact Preservation.preservation_BreakRestore cCnt defs hw
  | ScopeBody body n => exact Preservation.preservation_ScopeBody cCnt defs body n hw
  | ScopeExit n v => exact Preservation.preservation_ScopeExit cCnt defs n v hw
  | ReturnJump v l hjl => exact Preservation.preservation_ReturnJump cCnt defs v l hjl hw
  | ReturnRestore v => exact Preservation.preservation_ReturnRestore cCnt defs v hw
  | ArgNext v cls m sep vals exprs hn =>
    exact Preservation.preservation_ArgNext cCnt defs v cls m sep vals exprs hn hw
  | ArgDone v cls m sep vals exprs hn =>
    exact Preservation.preservation_ArgDone cCnt defs v cls m sep vals exprs hn hw
  | CallRestore v => exact Preservation.preservation_CallRestore cCnt defs v hw
  | NewNext v cls sep vals exprs hn =>
    exact Preservation.preservation_NewNext cCnt defs v cls sep vals exprs hn hw
  | NewDone v cls sep vals exprs hn a ha =>
    exact Preservation.preservation_NewDone cCnt defs v cls sep vals exprs hn a ha hw
