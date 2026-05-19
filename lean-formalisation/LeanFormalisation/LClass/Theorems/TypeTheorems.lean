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

set_option maxHeartbeats 1000000 in
-- TODO(phase-2/step-5): split this proof into one helper lemma per `Eval`
-- constructor so each case can be type-checked in isolation. Once that's
-- done the 10× heartbeat budget above will no longer be needed.
theorem preservation (s : CEK cCnt defs m) (s' : CEK cCnt defs m') :
  Wt cCnt defs m s → Eval cCnt defs m m' s s' → Wt cCnt defs m' s' := by
    intro hw he
    unhygienic induction he <;> unhygienic cases hw
    -- Batch: simple cases handled by solve_by_elim
    all_goals try
    { unhygienic cases a_3
      try (apply Wt.WtExprE <;> solve_by_elim)
      try (apply Wt.WtExprS <;> solve_by_elim)
      try (apply Wt.WtContS <;> solve_by_elim)
      try (apply Wt.WtContV <;> solve_by_elim) }
    all_goals try
    { unhygienic cases a_9
      try (apply Wt.WtExprE <;> solve_by_elim)
      try (apply Wt.WtExprS <;> solve_by_elim) }
    all_goals try
    { unhygienic cases a_10
      try (apply Wt.WtExprE <;> solve_by_elim)
      try (apply Wt.WtExprS <;> solve_by_elim)
      try (apply Wt.WtContS <;> solve_by_elim)
      try (apply Wt.WtContV <;> solve_by_elim) }
    -- Val: liftValue preserves type
    { cases a <;>
      { cases a_4
        apply Wt.WtContV <;> solve_by_elim } }
    -- Var: environment lookup
    { cases a_3
      apply Wt.WtContV (cnts := cnts)
      { apply a }
      { apply a_1 }
      { apply a_2 }
      { apply coh_get cCnt defs E
        { apply a }
        grind [coh_len] }
      { solve_by_elim }
      { assumption }
      { assumption }
      { assumption }
      { grind }
      { grind }
      have : Γ[x]! = type := by grind
      rw [this]
      exact a_10 }
    { cases a_3
      apply Wt.WtExprE <;> try solve_by_elim
      rename_i cls hcls hf ht eq
      apply ContType.FieldK (cCnt := cCnt) (defs := defs) ⟨cls, hcls⟩ <;> solve_by_elim }
    { cases a_3
      eapply Wt.WtExprE <;> try solve_by_elim
      apply ContType.BinOpLK <;> try solve_by_elim
      rename_i eq
      subst eq
      solve_by_elim }
    { cases a_3
      eapply Wt.WtExprE <;> try solve_by_elim
      apply ContType.UnOpK <;> try solve_by_elim
      rename_i eq
      subst eq
      solve_by_elim }
    { cases a_3
      rename_i lj
      rw [loop_jump_ext] at lj
      apply Wt.WtContV _ _ cnts
      { apply a }
      { apply a_1 }
      { apply a_2 }
      { apply ValueTyp.Unit }
      { apply a_4 }
      { apply a_5 }
      { assumption }
      { assumption }
      { grind }
      { grind }
      rcases lj.2 l (by omega) with ⟨r, hr⟩
      rcases a_7 l (by grind) r hr with ⟨J₁, hj⟩
      have lm := a_6 l (by grind) r hr
      rw [hj] at lm
      cases lm
      rw [hj]
      apply ContType.BreakRestoreK <;> solve_by_elim }
    { unhygienic cases a_3
      apply Wt.WtExprS (cnts := cnts)
      { apply a }
      { apply a_1 }
      { apply a_2 }
      { apply a_11 }
      { solve_by_elim }
      iterate 5 { assumption }
      have typ_lemma := stmt_mono _ _ _ _ _ _ a_11
      rcases typ_lemma with ⟨g1, hg1⟩
      cases g1
      simp only [TypR.extR, TypR.Stmt.injEq] at hg1
      have : E.length = Γ.length := by
        grind [coh_len]
      rename_i Γ₁
      have drop_lem : (List.drop (List.length Γ₂ - List.length E) Γ₂) = Γ := by
        rw [this, ←hg1]
        simp
      apply ContType.ScopeBodyK (cnts := cnts)
      { apply a_12 }
      { grind }
      { solve_by_elim }
      { solve_by_elim }
      { intro l hl n1 hd
        rcases a_7 l hl n1 hd with ⟨k, hk⟩
        have := a_6 l hl n1 hd
        rw [drop_lem]
        apply this }
      { solve_by_elim }
      { intros
        apply cont_gen_method <;> solve_by_elim }
      { solve_by_elim }
      rw [this, ←hg1]
      simp only [List.length_append, Nat.add_sub_cancel, List.drop_left']
      exact a_10 }
    { unhygienic cases a_4
      apply Wt.WtExprE (Δ := [.Method cls m_1]) (type := type) (cnts := [K])
      { apply Coh.CohEmp }
      { apply a_2 }
      { apply a_3 }
      { rw [defs_ok] at a_3
        have def_ok := a_3 cls m_1
        grind }
      { solve_by_elim }
      { solve_by_elim }
      { grind }
      { grind }
      { intro l hl cls1_1 m1 hm
        have : cls = cls1_1 := by grind
        subst this
        have : m1 = m_1 := by grind
        subst this
        have : [Cont.returnRestoreK E J :: K][l]! = Cont.returnRestoreK E J :: K := by
          grind
        rw [this]
        apply ContType.ReturnRestoreK <;> try solve_by_elim
        grind }
      { intro l hl cls m hlf
        rename_i cls1
        have : cls1 = cls := by
          grind
        subst this
        have : m_1 = m := by
          grind
        subst this
        grind }
      apply ContType.CallRestoreK <;> try solve_by_elim }
    { cases a_3
      apply Wt.WtExprE <;> try solve_by_elim
      apply ContType.ArgK
      { solve_by_elim }
      { simp }
      { grind }
      { grind }
      solve_by_elim }
    { cases a_4
      apply Wt.WtContV (.Addr a) _ cnts
      { apply coh_ext <;> solve_by_elim }
      { apply store_ext
        { apply a_2 }
        { apply ha }
        grind [Fin] }
      { apply a_3 }
      { apply ValueTyp.Cls cls cls a _ (fun _ => .Unit) <;>
        { try rw [Finmap.lookup_insert]
          grind [Fin] } }
      { solve_by_elim }
      { solve_by_elim }
      { intros
        apply cont_type_ext <;> solve_by_elim }
      { grind }
      { intros
        apply cont_type_ext <;> solve_by_elim }
      { grind }
      apply cont_type_ext <;> solve_by_elim }
    { cases a_3
      apply Wt.WtExprE <;> try solve_by_elim
      apply ContType.NewK (retTy := Ty.cls cls) <;> try solve_by_elim
      grind }
    { cases a_12
      apply Wt.WtContV <;> try solve_by_elim
      cases a_5
      rename_i ceq hv gt
      have ceq1 := Fin.eq_of_val_eq ceq
      subst ceq1
      clear ceq
      rename_i cls1 _ _ _ _ _
      have : cls = cls1 := by grind
      subst this
      simp only [a_1, Option.some.injEq, Object.mk.injEq, heq_eq_eq, true_and] at gt
      subst gt
      grind }
    { unhygienic cases a_10
      apply Wt.WtContS
      { apply Coh.CohBind <;> solve_by_elim }
      { solve_by_elim }
      { solve_by_elim }
      { solve_by_elim }
      { solve_by_elim }
      { intro l hl n1 hd
        rcases a_7 l hl n1 hd with ⟨j, hj⟩
        rw [hj]
        have := a_6 l hl n1 hd
        rw [hj] at this
        cases this
        have : type :: Γ = [type] ++ Γ := by
          grind
        apply cont_gen_loop <;> try solve_by_elim
        { rw [this]
          apply suffix_eq <;> solve_by_elim }
        grind }
      { solve_by_elim }
      { intros
        apply cont_gen_method <;> solve_by_elim }
      { solve_by_elim }
      solve_by_elim }
    -- AssignDone: update environment
    { unhygienic cases a_10
      apply Wt.WtContS (cnts := cnts)
      { apply coh_set
        { apply a }
        { grind [coh_len] }
        grind }
      { apply a_1 }
      { solve_by_elim }
      { solve_by_elim }
      iterate 6 { assumption } }
    { cases a_10
      apply Wt.WtExprE <;> try solve_by_elim
      apply ContType.BinOpRK
      { cases op <;> grind [simpleType, ValueTyp, BinOp.args] }
      solve_by_elim }
    -- BinOpR: step produces result
    { cases a_11
      apply Wt.WtContV <;> try solve_by_elim
      cases op <;>
      { grind [simpleType, ValueTyp, BinOp.args, ValueTyp, BinOp.step] } }
    -- UnOpDone: step produces result
    { cases a_11
      apply Wt.WtContV (cnts := cnts)
      { apply a_1 }
      { apply a_2 }
      { solve_by_elim }
      { cases a <;> solve_by_elim }
      { solve_by_elim }
      { solve_by_elim }
      iterate 5 { assumption } }
    -- LoopTrue: enter loop body, push JStackCtx
    { unhygienic cases a_10
      apply Wt.WtExprE _ _ (cnts := K :: cnts)
      { apply a }
      -- need n = Γ.length (holds via Coh at loop entry)
      -- then JCtx becomes Γ.length :: Δ matching body typing
      { solve_by_elim }
      { solve_by_elim }
      { apply a_12 }
      { grind }
      { grind }
      { intro l hl n1 hlj
        simp at hl
        by_cases hl1 : ∃ l1, l1 + 1 = l
        { rcases hl1 with ⟨l1, hl1⟩
          subst hl1
          have : ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l1 + 1]! = J[l1]! := by
            grind
          rw [this]
          have prev := a_6 l1 (by omega) n1 hlj
          rcases a_7 l1 (by omega) n1 hlj with ⟨j1, hj1⟩
          rw [hj1]
          rw [hj1] at prev
          cases prev
          apply ContType.BreakRestoreK <;> solve_by_elim }
        have eq :
          ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l]! =
          .breakRestoreK (List.length E) J :: K := by
            simp at hl1
            grind
        rw [eq]
        have : (List.drop (List.length Γ - List.length E) Γ) = Γ := by
          rw [coh_len _ _ _ _ _ a]
          grind
        apply ContType.BreakRestoreK <;> try solve_by_elim
        { grind [coh_len] }
        { grind }
        { grind }
        rw [this]
        grind }
      { intro l hl n1 hlj
        simp at hl
        by_cases hl1 : ∃ l1, l1 + 1 = l
        { rcases hl1 with ⟨l1, hl1⟩
          subst hl1
          grind }
        have eq :
          ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l]! =
          .breakRestoreK (List.length E) J :: K := by
            simp at hl1
            grind
        grind [coh_len] }
      { intro l hl cls m hlj
        simp at hl
        by_cases hl1 : ∃ l1, l1 + 1 = l
        { rcases hl1 with ⟨l1, hl1⟩
          subst hl1
          have : ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l1 + 1]! = J[l1]! := by
            grind
          rw [this]
          apply cont_gen_method (K' := cnts[l1]!) <;> try solve_by_elim
          { grind }
          grind }
        have : ((Cont.breakRestoreK (List.length E) J :: K) :: J)[l]! = (Cont.breakRestoreK (List.length E) J :: K) := by
          simp at hl1
          grind
        grind }
      { grind }
      rw [coh_len _ _ _ _ _ a]
      apply ContType.LoopContK _ _ _ cnts
      { simp }
      { simp only [Nat.sub_self, List.drop_zero]
        apply a_11 }
      { grind [coh_len] }
      { solve_by_elim }
      { grind }
      { grind }
      { grind }
      { grind }
      { grind }
      grind }
    { unhygienic cases a_10
      rw [coh_len _ _ _ _ _ a]
      apply Wt.WtExprE _ _ cnts_1
      { apply coh_mono
        apply a }
      { solve_by_elim }
      { solve_by_elim }
      { apply a_12 }
      { solve_by_elim }
      { assumption }
      { assumption }
      { assumption }
      { intros
        apply cont_gen_method <;> solve_by_elim }
      { assumption }
      apply ContType.LoopK <;> grind }
    { unhygienic cases a_10
      have : E.length = Γ.length := by grind [coh_len]
      apply Wt.WtContV _ _ cnts_1
      { apply coh_mono
        { apply a } }
      { apply a_1 }
      { apply a_2 }
      { apply a_3 }
      { solve_by_elim }
      { solve_by_elim }
      { grind }
      { solve_by_elim }
      { intros
        apply cont_gen_method <;> solve_by_elim }
      { solve_by_elim }
      grind [coh_len] }
    { unhygienic cases a_9
      apply Wt.WtExprE _ _ cnts
      { apply a }
      { apply a_1 }
      { apply a_2 }
      { solve_by_elim }
      { solve_by_elim }
      { assumption }
      { assumption }
      { assumption }
      { assumption }
      { assumption }
      apply ContType.ScopeExitK _ _ _ cnts_1 <;> try solve_by_elim }
    -- ScopeExit: drop environment, restore context
    { unhygienic cases a_10
      apply Wt.WtContV (Δ := Δ₂) (cnts := cnts_1)
      { apply coh_mono
        apply a }
      { apply a_1 }
      { solve_by_elim }
      { solve_by_elim }
      { solve_by_elim }
      { solve_by_elim }
      { grind [coh_len] }
      { solve_by_elim }
      { intros
        apply cont_gen_method <;> solve_by_elim }
      { solve_by_elim }
      grind [coh_len] }
    { unhygienic cases a_11
      apply Wt.WtContV (cnts := cnts)
      { apply a_1 }
      { apply a_2 }
      { apply a_3 }
      { apply a_4 }
      { solve_by_elim }
      { assumption }
      { assumption }
      { assumption }
      { assumption }
      { assumption }
      have ⟨hl, hΔl⟩ := method_jump_lookup cCnt defs cls m_1 a_12
      rcases a_10 l (by grind) cls m_1 hΔl with ⟨E₀, J₀, hk⟩
      subst a
      rw [hk]
      have lm := a_9 l (by grind) cls m_1 hΔl
      rw [hk] at lm
      cases lm
      apply ContType.ReturnRestoreK <;> try solve_by_elim
      grind }
    { unhygienic cases a_10
      apply Wt.WtExprE <;> try solve_by_elim
      apply ContType.ArgK <;> try solve_by_elim
      { simp }
      { grind }
      grind }
    { unhygienic cases a_10
      apply Wt.WtExprE (Γ := List.ofFn (defs.methods cls m_1).argTy) (cnts := [K])
      { rw [coh_iff]
        grind }
      { apply a_1 }
      { apply a_2 }
      { rw [defs_ok] at a_2
        apply a_2 }
      { solve_by_elim }
      { grind }
      { grind }
      { grind }
      { unhygienic intros
        have : [Cont.returnRestoreK E J :: K][l]! = Cont.returnRestoreK E J :: K := by
          grind
        rw [this]
        apply ContType.ReturnRestoreK <;> try solve_by_elim
        grind }
      { grind }
      apply ContType.CallRestoreK <;> try solve_by_elim
      grind }
    { unhygienic cases a_10
      apply Wt.WtExprE <;> try solve_by_elim
      apply ContType.NewK <;> try solve_by_elim
      { simp }
      { grind }
      grind }
    { cases a_11
      apply Wt.WtContV (Δ := Δ) _ _ cnts
      { apply coh_ext <;> solve_by_elim }
      { apply store_ext <;> grind }
      { apply a_3 }
      { apply ValueTyp.Cls cls cls a
        { rw [Finmap.lookup_insert] }
        { intro i
          apply value_typ_ext <;> grind}
        rfl }
      { solve_by_elim }
      { solve_by_elim }
      { intros
        apply cont_type_ext <;> grind }
      { solve_by_elim }
      { intros
        apply cont_type_ext <;> grind }
      { grind }
      apply cont_type_ext <;> grind }
