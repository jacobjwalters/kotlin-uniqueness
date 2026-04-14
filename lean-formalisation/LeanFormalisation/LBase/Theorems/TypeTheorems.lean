import LeanFormalisation.LBase.Theorems.TypeProperties
import LeanFormalisation.LBase.Theorems.ContextProperties


-- do casing on Continuation
theorem progress (s : CEK) :
  Wt s →
  (∃ E J, terminalState E J = s) ∨ ∃ s', Eval s s' := by
    intro hwt
    unhygienic induction s
    by_cases ht : ∃ E1 J1, terminalState E1 J1 = ⟨C, E, J, K⟩
    { grind }
    simp [terminalState] at ht
    right
    unhygienic cases hwt
    { cases e
      all_goals try
      { eapply Exists.intro
        solve_by_elim }
      all_goals try
      { eapply Exists.intro
        rw [←liftValue]
        solve_by_elim } }
    { cases s
      all_goals try
      { eapply Exists.intro
        solve_by_elim } }
    { unhygienic cases K
      { cases a_3 }
      unhygienic cases head
      all_goals try
      { eapply Exists.intro
        solve_by_elim }
      all_goals try
      { cases a_3 }
      { cases v <;> cases a_3
        all_goals try grind [value_type]
        all_goals
        { apply Exists.intro
          solve_by_elim } }
      { cases a_3
        cases op
        all_goals try
        { rw [BinOp.args] at *
          cases v <;> try grind [value_type]
          cases v_1 <;> try grind [value_type]
          eapply Exists.intro
          apply Eval.BinOpR
          solve_by_elim }
        { rw [BinOp.args] at *
          cases v <;> try grind [value_type]
          cases v_1 <;> try grind [value_type]
          rename_i m2 m1 _
          by_cases hm : m2 = m1 <;>
          { eapply Exists.intro
            apply Eval.BinOpR
            try rw [hm]
            solve_by_elim } }
        rw [BinOp.args] at *
        cases v <;> try grind [value_type]
        all_goals
        { cases v_1 <;> try grind [value_type]
          all_goals try
          { eapply Exists.intro
            apply Eval.BinOpR
            solve_by_elim } } }
      { cases a_3
        cases op
        rename_i op1 hc
        cases op1
        rw [UnOp.args] at a_2
        cases v <;> try grind [value_type]
        rename_i n
        cases n
        { eapply Exists.intro
          apply Eval.UnOpDone
          apply UnOp.step.isZeroTrue }
        eapply Exists.intro
        apply Eval.UnOpDone
        apply UnOp.step.isZeroFalse
        grind }
      { cases a_3
        cases v <;> try grind [value_type]
        all_goals
        { eapply Exists.intro
          solve_by_elim } }
      cases a_3
      cases v <;> try grind [value_type]
      cases a_1
      rename_i K1 _ _ _
      eapply Exists.intro
      apply Eval.LoopCont }
    unhygienic cases K
    { cases a_2
      grind }
    unhygienic cases head
    all_goals try
    { cases a_2 }
    all_goals try
    { cases a_2
      eapply Exists.intro
      solve_by_elim }

lemma jcoh_cont_type_drop (J : JStackCtx) (Γ : Ctx) (l : Nat) :
    l < Δ.length →
    JCoh J Γ Δ →
    ContType Tag.Expr
      (List.drop (l + 1) Δ)
      (List.drop (List.length Γ - J[l]!.1) Γ)
      J[l]!.2
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
    { unhygienic cases a_2
      apply Wt.WtContV (type := Ty.unit)
        (Δ := Δ.drop (l + 1))
      { apply coh_mono
        apply a }
      { rw [coh_len E Γ a]
        apply jcoh_drop
        apply a_1 }
      { simp [value_type] }
      rw [coh_len _ _ a]
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
    { cases a_3
      apply Wt.WtContS <;> solve_by_elim }
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
