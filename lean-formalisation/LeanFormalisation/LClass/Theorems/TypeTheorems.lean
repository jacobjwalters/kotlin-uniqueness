import LeanFormalisation.LClass.Theorems.TypeProperties
import LeanFormalisation.LClass.Theorems.ContextProperties

variable (cCnt : Nat) (defs : Defs cCnt)

-- do casing on Continuation
theorem progress (s : CEK cCnt defs m) :
  Wt cCnt defs m s →
  (terminalState cCnt defs s) ∨ ∃ m' s', Eval cCnt defs m m' s s' := by
    intro hwt
    unhygienic induction s
    { by_cases ht : terminalState cCnt defs (.Eval tg C E J S K)
      { grind }
      right
      unhygienic cases hwt
      { cases e
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.Var }
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.Field }
        { eapply Exists.intro
          eapply Exists.intro
          eapply Eval.Val
          solve_by_elim }
        { eapply Exists.intro
          eapply Exists.intro
          eapply Eval.Val
          solve_by_elim }
        { eapply Exists.intro
          eapply Exists.intro
          eapply Eval.Val
          solve_by_elim }
        { eapply Exists.intro
          eapply Exists.intro
          eapply Eval.Val
          solve_by_elim }
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.BinOp }
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.UnOp }
        { cases a_3
          rename_i cls args hc harg a
          subst harg
          by_cases hs : 0 = defs.fieldsCnt ⟨cls, hc⟩
          { rcases map_fresh_addr S with ⟨a, ha⟩
            eapply Exists.intro
            eapply Exists.intro
            apply Eval.New₀ (cCnt := cCnt) (defs := defs) ⟨cls, hc⟩ a args hs ha }
          eapply Exists.intro
          eapply Exists.intro
          apply Eval.New ⟨cls, hc⟩
          omega }
        { cases a_3
          rename_i m cls args hcls hm harg a hrt
          by_cases hs : 0 = (defs.methods ⟨cls, hcls⟩ ⟨m, hm⟩).nArg
          { eapply Exists.intro
            eapply Exists.intro
            subst harg
            apply Eval.Call₀ (cCnt := cCnt) (defs := defs) ⟨cls, hcls⟩ ⟨m, hm⟩ args hs }
          subst harg
          eapply Exists.intro
          eapply Exists.intro
          apply Eval.Call ⟨cls, hcls⟩ ⟨m, hm⟩
          omega }
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.Return }
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.If }
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.While }
        { cases a_3
          rename_i l hlj
          rw [loop_jump_ext] at hlj
          rcases hlj.2 l (by omega) with ⟨res, hres⟩
          rw [←loop_jump_ext] at hlj
          eapply Exists.intro
          eapply Exists.intro
          apply Eval.Break }
        eapply Exists.intro
        eapply Exists.intro
        apply Eval.Scope }
      cases s
      all_goals try
      { eapply Exists.intro
        eapply Exists.intro
        solve_by_elim } }
    by_cases ht : terminalState cCnt defs (.Cont res E J S K)
    { grind }
    right
    unhygienic cases hwt
    { unhygienic cases K
      { cases a_10
        by_contra
        apply ht
        rw [terminalState]
        trivial }
      unhygienic cases head
      all_goals try
      { eapply Exists.intro
        eapply Exists.intro
        solve_by_elim }
      all_goals try
      { cases a_10 }
      { cases a_10
        cases a_3
        rename_i cls ty hf fty hct cls1 addr vls ceq hlk hv
        have eq : cls1 = cls := by
          ext
          omega
        subst eq
        eapply Exists.intro
        eapply Exists.intro
        exact Eval.FieldDone addr cls1 ⟨f, hf⟩ vls hlk }
      { cases v <;> cases a_10
        all_goals try grind [ValueTyp]
        all_goals
        { apply Exists.intro
          eapply Exists.intro
          solve_by_elim } }
      { cases a_10
        cases op
        all_goals try
        { rw [BinOp.args] at *
          cases v <;> try grind [simpleType, ValueTyp]
          cases v_1 <;> try grind [simpleType, ValueTyp]
          eapply Exists.intro
          eapply Exists.intro
          apply Eval.BinOpR
          solve_by_elim }
        { rw [BinOp.args] at *
          rename_i v1 _
          cases a_3
          cases v1
          rename_i m2 m1
          by_cases hm : m2 = m1 <;>
          { eapply Exists.intro
            eapply Exists.intro
            apply Eval.BinOpR
            try rw [hm]
            solve_by_elim } }
        rw [BinOp.args] at *
        rename_i v1 _
        cases a_3 <;> cases v1
        all_goals
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.BinOpR <;> solve_by_elim } }
      { cases a_10
        cases op
        cases a_3
        rename_i n
        cases n
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.UnOpDone
          apply UnOp.step.isZeroTrue }
        eapply Exists.intro
        eapply Exists.intro
        apply Eval.UnOpDone
        apply UnOp.step.isZeroFalse
        grind }
      { cases a_10
        cases a_3
        all_goals
        { eapply Exists.intro
          eapply Exists.intro
          solve_by_elim } }
      { cases a_10
        cases a_3
        eapply Exists.intro
        eapply Exists.intro
        apply Eval.LoopCont }
      { cases a_10
        eapply Exists.intro
        eapply Exists.intro
        apply Eval.ReturnJump
        rfl }
      { cases a_10
        by_cases hsep : sep + 1 = (defs.methods cls m_1).nArg
        { eapply Exists.intro
          eapply Exists.intro
          apply Eval.ArgDone
          exact hsep }
        eapply Exists.intro
        eapply Exists.intro
        apply Eval.ArgNext
        omega }
      { cases a_10
        by_cases hsep : sep + 1 = (defs.fieldsCnt cls)
        { rcases map_fresh_addr S with ⟨addr, haddr⟩
          eapply Exists.intro
          eapply Exists.intro
          apply Eval.NewDone (a := addr) <;> solve_by_elim }
        eapply Exists.intro
        eapply Exists.intro
        apply Eval.NewNext
        omega }
      unhygienic cases a_10
      eapply Exists.intro
      eapply Exists.intro
      cases a_3
      apply Eval.BreakRestore }
    unhygienic cases K
    { cases a_9 }
    unhygienic cases head
    all_goals try
    { cases a_9 }
    all_goals try
    { cases a_9
      eapply Exists.intro
      eapply Exists.intro
      solve_by_elim }

set_option maxHeartbeats 1000000

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
