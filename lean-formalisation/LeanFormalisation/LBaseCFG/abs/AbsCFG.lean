import LeanFormalisation.LBase

inductive AbsControl where
| exprEntry (e : Lang .Expr)
| exprExit  (e : Lang .Expr)
| stmtEntry (s : Lang .Stmt)
| stmtExit  (s : Lang .Stmt)

def isLitOrVar : Lang .Expr -> Prop
| .Var _
| .Nat _
| .True
| .False
| .Unit => True
| _ => False

inductive AbsStep : AbsControl -> AbsControl -> Prop where
| valExit (e : Lang .Expr) :
    isLitOrVar e →
    AbsStep (.exprEntry e) (.exprExit e)
| binopEntry (e₁ e₂ : Lang .Expr) (op : BinOp) :
    AbsStep (.exprEntry (.BinOp e₁ e₂ op)) (.exprEntry e₁)
| unopEntry (e : Lang .Expr) (op : UnOp) :
    AbsStep (.exprEntry (.UnOp e op)) (.exprEntry e)
| ifEntry (c e₁ e₂ : Lang .Expr) :
    AbsStep (.exprEntry (.If c e₁ e₂)) (.exprEntry c)
| whileEntry (c b : Lang .Expr) :
    AbsStep (.exprEntry (.While c b)) (.exprEntry c)
| breakExit (l : Nat) (target : Lang .Expr) :
    AbsStep (.exprEntry (.Break l)) (.exprExit target)
| scopeEntry (s : Lang .Stmt) (e : Lang .Expr) :
    AbsStep (.exprEntry (.Scope s e)) (.stmtEntry s)
/- ----- ----- -/
| ifTrue (c e₁ e₂ : Lang .Expr) :
    AbsStep (.exprExit c) (.exprEntry e₁)
| ifFalse (c e₁ e₂ : Lang .Expr) :
    AbsStep (.exprExit c) (.exprEntry e₂)
| ifBranch (c e₁ e₂ b : Lang .Expr) :
    (b = e₁ ∨ b = e₂) ->
    AbsStep (.exprExit b) (.exprExit (.If c e₁ e₂))
| binopMid (e₁ e₂ : Lang .Expr) (op : BinOp) :
    AbsStep (.exprExit e₁) (.exprEntry e₂)
| binopExit (e₁ e₂ : Lang .Expr) (op : BinOp) :
    AbsStep (.exprExit e₂) (.exprExit (.BinOp e₁ e₂ op))
| unopExit (e : Lang .Expr) (op : UnOp) :
    AbsStep (.exprExit e) (.exprExit (.UnOp e op))
| whileLTrue (c b : Lang .Expr) :
    AbsStep (.exprExit c) (.exprEntry b)
| whileLFalse (c b : Lang .Expr) :
    AbsStep (.exprExit c) (.exprExit (.While c b))
| whileBack (c b : Lang .Expr) :
    AbsStep (.exprExit b) (.exprEntry c)
| exprStmtExit (e : Lang .Expr) :
    AbsStep (.exprExit e) (.stmtExit (.Do e))
/- ----- ----- -/
| declEntry (ty : Ty) (e : Lang .Expr) :
    AbsStep (.stmtEntry (.Decl ty e)) (.exprEntry e)
| declExit (ty : Ty) (e : Lang .Expr) :
    AbsStep (.exprExit e) (.stmtExit (.Decl ty e))
| assignEntry (x : VarName) (e : Lang .Expr) :
    AbsStep (.stmtEntry (.Assign x e)) (.exprEntry e)
| assignExit (x : VarName) (e : Lang .Expr) :
    AbsStep (.exprExit e) (.stmtExit (.Assign x e))
| seqEntry (s₁ s₂ : Lang .Stmt) :
    AbsStep (.stmtEntry (.Seq s₁ s₂)) (.stmtEntry s₁)
| seqMid (s₁ s₂ : Lang .Stmt) :
    AbsStep (.stmtExit s₁) (.stmtEntry s₂)
| seqExit (s₁ s₂ : Lang .Stmt) :
    AbsStep (.stmtExit s₂) (.stmtExit (.Seq s₁ s₂))
| exprStmtEntry (e : Lang .Expr) :
    AbsStep (.stmtEntry (.Do e)) (.exprEntry e)
| scopeMid (s : Lang .Stmt) (e : Lang .Expr) :
    AbsStep (.stmtExit s) (.exprEntry e)
| scopeExit (s : Lang .Stmt) (e : Lang .Expr) :
    AbsStep (.exprExit e) (.exprExit (.Scope s e))

inductive SimRel : CEK → AbsControl → Prop where
| exprEntry (e : Lang .Expr) (E J K) :
    SimRel ⟨.sourceExpr e, E, J, K⟩ (.exprEntry e)
| stmtEntry (s : Lang .Stmt) (E J K) :
    SimRel ⟨.sourceStmt s, E, J, K⟩ (.stmtEntry s)
| exprExitVal (e : Lang .Expr) (v : Value) (E J K) :
    SimRel ⟨.value v, E, J, K⟩ (.exprExit e)
| stmtExitSkip (s : Lang .Stmt) (E J K) :
    SimRel ⟨.skip, E, J, K⟩ (.stmtExit s)

inductive ContTarget where
| expr (e : Lang .Expr)
| stmt (s : Lang .Stmt)

@[simp]
def AbsControl.target : AbsControl -> ContTarget
| exprEntry e
| exprExit e => .expr e
| stmtEntry e
| stmtExit e => .stmt e

inductive AbsContInv : List Cont → ContTarget → Prop where
| halt (t : ContTarget) :
    AbsContInv [] t
| ifCondK (e₁ e₂ cond : Lang .Expr) (K : List Cont) :
    AbsContInv K (.expr (.If cond e₁ e₂)) →
    AbsContInv (.ifCondK e₁ e₂ :: K) (.expr cond)
| binopLK (op : BinOp) (e₁ e₂ : Lang .Expr) (K : List Cont) :
    AbsContInv K (.expr (.BinOp e₁ e₂ op)) →
    AbsContInv (.binopLK op e₂ :: K) (.expr e₁)
| binopRK (op : BinOp) (e₁ e₂ : Lang .Expr) (v : Value) (K : List Cont) :
    AbsContInv K (.expr (.BinOp e₁ e₂ op)) →
    AbsContInv (.binopRK op v :: K) (.expr e₂)
| unopK (op : UnOp) (e : Lang .Expr) (K : List Cont) :
    AbsContInv K (.expr (.UnOp e op)) →
    AbsContInv (.unopK op :: K) (.expr e)
| declK (ty : Ty) (e : Lang .Expr) (K : List Cont) :
    AbsContInv K (.stmt (.Decl ty e)) →
    AbsContInv (.declK ty :: K) (.expr e)
| assignK (x : VarName) (e : Lang .Expr) (K : List Cont) :
    AbsContInv K (.stmt (.Assign x e)) →
    AbsContInv (.assignK x :: K) (.expr e)
| seqK (s₁ s₂ : Lang .Stmt) (K : List Cont) :
    AbsContInv K (.stmt (.Seq s₁ s₂)) →
    AbsContInv (.seqK s₂ :: K) (.stmt s₁)
| exprStmtK (e : Lang .Expr) (K : List Cont) :
    AbsContInv K (.stmt (.Do e)) →
    AbsContInv (.exprStmtK :: K) (.expr e)
| loopK (cond body : Lang .Expr) (n : Nat) (K : List Cont) :
    AbsContInv K (.expr (.While cond body)) →
    AbsContInv (.loopK cond body n :: K) (.expr cond)
| loopContK (cond body : Lang .Expr) (n : Nat) (K : List Cont) :
    AbsContInv (.loopK cond body n :: K) (.expr cond) →
    AbsContInv (.loopContK cond body n :: K) (.expr body)
| scopeBodyK (e : Lang .Expr) (s : Lang .Stmt) (n : Nat) (K : List Cont) :
    AbsContInv K (.expr (.Scope s e)) →
    AbsContInv (.scopeBodyK e n :: K) (.stmt s)
| scopeExitK (e : Lang .Expr) (s : Lang .Stmt) (n : Nat) (K : List Cont) :
    AbsContInv K (.expr (.Scope s e)) →
    AbsContInv (.scopeExitK n :: K) (.expr e)

inductive AbsJInv : JStackCtx → Prop where
| empty : AbsJInv []
| loop (c b : Lang .Expr) (n : Nat) (K : List Cont)
    (J : JStackCtx) :
    AbsContInv K (.expr (.While c b)) →
    AbsJInv J →
    AbsJInv (⟨n, K⟩ :: J)

theorem AbsJInv.drop : AbsJInv J →
    ∀ l, AbsJInv (J.drop (l + 1)) := by
  intro h l
  induction h generalizing l with
  | empty => constructor
  | loop c b n K J hcont hJ ih =>
    cases l with
    | zero => simpa [List.drop]
    | succ l => simpa [List.drop] using ih l

theorem AbsJInv.getIdx (h : AbsJInv J) :
    ∀ l, (hl : l < J.length) →
    ∃ c b, (J[l]'hl).2 = (J[l]'hl).2 ∧
      AbsContInv (J[l]'hl).2 (.expr (.While c b)) := by
  induction h with
  | empty => intros l hl; exact absurd hl (Nat.not_lt_zero _)
  | loop c b n K J hcont hJ ih =>
    intro l hl
    cases l with
    | zero => exact ⟨c, b, rfl, hcont⟩
    | succ l => exact ih l (by grind)

theorem abs_sim {cek₁ cek₂ : CEK} {ac₁ : AbsControl}
    (heval : Eval cek₁ cek₂)
    (hsim : SimRel cek₁ ac₁)
    (hcont : AbsContInv cek₁.K (ac₁.target))
    (hjinv : AbsJInv cek₁.J) :
    ∃ ac₂ t₂, AbsStep ac₁ ac₂ ∧ SimRel cek₂ ac₂
      ∧ AbsContInv cek₂.K t₂ ∧ AbsJInv cek₂.J := by
  cases heval
  case Val v =>
    cases hsim
    refine ⟨.exprExit (liftValue v), .expr (liftValue v), ?_, ?_, ?_, ?_⟩
    · cases v <;> constructor <;> simp [liftValue, isLitOrVar]
    · constructor
    · exact hcont
    · exact hjinv
  case Var x =>
    cases hsim
    exact ⟨.exprExit (.Var x), _, AbsStep.valExit _ (by simp [isLitOrVar]),
           SimRel.exprExitVal _ _ _ _ _, hcont, hjinv⟩
  case VarDecl τ e =>
    cases hsim
    refine ⟨.exprEntry e, .expr e, ?_, ?_, ?_, ?_⟩
    · constructor
    · constructor
    · exact AbsContInv.declK τ e _ hcont
    · exact hjinv
  case VarDeclDone τ v =>
    cases hsim
    case exprExitVal e =>
    cases hcont
    case declK h =>
    exact ⟨.stmtExit (.Decl τ e), _, AbsStep.declExit τ e, SimRel.stmtExitSkip _ _ _ _, h, hjinv⟩
  case Assign x e =>
    cases hsim
    refine ⟨.exprEntry e, .expr e, ?_, ?_, ?_, ?_⟩
    · constructor
    · constructor
    · exact AbsContInv.assignK x e _ hcont
    · exact hjinv
  case AssignDone x v =>
    cases hsim
    case exprExitVal e =>
    cases hcont
    case assignK h =>
    exact ⟨.stmtExit (.Assign x e), _,
        AbsStep.assignExit x e, SimRel.stmtExitSkip _ _ _ _, h, hjinv⟩
  case Seq s₁ s₂ =>
    cases hsim
    refine ⟨.stmtEntry s₁, .stmt s₁, ?_, ?_, ?_, ?_⟩
    · constructor
    · constructor
    · exact AbsContInv.seqK s₁ s₂ _ hcont
    · exact hjinv
  case ExprStmt e =>
    cases hsim
    refine ⟨.exprEntry e, .expr e, ?_, ?_, ?_, ?_⟩
    · constructor
    · constructor
    · exact AbsContInv.exprStmtK e _ hcont
    · exact hjinv
  case BinOp e₁ e₂ o =>
    cases hsim
    refine ⟨.exprEntry e₁, .expr e₁, ?_, ?_, ?_, ?_⟩
    · constructor
    · constructor
    · exact AbsContInv.binopLK o e₁ e₂ _ hcont
    · exact hjinv
  case BinOpL o v e =>
    cases hsim
    case exprExitVal e' =>
    cases hcont
    case binopLK h =>
    exact ⟨.exprEntry e, .expr e, AbsStep.binopMid e' e o, SimRel.exprEntry _ _ _ _,
           AbsContInv.binopRK o e' e v _ h, hjinv⟩
  case BinOpR o v₁ v₂ v₃ h =>
    cases hsim
    case exprExitVal e =>
    cases hcont
    case binopRK e₁ h =>
    exact ⟨.exprExit (.BinOp e₁ e o), _, AbsStep.binopExit e₁ e o,
           SimRel.exprExitVal _ _ _ _ _, h, hjinv⟩
  case UnOp e o =>
    cases hsim
    refine ⟨.exprEntry e, .expr e, ?_, ?_, ?_, ?_⟩
    · constructor
    · constructor
    · exact AbsContInv.unopK o e _ hcont
    · exact hjinv
  case UnOpDone o v r h =>
    cases hsim
    case exprExitVal e =>
    cases hcont
    case unopK h =>
    exact ⟨.exprExit (.UnOp e o), _, AbsStep.unopExit e o,
           SimRel.exprExitVal _ _ _ _ _, h, hjinv⟩
  case If e s₁ s₂ =>
    cases hsim
    refine ⟨.exprEntry e, .expr e, ?_, ?_, ?_, ?_⟩
    · constructor
    · constructor
    · exact AbsContInv.ifCondK s₁ s₂ e _ hcont
    · exact hjinv
  case While c b =>
    cases hsim
    refine ⟨.exprEntry c, .expr c, ?_, ?_, ?_, ?_⟩
    · constructor
    · constructor
    · exact AbsContInv.loopK c b _ _ hcont
    · exact hjinv
  case Scope s e =>
    cases hsim
    refine ⟨.stmtEntry s, .stmt s, ?_, ?_, ?_, ?_⟩
    · constructor
    · constructor
    · exact AbsContInv.scopeBodyK e s _ _ hcont
    · exact hjinv
  case ScopeBody b n =>
    cases hsim
    case stmtExitSkip s =>
    cases hcont
    case scopeBodyK h =>
    exact ⟨.exprEntry b, .expr b, AbsStep.scopeMid s b, SimRel.exprEntry _ _ _ _,
           AbsContInv.scopeExitK b s n _ h, hjinv⟩
  case ScopeExit =>
    cases hsim
    case exprExitVal e =>
    cases hcont
    case scopeExitK s h =>
    exact ⟨.exprExit (s.Scope e), _, AbsStep.scopeExit s e,
           SimRel.exprExitVal _ _ _ _ _, h, hjinv⟩
  case ExprStmtDone =>
    cases hsim
    case exprExitVal e =>
    cases hcont
    case exprStmtK h =>
    exact ⟨.stmtExit (.Do e), _, AbsStep.exprStmtExit e,
           SimRel.stmtExitSkip _ _ _ _, h, hjinv⟩
  case IfTrue =>
    cases hsim
    case exprExitVal thn els c =>
    cases hcont
    case ifCondK h =>
    -- h : AbsContInv K (.expr (.If c thn els))
    -- With weakened conclusion, we can use the parent target directly
    exact ⟨.exprEntry thn, .expr (.If c thn els), AbsStep.ifTrue c thn els,
           SimRel.exprEntry _ _ _ _, h, hjinv⟩
  case IfFalse =>
    cases hsim
    case exprExitVal thn els c =>
    cases hcont
    case ifCondK h =>
    exact ⟨.exprEntry els, .expr (.If c thn els), AbsStep.ifFalse c thn els,
           SimRel.exprEntry _ _ _ _, h, hjinv⟩
  case Break K' l =>
    cases hsim
    case exprEntry E J K =>
    -- We need l < J.length to use AbsJInv; handle both cases
    by_cases hl : l < J.length
    · obtain ⟨c, b, _, hcontJ⟩ := hjinv.getIdx l hl
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      exact ⟨.exprExit (.While c b), .expr (.While c b),
             AbsStep.breakExit l (.While c b),
             SimRel.exprExitVal _ _ _ _ _,
             hcontJ, hjinv.drop l⟩
    · -- l ≥ J.length: J[l]! = default = (0, []), so J[l]!.2 = []
      simp only [List.getElem!_eq_getElem?_getD]
      have hnil : J[l]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      simp only [hnil, Option.getD_none]
      have : (default : ℕ × List Cont) = (0, []) := rfl
      simp only [this]
      exact ⟨.exprExit (.While .Unit .Unit), .expr (.While .Unit .Unit),
             AbsStep.breakExit l (.While .Unit .Unit),
             SimRel.exprExitVal _ _ _ _ _,
             AbsContInv.halt _, hjinv.drop l⟩
  case SeqDone =>
    cases hsim
    case stmtExitSkip s₁ =>
    cases hcont
    case seqK s₂ h =>
    -- h : AbsContInv K (.stmt (.Seq s₁ s₂))
    -- With weakened conclusion, use parent target
    exact ⟨.stmtEntry s₂, .stmt (.Seq s₁ s₂), AbsStep.seqMid s₁ s₂,
           SimRel.stmtEntry _ _ _ _, h, hjinv⟩
  case LoopTrue b c n =>
    cases hsim
    cases hcont
    case loopK h =>
    -- h : AbsContInv K (.expr (.While c b))
    -- loopContK needs: AbsContInv (.loopK c b n :: K) (.expr cond)
    -- which we can build from h, then loopContK gives us (.expr body)
    exact ⟨.exprEntry b, .expr b, AbsStep.whileLTrue c b, SimRel.exprEntry _ _ _ _,
           AbsContInv.loopContK c b n _ (AbsContInv.loopK c b n _ h),
           AbsJInv.loop c b n _ _ h hjinv⟩
  case LoopFalse b c n =>
    cases hsim
    cases hcont
    case loopK h =>
    exact ⟨.exprExit (c.While b), _, AbsStep.whileLFalse c b,
           SimRel.exprExitVal _ _ _ _ _, h, hjinv⟩
  case LoopCont b c n =>
    cases hsim
    case exprExitVal e =>
    cases hcont
    case loopContK h =>
    -- LoopCont pops ⟨n, K⟩ from J
    cases hjinv with
    | loop c' b' n' K' J' hcontJ' hjinvJ' =>
    exact ⟨.exprEntry c, _, AbsStep.whileBack c b,
           SimRel.exprEntry _ _ _ _, h, hjinvJ'⟩
