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

theorem abs_sim {cek₁ cek₂ : CEK} {ac₁ : AbsControl}
    (heval : Eval cek₁ cek₂)
    (hsim : SimRel cek₁ ac₁)
    (hcont : AbsContInv cek₁.K (ac₁.target)) :
    ∃ ac₂, AbsStep ac₁ ac₂ ∧ SimRel cek₂ ac₂ ∧ AbsContInv cek₂.K (ac₂.target) := by
  cases heval
  case Val v =>
    cases hsim
    use .exprExit (liftValue v)
    split_ands <;> first | constructor | assumption
    cases v <;> constructor
  case Var x =>
    cases hsim
    exists .exprExit (.Var x)
    split_ands <;> first | assumption | repeat constructor
  case VarDecl τ e =>
    cases hsim
    exists .exprEntry e
    split_ands <;> try constructor
    cases hcont <;> try constructor <;> assumption
  case VarDeclDone τ v =>
    cases hsim
    case exprExitVal e
    exists .stmtExit (.Decl τ e)
    split_ands <;> try constructor
    cases hcont
    assumption
  case Assign x e =>
    cases hsim
    exists .exprEntry e
    split_ands <;> try constructor
    cases hcont <;> try constructor <;> assumption
  case AssignDone x v =>
    cases hsim
    case exprExitVal e
    exists .stmtExit (.Assign x e)
    split_ands <;> try constructor
    cases hcont
    assumption
  case Seq s₁ s₂ =>
    cases hsim
    exists .stmtEntry s₁
    split_ands <;> try constructor
    cases hcont <;> constructor <;> assumption
  case ExprStmt e =>
    cases hsim
    exists .exprEntry e
    split_ands <;> try constructor
    cases hcont <;> constructor <;> assumption
  case BinOp e₁ e₂ o =>
    cases hsim
    exists .exprEntry e₁
    split_ands <;> try constructor
    cases hcont <;> constructor <;> assumption
  case BinOpL o v e =>
    cases hsim
    case exprExitVal e' =>
    exists (.exprEntry e)
    split_ands
    · exact AbsStep.binopMid e' e o
    · constructor
    · cases hcont
      constructor; assumption
  case BinOpR o v₁ v₂ v₃ h =>
    cases hsim
    case exprExitVal e =>
    cases hcont
    case binopRK e₁ h =>
    exists .exprExit (.BinOp e₁ e o)
    split_ands <;> try constructor
    assumption
  case UnOp e o =>
    cases hsim
    exists .exprEntry e
    split_ands <;> try constructor
    cases hcont <;> constructor <;> assumption
  case UnOpDone o v r h =>
    cases hsim
    case exprExitVal e =>
    exists .exprExit (.UnOp e o)
    split_ands <;> try constructor
    cases hcont
    assumption
  case If e s₁ s₂ =>
    cases hsim
    exists .exprEntry e
    split_ands <;> try constructor
    cases hcont <;> constructor <;> assumption
  case While c b =>
    cases hsim
    exists .exprEntry c
    split_ands <;> try constructor
    cases hcont <;> constructor <;> assumption
  case Scope s e =>
    cases hsim
    exists .stmtEntry s
    split_ands <;> try constructor
    cases hcont <;> constructor <;> assumption
  case ScopeBody b n =>
    cases hsim
    case stmtExitSkip s =>
    exists .exprEntry b
    split_ands
    · exact AbsStep.scopeMid s b
    · constructor
    · cases hcont
      constructor <;> assumption
  case ScopeExit =>
    cases hsim
    case exprExitVal e =>
    cases hcont
    case scopeExitK s k =>
    exists .exprExit (s.Scope e)
    split_ands <;> try constructor
    assumption
  case ExprStmtDone =>
    cases hsim
    case exprExitVal e =>
    exists (.stmtExit (.Do e))
    split_ands
    · constructor
    · constructor
    · cases hcont
      assumption
  case IfTrue =>
    cases hsim
    case exprExitVal thn els c =>
    cases hcont
    case ifCondK h =>
    exists .exprEntry thn
    split_ands
    · exact AbsStep.ifTrue c thn els
    · constructor
    -- h : AbsContInv K✝ (ContTarget.expr (c.If thn els))
    -- ⊢ AbsContInv K✝ (ContTarget.expr thn)
    sorry
  case IfFalse =>
    cases hsim
    case exprExitVal thn els c =>
    cases hcont
    case ifCondK h =>
    exists .exprEntry els
    split_ands
    · exact AbsStep.ifFalse c thn els
    · constructor
    -- h : AbsContInv K✝ (ContTarget.expr (c.If thn els))
    -- ⊢ AbsContInv K✝ (ContTarget.expr els)
    sorry
  case Break K' l =>
    cases hsim
    -- Big Sorry
    sorry
  case SeqDone =>
    cases hsim
    case stmtExitSkip s₁ =>
    cases hcont
    case seqK s₂ h =>
    -- h : AbsContInv K✝ (ContTarget.stmt (s₁;s₂))
    -- need: stmtEntry s₂ and AbsContInv K✝ (ContTarget.stmt s₂)
    sorry
  case LoopTrue b c n =>
    cases hsim
    cases hcont
    case _ e =>
    exists .exprEntry b
    split_ands
    · exact AbsStep.whileLTrue c b
    · constructor
    -- e : AbsContInv K✝ (ContTarget.expr (c.While b))
    -- ⊢ AbsContInv (Cont.loopContK c b n :: K✝) (ContTarget.expr b)
    sorry
  case LoopFalse b c n =>
    cases hsim
    cases hcont
    case _ e =>
    exists .exprExit (c.While b)
    split_ands <;> try constructor
    assumption
  case LoopCont b c n =>
    cases hsim
    case _ e =>
    cases hcont
    exists .exprEntry c
    split_ands
    · exact AbsStep.whileBack c b
    · constructor
    · assumption
