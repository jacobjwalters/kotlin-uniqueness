import LeanFormalisation.LBase

namespace LeanFormalisation
namespace AltCFG

inductive CFGNodeKind where
| exprEntry (e : Lang .Expr)
| exprExit (e : Lang .Expr)
| stmtEntry (s : Lang .Stmt)
| stmtExit (s : Lang .Stmt)
deriving Repr, DecidableEq

structure CFGNode where
  id : Nat
  kind : CFGNodeKind
deriving Repr, DecidableEq

inductive EdgeKind where
| normal
| trueBranch
| falseBranch
| back
| breakOut
deriving Repr, DecidableEq

structure CFGEdge where
  src : CFGNode
  dst : CFGNode
  kind : EdgeKind
deriving Repr, DecidableEq

structure CFG where
  entry : CFGNode
  exit : CFGNode
  edges : List CFGEdge
deriving Repr

private def mkEdge (src dst : CFGNode) (kind : EdgeKind := .normal) : CFGEdge :=
  ⟨src, dst, kind⟩

private structure BuildResult where
  entry : CFGNode
  exit : CFGNode
  edges : List CFGEdge
  nextId : Nat

mutual
  private def exprSize : Lang .Expr → Nat
  | .Var _
  | .True
  | .False
  | .Nat _
  | .Unit
  | .Break => 1
  | .BinOp e₁ e₂ _ => 1 + exprSize e₁ + exprSize e₂
  | .UnOp e _ => 1 + exprSize e
  | .If c e₁ e₂ => 1 + exprSize c + exprSize e₁ + exprSize e₂
  | .While c body => 1 + exprSize c + exprSize body
  | .Scope s e => 1 + stmtSize s + exprSize e

  private def stmtSize : Lang .Stmt → Nat
  | .Decl _ e => 1 + exprSize e
  | .Assign _ e => 1 + exprSize e
  | .Seq s₁ s₂ => 1 + stmtSize s₁ + stmtSize s₂
  | .Do e => 1 + exprSize e
end

mutual
  def buildExpr (breakTarget : Option CFGNode) (nextId fuel : Nat)
      (e : Lang .Expr) : BuildResult :=
    match fuel with
    | 0 =>
      let entry : CFGNode := { id := nextId, kind := .exprEntry e }
      let exit : CFGNode := { id := nextId + 1, kind := .exprExit e }
      { entry := entry
      , exit := exit
      , edges := []
      , nextId := nextId + 2
      }
    | fuel + 1 =>
      let entry : CFGNode := { id := nextId, kind := .exprEntry e }
      let exit : CFGNode := { id := nextId + 1, kind := .exprExit e }
      let nextId := nextId + 2
      match e with
      | .Var _
      | .True
      | .False
      | .Nat _
      | .Unit =>
          { entry := entry
          , exit := exit
          , edges := [mkEdge entry exit]
          , nextId := nextId
          }
      | .BinOp e₁ e₂ _ =>
          let r₁ := buildExpr breakTarget nextId fuel e₁
          let r₂ := buildExpr breakTarget r₁.nextId fuel e₂
          { entry := entry
          , exit := exit
          , edges :=
                [ mkEdge entry r₁.entry
                , mkEdge r₁.exit r₂.entry
                , mkEdge r₂.exit exit
                ] ++ r₁.edges ++ r₂.edges
          , nextId := r₂.nextId
          }
      | .UnOp arg _ =>
          let r := buildExpr breakTarget nextId fuel arg
          { entry := entry
          , exit := exit
          , edges := [mkEdge entry r.entry, mkEdge r.exit exit] ++ r.edges
          , nextId := r.nextId
          }
      | .If cond e₁ e₂ =>
          let c := buildExpr breakTarget nextId fuel cond
          let t := buildExpr breakTarget c.nextId fuel e₁
          let f := buildExpr breakTarget t.nextId fuel e₂
          { entry := entry
          , exit := exit
          , edges :=
              [ mkEdge entry c.entry
              , mkEdge c.exit t.entry .trueBranch
              , mkEdge c.exit f.entry .falseBranch
              , mkEdge t.exit exit
              , mkEdge f.exit exit
              ] ++ c.edges ++ t.edges ++ f.edges
          , nextId := f.nextId
          }
      | .While cond body =>
          let c := buildExpr (some exit) nextId fuel cond
          let b := buildExpr (some exit) c.nextId fuel body
          { entry := entry
          , exit := exit
          , edges :=
              [ mkEdge entry c.entry
              , mkEdge c.exit b.entry .trueBranch
              , mkEdge c.exit exit .falseBranch
              , mkEdge b.exit c.entry .back
              ] ++ c.edges ++ b.edges
          , nextId := b.nextId
          }
      | .Break =>
          let edges :=
            match breakTarget with
            | some t => [mkEdge entry t .breakOut]
            | none => []
          { entry := entry
          , exit := exit
          , edges := edges
          , nextId := nextId
          }
      | .Scope s res =>
          let sRes := buildStmt breakTarget nextId fuel s
          let rRes := buildExpr breakTarget sRes.nextId fuel res
          { entry := entry
          , exit := exit
          , edges :=
                [ mkEdge entry sRes.entry
                , mkEdge sRes.exit rRes.entry
                , mkEdge rRes.exit exit
                ] ++ sRes.edges ++ rRes.edges
          , nextId := rRes.nextId
          }

  def buildStmt (breakTarget : Option CFGNode) (nextId fuel : Nat)
      (s : Lang .Stmt) : BuildResult :=
    match fuel with
    | 0 =>
      let entry : CFGNode := { id := nextId, kind := .stmtEntry s }
      let exit : CFGNode := { id := nextId + 1, kind := .stmtExit s }
      { entry := entry
      , exit := exit
      , edges := []
      , nextId := nextId + 2
      }
    | fuel + 1 =>
      let entry : CFGNode := { id := nextId, kind := .stmtEntry s }
      let exit : CFGNode := { id := nextId + 1, kind := .stmtExit s }
      let nextId := nextId + 2
      match s with
      | .Decl _ init =>
          let r := buildExpr breakTarget nextId fuel init
          { entry := entry
          , exit := exit
          , edges := [mkEdge entry r.entry, mkEdge r.exit exit] ++ r.edges
          , nextId := r.nextId
          }
      | .Assign _ rhs =>
          let r := buildExpr breakTarget nextId fuel rhs
          { entry := entry
          , exit := exit
          , edges := [mkEdge entry r.entry, mkEdge r.exit exit] ++ r.edges
          , nextId := r.nextId
          }
      | .Seq s₁ s₂ =>
          let r₁ := buildStmt breakTarget nextId fuel s₁
          let r₂ := buildStmt breakTarget r₁.nextId fuel s₂
          { entry := entry
          , exit := exit
          , edges :=
                [ mkEdge entry r₁.entry
                , mkEdge r₁.exit r₂.entry
                , mkEdge r₂.exit exit
                ] ++ r₁.edges ++ r₂.edges
          , nextId := r₂.nextId
          }
      | .Do e =>
          let r := buildExpr breakTarget nextId fuel e
          { entry := entry
          , exit := exit
          , edges := [mkEdge entry r.entry, mkEdge r.exit exit] ++ r.edges
          , nextId := r.nextId
          }
end

def exprEdges (breakTarget : Option CFGNode) (e : Lang .Expr) : List CFGEdge :=
  (buildExpr breakTarget 0 (exprSize e) e).edges

def stmtEdges (breakTarget : Option CFGNode) (s : Lang .Stmt) : List CFGEdge :=
  (buildStmt breakTarget 0 (stmtSize s) s).edges

def exprCFG (e : Lang .Expr) : CFG :=
  let r := buildExpr none 0 (exprSize e) e
  CFG.mk r.entry r.exit r.edges

def stmtCFG (s : Lang .Stmt) : CFG :=
  let r := buildStmt none 0 (stmtSize s) s
  CFG.mk r.entry r.exit r.edges

def CFG.outEdges (g : CFG) (n : CFGNode) : List CFGEdge :=
  g.edges.filter (fun e => decide (e.src = n))

def CFG.inEdges (g : CFG) (n : CFGNode) : List CFGEdge :=
  g.edges.filter (fun e => decide (e.dst = n))

def CFG.succ (g : CFG) (n : CFGNode) : List CFGNode :=
  (g.outEdges n).map (fun e => e.dst) |>.eraseDups

def CFG.pred (g : CFG) (n : CFGNode) : List CFGNode :=
  (g.inEdges n).map (fun e => e.src) |>.eraseDups

def CFG.nodes (g : CFG) : List CFGNode :=
  (g.edges.foldr (fun ed acc => ed.src :: ed.dst :: acc) [g.entry, g.exit]).eraseDups

-- Example:
-- let _ : Nat = 5;
-- do while (true) (scope { _₀ := 0 } unit)
def exampleProgram : Lang .Stmt :=
  .Seq (.Decl .nat (.Nat 5))
       (.Do (.While .True (.Scope (.Assign 0 (.Nat 0)) .Unit)))

def exampleCFG : CFG := stmtCFG exampleProgram

end AltCFG
end LeanFormalisation
