import LeanFormalisation.LBaseCFG.LBaseCFGDefs
import LeanFormalisation.LBaseCFG.LBaseCFGProofs
-- edit the program in SampleProgram to change the script's output.
import LeanFormalisation.LBaseCFG.SampleProgram

def toDot (root : CFGNode) (fuel : Nat) : String :=
  let g     := buildFuncGraph root fuel
  let nodes := reachableNodes root fuel
  let nodeLines := nodes.foldl (fun acc n =>
    acc ++ s!"  \"{repr n}\";\n"
  ) ""
  let edgeLines := nodes.foldl (fun acc n =>
    n.succs.foldl (fun acc' m =>
      if g.edges ⟨n, m⟩ then
        acc' ++ s!"  \"{repr n}\" -> \"{repr m}\";\n"
      else acc'
    ) acc
  ) ""
  "digraph CFG {\n  rankdir=TD;\n  node\
    [shape=box fontname=\"monospace\" width=3 nojustify=false];\n"
    ++ nodeLines ++ edgeLines ++ "}"

private def fmtExpr : Lang .Expr → String
  | .True        => "true"
  | .False       => "false"
  | .Unit        => "()"
  | .Break       => "break"
  | .Var n       => s!"x{n}"
  | .Nat n       => toString n
  | .BinOp l r op => s!"({fmtExpr l} {repr op} {fmtExpr r})"
  | .UnOp e op   => s!"({repr op} {fmtExpr e})"
  | .If c _ _    => s!"if {fmtExpr c}"
  | .While c _   => s!"while {fmtExpr c}"
  | .Scope _ e   => s!"scope(...){fmtExpr e}"

instance : ToString τ where
  toString
    | .Nat  => "Nat"
    | .Unit => "Unit"
    | .Bool => "Bool"

private def fmtStmt : Lang .Stmt → String
  | .Decl t e    => s!"let x {t} = {fmtExpr e}"
  | .Assign n e  => s!"{n} = {fmtExpr e}"
  | .Seq _ _     => s!"seq"
  | .Do e        => s!"do {fmtExpr e}"

private def fmtControl : CFGControl → String
  | .sourceStmt s  => fmtStmt s
  | .sourceExpr e  => fmtExpr e
  | .skip => ".skip"
  | .value => s!".value"

private def fmtKont : CFGCont → String
  | .seqK s            => s!"seq▸{fmtStmt s}"
  | .declK n           => s!"decl x{n}"
  | .assignK n         => s!"x{n}:="
  | .exprStmtK         => "exprStmt"
  | .scopeExitK        => "scopeExit"
  | .scopeBodyK _      => "scopeBody"
  | .loopContK _ _     => "loopCont"
  | .loopK _ _         => "loop"
  | .unopK .IsZero     => "isZero"
  | .binopRK .BoolEq   => "binopR(==)"
  | .binopRK .NatEq    => "binopR(==)"
  | .binopRK .Sub      => "binopR(-)"
  | .binopRK .Add      => "binopR(+)"
  | .binopLK .BoolEq _ => "binopL(==)"
  | .binopLK .NatEq _  => "binopL(==)"
  | .binopLK .Sub _    => "binopL(-)"
  | .binopLK .Add _    => "binopL(+)"
  | .ifCondK _ _       => "ifCond"

private def fmtNode (n : CFGNode) : String :=
  let ctrl := fmtControl n.control
  let kont := match n.kont with
    | []  => "·"
    | ks  => ks.map fmtKont |>.intersperse "\\l " |> String.join
  s!"{ctrl}\\l⊣ {kont}\\l"

def toFmtDot (root : CFGNode) (fuel : Nat) : String :=
  let g     := buildFuncGraph root fuel
  let nodes := reachableNodes root fuel
  let nodeLines := nodes.foldl (fun acc n =>
    acc ++ s!"  \"{repr n}\" [label=\"{fmtNode n}\"];\n"
  ) ""
  let edgeLines := nodes.foldl (fun acc n =>
    n.succs.foldl (fun acc' m =>
      if g.edges ⟨n, m⟩ then
        acc' ++ s!"  \"{repr n}\" -> \"{repr m}\";\n"
      else acc'
    ) acc
  ) ""
  "digraph CFG {\n  rankdir=TD;\n  node\
    [shape=box fontname=\"monospace\" width=6 nojustify=false];\n"
    ++ nodeLines ++ edgeLines ++ "}"

def main (_ : List String) : IO Unit := do
  -- imported from SampleProgram.lean
  let program := sampleProgram
  let dot := toFmtDot (cfgInit program) (cfgFuel program)
  IO.println dot
