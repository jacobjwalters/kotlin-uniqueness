import LeanFormalisation.LBase.CFG.AltCFG
import LeanFormalisation.LBase.CFG.SampleProgram

open LeanFormalisation AltCFG
namespace AltCFGRepr

abbrev DotAttrs := List (String × String)

structure DotOverlay where
  nodeMeta : CFGNode → List String := fun _ => []
  edgeMeta : CFGEdge → List String := fun _ => []
  nodeAttrs : CFGNode → DotAttrs := fun _ => []
  edgeAttrs : CFGEdge → DotAttrs := fun _ => []

-- blegh
private def simplify (s : String) : String :=
  s
  |>.replace "LeanFormalisation.AltCFG." ""
  |>.replace "LeanFormalisation." ""
  |>.replace "Lang." ""
  |>.replace "τ." ""
  |>.replace "BinOp." ""
  |>.replace "UnOp." ""
  |>.replace "CFGNodeKind." ""
  |>.replace "CFGNode." ""
  |>.replace "EdgeKind." ""

private def showSimpleRepr {α : Type} [Repr α] (x : α) : String :=
  simplify s!"{repr x}"

private def showNode (n : CFGNode) : String :=
  s!"n{n.id}:{showSimpleRepr n.kind}"

private def escapeDot (s : String) : String :=
  (s.replace "\\" "\\\\")
    |>.replace "\"" "\\\""
    |>.replace "\n" "\\n"

private def renderAttrs (attrs : DotAttrs) : String :=
  if attrs.isEmpty then
    ""
  else
    let rendered := attrs.map (fun (k, v) => s!"{k}=\"{escapeDot v}\"")
    s!" [{String.intercalate ", " rendered}]"

private def renderLabel (base : String) (extras : List String) : String :=
  let lines := (base :: extras).filter (fun s => s != "")
  String.intercalate "\\n" (lines.map escapeDot)

def toDotWith (g : CFG) (overlay : DotOverlay) : String :=
  let nodeLines := g.nodes.foldl (fun acc n =>
    let nodeId := showNode n
    let label := renderLabel nodeId (overlay.nodeMeta n)
    let attrs := ("label", label) :: overlay.nodeAttrs n
    acc ++ s!"  \"{escapeDot nodeId}\"{renderAttrs attrs};\n"
  ) ""
  let edgeLines := g.edges.foldl (fun acc e =>
    let src := showNode e.src
    let dst := showNode e.dst
    let edgeLabel := renderLabel (showSimpleRepr e.kind) (overlay.edgeMeta e)
    let attrs := ("label", edgeLabel) :: overlay.edgeAttrs e
    acc ++ s!"  \"{escapeDot src}\" -> \"{escapeDot dst}\"{renderAttrs attrs};\n"
  ) ""
  "digraph AltCFG {\n  rankdir=TD;\n  node\
    [shape=box fontname=\"monospace\" width=4 nojustify=false];\n"
    ++ nodeLines ++ edgeLines ++ "}"

def toDot (g : CFG) : String :=
  toDotWith g {}

end AltCFGRepr

-- def main (_ : List String) : IO Unit := do
--   let g := AltCFG.stmtCFG sampleProgram
--   IO.println (AltCFGRepr.toDot g)
