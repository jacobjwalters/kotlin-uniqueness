import LeanFormalisation.LBase

def sampleProgram : Lang .Stmt :=
  .Seq
    (.Decl .Nat (.Nat 5))
    (.Seq
      (.Decl .Nat (.Nat 3))
      (.Do (.If (.BinOp (.Var 0) (.Var 1) .Add)
        (.Scope (.Assign 0 (.Nat 10)) .Unit)
        (.Scope (.Assign 1 (.Nat 20)) .Unit)
      ))
    )
