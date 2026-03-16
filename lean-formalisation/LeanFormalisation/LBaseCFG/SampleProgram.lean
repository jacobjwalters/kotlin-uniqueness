import LeanFormalisation.LBase

def simpleProgram : Lang .Stmt :=
  .Seq
  (.Decl .Nat (.Nat 5))
  (.Seq
    (.Decl .Nat (.Nat 3))
    (.Do (.If (.BinOp (.Var 0) (.Var 1) .Add)
      (.Scope (.Assign 0 (.Nat 10)) .Unit)
      (.Scope (.Assign 1 (.Nat 20)) .Unit)
    ))
  )

def complexProgram : Lang .Stmt :=
  .Seq
  (.Decl .Nat (.Nat 100))
  (.Seq
    (.Decl .Nat (.Nat 50))
    (.Do (.If (.BinOp (.Var 0) (.Var 1) .Add)
      (.Scope
        (.Seq
          (.Assign 0 (.Nat 5))
          (.Do (.If (.BinOp (.Var 1) (.Nat 10) .Add)
            (.Scope (.Assign 1 (.Nat 15)) .Unit)
            (.Scope (.Assign 1 (.Nat 25)) .Unit)
          ))
        )
        .Unit
      )
      (.Scope
        (.Seq
          (.Assign 0 (.Nat 3))
          (.Do (.If (.BinOp (.Var 0) (.Nat 7) .Add)
            (.Scope (.Assign 1 (.Nat 30)) .Unit)
            (.Scope (.Assign 1 (.Nat 40)) .Unit)
          ))
        )
        .Unit
      )
    ))
  )

def whileProgram : Lang .Stmt :=
  .Seq
  (.Decl .Nat (.Nat 0))
  (.Seq
    (.Decl .Nat (.Nat 10))
    (.Do (.While (.BinOp (.Var 0) (.Var 1) .Add)
      (.Scope
        (.Assign 0 (.Nat 1))
        .Unit
      )
    ))
  )

def sampleProgram := whileProgram
