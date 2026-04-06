import LeanFormalisation.LBase.LBaseDefs

def simpleProgram : Lang .Stmt :=
  .Seq
  (.Decl .nat (.Nat 5))
  (.Seq
    (.Decl .nat (.Nat 3))
    (.Do (.If (.BinOp (.Var 0) (.Var 1) .Add)
      (.Scope (.Assign 0 (.Nat 10)) .Unit)
      (.Scope (.Assign 1 (.Nat 20)) .Unit)
    ))
  )

def complexProgram : Lang .Stmt :=
  .Seq
  (.Decl .nat (.Nat 100))
  (.Seq
    (.Decl .nat (.Nat 50))
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
  (.Decl .nat (.Nat 0))
  (.Seq
    (.Decl .nat (.Nat 10))
    (.Do (.While (.BinOp (.Var 0) (.Var 1) .Add)
      (.Scope
        (.Assign 0 (.Nat 1))
        .Unit
      )
    ))
  )

def sampleProgram := simpleProgram
