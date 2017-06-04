open ../synth2[spec]

--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
one sig X1, X2, K extends IntVar {}
one sig I0, I1, I2 extends IntLit {}
fact {
  IntLit<:val = I0->0 + I1->1 + I2->2
}

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
fact { IntVarVal = Int }

pred spec[root: Node, eval: Node -> Int] {
  eval[X1] < eval[X2] implies (eval[K] < eval[X1] implies eval[root] = 0)
  eval[X1] < eval[X2] implies (eval[K] > eval[X2] implies eval[root] = 2)
  eval[X1] < eval[X2] implies ((eval[K] > eval[X1] and eval[K] < eval[X2]) implies eval[root] = 1)
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synthIntNodeI for 10 but -1..3 Int, 0 BoolLit, 0 BoolVar, 
                                        0 BinaryIntOp, 0 UnaryIntOp, 
                                        0 Equals, 0 BoolComp
run synthIntNodeI for 0 but -1..3 Int, exactly 2 ITE, exactly 2 LT
