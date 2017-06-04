open ../synth2[spec]

--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
one sig X1, X2, X3, K extends IntVar {}
one sig I0, I1, I2, I3 extends IntLit {}
fact {
  IntLit<:val = I0->0 + I1->1 + I2->2 + I3->3
}

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
fact { IntVarVal = Int }

pred spec[root: Node, eval: Node -> Int] {
  (eval[X1] < eval[X2] and eval[X2] < eval[X3]) implies
    (eval[K] < eval[X1] implies eval[root] = 0)
  (eval[X1] < eval[X2] and eval[X2] < eval[X3]) implies
    (eval[K] > eval[X3] implies eval[root] = 3)

  (eval[X1] < eval[X2] and eval[X2] < eval[X3]) implies
    ((eval[K] > eval[X1] and eval[K] < eval[X2]) implies eval[root] = 1)
  (eval[X1] < eval[X2] and eval[X2] < eval[X3]) implies
    ((eval[K] > eval[X2] and eval[K] < eval[X3]) implies eval[root] = 2)

}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synthIntNodeI for 14 but -1..4 Int, 0 BoolLit, 0 BoolVar, 
                                        0 BinaryIntOp, 0 UnaryIntOp, 
                                        0 Equals, 0 BoolComp

run synthIntNodeI for 0 but -1..4 Int, exactly 4 ITE, exactly 3 LT
