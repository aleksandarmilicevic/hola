open synth[spec]

--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
one sig X1, X2, X3, K extends Var {}
one sig I0 extends IntLit {} { val = 0 }
one sig I1 extends IntLit {} { val = 1 }
one sig I2 extends IntLit {} { val = 2 }
one sig I3 extends IntLit {} { val = 3 }

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> (Int + Bool)] {
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
run synth for 14 but -1..4 Int, 0 And, 0 Or, 0 Not, 0 Equals
run synth for 14 but -1..4 Int, 0 And, 0 Or, 0 Not, 0 Equals, exactly 4 ITE, exactly 3 LT
