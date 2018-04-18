open synth[spec]

--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
one sig X1, X2, X3, X4, X5, K extends Var {}
one sig I0 extends IntLit {} { val = 0 }
one sig I1 extends IntLit {} { val = 1 }
one sig I2 extends IntLit {} { val = 2 }
one sig I3 extends IntLit {} { val = 3 }
one sig I4 extends IntLit {} { val = 4 }
one sig I5 extends IntLit {} { val = 5 }

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> (Int + Bool)] {
  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4] and eval[X4] < eval[X5]) implies
    (eval[K] < eval[X1] implies eval[root] = 0)
  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4] and eval[X4] < eval[X5]) implies
    (eval[K] > eval[X5] implies eval[root] = 5)

  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4] and eval[X4] < eval[X5]) implies
    ((eval[K] > eval[X1] and eval[K] < eval[X2]) implies eval[root] = 1)
  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4] and eval[X4] < eval[X5]) implies
    ((eval[K] > eval[X2] and eval[K] < eval[X3]) implies eval[root] = 2)
  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4] and eval[X4] < eval[X5]) implies
    ((eval[K] > eval[X3] and eval[K] < eval[X4]) implies eval[root] = 3)
  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4] and eval[X4] < eval[X5]) implies
    ((eval[K] > eval[X4] and eval[K] < eval[X5]) implies eval[root] = 4)
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synth for 22 but 0..6 Int, 0 And, 0 Or, 0 Not, 0 Equals
run synth for 22 but 0..6 Int, 0 And, 0 Or, 0 Not, 0 Equals, exactly 6 ITE, exactly 5 LT
