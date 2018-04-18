open synth[spec]

--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
one sig X1, X2, K extends Var {}
one sig Zero extends IntLit {} { val = 0 }
one sig One extends IntLit  {} { val = 1 }
one sig Two extends IntLit  {} { val = 2 }

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> (Int + Bool)] {
  eval[X1] < eval[X2] implies (eval[K] < eval[X1] implies eval[root] = 0)
  eval[X1] < eval[X2] implies (eval[K] > eval[X2] implies eval[root] = 2)
  eval[X1] < eval[X2] implies ((eval[K] > eval[X1] and eval[K] < eval[X2]) implies eval[root] = 1)
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synth for 10 but -1..3 Int, 0 And, 0 Or, 0 Not, 0 Equals
run synth for 10 but -1..3 Int, 0 And, 0 Or, 0 Not, 0 Equals, exactly 2 ITE, exactly 2 LT
