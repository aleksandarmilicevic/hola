module array_search

open synth<spec>

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> (Int + Bool)] {
  eval[X1] < eval[X2] implies (eval[K] < eval[X1] implies eval[root] = 0)
  eval[X1] < eval[X2] implies (eval[K] > eval[X2] implies eval[root] = 2)
  eval[X1] < eval[X2] implies ((eval[K] > eval[X1] and eval[K] < eval[X2]) implies eval[root] = 1)
}

