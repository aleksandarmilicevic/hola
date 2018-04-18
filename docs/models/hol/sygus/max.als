module max

open synth[spec]

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> (Int + Bool)] {
    all v: Var | eval[root] >= eval[v]
    some v: Var | eval[root] = eval[v]
}
