module max

open ../synth2[spec]

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> Int] {
    all v: IntVar | eval[root] >= eval[v]
    some v: IntVar | eval[root] = eval[v]
}

fact { IntVarVal = Int }
