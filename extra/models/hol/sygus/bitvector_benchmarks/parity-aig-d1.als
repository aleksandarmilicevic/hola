module parity_aig_d1

open parity[spec]

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/bitvector-benchmarks/parity-AIG-d1.sl)
--------------------------------------------------------------------------------

pred spec[root: Node, eval: Node -> (Int + Bit)] {
  let a = eval[A], b = eval[B], c = eval[C], d = eval[D] |
    parity[a, b, c, d] = eval[root]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

// SIMPLIFIED: use AndInv only: 
//  * with partial ordering: finds an instance in ~20s
//  * without partial ordering: finds an instance in ~80s
run synthBoolNodeB for 0 but -1..0 Int, exactly 15 AndInv
