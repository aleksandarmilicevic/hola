module parity_aig_d0

open parity[spec]

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/bitvector-benchmarks/parity-AIG-d0.sl)
--------------------------------------------------------------------------------

pred spec[root: Node, eval: Node -> (Int + Bit)] {
  let a = eval[A], b = eval[B], c = eval[C], d = eval[D] |
    parity[a, b, c, d] = And[eval[root],
                             Not[And[And[Not[And[a, b]], 
                                     Not[And[Not[a], Not[b]]]], 
                                 And[Not[And[Not[c], Not[d]]], 
                                     Not[And[c, d]]]]]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

// SIMPLIFIED: use AndInv only: finds an instance in ~1s
run synthBoolNodeB for 0 but -1..0 Int, exactly 7 AndInv

// SIMPLIFIED: use And, Nand, and Not: finds an instance in ~3s
run synthBoolNodeB for 0 but -1..0 Int, exactly 5 Nand, exactly 4 Not, exactly 2 And

// ORIGINAL: only Not and And: times out after 12h
run synthBoolNodeB for 0 but -1..0 Int, exactly 9 Not, exactly 7 And
