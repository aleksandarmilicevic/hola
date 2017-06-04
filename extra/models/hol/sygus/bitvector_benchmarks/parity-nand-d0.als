module parity_nand_d0

open parity[spec]

one sig LitTrue, LitFalse extends BoolLit {}
fact {
  BoolLit<:val = LitTrue -> BitTrue + LitFalse -> BitFalse
}

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/bitvector-benchmarks/parity-AIG-d0.sl)
--------------------------------------------------------------------------------

pred spec[root: Node, eval: Node -> (Int + Bit)] {
  let a = eval[A], b = eval[B], c = eval[C], d = eval[D] |
    parity[a, b, c, d] = Not[And[eval[root],
                                 Not[And[Not[And[Not[And[d, Not[And[d, a]]]], 
                                                 Not[And[a, Not[And[d, a]]]]]], 
                                         Not[And[Not[And[Not[And[BitTrue, c]], 
                                                         Not[And[BitTrue, b]]]], 
                                                 Not[And[b, c]]]]]]]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

// ORIGINAL: use only Nand:
//  * with partial ordering: finds an instance in ~1.5s
//  * without partial ordering: finds an instance in ~8s
run synthBoolNodeB for 0 but -1..0 Int, exactly 11 Nand

