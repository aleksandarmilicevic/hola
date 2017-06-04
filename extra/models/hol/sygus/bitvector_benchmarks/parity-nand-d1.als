module parity_nand_d1

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
    parity[a, b, c, d] = eval[root]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

// ORIGINAL: use only Nand
//  * with partial ordering: finds an instance in ~30s
//  * without partial ordering: t/o 
run synthBoolNodeB for 0 but -1..0 Int, exactly 23 Nand
