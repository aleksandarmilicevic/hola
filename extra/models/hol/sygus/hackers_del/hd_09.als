/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 *
 * Absolute value function
 */
module hd_09

open ../synth2[spec]

--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------
one sig X extends IntVar {}
one sig Lit0, Lit1, /*LitFFFFFFFF, */Lit0000001F extends IntLit {}
fact {
  IntLit<:val = Lit0->0 + Lit1->1 + Lit0000001F->0x0000001F
}

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> Int] {
  let x = eval[X] |
    bveq[hd09[x], eval[root]]
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd09[x: Int]: Int {
  bvsub[bvxor[x, bvsha[x, 0x0000001F]], 
        bvsha[x, 0x0000001F]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-09-d0-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(7)]} Int, 6 IntVarVal,
                            exactly 1 BvSub, exactly 1 BvXor, exactly 1 BvSha

// TOO SLOW
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-09-d1-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(7)]} Int, 6 IntVarVal,
                            exactly 1 BvAdd, exactly 1 BvSub, exactly 1 BvNot, exactly 1 BvNeg, exactly 1 BvAnd, exactly 1 BvOr, exactly 1 BvXor

// TOO SLOW
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-09-d5-prog.sl)
run synth for 0 but {bitwidth: 32, atoms: bw(7)} Int, 6 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp

