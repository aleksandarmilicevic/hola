/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 *
 * Form a bit mask that identifies the rightmost one bit and trailing zeros 
 */
module hd_04

open hd[hd04]

one sig Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit1->1
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd04[x: Int]: Int {
  bvxor[x, bvsub[x, 1]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-04-d0-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 1 BvSub, exactly 1 BvXor

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-04-d1-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 1 BvSub, exactly 1 BvXor, exactly 1 BvNeg, exactly 1 BvAdd, exactly 1 BvOr, exactly 1 BvAnd


-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-04-d5-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp
