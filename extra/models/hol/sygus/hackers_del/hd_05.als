/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 *
 * Right propagate the rightmost one bit
 */
module hd_05

open hd[hd05]

one sig Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit1->1
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd05[x: Int]: Int {
  bvor[x, bvsub[x, 1]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-05-d0-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 1 BvSub, exactly 1 BvOr

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-05-d1-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 1 BvSub, exactly 1 BvOr, exactly 1 BvNeg, exactly 1 BvAdd, exactly 1 BvOr, exactly 1 BvAnd


-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-05-d5-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp
