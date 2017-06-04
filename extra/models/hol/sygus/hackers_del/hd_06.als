/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 *
 * Turn on the right most 0 bit
 */
module hd_06

open hd[hd06]

one sig Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit1->1
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd06[x: Int]: Int {
  bvor[x, bvadd[x, 1]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-06-d0-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, of_bw: 4, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 1 BvAdd, exactly 1 BvOr

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-06-d1-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, of_bw: 4, atoms: bw(5)} Int, 4 IntVarVal,
                            exactly 1 BvAdd, exactly 1 BvOr, exactly 1 BvNeg, exactly 1 BvSub, exactly 1 BvOr, exactly 1 BvAnd


-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-06-d5-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: bw(5)} Int, 4 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp
