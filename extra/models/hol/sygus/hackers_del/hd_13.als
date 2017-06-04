/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 * 
 * sign function
 */
module hd_13

open hdXY[hd13]

one sig Lit1F extends IntLit {}
fact {
  IntLit<:val = Lit1F->0x0000001F
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd13[x, y: Int]: Bit {
  bvor[bvsha[x, 0x1F], 
       bvshr[bvnot[x], 0x1F]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-13-d0-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: bw(7)} Int, 7 IntVarVal,
                            exactly 1 BvOr, exactly 1 BvSha, exactly 1 BvNot, exactly 1 BvShr

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-13-d1-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: bw(7)} Int, 7 IntVarVal,
                            exactly 1 BvAdd, exactly 1 BvSub, exactly 1 BvNot, exactly 1 BvNeg, exactly 1 BvAnd, exactly 1 BvOr, exactly 1 BvXor


-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-13-d5-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: bw(7)} Int, 7 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp
