/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 * 
 * Test if (nlz x) <= (nlz y) where nlz is the number of leading zeros
 */
module hd_12

open hdXY[hd12]

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd12[x, y: Int]: Bit {
  bvand[x, bvnot[y]] <= y implies BitTrue else BitFalse
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-12-d0-prog.sl)
run synthBoolNodeI for 0 but {bitwidth: 32, atoms: bw(4)} Int, 4 IntVarVal,
                            exactly 1 LTE, exactly 1 BvAnd, exactly 1 BvNot

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-12-d1-prog.sl)
run synthBoolNodeI for 0 but {bitwidth: 32, atoms: bw(4)} Int, 4 IntVarVal,
                            exactly 1 LTE, exactly 1 BvAdd, exactly 1 BvSub, exactly 1 BvNot, exactly 1 BvNeg, exactly 1 BvAnd, exactly 1 BvOr, exactly 1 BvXor


-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-12-d5-prog.sl)
run synthBoolNodeI for 0 but {bitwidth: 32, atoms: bw(4)} Int, 4 IntVarVal,
                            exactly 1 IntComp, exactly 3 BinaryIntOp, exactly 2 UnaryIntOp
