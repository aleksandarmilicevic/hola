/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 *
 * Isolate the right most one bit
 */

module hd_03

open hd[hd03]

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd03[x: Int]: Int {
  bvand[x, bvneg[x]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-03-d0-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 1 BvAnd, exactly 1 BvNeg

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-03-d1-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 1 BvAnd, exactly 1 BvNeg, exactly 1 BvOr, exactly 1 BvAdd, exactly 1 BvSub


-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-03-d5-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp
