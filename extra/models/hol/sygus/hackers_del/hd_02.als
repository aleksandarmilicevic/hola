/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 *
 * Test if unsigned int is of form 2^n - 1
 */

module hd_02

open hd[hd02]

one sig Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit1->1
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd02[x: Int]: Int {
  bvand[x, bvadd[x, 1]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-02-d0-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 1 BvAnd, exactly 1 BvAdd

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-02-d1-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal, 
                            exactly 1 BvAnd, exactly 1 BvSub, exactly 1 BvOr, exactly 1 BvAdd, exactly 1 BvXor


-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-02-d5-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp
