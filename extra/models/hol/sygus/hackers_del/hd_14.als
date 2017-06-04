/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 * 
 * floor of average of two integers
 */
module hd_14

open hdXY[hd14]

one sig Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit1->1
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd14[x, y: Int]: Int {
  bvadd[bvand[x, y], 
        bvshr[bvxor[x, y], 1]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-14-d0-prog.sl)
run synthIntNodeI for 0 but 5 Int, 5 IntVarVal,
                            exactly 1 BvXor, exactly 1 BvShr, exactly 1 BvAnd, exactly 1 BvAdd

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-14-d1-prog.sl)
run synthIntNodeI for 0 but 4 Int, 4 IntVarVal,
                            exactly 1 BvAdd, exactly 1 BvSub, exactly 1 BvNot, exactly 1 BvNeg, exactly 1 BvAnd, exactly 1 BvOr, exactly 1 BvXor, exactly 1 BvShr, exactly 1 BvSha


-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-14-d5-prog.sl)
run synthIntNodeI for 0 but 4 Int, 4 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp
