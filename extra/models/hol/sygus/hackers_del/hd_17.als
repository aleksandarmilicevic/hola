/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 * 
 * turn off the rightmost string of contiguous ones
 */
module hd_17

open hd[hd17]

one sig Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit1->1
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd17[x: Int]: Int {
  bvand[bvadd[bvor[x, bvsub[x, 1]], 1], x]
}

fact {
  BvAnd.left = BvAdd
  BvAnd.right = X
  BvAdd.left = BvOr
  BvAdd.right = Lit1
  BvOr.left = X
  BvOr.right = BvSub
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-17-d0-prog.sl)
run synthIntNodeI for 0 but 5 Int, 5 IntVarVal,
                            exactly 1 BvAnd, exactly 1 BvAdd, exactly 1 BvSub, exactly 1 BvOr

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-17-d1-prog.sl)
run synthIntNodeI for 0 but 5 Int, 5 IntVarVal,
                            exactly 1 BvAdd, exactly 1 BvSub, exactly 1 BvNot, exactly 1 BvNeg, exactly 1 BvAnd, exactly 1 BvOr, exactly 1 BvXor

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-17-d5-prog.sl)
run synthIntNodeI for 0 but 5 Int, 5 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp

