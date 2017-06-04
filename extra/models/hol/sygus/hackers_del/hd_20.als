/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 *
 * next higher unsigned number with same number of 1 bits
 */
module hd_20

open hd[hd20]

one sig Lit2 extends IntLit {}
fact {
  IntLit<:val = Lit->2
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd20[x: Int]: Int {
  bvor[bvadd[x, bvand[bvneg[x], x]], bvdiv[bvshr[bvxor[x, bvand[bvneg[x], x]], 2], bvand[bvneg[x], x]]]
}


--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-19-d0-prog.sl)
run synthIntNodeI for 0 but 4 Int, 4 IntVarVal,
                        exactly 1 BvAnd, exactly 1 BvXor, exactly 1 BvOr, exactly 1 BvAdd, exactly 1 BvShr, exactly 1 BvNeg, exactly 1 BvDiv

// others TOO SLOW 
