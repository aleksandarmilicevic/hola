/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 *
 * 
 */
module hd_19

open ../synth2[spec]

--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------
one sig X, K, M extends IntVar {}

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> Int] {
  let x = eval[X], k = eval[K], m = eval[M] |
    bveq[hd19[x, k, m], eval[root]]
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd19[x, k, m: Int]: Int {
  bvxor[x, bvxor[bvshl[bvand[bvxor[bvshr[x, k], x], m], k], bvand[bvxor[bvshr[x, k], x], m]]]
}


--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-19-d0-prog.sl)
run synthIntNodeI for 0 but 4 Int, 4 IntVarVal,
                            exactly 2 BvAnd, exactly 4 BvXor, exactly 1 BvShl, exactly 2 BvShr

// others TOO SLOW 
