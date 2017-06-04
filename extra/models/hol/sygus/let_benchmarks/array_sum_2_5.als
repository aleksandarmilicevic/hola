module array_sum_2_5

open array_sum[spec]

/**
 * https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/let-benchmarks/array_sum/array_sum_2_5.sl
 */

one sig X1, X2 extends IntVar {}
one sig I0, I1, I2 extends IntLit {}
fact {
  IntLit<:val = I0->0 + I1->1 + I2->2
}

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node->Int] {
  let x1=eval[X1], x2=eval[X2], findSum=eval[root] |
    x1.plus[x2] > 5 implies findSum = x1.plus[x2]
    else findSum = 0
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

// SAT: (~60s)
run synth for 0 but -3..6 Int, {atoms: -3..3} IntVarVal, 
                exactly 1 Let, exactly 1 Z, exactly 1 ITE, exactly 3 Plus, exactly 1 GT
