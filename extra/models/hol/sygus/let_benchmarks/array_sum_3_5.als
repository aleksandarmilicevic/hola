module array_sum_3_5

open array_sum[spec]

/**
 * https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/let-benchmarks/array_sum/array_sum_3_5.sl
 */

one sig X1, X2, X3 extends IntVar {}
one sig I0, I1, I2, I3 extends IntLit {}
fact {
  IntLit<:val = I0->0 + I1->1 + I2->2 + I3->3
}

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node->Int] {
  let x1=eval[X1], x2=eval[X2], x3=eval[X3], findSum=eval[root] |
    x1.plus[x2] > 5 implies findSum = x1.plus[x2]
    else x2.plus[x3] > 5 implies findSum = x2.plus[x3]
         else findSum = 0
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

// SAT (~123s)
run synth for 0 but -3..6 Int, {atoms: -3..3} IntVarVal, 
                exactly 2 Let, exactly 2 Z, exactly 2 ITE, exactly 3 Plus, exactly 2 GT
