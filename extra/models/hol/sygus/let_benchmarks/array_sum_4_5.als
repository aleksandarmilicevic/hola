module array_sum_4_5

open array_sum[spec]

/**
 * https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/let-benchmarks/array_sum_4_5.sl
 */

one sig X1, X2, X3, X4 extends IntVar {}
one sig I0, I5 extends IntLit {}
fact {
  IntLit<:val = I0->0 + I5->5 //+ I1->1 + I2->2 + I3->3 + I4->4 
}

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

pred spec[root: Node, eval: Node->Int] {
  let x1=eval[X1], x2=eval[X2], x3=eval[X3], x4=eval[X4], findSum=eval[root] |
    x1.plus[x2] > 5 implies findSum = x1.plus[x2]
    else x2.plus[x3] > 5 implies findSum = x2.plus[x3]
         else x3.plus[x4] > 5 implies findSum = x3.plus[x4]
              else findSum = 0
}

--------------------------------------------------------------------------------
-- Solution
--------------------------------------------------------------------------------
/*
one sig Let0, Let1, Let2 extends Let {}
one sig Z0, Z1, Z2 extends Z {}
one sig GT0, GT1, GT2 extends GT {}
one sig ITE0, ITE1, ITE2 extends ITE {}
one sig P0, P1, P2 extends Plus {}

fact {
  Let<:zVar = Let0->Z0 + Let1->Z1 + Let2->Z2
  Let<:zExpr = Let0->P0 + Let1->P1 + Let2->P2
  Let<:body = Let0->ITE0 + Let1->ITE1 + Let2->ITE2

  IntOp<:left = P0->X1 + P1->X2 + P2->X3
  IntOp<:right = P0->X2 + P1->X3 + P2->X4

  IntComp<:left = GT0->Z0 + GT1->Z1 + GT2->Z2
  IntComp<:right = GT0->I5 + GT1->I5 + GT2->I5

  ITE<:cond  = ITE0->GT0 + ITE1->GT1 + ITE2->GT2
  ITE<:then  = ITE0->Z0 + ITE1->Z1 + ITE2->Z2
  ITE<:elsen = ITE0->Let1 + ITE1->Let2 + ITE2->I0
}*/

one sig Let0, Let1, Let2 extends Let {}
one sig Z0, Z1, Z2 extends Z {}
one sig GT0, GT1, GT2 extends GT {}
one sig ITE0, ITE1, ITE2 extends ITE {}
one sig P0, P1, P2 extends Plus {}

fact {
  Let<:zVar = Let0->Z0 + Let1->Z1 + Let2->Z2
  ITE<:cond  = ITE0->GT0 + ITE1->GT1 + ITE2->GT2

  (Let1+Let2) !in Let0.^children
  Let2 !in Let1.^children 
  (ITE1+ITE2) !in ITE0.^children
  ITE2 !in ITE1.^children
    
}


--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
// SAT (~4500s)
run synth for 0 but -3..6 Int, {atoms: -3..3} IntVarVal, 
                exactly 3 Let, exactly 3 Z, exactly 3 ITE, exactly 3 Plus, exactly 3 GT
