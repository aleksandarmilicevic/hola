module sketch_tutorial3

open ../synth2[spec]

one sig X1, X2, X3 extends IntVar {}

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/sketch-benchmarks/tutorial3.sl)
--------------------------------------------------------------------------------

pred spec[root: Node, eval: Node -> Int] {
  let x1=eval[X1], x2=eval[X2], x3=eval[X3] |
    // eval[root] = (x1+x1) * (x2-x3)
    bveq[eval[root], 
         mul[plus[x1, x1], 
             minus[x2, x3]]]
}    

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run synthIntNodeI for 0 but 4 Int, exactly 1 BvAdd, exactly 1 BvSub, exactly 1 BvMul

