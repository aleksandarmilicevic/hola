module sketch_tutorial2

open ../synth2[spec]

one sig X1, X2 extends IntVar {}
one sig Let1Y, Let1Z, Let2Y, Let2Z extends IntLit {} {
  val >= 0
}

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/sketch-benchmarks/tutorial2.sl)
--------------------------------------------------------------------------------

fun axpb1[x, y, z: Int]: Int { plus[mul[y, x], z] }
fun axpb2[x, y, z: Int]: Int { plus[mul[y, x], z] }

pred spec[root: Node, eval: Node -> Int] {
  let x1=eval[X1], x2=eval[X2], l1y=eval[Let1Y], l1z=eval[Let1Z], l2y=eval[Let2Y], l2z=eval[Let2Z] |
    // (?*x1 + ?) * (?*x2 + ?) = 2x1 * (x2 + 5)
    bveq[mul[axpb1[x1, l1y, l1z],
             axpb2[x2, l2y, l2z]],
         mul[plus[x1,x1], plus[x2, 5]]]
}    

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run synthIntNodeI for 0 but 5 Int

