module zmorton_d5

open ../synth2[spec]

one sig I, J extends IntVar {}
one sig Hex1, Hex2, HexFFFF, Hex33333333, Hex55555555 extends IntLit {}
//one sig Hex1, Hex2, HexFFFF extends IntLit {}

fact {
  IntLit<:val = Hex1->1 + Hex2->2 + HexFFFF->0xFFFF + Hex33333333->0x33333333 + Hex55555555->0x55555555
}

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/bitvector-benchmarks/parity-AIG-d0.sl)
--------------------------------------------------------------------------------

/*
pred spec[root: Node, eval: Node -> (Int + Bit)] { 
  eval[root] = bvor[bvnot[eval[I]], bvnot[eval[J]]]
}

run synthIntNodeI for 0 but {bitwidth: 32, atoms: -8..7} Int, exactly 1 BvAnd, exactly 1 BvNot
*/
fun zmorton_spec[i, j: Int]: Int {
  bvor[bvand[0x55555555, bvor[bvand[0x33333333, bvor[bvshl[bvand[0xFFFF, j], 2], bvand[0xFFFF, j]]], 
                              bvshl[bvand[0x33333333, bvor[bvshl[bvand[0xFFFF, j], 2], bvand[0xFFFF, j]]], 1]]], 
       bvshl[bvand[0x55555555, bvor[bvshl[bvand[0x33333333, bvor[bvshl[bvand[0xFFFF, i], 2], bvand[0xFFFF, i]]], 1], 
                                    bvand[0x33333333, bvor[bvshl[bvand[0xFFFF, i], 2], bvand[0xFFFF, i]]]]], 1]]
}

fun zmorton_impl[root: Node, eval: Node -> (Int + Bit)]: Int {
  eval[root]
}

pred spec[root: Node, eval: Node -> (Int + Bit)] {
  let i = eval[I], j = eval[J] |
    bveq[zmorton_spec[i, j], zmorton_impl[root, eval]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(4)]} Int, 3 IntVarVal,
                            exactly 14 BvAnd, exactly 7 BvOr, exactly 7 BvShl

