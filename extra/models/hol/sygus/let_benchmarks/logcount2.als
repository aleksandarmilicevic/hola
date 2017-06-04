module logcount2

open util/integer as b

/**
 * https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/let-benchmarks/logcount2.sl
 */

--------------------------------------------------------------------------------
-- AST Nodes
--------------------------------------------------------------------------------
abstract sig Node {}
abstract sig IntNode  extends Node {}
abstract sig IntVar extends IntNode {}

one sig X1 extends IntVar {}

sig ConstBV in Int {}
sig ShiftConst in Int {}
  
sig Let extends IntNode {
  tmp: one Node,
  m, o: one ConstBV,
  n: one ShiftConst
}
pred semanticsLet[eval: Node->Int, l: Let] { 
  eval[l] = bvadd[bvand[eval[l.tmp], l.m],
                  bvand[bvshr[eval[l.tmp], l.n], l.o]]
}

pred semantics[eval: Node->Int] {
  all n: Node | one eval[n]
  all n: Let | semanticsLet[eval, n]
}

pred acyclic[r: univ->univ, s: set univ] { all x: s | x !in x.^r }

fact {
  acyclic[tmp, Node]
}

fun sumBits[x: Int]: Int {
  bvadd[bvadd[bvadd[bvadd[bvadd[bvadd[bvadd[bveq[bvand[x, 0x01], 0x01] implies 0x01 else 0x00, 
                                          bveq[bvand[x, 0x02], 0x02] implies 0x01 else 0x00], 
                                    bveq[bvand[x, 0x04], 0x04] implies 0x01 else 0x00], 
                              bveq[bvand[x, 0x08], 0x08] implies 0x01 else 0x00], 
                        bveq[bvand[x, 0x10], 0x10] implies 0x01 else 0x00], 
                  bveq[bvand[x, 0x20], 0x20] implies 0x01 else 0x00], 
            bveq[bvand[x, 0x40], 0x40] implies 0x01 else 0x00],
      bveq[bvand[x, 0x80], 0x80] implies 0x01 else 0x00]
}

pred synth[countSketch: Node] {
  all env: IntVar -> one Int {
    some eval: IntNode->Int when {
      env in eval
      semantics[eval]
    }{
      let x1=eval[X1] |
         sumBits[x1] = eval[countSketch]
    }
  }
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

// only necessary constants --> SAT (~30s)
run synth for 0 but 8 Int, {bitwidth: 8, atoms: [0x00, 0x55, 0x33, 0x0F, 0x01, 0x02, 0x04]} ConstBV, 
                           {bitwidth: 8, atoms: [0x00, 0x55, 0x33, 0x0F, 0x01, 0x02, 0x04]} ShiftConst,   
                           exactly 3 Let

// larger scope for constants --> SAT
run synth for 0 but 8 Int, {bitwidth: 8, atoms: 1..100} ConstBV, {atoms: 0..7} ShiftConst, exactly 3 Let

// full scope for constants --> SAT
run synth for 0 but 8 Int, {bitwidth: 8, atoms: bw(8)} ConstBV, {atoms: 0..7} ShiftConst, exactly 3 Let

// with constants from https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/let-benchmarks/logcount2.sl 
// --> UNSAT
run synth for 0 but 8 Int, {bitwidth: 8, atoms: [0x00, 0xAA, 0xCC, 0xE0, 0x01, 0x02, 0x04]} ConstBV,
                           {bitwidth: 8, atoms: [0x00, 0xAA, 0xCC, 0xE0, 0x01, 0x02, 0x04]} ShiftConst, exactly 3 Let


// with constants from https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/let-benchmarks/logcount2-d1.sl 
// --> UNSAT
run synth for 0 but 8 Int, {bitwidth: 8, atoms: [0x00, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0xA0, 0xB0, 0xC0, 0xD0, 0xE0, 0xF0, 0x01, 0x02, 0x04]} ConstBV, 
                           {bitwidth: 8, atoms: [0x00, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0xA0, 0xB0, 0xC0, 0xD0, 0xE0, 0xF0, 0x01, 0x02, 0x04]} ShiftConst,
                           exactly 3 Let expect 0

// full scope for constants --> SAT
// (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/let-benchmarks/logcount2-d5.sl )
run synth for 0 but 8 Int, 8 ConstBV, 8 ShiftConst, exactly 3 Let
