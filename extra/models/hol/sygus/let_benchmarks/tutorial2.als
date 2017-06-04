module tutorial2

open util/integer as b

--------------------------------------------------------------------------------
-- AST Nodes
--------------------------------------------------------------------------------
abstract sig Node {}
abstract sig IntNode  extends Node {}
abstract sig IntVar extends IntNode {}

one sig X1, X2 extends IntVar {}

sig CInt in Int {}
  
one sig Y, Z extends IntNode {}
sig LetAxpb1, LetAxpb2 extends IntNode {
  yVal, zVal: one CInt
}
pred semanticsLetAxpb1[eval: Node->Int, n: LetAxpb1] { 
  eval[n] = plus[mul[n.yVal, eval[X1]], n.zVal]
}
pred semanticsLetAxpb2[eval: Node->Int, n: LetAxpb2] { 
  eval[n] = plus[mul[n.yVal, eval[X2]], n.zVal]
}

pred semantics[eval: Node->Int] {
  all n: Node | one eval[n]
  all n: LetAxpb1 | semanticsLetAxpb1[eval, n]
  all n: LetAxpb2 | semanticsLetAxpb2[eval, n]
}

pred synth[axpb1: LetAxpb1, axpb2: LetAxpb2] {
  all env: IntVar -> one Int {
    some eval: IntNode->Int when {
      env in eval
      semantics[eval]
    }{
      let x1=eval[X1], x2=eval[X2] |
        bveq[mul[eval[axpb1], eval[axpb2]],
             mul[plus[x1,x1], plus[x2, 5]]]
    }
  }
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run synth for 0 but 6 Int, exactly 1 LetAxpb1, exactly 1 LetAxpb2, {atoms: 0..15} CInt

