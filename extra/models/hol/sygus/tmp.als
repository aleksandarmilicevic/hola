module ParityNandD1

one sig A extends BoolVar {}

one sig B extends BoolVar {}

one sig C extends BoolVar {}

one sig D extends BoolVar {}

one sig LitTrue extends BoolLit {}

one sig LitFalse extends BoolLit {}

fun parity[a: Bit, b: Bit, c: Bit, d: Bit]: Bit {
  
    Xor[Not[Xor[a, b]], Not[Xor[c, d]]]
}

pred spec[root: Node, eval: Node -> (Int + Bit)] {
  
    let a = eval[A], b = eval[B], c = eval[C], d = eval[D] |
      parity[a, b, c, d] = eval[root]
}

fact bool_lit_vals {
  boolval = LitTrue -> -1 + LitFalse -> 0
}
// =============================================
// == module Synth2

abstract sig Node  {}

abstract sig IntNode extends Node {}

sig ITE extends IntNode {
  condition: one BoolNode,
  then: one IntNode,
  elsen: one IntNode
}

abstract sig BoolNode extends Node {}

abstract sig IntCmp extends BoolNode {
  left: one IntNode,
  right: one IntNode
}

abstract sig BoolCmp extends BoolNode {
  left: one BoolNode,
  right: one BoolNode
}

abstract sig BoolInvCmp extends BoolCmp {
  invLhs: one Bit,
  invRhs: one Bit,
  invOut: one Bit
}

sig Equals extends IntCmp {}

sig GT extends IntCmp {}

sig GTE extends IntCmp {}

sig LT extends IntCmp {}

sig LTE extends IntCmp {}

sig And extends BoolCmp {}

sig Nand extends BoolCmp {}

sig Or extends BoolCmp {}

sig Nor extends BoolCmp {}

sig Xor extends BoolCmp {}

sig AndInv extends BoolInvCmp {}

sig OrInv extends BoolInvCmp {}

sig Not extends BoolNode {
  arg: one BoolNode
}

abstract sig IntVar extends IntNode {}

abstract sig IntLit extends IntNode {
  intval: one Int
}

abstract sig BoolVar extends BoolNode {}

abstract sig BoolLit extends BoolNode {
  boolval: one Bit
}

pred iteSemantics[eval: Node -> (Int + Bit)] {
  all n: ITE {
    eval[n.condition] = -1 implies {
      eval[n.then] = eval[n]
    } else {
      eval[n.elsen] = eval[n]
    }
  }
}

pred gteSemantics[eval: Node -> (Int + Bit)] {
  all n: GTE {
    eval[n.left] >= eval[n.right] implies {
      eval[n] = -1
    } else {
      eval[n] = 0
    }
  }
}

pred lteSemantics[eval: Node -> (Int + Bit)] {
  all n: LTE {
    eval[n.left] <= eval[n.right] implies {
      eval[n] = -1
    } else {
      eval[n] = 0
    }
  }
}

pred gtSemantics[eval: Node -> (Int + Bit)] {
  all n: GT {
    eval[n.left] > eval[n.right] implies {
      eval[n] = -1
    } else {
      eval[n] = 0
    }
  }
}

pred ltSemantics[eval: Node -> (Int + Bit)] {
  all n: LT {
    eval[n.left] < eval[n.right] implies {
      eval[n] = -1
    } else {
      eval[n] = 0
    }
  }
}

pred eqSemantics[eval: Node -> (Int + Bit)] {
  all n: Equals {
    eval[n.left] = eval[n.right] implies {
      eval[n] = -1
    } else {
      eval[n] = 0
    }
  }
}

pred andSemantics[eval: Node -> (Int + Bit)] {
  all n: And {
    eval[n] = eval[n.left].And[eval[n.right]]
  }
}

pred nandSemantics[eval: Node -> (Int + Bit)] {
  all n: Nand {
    eval[n] = eval[n.left].Nand[eval[n.right]]
  }
}

pred orSemantics[eval: Node -> (Int + Bit)] {
  all n: Or {
    eval[n] = eval[n.left].Or[eval[n.right]]
  }
}

pred norSemantics[eval: Node -> (Int + Bit)] {
  all n: Nor {
    eval[n] = eval[n.left].Nor[eval[n.right]]
  }
}

pred xorSemantics[eval: Node -> (Int + Bit)] {
  all n: Xor {
    eval[n] = eval[n.left].Xor[eval[n.right]]
  }
}

pred notSemantics[eval: Node -> (Int + Bit)] {
  all n: Not {
    eval[n] = eval[n.arg].Not
  }
}

pred andInvSemantics[eval: Node -> (Int + Bit)] {
  all n: AndInv {
    eval[n] = eval[n.left].Xor[n.invLhs].And[eval[n.right].Xor[n.invRhs]].Xor[n.invOut]
  }
}

pred orInvSemantics[eval: Node -> (Int + Bit)] {
  all n: OrInv {
    eval[n] = eval[n.left].Xor[n.invLhs].Or[eval[n.right].Xor[n.invRhs]].Xor[n.invOut]
  }
}

pred intLitSemantics[eval: Node -> (Int + Bit)] {
  all i: IntLit {
    eval[i] = i.intval
  }
}

pred boolLitSemantics[eval: Node -> (Int + Bit)] {
  all i: BoolLit {
    eval[i] = i.boolval
  }
}

pred semantics[eval: Node -> (Int + Bit)] {
  all bnode: BoolNode {
    one eval[bnode]
    eval[bnode] in Bit
  }
  all inode: IntNode {
    one eval[inode]
    eval[inode] in Int
  }
  iteSemantics[eval]
  gteSemantics[eval]
  lteSemantics[eval]
  gtSemantics[eval]
  ltSemantics[eval]
  eqSemantics[eval]
  andSemantics[eval]
  nandSemantics[eval]
  orSemantics[eval]
  norSemantics[eval]
  xorSemantics[eval]
  andInvSemantics[eval]
  orInvSemantics[eval]
  notSemantics[eval]
  intLitSemantics[eval]
  boolLitSemantics[eval]
}

pred irreflexive[r: univ -> univ] {
  no iden & r
}

pred acyclic[r: univ -> univ, s: set univ] {
  all x: s {
    ! x in x.^r
  }
}

pred allVarsReachableFrom[root: Node] {
  all v: BoolVar + IntVar {
    v in root.^(condition + then + elsen + arg + IntCmp <: left + IntCmp <: right + BoolCmp <: left + BoolCmp <: right)
  }
}

pred synth[root: Node] {
  
    allVarsReachableFrom[root]
    //all envI: IntVar -> one Int {
    all envB: BoolVar -> one Bit {
      some eval: IntNode->Int + BoolNode->Bit |{
        //envI in eval
        envB in eval
        semantics[eval]
      } |{
        spec[root, eval]
      }
    }
    //}
}

pred synthBoolNode[root: BoolNode] {
  synth[root]
}

pred synthIntNode[root: IntNode] {
  synth[root]
}

fact fact_0 {
  acyclic[condition + then + elsen + arg + IntCmp <: left + IntCmp <: right + BoolCmp <: left + BoolCmp <: right, Node]
}
// -------------------------------------------

run synthBoolNode for 3 but -1..0 Int, exactly 23 Nand, 0 AndInv, 0 Not, 0 And, 0 ITE, 0 IntVar, 0 IntLit, 0 Nor, 0 OrInv, 0 GT, 0 GTE, 0 LT, 0 LTE, 0 Equals, 0 Or

