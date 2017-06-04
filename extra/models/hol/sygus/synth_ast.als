module synth_ast

open util/integer as b

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------
/* use the builtin Int and Bit */
sig IntVarVal in Int {}

--------------------------------------------------------------------------------
-- AST Nodes
--------------------------------------------------------------------------------
abstract sig Node {}
abstract sig BoolNode extends Node {}
abstract sig IntNode  extends Node {}

---------------------------------------------
-- BoolNodes
---------------------------------------------

abstract sig BoolVar extends BoolNode {}

abstract sig BoolLit extends BoolNode {
  val: one Bit
}

abstract sig IntComp  extends BoolNode {
  left, right: one IntNode
}
abstract sig BoolComp extends BoolNode {
  left, right: one BoolNode
}
abstract sig BoolInvComp extends BoolComp {
  invLhs, invRhs, invOut: one Bit
}

sig Equals, GTE, LTE, GT, LT extends IntComp {}
sig Nand, And, Nor, Or, Xor extends BoolComp {}
sig Not extends BoolNode {
  arg: one (BoolVar + And) // one BoolNode
}

sig AndInv, OrInv extends BoolInvComp {}

---------------------------------------------
-- IntNodes
---------------------------------------------

abstract sig IntVar extends IntNode {}
abstract sig IntLit extends IntNode {
  val: one Int
}

abstract sig BinaryIntOp extends IntNode {
  left, right: one IntNode
}
abstract sig UnaryIntOp extends IntNode {
  arg: one IntNode
}

sig BvShl, BvShr, BvSha, BvAnd, BvOr, BvXor extends BinaryIntOp {}
sig BvAdd, BvSub, BvMul, BvDiv extends BinaryIntOp {}
sig BvNot, BvNeg extends UnaryIntOp {}

sig ITE extends IntNode {
  condition: one BoolNode,
  then: one IntNode,
  elsen: one IntNode
}

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------
pred semantics[eval: Node -> (Int + Bit)] {
  all n: IntNode  | one eval[n] and eval[n] in Int
  all n: BoolNode | one eval[n] and eval[n] in Bit
  
  all n: ITE {
    /*eval[n] in Int
    eval[n.condition] in Bit
    eval[n.then] in Int
    eval[n.elsen] in Int*/
    eval[n.condition] = BitTrue implies
      eval[n.then] = eval[n] else eval[n.elsen] = eval[n]
  }

  // redundant stuff
  /*
  all n: IntComp  | eval[n.left] in Int and eval[n.right] in Int
  all n: BoolComp | eval[n.left] in Bit and eval[n.right] in Bit
  all n: Not      | eval[n.arg] in Bit
  all v: IntVar   | one eval[v] and eval[v] in Int
  all v: BoolVar  | one eval[v] and eval[v] in Bit
  */
  // ---------------

  all n: Equals   | eval[n.left] = eval[n.right] implies
                      eval[n] = BitTrue else eval[n] = BitFalse
  all n: GTE      | eval[n.left] >= eval[n.right] implies
                      eval[n] = BitTrue else eval[n] = BitFalse
  all n: LTE      | eval[n.left] <= eval[n.right] implies
                      eval[n] = BitTrue else eval[n] = BitFalse
  all n: GT       | eval[n.left] > eval[n.right] implies
                      eval[n] = BitTrue else eval[n] = BitFalse
  all n: LT       | eval[n.left] < eval[n.right] implies
                      eval[n] = BitTrue else eval[n] = BitFalse

  all n: And      | eval[n] = And[eval[n.left], eval[n.right]]
  all n: Nand     | eval[n] = Nand[eval[n.left], eval[n.right]]
  all n: Or       | eval[n] = Or [eval[n.left], eval[n.right]]
  all n: Nor      | eval[n] = Nor[eval[n.left], eval[n.right]]
  all n: Xor      | eval[n] = Xor[eval[n.left], eval[n.right]]
  all n: Not      | eval[n] = Not[eval[n.arg]]

  all n: BvShl    | eval[n] = bvshl[eval[n.left], eval[n.right]]
  all n: BvShr    | eval[n] = bvshr[eval[n.left], eval[n.right]]
  all n: BvSha    | eval[n] = bvsha[eval[n.left], eval[n.right]]
  all n: BvAnd    | eval[n] = bvand[eval[n.left], eval[n.right]]
  all n: BvOr     | eval[n] = bvor[eval[n.left], eval[n.right]]
  all n: BvXor    | eval[n] = bvxor[eval[n.left], eval[n.right]]
  all n: BvNot    | eval[n] = bvnot[eval[n.arg]]
  all n: BvNeg    | eval[n] = bvneg[eval[n.arg]]
  all n: BvAdd    | eval[n] = bvadd[eval[n.left], eval[n.right]]
  all n: BvMul    | eval[n] = bvmul[eval[n.left], eval[n.right]]
  all n: BvDiv    | eval[n] = bvdiv[eval[n.left], eval[n.right]]
  all n: BvSub    | eval[n] = bvsub[eval[n.left], eval[n.right]]

  all n: AndInv   | eval[n] = Xor[And[Xor[eval[n.left], n.invLhs], Xor[eval[n.right], n.invRhs]], n.invOut]
  all n: OrInv    | eval[n] = Xor[Or[Xor[eval[n.left], n.invLhs], Xor[eval[n.right], n.invRhs]], n.invOut]

  all i: IntLit   | eval[i] = i.val 
  all b: BoolLit  | eval[b] = b.val 
}

/*
-- way too slow and memory consuming
fun fEval[n: Node, env: (IntVar->Int + BoolVar->Bit)]: Int {
  (n in BvSub)          implies { bvsub[fEval[n.(BinaryIntOp<:left), env], fEval[n.(BinaryIntOp<:right), env]]
  } else (n in BvAdd)   implies { bvadd[fEval[n.(BinaryIntOp<:left), env], fEval[n.(BinaryIntOp<:right), env]]
  } else (n in BvMul)   implies { bvmul[fEval[n.(BinaryIntOp<:left), env], fEval[n.(BinaryIntOp<:right), env]]
  } else (n in BvXor)   implies { bvxor[fEval[n.(BinaryIntOp<:left), env], fEval[n.(BinaryIntOp<:right), env]]
  } else (n in BvOr)    implies { bvor[fEval[n.(BinaryIntOp<:left), env],  fEval[n.(BinaryIntOp<:right), env]]
  } else (n in BvAnd)   implies { bvand[fEval[n.(BinaryIntOp<:left), env], fEval[n.(BinaryIntOp<:right), env]]
  } else (n in BvSha)   implies { bvsha[fEval[n.(BinaryIntOp<:left), env], fEval[n.(BinaryIntOp<:right), env]] 
  } else (n in BvShr)   implies { bvshr[fEval[n.(BinaryIntOp<:left), env], fEval[n.(BinaryIntOp<:right), env]] 
  } else (n in BvShl)   implies { bvshl[fEval[n.(BinaryIntOp<:left), env], fEval[n.(BinaryIntOp<:right), env]]
  } else (n in BvNot)   implies { bvnot[fEval[n.(UnaryIntOp<:arg), env]] 
  } else (n in BvNeg)   implies { bvneg[fEval[n.(UnaryIntOp<:arg), env]] 
  } else (n in IntLit)  implies { n.(IntLit<:val)
  } else (n in BoolLit) implies { n.(BoolLit<:val) 
  } else (n in IntVar)  implies { env[n]
  } else (n in BoolVar) implies { env[n]
  // TODO: add other cases
  } else {
    0 // should never come down to this
  }
}
*/
--------------------------------------------------------------------------------
-- Utility predicates & functions
--------------------------------------------------------------------------------

fun binRels[]: Node -> Node {
  condition + then + elsen +
   IntComp<:left + BoolComp<:left + BinaryIntOp<:left + 
   IntComp<:right + BoolComp<:right + BinaryIntOp<:right +
   Not<:arg + UnaryIntOp<:arg
}

pred allVarsReachableFrom[root: Node] {
  all v: BoolVar + IntVar |
    v in root.^(binRels)
}

pred acyclic[r: univ->univ, s: set univ] {
  all x: s | x !in x.^r
}

--------------------------------------------------------------------------------
-- Facts
--------------------------------------------------------------------------------

fact {
  acyclic[binRels, Node]
}
