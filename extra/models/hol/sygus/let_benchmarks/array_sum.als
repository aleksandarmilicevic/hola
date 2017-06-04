module array_sum<spec>

open util/integer as b

/**
 * Common model for all array_sum benchmarks
 */

--------------------------------------------------------------------------------
-- AST Nodes
--------------------------------------------------------------------------------
abstract sig Node {}
abstract sig IntNode   extends Node {}
abstract sig BoolNode  extends Node {}
abstract sig IntVar    extends IntNode {}
abstract sig LetIntVar extends IntNode {}
abstract sig IntLit    extends IntNode {
  val: one Int
}
abstract sig IntOp extends IntNode {
  left, right: one IntNode
}
abstract sig IntComp extends BoolNode {
  left: one IntNode,
  right: one IntNode
}

sig IntVarVal in Int {}

sig Z extends LetIntVar {} // let variable
sig Let extends IntNode {
  zVar: one Z,
  zExpr: one IntNode,
  body: one IntNode
} {
  this.@zVar !in this.@zExpr.*(children)
}
fact {
  all z: Z | one l: Let | l.zVar = z
  no disj l1, l2: Let | l1.zVar = l2.zVar
}

sig Plus extends IntOp {}
sig LT, LTE, GT, GTE extends IntComp {}

sig ITE extends IntNode {
  cond: one BoolNode,
  then: one IntNode, 
  elsen: one IntNode
}

--------------------------------------------------------------------------------
-- Helpers/Facts
--------------------------------------------------------------------------------

pred acyclic[r: univ->univ, s: set univ] { all x: s | x !in x.^r }
fun children[]: Node->Node {
  cond + then + elsen + zExpr + body +
  IntOp<:left + IntOp<:right + IntComp<:left + IntComp<:right
}
fun parents[]: Node->Node { ~children }
fact {
  acyclic[children, Node]
  all z: LetIntVar | all p: z.parents | z in p.*parents.zVar
  all n: Let + IntComp + ITE + IntOp | lone n.parents
  /*all n: Node - LetIntVar |
    (n.^children & LetIntVar) in (n.*parents.zVar)*/
}

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------

pred Plus.sem[eval: Node->Int] { eval[this] = plus[eval[left], eval[right]] }
pred Let.sem[eval: Node->Int]  { eval[this.@zVar] = eval[this.@zExpr] && eval[this] = eval[body] }
pred ITE.sem[eval: Node->Int]  { eval[this] = (eval[cond] = BitTrue implies eval[then] else eval[elsen]) }
pred LT.sem[eval: Node->Int]   { eval[this] = (eval[left] < eval[right] implies BitTrue else BitFalse) }
pred GT.sem[eval: Node->Int]   { eval[this] = (eval[left] > eval[right] implies BitTrue else BitFalse) }
pred LTE.sem[eval: Node->Int]  { eval[this] = (eval[left] <= eval[right] implies BitTrue else BitFalse) }
pred GTE.sem[eval: Node->Int]  { eval[this] = (eval[left] >= eval[right] implies BitTrue else BitFalse) }

pred semantics[eval: IntNode->Int + BoolNode->Bit] {
  --all n: Node     | one eval[n]
  all n: IntNode  | one eval[n] && eval[n] in Int
  all n: BoolNode | one eval[n] && eval[n] in Bit
  all n: IntLit   | eval[n] = n.val 

  all n: Plus     | n.sem[eval]
  all n: Let      | n.sem[eval]
  all n: ITE      | n.sem[eval]
  all n: LT       | n.sem[eval]
  all n: GT       | n.sem[eval]
  all n: LTE      | n.sem[eval]
  all n: GTE      | n.sem[eval]
}

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

pred synth[root: IntNode] {
  no root.parents
  all env: IntVar -> one IntVarVal {
    some eval: IntNode->Int + BoolNode->Bit when {
      env in eval
      semantics[eval]
    }{
      spec[root, eval]
    }
  }
}
