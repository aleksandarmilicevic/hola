
--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
abstract sig Bool {}
one sig BoolTrue extends Bool {}
one sig BoolFalse extends Bool {}


abstract sig Var extends IntNode {}
one sig X, Y extends Var {}


--------------------------------------------------------------------------------
-- AST Nodes
--------------------------------------------------------------------------------
abstract sig Node {}

abstract sig IntNode extends Node {}

sig ITE extends IntNode {
  condition: BoolNode,
  then: IntNode,
  elsen: IntNode
}

abstract sig BoolNode extends Node {}
sig GTE extends BoolNode {
  left, right: IntNode
}

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------
pred semantics[eval: Node -> (Int + Bool)] {
  all n: ITE {
    eval[n] in Int
    eval[n.condition] = BoolTrue implies
      eval[n.then] = eval[n] else eval[n.elsen] = eval[n]
  }

 all n: GTE {
    eval[n] in Bool
    eval[n.left] >= eval[n.right] implies
      eval[n] = BoolTrue else eval[n] = BoolFalse
  }
}

--------------------------------------------------------------------------------
-- Property
--------------------------------------------------------------------------------
pred irreflexive [r: univ -> univ] {no iden & r}

pred acyclic[r: univ->univ, s: set univ] {
  all x: s | x !in x.^r
}

fact {
  acyclic[condition+then+elsen+left+right, Node]
}

pred spec[root: Node, eval: Node -> (Int + Bool)] {
    eval[root] >= eval[X]
    eval[root] >= eval[Y]

    eval[root] = eval[X] or eval[root] = eval[Y]
}

pred synth[root: IntNode] {
  all env: Var -> one Int {
    some eval: Node -> one (Int+Bool) |{
      env in eval
      semantics[eval]
    } |{
      spec[root, eval]
    }
  }
}

run synth for 15 but 2 int
