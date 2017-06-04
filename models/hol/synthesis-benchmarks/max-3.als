
--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
abstract sig Bool {}
one sig BoolTrue extends Bool {}
one sig BoolFalse extends Bool {}


abstract sig Var extends IntNode {}
one sig X, Y, Z extends Var {}


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
    eval[n.condition] in Bool
    eval[n.then] in Int
    eval[n.elsen] in Int
    eval[n.condition] = BoolTrue implies
      eval[n.then] = eval[n] else eval[n.elsen] = eval[n]
  }

 all n: GTE {
    eval[n] in Bool
    eval[n.left] in Int
    eval[n.right] in Int
    eval[n.left] >= eval[n.right] implies
      eval[n] = BoolTrue else eval[n] = BoolFalse
  }

  all v: Var | one eval[v] and eval[v] in Int
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
    eval[root] >= eval[Z]

    eval[root] = eval[X] or
      eval[root] = eval[Y] or
        eval[root] = eval[Z]
}

pred program[root: Node] {
  root in ITE

  root.condition in GTE
  root.condition.left = X
  root.condition.right = Y

  root.then in ITE

  root.then.condition in GTE
  root.then.condition.left = X
  root.then.condition.right = Z

  root.then.then = X
  root.then.elsen = Z

  root.elsen in ITE

  root.elsen.condition in GTE
  root.elsen.condition.left = Y
  root.elsen.condition.right = Z

  root.elsen.then = Y
  root.elsen.elsen = Z
}

pred synth[root: IntNode] {
  all env: Var -> one Int {
    some eval: Node -> one (Int+Bool) when env in eval && semantics[eval] |
      spec[root, eval]
  }
}


pred synthOld[root: IntNode] {
  all eval: Node -> one (Int+Bool) when semantics[eval] |
    spec[root, eval]
}

run synth for 9 but 2 Int
run synth for 9 but 2 Int, exactly 2 ITE, exactly 2 GTE

run synthOld for 9 but 2 Int
