--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
abstract sig Bool {}
one sig BoolTrue extends Bool {}
one sig BoolFalse extends Bool {}


abstract sig Var extends IntNode {}
one sig X1, X2, X3, X4, K extends Var {}

abstract sig IntLit extends IntNode {}
one sig Zero,One,Two,Three,Four extends IntLit{}



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
sig GT, LT extends BoolNode {
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

 all n: GT {
    eval[n] in Bool
    eval[n.left] > eval[n.right] implies
    eval[n] = BoolTrue else eval[n] = BoolFalse
  }

 all n: LT {
    eval[n] in Bool
    eval[n.left] < eval[n.right] implies
    eval[n] = BoolTrue else eval[n] = BoolFalse
  }

  eval[Zero] = 0
  eval[One] = 1
  eval[Two] = 2
  eval[Three] = 3
  eval[Four] = 4

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
  acyclic[condition+then+elsen+(GT <: left)+(LT <: left)+(GT <: right)+(LT <: right), Node]
}

pred spec[root: Node, eval: Node -> (Int + Bool)] {
  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4]) implies
    (eval[K] < eval[X1] implies eval[root] = 0)
  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4]) implies
    (eval[K] > eval[X4] implies eval[root] = 4)

  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4]) implies
    ((eval[K] > eval[X1] and eval[K] < eval[X2]) implies eval[root] = 1)
  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4]) implies
    ((eval[K] > eval[X2] and eval[K] < eval[X3]) implies eval[root] = 2)
  (eval[X1] < eval[X2] and eval[X2] < eval[X3] and eval[X3] < eval[X4]) implies
    ((eval[K] > eval[X3] and eval[K] < eval[X4]) implies eval[root] = 3)
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

run synth for 18 but -1..5 Int
run synth for 18 but -1..5 Int, exactly 5 ITE, exactly 3 LT
