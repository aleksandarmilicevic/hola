--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
abstract sig Bool {}
one sig BoolTrue extends Bool {}
one sig BoolFalse extends Bool {}


abstract sig Var extends IntNode {}
one sig X1, X2, K extends Var {}

abstract sig IntLit extends IntNode {}
one sig Zero extends IntLit {}
one sig One extends IntLit {}
one sig Two extends IntLit {}


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
  eval[X1] < eval[X2] implies (eval[K] < eval[X1] implies eval[root] = 0)
  eval[X1] < eval[X2] implies (eval[K] > eval[X2] implies eval[root] = 2)
  eval[X1] < eval[X2] implies ((eval[K] > eval[X1] and eval[K] < eval[X2]) implies eval[root] = 1)
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

run synth for 10 but -1..3 Int
run synth for 10 but -1..3 Int, exactly 2 ITE, exactly 2 LT
