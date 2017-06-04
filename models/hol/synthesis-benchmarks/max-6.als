
--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
abstract sig Bool {}
one sig BoolTrue extends Bool {}
one sig BoolFalse extends Bool {}


abstract sig Var extends IntNode {}
one sig X, Y, Z, U, V, W extends Var {}


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
    eval[root] >= eval[U]
    eval[root] >= eval[V]
    eval[root] >= eval[W]

    eval[root] = eval[X] or
      eval[root] = eval[Y] or
        eval[root] = eval[Z] or
          eval[root] = eval[U] or
            eval[root] = eval[V] or
              eval[root] = eval[W] 
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

run synth for 16 but 0..5 Int
run synth for 16 but 0..5 Int, exactly 5 ITE, exactly 5 GTE
