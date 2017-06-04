--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
abstract sig Var extends IntNode {}
one sig X, Y extends Var {}

sig IntLit extends IntNode {
  intval: Int
}


--------------------------------------------------------------------------------
-- AST Nodes
--------------------------------------------------------------------------------
abstract sig Node {}

abstract sig IntNode extends Node {}

sig Plus, Minus extends IntNode {
  left, right: IntNode
}

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------
pred semantics[eval: Node -> Int] {
  all n: Plus {
    eval[n] in Int
    eval[n] = add[eval[n.left], eval[n.right]]
  }

  all n: Minus {
    eval[n] in Int
    eval[n] = minus[eval[n.left], eval[n.right]]
  }

  all n: IntLit | eval[n] = n.intval
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
  acyclic[(Plus <: left)+(Minus <: left)+(Plus <: right)+(Minus <: right), Node]
}

pred spec[add1, add2: Node, eval: Node -> Int] {
  eval[add1] = eval[add2]
}

run {
  some add1, add2: IntNode {
    all env: Var -> one Int {
      some eval: Node -> one Int |{
        env in eval
        semantics[eval]
      } |{
        spec[add1, add2, eval]
      }
    }
  }
} for 2 but 3 Int
