
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
abstract sig IntComp extends BoolNode {
  left, right: IntNode
}
sig Equals, GTE, LTE extends IntComp {}

abstract sig BoolComp extends BoolNode {
  left, right: BoolNode
}
sig And, Or extends BoolComp {}

sig Not extends BoolNode {
  arg: BoolNode
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

 all n: BoolNode | eval[n] in Bool
 all n: IntComp | eval[n.left] in Int and eval[n.right] in Int
 all n: BoolComp | eval[n.left] in Bool and eval[n.right] in Bool
 all n: Not | eval[n.arg] in Bool

 all n: Equals | eval[n.left] = eval[n.right] implies
                    eval[n] = BoolTrue else eval[n] = BoolFalse
 all n: GTE | eval[n.left] >= eval[n.right] implies
                    eval[n] = BoolTrue else eval[n] = BoolFalse
 all n: LTE | eval[n.left] <= eval[n.right] implies
                    eval[n] = BoolTrue else eval[n] = BoolFalse

 all n: And | (eval[n.left] = BoolTrue and eval[n.right] = BoolTrue) implies
                    eval[n] = BoolTrue else eval[n] = BoolFalse
 all n: Or | (eval[n.left] = BoolTrue or eval[n.right] = BoolTrue) implies
                  eval[n] = BoolTrue else eval[n] = BoolFalse
 all n: Not | eval[n.arg] = BoolFalse implies
                    eval[n] = BoolTrue else eval[n] = BoolFalse


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
  acyclic[condition+then+elsen+IntComp<:left+BoolComp<:left+IntComp<:right+BoolComp<:right+arg, Node]
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
    some eval: Node -> one (Int+Bool) | env in eval && semantics[eval] |
      spec[root, eval]
  }
}


pred synthOld[root: IntNode] {
  all eval: Node -> one (Int+Bool) | semantics[eval] |
    spec[root, eval]
}

run synth for 7 but 0..2 Int
run synth for 7 but 0..2 Int, exactly 2 ITE, exactly 2 GTE

run synthOld for 7 but 0..2 Int
