module sygus

-----------------------------------
-- AST
-----------------------------------
abstract sig Bool {}
one sig BoolTrue extends Bool {}
one sig BoolFalse extends Bool {}

abstract sig Node {}
abstract sig BoolNode extends Node {}
abstract sig IntNode  extends Node {}
abstract sig Var      extends IntNode {}

abstract sig IntLit   extends IntNode { val: one Int }
abstract sig IntComp  extends BoolNode {
  left, right: IntNode
}
abstract sig BoolComp extends BoolNode {
  left, right: BoolNode
}

sig EQ, GTE, LTE, GT, LT extends IntComp {}
sig And, Or extends BoolComp {}
sig Not     extends BoolNode { arg: BoolNode }
sig ITE     extends IntNode {
  condition: BoolNode, then, elsen: IntNode
}

------------------------------------------------------------------
-- Semantics
------------------------------------------------------------------
pred semantics[eval: Node -> (Int + Bool)] {
  all n: ITE {
    eval[n] in Int
    eval[n.condition] in Bool && eval[n.then] in Int && eval[n.elsen] in Int
    eval[n.condition] = BoolTrue implies
      eval[n.then] = eval[n] else eval[n.elsen] = eval[n]
  }

  all n: BoolNode | eval[n] in Bool
  all n: IntComp  | eval[n.left] in Int and eval[n.right] in Int
  all n: BoolComp | eval[n.left] in Bool and eval[n.right] in Bool
  all v: Var      | one eval[v] and eval[v] in Int
  all i: IntLit   | one eval[i] and eval[i] in Int and eval[i] = i.val

  all n: Not  | eval[n.arg] in Bool
  all n: EQ   | eval[n.left] = eval[n.right] implies
                  eval[n] = BoolTrue else eval[n] = BoolFalse
  all n: GTE  | eval[n.left] >= eval[n.right] implies
                  eval[n] = BoolTrue else eval[n] = BoolFalse
  all n: LTE  | eval[n.left] <= eval[n.right] implies
                  eval[n] = BoolTrue else eval[n] = BoolFalse

  all n: GT   | eval[n.left] > eval[n.right] implies
                  eval[n] = BoolTrue else eval[n] = BoolFalse

  all n: LT   | eval[n.left] < eval[n.right] implies
                  eval[n] = BoolTrue else eval[n] = BoolFalse

  all n: And  | (eval[n.left] = BoolTrue and eval[n.right] = BoolTrue) implies
                 eval[n] = BoolTrue else eval[n] = BoolFalse
  all n: Or   | (eval[n.left] = BoolTrue or eval[n.right] = BoolTrue) implies
                 eval[n] = BoolTrue else eval[n] = BoolFalse
  all n: Not  | eval[n.arg] = BoolFalse implies
                 eval[n] = BoolTrue else eval[n] = BoolFalse
}

--------------------------------------------------------------------------------
-- Facts
--------------------------------------------------------------------------------
pred acyclic[r: univ->univ, s: set univ] {
  all x: s | x !in x.^r
}

fact {
  acyclic[arg + condition + then + elsen + 
          IntComp<:left   + IntComp<:right + 
          BoolComp<:left  + BoolComp<:right, Node]
}

--------------------------------------------------------------------------------
-- Synthesis predicate
--------------------------------------------------------------------------------
pred synth[root: IntNode] {
  all env: Var -> one Int |
    some eval: Node -> one (Int+Bool) when env in eval && semantics[eval] |
      spec[root, eval]
}


--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------
one sig X, Y, Z, U extends Var {}

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> (Int + Bool)] {
  all v: Var | eval[root] >= eval[v]
  some v: Var | eval[root] = eval[v]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synth for 10 but 0..3 Int
run synth for 10 but 0..3 Int, exactly 3 ITE, exactly 3 GTE
