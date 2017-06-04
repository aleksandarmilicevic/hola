module synth<spec>

open util/boolean as b

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------
/* use the builtin Int, and Bool from the util/boolean library */

/*
abstract sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}
*/
--------------------------------------------------------------------------------
-- AST Nodes
--------------------------------------------------------------------------------
abstract sig Node {}
abstract sig BoolNode extends Node {}
abstract sig IntNode  extends Node {}

abstract sig IntComp  extends BoolNode {
  left, right: one IntNode
}
abstract sig BoolComp extends BoolNode {
  left, right: one BoolNode
}

sig And, Or, Xor extends BoolComp {}
sig Not extends BoolNode {
  arg: one BoolNode
}

sig Equals, GTE, LTE, GT, LT extends IntComp {}
abstract sig IntVar extends IntNode {}
abstract sig IntLit extends IntNode {
  val: one Int
}

sig ITE extends IntNode {
  condition: one BoolNode,
  then: one IntNode,
  elsen: one IntNode
}


--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------
pred semantics[eval: Node -> (Int + Bool)] {
  all n: ITE {
    /*eval[n] in Int
    eval[n.condition] in Bool
    eval[n.then] in Int
    eval[n.elsen] in Int*/
    eval[n.condition] = True implies
      eval[n.then] = eval[n] else eval[n.elsen] = eval[n]
  }

  all n: IntNode  | one eval[n] and eval[n] in Int
  all n: BoolNode | one eval[n] and eval[n] in Bool
  
  // redundant stuff
  /*
  all n: IntComp  | eval[n.left] in Int and eval[n.right] in Int
  all n: BoolComp | eval[n.left] in Bool and eval[n.right] in Bool
  all n: Not      | eval[n.arg] in Bool
  all v: IntVar   | one eval[v] and eval[v] in Int
  */
  // ---------------

  all n: Equals   | eval[n.left] = eval[n.right] implies
                      eval[n] = True else eval[n] = False
  all n: GTE      | eval[n.left] >= eval[n.right] implies
                      eval[n] = True else eval[n] = False
  all n: LTE      | eval[n.left] <= eval[n.right] implies
                      eval[n] = True else eval[n] = False
  all n: GT       | eval[n.left] > eval[n.right] implies
                      eval[n] = True else eval[n] = False
  all n: LT       | eval[n.left] < eval[n.right] implies
                      eval[n] = True else eval[n] = False

  /*
  all n: And      | (eval[n.left] = True and eval[n.right] = True) implies
                     eval[n] = True else eval[n] = False
  all n: Or       | (eval[n.left] = True or eval[n.right] = True) implies
                     eval[n] = True else eval[n] = False
  all n: Xor      | ((eval[n.left] = True and eval[n.right] = False) or (eval[n.left] = False and eval[n.right] = False)) implies
                     eval[n] = True else eval[n] = False
  all n: Not      | eval[n.arg] = False implies
                     eval[n] = True else eval[n] = False
  */

  all n: And      | eval[n] = b/And[eval[n.left], eval[n.right]]
  all n: Or       | eval[n] = b/Or [eval[n.left], eval[n.right]]
  all n: Xor      | eval[n] = b/Xor[eval[n.left], eval[n.right]]
  all n: Not      | eval[n] = b/Not[eval[n.arg]]

  all i: IntLit   | eval[i] = i.val 
}

--------------------------------------------------------------------------------
-- Facts
--------------------------------------------------------------------------------
pred acyclic[r: univ->univ, s: set univ] {
  all x: s | x !in x.^r
}

fun binRels[]: Node -> Node {
  condition + then + elsen +
    IntComp<:left + BoolComp<:left +
    IntComp<:right + BoolComp<:right +
    arg
}


fact {
  acyclic[binRels, Node]
}

pred allVarsReachableFrom[root: Node] {
  all v: IntVar |
    v in root.^(binRels)
}

--------------------------------------------------------------------------------
-- Synthesis predicate
--------------------------------------------------------------------------------
pred synth[root: Node] {
  allVarsReachableFrom[root]
  all envI: IntVar -> one Int {
    some eval: IntNode->Int + BoolNode->Bool when {
      envI in eval
      semantics[eval]
    }{
      spec[root, eval]
    }
  }
}

pred synthITE[root: ITE]           { synth[root] }
pred synthIntNode[root: IntNode]   { synth[root] }
pred synthBoolNode[root: BoolNode] { synth[root] }
