
--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
abstract sig Val {}

abstract sig Bool extends Val {}
one sig BoolTrue extends Bool {}
one sig BoolFalse extends Bool {}

sig IntVal extends Val {
  intvalue: Int
}

abstract sig Var extends Node {}
one sig X, Y, Z extends Var {}


--------------------------------------------------------------------------------
-- AST Nodes
--------------------------------------------------------------------------------
abstract sig Node {}

abstract sig IntNode extends Node {}

sig ITENode extends IntNode {
  condition: BoolNode,
  then: IntNode,
  elsen: IntNode
} 

abstract sig BoolNode extends Node {}
sig GTENode extends BoolNode {
  left, right: IntNode
}

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------
one sig Interpret {
  val: (Var -> Val) -> Node -> (Int + Bool)
} {
  all n: ITENode, env: Var -> Val {
    val[env, n] in Int
    val[env, n.condition] = BoolTrue implies 
      val[env, n.then] = val[env, n] else val[env, n.elsen] = val[a, n]
 }

  all n: GTENode, env: Var -> Val {
    val[env, n] in Bool
    val[env, n.left] >= val[env, n.right] <=> val[env, n] = BoolTrue
    not(val[env, n.left] >= val[env, n.right]) <=> val[env, n] = BoolFalse
  }

  all env: Var -> Val {
    val[env, X] = env[X]
    val[env, Y] = env[Y]
    val[env, Z] = env[Z]
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


run {
  -- this is the spec provided in the problem definition
  some root: IntNode | all env: Var -> Val {
    Interpret.val[env, root] >= env[X]
    Interpret.val[env, root] >= env[Y]
    Interpret.val[env, root] >= env[Z]

    Interpret.val[a, root] = env[X] or Interpret.val[a, root] = env[Y] or Interpret.val[a, root] = env[Z]
  }

} for 7 but 2 int
