abstract sig Node {}
sig AndNode extends Node {
  left, right: Node
}

abstract sig Var extends Node {}
one sig X, Y extends Var {}

abstract sig Val {}
one sig BTrue, BFalse extends Val {}

pred prop[xval, yval, astval: Val, ast: Node, eval: Node -> Val] {
  (eval[X] = xval and eval[Y] = yval) implies eval[ast] = astval
}

run {
  some ast: AndNode |
    all eval: Node -> Val {
        (all n: AndNode |
           eval[n.left] = BTrue and eval[n.right] = BTrue implies 
             eval[n] = BTrue else eval[n] = BFalse) implies
        (prop[BTrue, BTrue, BTrue, ast, eval] and
         prop[BTrue, BFalse, BFalse, ast, eval] and
         prop[BFalse, BTrue, BFalse, ast, eval] and
         prop[BFalse, BFalse, BFalse, ast, eval])

  }
} for 3
