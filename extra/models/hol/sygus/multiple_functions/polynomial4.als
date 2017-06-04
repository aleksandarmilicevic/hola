module multfun_polynomial4

open ../synth_ast

one sig X, Y extends IntVar {}
one sig Lit0, Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit0->0 + Lit1->1
}

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/multiple-functions/polynomial4.sl)
--------------------------------------------------------------------------------

pred synth[addExpr1, addExpr2: Node] {
  all envI: IntVar -> one Int {
    some eval: IntNode->Int + BoolNode->Bit when {
      envI in eval &&
      semantics[eval]
    }{
      let x=eval[X], y=eval[Y] |
        plus[eval[addExpr1], eval[addExpr2]] = plus[plus[plus[x, y], y], plus[x, y]]
    }
  }
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run synth for 0 but 4 Int, exactly 2 BvSub, exactly 2 BvAdd
