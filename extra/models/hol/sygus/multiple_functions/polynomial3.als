module multfun_polynomial3

open ../synth_ast

one sig X, Y extends IntVar {}
one sig Lit0, Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit0->0 + Lit1->1
}

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/multiple-functions/polynomial3.sl)
--------------------------------------------------------------------------------

pred synth[addExpr1, addExpr2: Node] {
  all envI: IntVar -> one Int {
    some eval: IntNode->Int + BoolNode->Bit when {
      envI in eval &&
      semantics[eval]
    }{
      plus[eval[addExpr1], eval[addExpr2]] = minus[eval[X], plus[eval[X], eval[Y]]]
    }
  }
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run synth for 0 but 4 Int, exactly 1 BvSub, exactly 1 BvAdd
