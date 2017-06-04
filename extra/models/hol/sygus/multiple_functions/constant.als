module multfun_constant

open ../synth_ast

one sig X, Y extends IntVar {}
one sig Lit0, Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit0->0 + Lit1->1
}

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/multiple-functions/constant.sl)
--------------------------------------------------------------------------------

pred synth[root: Node] {
  Y !in (root.*binRels)
  X in (root.*binRels)
  all envI: IntVar -> one Int {
    some eval: IntNode->Int + BoolNode->Bit when {
      envI in eval &&
      semantics[eval]
    }{
      some eval2: IntNode->Int + BoolNode->Bit when {
        (envI ++ (X->envI[Y])) in eval2
        semantics[eval2]
      }{
        eval[root] = eval2[root]
      }
    }
  }
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run synth for 0 but 4 Int, exactly 1 BvSub, exactly 1 BvAdd
