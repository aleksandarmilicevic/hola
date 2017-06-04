module multfun_polynomial1

open ../synth_ast

one sig X, Y extends IntVar {}

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/multiple-functions/polynomial1.sl)
--------------------------------------------------------------------------------

pred synth[root1, root2: Node] {
  all envI: IntVar -> one Int {
    some eval: IntNode->Int + BoolNode->Bit when {
      envI in eval &&
      semantics[eval]
    }{
      plus[eval[root1], eval[root2]] = plus[eval[X], eval[Y]]
    }
  }
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run synth for 0 but 4 Int, exactly 1 BvSub, exactly 1 BvAdd
