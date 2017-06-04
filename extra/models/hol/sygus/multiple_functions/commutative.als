module commutative

open ../synth_ast

one sig X, Y extends IntVar {}

--------------------------------------------------------------------------------
-- Specification
-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/multiple-functions/commutative.sl)
--------------------------------------------------------------------------------

pred synth[root: Node] {
  allVarsReachableFrom[root]
  //one (root.*binRels & (BvSub + BvAdd))
  all env: IntVar -> one Int {
    some eval: IntNode->Int + BoolNode->Bit when {
      env in eval &&
      semantics[eval]
    }{
      some eval2: IntNode->Int + BoolNode->Bit when {
        (env ++ (X->env[Y] + Y->env[X])) in eval2
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
