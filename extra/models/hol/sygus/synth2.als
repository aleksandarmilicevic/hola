module synth2<spec>

open synth_ast

--------------------------------------------------------------------------------
-- Synthesis predicate
--------------------------------------------------------------------------------
pred synth[root: Node] {
  all envI: IntVar -> one IntVarVal {
  all envB: BoolVar -> one Bit {
    some eval: IntNode->Int + BoolNode->Bit when {
      envI in eval
      envB in eval
      semantics[eval]
    }{
      spec[root, eval]
    }
  }
  }
}

pred synthI[root: Node] {
  all envI: IntVar -> one IntVarVal {
    some eval: IntNode->Int + BoolNode->Bit when {
      envI in eval
      semantics[eval]
    }{
      spec[root, eval]
    }
  }
}

pred synthB[root: Node] {
  all envB: BoolVar -> one Bit {
    some eval: IntNode->Int + BoolNode->Bit when {
      envB in eval
      semantics[eval]
    }{
      spec[root, eval]
    }
  }
}

pred synthIntNode[root: IntNode]    { synth[root] }
pred synthIntNodeI[root: IntNode]   { synthI[root] }
pred synthIntNodeB[root: IntNode]   { synthB[root] }

pred synthBoolNode[root: BoolNode]  { synth[root] }
pred synthBoolNodeI[root: BoolNode] { synthI[root] }
pred synthBoolNodeB[root: BoolNode] { synthB[root] }
