module max<gteNexts, iteNexts>

open ../synth[spec]

--------------------------------------------------------------------------------
-- Symmetry breaking predicate
--------------------------------------------------------------------------------
pred sb[root: Node] {
  all disj gte0, gte1: GTE | gte1 in gte0.^(binRels) implies gte1 in gteNexts[gte0]
  all disj ite0, ite1: ITE | ite1 in ite0.^(binRels) implies ite1 in iteNexts[ite0]
--  all disj ite0, ite1, ite2: ITE | (ite0.then = ite1 && ite0.elsen = ite2) implies ite2 in iteNexts[ite1]
  all ite: ITE {
    all disj n1, n2: Node when {
      n1 in ite.then.*binRels
      n2 in ite.elsen.*binRels
    } {
      (n1 + n2) in ITE => n2 in iteNexts[n1]
      (n1 + n2) in GTE => n2 in gteNexts[n2]
    }
  }  
  all gte: GTE {
    all disj n1, n2: Node | (
      n1 in gte.left.*binRels &&
      n2 in gte.right.*binRels
    ) implies {
      (n1 + n2) in ITE => n2 in iteNexts[n1]
      (n1 + n2) in GTE => n2 in gteNexts[n2]
    }
  }  
}

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> (Int + Bool)] {
    //sb[root]
    all v: IntVar | eval[root] >= eval[v]
    some v: IntVar | eval[root] = eval[v]
}

--fact { IntVarVal = Int }
