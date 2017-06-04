module parityfixed

--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------
abstract sig Node {}
abstract sig BoolNode extends Node {}
abstract sig BoolVar extends BoolNode {}
abstract sig BoolLit extends BoolNode { val: one Bit }

sig Not extends BoolNode {
  arg: one And
}
sig And extends BoolNode {
  left, right: one (Not + BoolVar + BoolLit)
}

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------
pred semantics[eval: Node -> Bit] {
  all n: Node | one eval[n]
  all n: And  | eval[n] = And[eval[n.left], eval[n.right]]
  all n: Not  | eval[n] = Not[eval[n.arg]]
  all l: BoolLit | eval[l] = l.val
}

pred acyclic[r: univ->univ, s: set univ] {
  all x: s | x !in x.^r
}

fact {
  acyclic[left+right+arg, Node]
}

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------
one sig A, B, C, D extends BoolVar {}
one sig BoolTrue, BoolFalse extends BoolLit {}

fact {
  BoolLit<:val = BoolTrue->BitTrue + BoolFalse->BitFalse
}

fun parity[a, b, c, d: Bit]: Bit {
  Xor[Not[Xor[a, b]], Not[Xor[c, d]]]
}

pred spec[root: Node, eval: Node -> (Int + Bit)] {
  let a = eval[A], b = eval[B], c = eval[C], d = eval[D] |
    parity[a, b, c, d] = eval[root]
}

--------------------------------------------------------------------------------
-- Atoms
--------------------------------------------------------------------------------

one sig N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, 
        N11, N12, N13, N14, N15, N16, N17, N18, N19, N20, 
        N21, N22, N23 extends Not {}
one sig A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, 
        A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, 
        A21, A22, A23 extends And {}

fun nNext: Not->Not {
  N1->N2 + N2->N3 + N3->N4 + N4->N5 + N5->N6 + N6->N7 + N7->N8 + N8->N9 + N9->N10 + N10->N11 + 
  N11->N12 + N12->N13 + N13->N14 + N14->N15 + N15->N16 + N16->N17 + N17->N18 + N18->N19 + N19->N20 + N20->N21 + N21->N22 + N22->N23
}

fun aNext: And->And {
  A1->A2 + A2->A3 + A3->A4 + A4->A5 + A5->A6 + A6->A7 + A7->A8 + A8->A9 + A9->A10 + A10->A11 + 
  A11->A12 + A12->A13 + A13->A14 + A14->A15 + A15->A16 + A16->A17 + A17->A18 + A18->A19 + A19->A20 + A20->A21 + A21->A22 + A22->A23
}

fun nOrd: Not->Int {
    N1->1 + N2->2 + N3->3 + N4->4 + N5->5 + N6->6 + N7->7 + N8->8 + N9->9 + N10->10 + 
    N11->11 + N12->12 + N13->13 + N14->14 + N15->15 + N16->16 + N17->17 + N18->18 + N19->19 + N20->20 + 
    N21->21 + N22->22 + N23->23
}

fun aOrd: And->Int {
    A1->1 + A2->2 + A3->3 + A4->4 + A5->5 + A6->6 + A7->7 + A8->8 + A9->9 + A10->10 + 
    A11->11 + A12->12 + A13->13 + A14->14 + A15->15 + A16->16 + A17->17 + A18->18 + A19->19 + A20->20 + 
    A21->21 + A22->22 + A23->23
}

fun binRels: Node->Node { arg+left+right }

--------------------------------------------------------------------------------
-- Symmetry breaking predicate
--------------------------------------------------------------------------------
pred sb[root: Node] {
  all disj n0, n1: Not | n1 in n0.^(binRels) implies nOrd[n1] > nOrd[n0]
  all disj a0, a1: And | a1 in a0.^(binRels) implies aOrd[a1] > aOrd[a0]
  all a: And | ((a.left+a.right) in Not) implies nOrd[a.left] < nOrd[a.right]
}

fact {
  arg = N1->A1 + N2->A2 + N3->A3 + N4->A4 + N5->A5 + N6->A6 + N7->A7 + N8->A8 + N9->A9 + N10->A10 + 
        N11->A11 + N12->A12 + N13->A13 + N14->A14 + N15->A15 + N16->A16 + N17->A17 + N18->A18 + N19->A19 + N20->A20 + 
        N21->A21 + N22->A22 + N23->A23
}


--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
pred synth[root: N1] {
  BoolVar in root.^(binRels) //all vars reachable from root
  sb[root]
  all env: BoolVar -> one Bit {
    some eval: BoolNode->Bit when {
      env in eval
      semantics[eval]
    }{
      spec[root, eval]
    }
  }
}

// ORIGINAL: use only Not+And
run synth for 0 but -1..23 Int, exactly 23 Not, exactly 23 And






