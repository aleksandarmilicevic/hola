open mmax[gteNexts, iteNexts]

--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
one sig X, Y, Z, U, V, W extends IntVar {}

--------------------------------------------------------------------------------
-- AST Nodes
--------------------------------------------------------------------------------

one sig GTE0, GTE1, GTE2, GTE3, GTE4 extends GTE {}
one sig ITE0, ITE1, ITE2, ITE3, ITE4 extends ITE {}

fun gteNexts[]: GTE -> GTE {
  GTE0->GTE1 + GTE0->GTE2 + GTE0->GTE3 + GTE0->GTE4 +
  GTE1->GTE2 + GTE1->GTE3 + GTE1->GTE4 +
  GTE2->GTE3 + GTE2->GTE4 +
  GTE3->GTE4
}

fun iteNexts[]: ITE -> ITE {
  ITE0->ITE1 + ITE0->ITE2 + ITE0->ITE3 + ITE0->ITE4 +
  ITE1->ITE2 + ITE1->ITE3 + ITE1->ITE4 +
  ITE2->ITE3 + ITE2->ITE4 +
  ITE3->ITE4
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run synth for 0 but 0..5 Int
