open max

--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
one sig X, Y, Z extends Var {}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synth for 7 but 0..2 Int, 0 IntLit, 0 GT, 0 LT
run synth for 7 but 0..2 Int, 0 IntLit, 0 GT, 0 LT, exactly 2 ITE, exactly 2 GTE
