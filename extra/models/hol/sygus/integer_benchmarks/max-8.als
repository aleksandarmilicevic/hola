open max

--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------
one sig X, Y, Z, U, V, W, P, Q extends IntVar {}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synthIntNodeI for 19 but -1..6 Int, 0 IntLit, 0 BoolLit, 0 BoolVar, 0 BinaryIntOp, 0 UnaryIntOp, 
                                        0 GT, 0 LT, 0 Xor, 0 Nand, 0 Nor, 0 BoolInvComp
run synthIntNodeI for 0 but -1..6 Int, exactly 7 ITE, exactly 7 GTE
