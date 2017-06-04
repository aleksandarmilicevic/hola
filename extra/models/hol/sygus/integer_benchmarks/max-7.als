open max
 
--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------
one sig X, Y, Z, U, V, W, P extends IntVar {}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synthIntNodeI for 17 but -1..5 Int, 0 IntLit, 0 BoolLit, 0 BoolVar, 0 BinaryIntOp, 0 UnaryIntOp, 
                                        0 GT, 0 LT, 0 Xor, 0 Nand, 0 Nor, 0 BoolInvComp
run synthIntNodeI for 0 but -1..5 Int, exactly 6 ITE, exactly 6 GTE
