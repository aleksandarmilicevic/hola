open max

--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
one sig X, Y, Z, U extends IntVar {}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synthIntNodeI for 10 but -1..2 Int, 0 IntLit, 0 BoolLit, 0 BoolVar, 0 BinaryIntOp, 0 UnaryIntOp, 
                                        0 GT, 0 LT, 0 Xor, 0 Nand, 0 Nor, 0 BoolInvComp
run synthIntNodeI for 0 but -1..2 Int, exactly 3 ITE, exactly 3 GTE
