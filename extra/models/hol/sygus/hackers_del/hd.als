/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 */

module hd<hdspec>

open ../synth2[spec]

--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------
one sig X extends IntVar {}
/*one sig Lit0, Lit1, LitFFFFFFFF extends IntLit {}
fact {
  IntLit<:val = Lit0->0 + Lit1->1 + LitFFFFFFFF->0xFFFFFFFF
}
*/
--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> (Int + Bit)] {
  let x = eval[X] |
    bveq[hdspec[x], eval[root]]
}
