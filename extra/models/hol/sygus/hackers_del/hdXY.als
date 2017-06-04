/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 */

module hdXY<hdspec>

open ../synth2[spec]

--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------
one sig X, Y extends IntVar {}

--------------------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------------------
pred spec[root: Node, eval: Node -> Int] {
  let x = eval[X], y = eval[Y] |
    bveq[hdspec[x, y], eval[root]]
}
