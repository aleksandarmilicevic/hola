--open util/ordering[Time]

abstract sig Color  {}
one sig Red, Blue extends Color {}

sig Prisoner  {
  hatColor: Color,
}

one sig Game {
  fst: Prisoner,
  nxt: Prisoner -> Prisoner
} {
  pred/totalOrder[Prisoner, fst, nxt]
}

/*
sig Time {}
sig Strategy {
  ord: Game -> Time
}
*/

fact hatColors {
  colors_fact[hatColor]
}

fun sees[g: Game, p: Prisoner]: set Prisoner {
  /* all in front except the last */
  p.^(g.nxt) - (Prisoner-(g.nxt.Prisoner))
}

pred colors_fact[rel: Prisoner -> Color] {
  #rel.Red = 2 and #rel.Blue = 2
}

pred deduction_rule[g: Game, p: Prisoner,
                    rel: Prisoner -> Color,
                    seen: Prisoner -> Color
] {
  colors_fact[rel]
  sees[g, p] <: hatColor in rel
  no seen & rel
}

pred wins0[g: Game, p: Prisoner] {
  -- one g
  all ded: Prisoner -> one Color {
    deduction_rule[g, p, ded, none->none] => p.hatColor = ded[p]
  }
}

pred wins1[g: Game, p: Prisoner] {
  some g0: Game {
    wins0[g0, p]
  }
}

run {
  all g: Game |
    some p: Prisoner |
      wins0[g, p]
} for 4 but exactly 4 Prisoner
