open util/ordering[Prisoner] as Prisoner_ord

abstract sig Color  {}
one sig Red, Blue extends Color {}

sig Prisoner  {
  hatColor: Color,
}

fact hatColors {
  colors_fact[hatColor]
}

fun sees[p: Prisoner]: set Prisoner {
  p.nexts - Prisoner_ord/last
}

pred colors_fact[rel: Prisoner -> Color] {
  #rel.Red = 2
  #rel.Blue = 2
}

pred deduction_rule[p: Prisoner, rel: Prisoner -> Color] {
  colors_fact[rel]
  sees[p] <: hatColor in rel
}

run {
  some p: Prisoner {
    all ded: Prisoner -> one Color {
      deduction_rule[p, ded] => p.hatColor = ded[p]
    }
  }
} for 4 but exactly 4 Prisoner
