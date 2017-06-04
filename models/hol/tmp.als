sig S {
  f: Int
}
sig A extends S {}
sig B extends S {}

one sig G {
  x: A->(B+Int)
}

pred p[r: A -> (B+Int)] {
  (r.(B+Int)).f in (r[A].f + r[A])
}

pred q[r: A -> (B+Int)] {
  all a: A | one r[a]
}


run {
  G.x = {a: A, b: (B+Int) | q[a -> b] }
  some G.x
  -- #G.x > 2
  --some G.x[A] & Int
} for 5 but 4 Int
