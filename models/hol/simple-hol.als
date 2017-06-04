sig A, B {}

pred test[r: A -> B] {
  r in ^r
}

run {
  all r: A -> B |
    test[r]
}
