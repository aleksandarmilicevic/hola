open util/integer

/*
sig S {
  a: one Int,
  b: one Int,
  c: one Int
} {
  c = bvand[a, b]
  a != b
  b != c
  c != a
  a > 0
  b > 0
  c > 0
}*/

check andZero { 
  all i: Int | bvand[i, 0] = 0 
} for 3 but 4 Int expect 0

check andIdempotent {
  all i: Int | bvand[i, i] = i
} for 3 but 4 Int expect 0

check andMinusOne{
  all i: Int | bvand[i, -1] = i
} for 3 but 4 Int expect 0

check orZero { 
  all i: Int | bvor[i, 0] = i
} for 3 but 4 Int expect 0

check orIdempotent {
  all i: Int | bvor[i, i] = i
} for 3 but 4 Int expect 0

check orMinusOne{
  all i: Int | bvor[i, -1] = -1
} for 3 but 4 Int expect 0


run findBVANDZeroOne {
  some z: Int | all i: Int | bvand[i, z] = 0
  some o: Int | all i: Int | bvand[i, o] = i
} for 3 but 4 Int expect 1

run findBVORZeroOne {
  some z: Int | all i: Int | bvor[i, z] = -1
  some o: Int | all i: Int | bvor[i, o] = i
} for 3 but 4 Int expect 1
