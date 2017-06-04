open util/ordering[Time]

sig Time {}

sig Node {covered: set Time}

sig Edge {
  weight: Int,
  nodes: set Node,
  chosen: set Time
} {
  weight >= 0 and #nodes = 2
}

pred cutting (e: Edge, t: Time) {
  (some e.nodes & covered.t) and (some e.nodes & (Node - covered.t))
}

pred step (t, t': Time) {
  -- stutter if done, else choose a minimal edge from a covered to an uncovered node
  covered.t = Node =>
         chosen.t' = chosen.t and covered.t' = covered.t
  else some e: Edge {
         cutting[e,t] and (no e2: Edge | cutting[e2,t] and e2.weight < e.weight)
         chosen.t' = chosen.t + e
         covered.t' = covered.t + e.nodes}
}

fact prim {
  -- initially just one node marked
  one covered.first and no chosen.first
  -- steps according to algorithm
  all t: Time - last | step[t, t.next]
  -- run is complete
  covered.last = Node
}

pred spanningTree (edges: set Edge) {
  -- empty if only 1 node and 0 edges, otherwise covers set of nodes
  (one Node and no Edge) => no edges else edges.nodes = Node
  -- connected and a tree
  #edges = (#Node).minus[1]
  let adj = {a, b: Node | some e: edges | a + b in e.nodes} |
    Node -> Node in *adj
}

correct_and_smallest: check {
  spanningTree[chosen.last]
  no edges: set Edge {
    spanningTree[edges]
    (sum e: edges | e.weight) < (sum e: chosen.last | e.weight)}
} for 5 but 6 Edge, 5 Int

correct: check { spanningTree [chosen.last] } for 5 but 10 Edge, 5 Int

smallest: check {
  no edges: set Edge {
    spanningTree[edges]
    (sum e: edges | e.weight) < (sum e: chosen.last | e.weight)}
} for 5 but 7 Edge, 5 Int
