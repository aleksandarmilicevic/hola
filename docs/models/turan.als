some sig Node  {}

// between every two nodes there is an edge
pred clique[edges: Node -> Node, clq: set Node] {
  all disj n1, n2: clq | n1 -> n2 in edges
}

// no other clique with more nodes
pred maxClique[edges: Node -> Node, clq: set Node] {
  clique[edges, clq]
  no cq2: set Node | cq2!=clq && clique[edges,cq2] && #cq2>#clq
}

// symmetric and irreflexive
pred edgeProps[edges: Node -> Node] {
  (~edges in edges) and (no edges & iden)
}

// max number of edges in a (k+1)-free graph with n 
// nodes is (k-1)n^2/(2k)
check Turan {
  all edges: Node -> Node when edgeProps[edges] |
    some mClq: set Node when maxClique[edges, mClq] |
      let n = #Node, k = #mClq, e = (#edges).div[2] |
        e <= k.minus[1].mul[n].mul[n].div[2].div[k]
} for 7 but 0..294 Int -- checks in ~6s

// same as above, but with inlined domain constraints
check Turan_slow {
  all edges: Node -> Node | edgeProps[edges] implies {
    some mClq: set Node {
      maxClique[edges, mClq]
      let n = #Node, k = #mClq, e = (#edges).div[2] |
        e <= k.minus[1].mul[n].mul[n].div[2].div[k]
    }
  }
} for 7 but 0..294 Int -- checks in ~43s

