some sig Node  {}

// between every two nodes there is an edge
pred clique[edges: Node -> Node, clq: set Node] {
  all disj n1, n2: clq | n1 -> n2 in edges
}

// no other clique with more nodes
pred maxClique[edges: Node -> Node, clq: set Node] {
  clique[edges, clq]
  no clq2: set Node | clq2!=clq and clique[edges,clq2] and #clq2>#clq
}

// symmetric and irreflexive
pred edgeProps[edges: Node -> Node] {
  (~edges in edges) and (no edges & iden)
}

// max number of edges in a ($k+1$)-free graph with $n$ nodes is $\frac{(k-1)n^2}{2k}$
check Turan_slow {
  all edges: Node -> Node | edgeProps[edges] implies
    some mClq: set Node {
      maxClique[edges, mClq]
      let n = #Node, k = #mClq, e = (#edges).div[2] |
        e <= k.minus[1].mul[n].mul[n].div[2].div[k]
    }
} for 5 but 0..100 Int -- checks in ~4s
--for 6 but 0..180 Int -- checks in ~10s
--for 7 but 0..294 Int -- checks in ~43s


check Turan {
  all edges: Node -> Node when edgeProps[edges] |
    some mClq: set Node when maxClique[edges, mClq] |
      let n = #Node, k = #mClq, e = (#edges).div[2] |
        e <= k.minus[1].mul[n].mul[n].div[2].div[k]
}--for 5 but 0..100 Int -- checks in ~300ms
--for 6 but 0..180 Int -- checks in ~3s
for 7 but 0..294 Int -- checks in ~6s
--for 8 but 0..448 Int -- checks in ~10s
--for 9 but 0..648 Int -- checks in ~44s
--for 10 but 0..900 Int -- checks in ~170s
