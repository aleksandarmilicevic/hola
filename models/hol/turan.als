sig Node  {}

sig Edge  {
  src: one Node,
  dst: one Node - src
}

sig Graph  {
  nodes: set Node,
  edges: set Edge
} {
  edges.(src+dst) in nodes
}

fun eNodes[e: Edge]: set Node { e.(src + dst) }
fun n2n: Node -> Node { (~src).dst }

fact {
  one Graph
  Graph.nodes = Node
  Graph.edges = Edge
  some Graph.nodes
}

fact noSymEdges {
  no e1: Edge, e2: Edge - e1 |
    eNodes[e1] = eNodes[e2]
}


pred clique[g: Graph, clq: set Node] {
  clq in g.nodes
  all n1: clq, n2: clq - n1 |
    some e: g.edges |
      (n1 + n2) in eNodes[e]
}


pred maxClique[g: Graph, clq: set Node] {
  clique[g, clq]
  no clq2: set Node {
    clq2 != clq
    clique[g, clq2]
    #clq2 > #clq
  }
}


pred noClique[g: Graph, n: Int] {
  no clq: set Node {
    #clq = n
    clique[g, clq]
  }
}

check {
  all g: Graph |
    some mClq: set Node when maxClique[g, mClq] |
      let n = #g.nodes, k = plus[#mClq,1] |
        #g.edges <= k.minus[2].mul[n].mul[n].div[2].div[k.minus[1]]
} for 6 but 0..180 Int, 15 Edge


