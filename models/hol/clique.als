module GraphModel

sig Node  {
  val: lone Int
}

sig Edge  {
  src: one Node,
  dst: one Node
} {
  this.@src != this.@dst
}

sig Graph  {
  nodes: set Node,
  edges: set Edge
} {
  this.@edges.(@src + @dst) in this.@nodes
}

fact {
  Graph.edges = Edge
  Graph.nodes = Node
}

pred aux_maxCliqueFix_1394921187_003_2553[g: Graph, clq: set Node] {
  #g.nodes = 2
  some g.edges
}

fun valsum[nodes: set Node]: Int {
  sum n: nodes | n.val
}

pred clique[g: Graph, clq: set Node] {
  clq in g.nodes
  all n1: clq {
    all n2: clq - n1 {
      some e: g.edges {
        e.src = n1 && e.dst = n2 || e.src = n2 && e.dst = n1
      }
    }
  }
}

pred fixClique[g: Graph, clq: set Node] {
  fix clique[g, clq] while #clq > #_clq
}

pred fixFixClique1[g: Graph, clq: set Node] {
  fix maxClique[g, clq] while valsum[clq] > valsum[_clq]
}

pred fixFixClique2[g: Graph, clq: set Node] {
  #clq < #g.nodes
  fix fixClique[g, clq] while valsum[clq] > valsum[_clq]
}

pred maxClique[g: Graph, clq: set Node] {
  clique[g, clq]
  no clq2: set Node {
    clq2 != clq
    clique[g, clq2]
    #clq2 > #clq
  }
}

pred maxMaxClique[g: Graph, clq: set Node] {
  maxClique[g, clq]
  no clq2: set Node {
    clq2 != clq
    maxClique[g, clq]
    valsum[clq2] > valsum[clq]
  }
}

pred noClique[g: Graph, n: Int] {
  no clq: set Node {
    #clq = n
    clique[g, clq]
  }
}

pred noSymEdges[g: Graph] {
  no e1: g.edges, e2: g.edges {
    e1 != e2
    e1.src = e2.dst && e1.dst = e2.src || e1.src = e2.src && e1.dst = e2.dst
  }
}

assert maxClique_props {
  all g: Graph, clq: set Node {
    #g.nodes = 2 && some g.edges && maxClique[g, clq] => g.nodes = clq
  }
}

run noClique for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge
run maxClique for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge
run maxMaxClique for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge

run noClique_sat1 {
  some g: Graph, n: Int {
    n = 1
    noClique[g, n]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge

run noClique_unsat {
  some g: Graph, n: Int {
	n = 1
    some g.nodes
    noClique[g, n]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge

run maxClique_sat {
  some g: Graph, clq: set Node {
    #g.nodes = 5
    #clq = 2
    maxClique[g, clq]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge

run maxClique_sat1 {
  some g: Graph, clq: set Node {
    #g.nodes = 2
    some g.edges
    maxClique[g, clq]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge

run maxClique_unsat {
  some g: Graph, clq: set Node {
    #g.nodes < #clq
    maxClique[g, clq]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge

run maxClique_unsat1 {
  some g: Graph, clq: set Node {
    #g.nodes = 2
    some g.edges
    #clq < 2
    maxClique[g, clq]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge

check maxClique_props for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge
