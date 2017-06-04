module graph

--------------------------------------------------------------------------------
-- Sigs
--------------------------------------------------------------------------------
sig Node  {
  val: lone Int
}

sig Edge  {
  src: one Node,
  dst: one Node
} {
  src != dst
}

sig Graph  {
  nodes: set Node,
  edges: set Edge
} {
  edges.(src + dst) in nodes
}

--------------------------------------------------------------------------------
-- Functions/Predicates/Assertions
--------------------------------------------------------------------------------

/* sum of node values */
fun valsum[nodes: set Node]: Int {
  sum n: nodes | n.val
}

/* every two nodes in 'clq' are connected */
pred clique[g: Graph, clq: set Node] {
  clq in g.nodes
  all disj n1, n2: clq |
    some e: g.edges |
      (n1 + n2) = e.(src + dst)
}

/* 'clq' is clique and there is no other clique with more nodes */
pred maxClique[g: Graph, clq: set Node] {
  clique[g, clq]
  no clq2: set Node {
    clq2 != clq
    clique[g, clq2]
    #clq2 > #clq
  }
}

/* 'clq' is maxClique and there is no other maxClique with greater sum */
pred maxMaxClique[g: Graph, clq: set Node] {
  maxClique[g, clq]
  no clq2: set Node {
    clq2 != clq
    maxClique[g, clq2]
    valsum[clq2] > valsum[clq]
  }
}

/* graph 'g' has no clique of size 'n' */
pred noClique[g: Graph, n: Int] {
  no clq: set Node {
    #clq = n
    clique[g, clq]
  }
}

/* assertion: if a graph has exactly 2 nodes and some edges,
   it's max-clique must contain both nodes */
assert maxClique_props {
  all g: Graph, clq: set Node {
    #g.nodes = 2 && some g.edges && maxClique[g, clq] => g.nodes = clq
  }
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run noClique for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 1
run maxClique for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 1
run maxMaxClique for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 1

/* find a graph that has no clique of size 1 => SAT */
run noClique_sat1 {
  some g: Graph, n: Int {
    n = 1
    noClique[g, n]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 1

/* find a graph that has some nodes and no clique of size 1 => UNSAT */
run noClique_unsat {
  some g: Graph, n: Int {
	n = 1
    some g.nodes
    noClique[g, n]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 0

/* find a graph with 5 nodes and a max-clique of size 2 => SAT */
run maxClique_sat {
  some g: Graph, clq: set Node {
    #g.nodes = 5
    #clq = 2
    maxClique[g, clq]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 1

/* find a graph with 2 nodes and some edges that has a max-clique => SAT */
run maxClique_sat1 {
  some g: Graph, clq: set Node {
    #g.nodes = 2
    some g.edges
    maxClique[g, clq]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 1

/* find a graph with fewer nodes than its max-clique => UNSAT */
run maxClique_unsat {
  some g: Graph, clq: set Node {
    #g.nodes < #clq
    maxClique[g, clq]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 0

/* find a graph with 2 nodes and some edges that has a max-clique with less than 2 nodes => UNSAT */
run maxClique_unsat1 {
  some g: Graph, clq: set Node {
    #g.nodes = 2
    some g.edges
    #clq < 2
    maxClique[g, clq]
  }
} for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 0

check maxClique_props for 5 but 5 Int, exactly 1 Graph, 5 Node, 10 Edge expect 0
