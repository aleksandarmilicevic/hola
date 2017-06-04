open graph

/* don't care about node values here */
fact { all n: Node | no n.val }

/* nodes connected by a given edge */
fun eNodes[e: Edge]: set Node { e.(src+dst) }

--------------------------------------------------------------------------------
-- Functions/Predicates/Assertions
--------------------------------------------------------------------------------

/* n1 -> n2 in conn[g] if n1 and n2 are neighbours in graph g */
fun conn[g: Graph]: Node -> Node {
  {n1, n2: g.nodes | some e: g.edges | eNodes[e] = n1 + n2}
}

/* holds over (n1, n2, g) iff there's a path from n1 to n2 in graph g*/
pred connected[n1, n2: Node, g: Graph] {
  n1 -> n2 in ^(conn[g])
}

/* An independent set is a set of nodes, no two of which are neighbours */
pred independentSet[g: Graph, indset: set Node] {
  indset in g.nodes
  all disj n1, n2: indset |
    no e: g.edges |
      eNodes[e] = n1 + n2
}

/* 'indset' is independent set and there is no other independent set with more nodes */
pred maxIndependentSet[g: Graph, indset: set Node] {
  independentSet[g, indset]
  no indset2: set Node {
    indset2 != indset
    independentSet[g, indset2]
    #indset2 > #indset
  }
}

/* A vertex cover is a set of nodes such that every edge in g is
   adjacent to at least one node in the set */
pred vertexCover[g: Graph, cover: set Node] {
  cover in g.nodes
  all e : g.edges |
    some eNodes[e] & cover
}


/* 'cover' is a vertex cover and there is no other vertex cover with fewer nodes */
pred minVertexCover[g: Graph, cover: set Node] {
  vertexCover[g, cover]
  no cover2: set Node {
    cover != cover2
    vertexCover[g, cover2]
    #cover2 < #cover
  }
}

/* edges that cross the two disjoint node set as determined by the cut */
fun crossing[g: Graph, cut: set Node]: set Edge {
  let cut' = g.nodes - cut |
    {e: g.edges | (e.src in cut and e.dst in cut') or (e.dst in cut and e.src in cut')}
}

/* 'cut' is set of nodes such that there is no other set of nodes that has more crossing edges */
pred maxCut[g: Graph, cut: set Node] {
  cut in g.nodes
  no cut2: set Node {
    cut2 in g.nodes
    cut2 != cut
    #crossing[g, cut2] > #crossing[g, cut]
  }
}
