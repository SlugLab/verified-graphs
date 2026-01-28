use vstd::prelude::*;

verus! {

#[verifier::ext_equal]
pub struct Vertex(pub(crate) nat);

impl Vertex {
    /// Returns the vertex as a natural number.
    pub(crate) open spec fn as_nat(self) -> nat {
        self.0
    }

    /// Returns if a vertex is isolated in graph G.
    ///
    /// [Tutte, Section I.1] A vertex of zero valency is said to be isolated.
    pub(crate) open spec fn is_isolated_in(self, g: Graph) -> bool
        recommends
            g.vertices.contains(self),
    {
        g.valency(self) == 0
    }

    /// Returns if a vertex is monovalent in graph G.
    ///
    /// [Tutte, Section I.1] [We] describe a vertex of valency 1 as monovalent.
    pub(crate) open spec fn is_monovalent_in(self, g: Graph) -> bool
        recommends
            g.vertices.contains(self),
    {
        g.valency(self) == 1
    }
}

#[verifier::ext_equal]
pub struct Edge {
    pub tail: Vertex,
    pub head: Vertex,
}

impl Edge {
    /// Returns if the edge is incident to the given vertex.
    ///
    /// An edge E is incident to a vertex v if v is either the head or tail of E.
    pub(crate) open spec fn is_incident_to(self, v: Vertex) -> bool {
        ||| self.tail == v
        ||| self.head == v
    }

    /// Returns if an edge is a loop.
    ///
    /// [Tutte, Section I.1] [An] edge has two ends, with the explanation that
    /// in the case of a loop the two ends are coincident.
    pub(crate) open spec fn is_loop(self) -> bool {
        self.tail == self.head
    }

    /// Returns if an edge is a link.
    pub(crate) open spec fn is_link(self) -> bool {
        !self.is_loop()
    }

    /// Returns if an edge is an isthmus of a graph G.
    pub(crate) open spec fn is_isthmus_of(self, g: Graph) -> bool {
        &&& g.edges.contains(self)
        &&& {
            let components = g.remove_edge(self).components();
            &&& components.len() == 2
            &&& {
                let c = components.choose();
                let d = components.remove(c).choose();
                ||| {
                    &&& c.vertices.contains(self.head)
                    &&& !c.vertices.contains(self.tail)
                    &&& !d.vertices.contains(self.head)
                    &&& d.vertices.contains(self.tail)
                }
                ||| {
                    &&& c.vertices.contains(self.tail)
                    &&& !c.vertices.contains(self.head)
                    &&& !d.vertices.contains(self.tail)
                    &&& d.vertices.contains(self.head)
                }
            }
        }
    }

    /// Returns the edge's end-graphs in graph G.
    pub(crate) open spec fn end_graphs_in(self, g: Graph) -> Set<Graph>
        recommends
            self.is_isthmus_of(g),
    {
        g.remove_edge(self).components()
    }

    /// Reverses the head and tail of the edge.
    pub(crate) open spec fn reverse(self) -> Self {
        Self { tail: self.head, head: self.tail }
    }
}

/// A finite graph.
#[allow(dead_code)]
#[verifier::ext_equal]
pub struct Graph {
    /// Set of vertices.
    pub(crate) vertices: Set<Vertex>,
    /// Set of edges.
    pub(crate) edges: Set<Edge>,
}

impl Graph {
    /// Well-formedness for a graph.
    ///
    /// Formally, a graph G is an ordered pair G = (V, E), where V is the set of
    /// vertices, and E is the set of edges such that E ⊆ {(u, v) | (u, v) ∈
    /// V^2)}.
    ///
    /// We restrict V and E to be finite to make G a finite graph.
    #[verifier::type_invariant]
    pub(crate) open spec fn well_formed(self) -> bool {
        &&& self.vertices.finite()
        &&& self.edges.finite()
        &&& (forall|e: Edge|
            #![auto]
            self.edges.contains(e) ==> {
                &&& self.vertices.contains(e.tail)
                &&& self.vertices.contains(e.head)
            })
    }

    /// Creates a new graph with the given set of vertices and edges.
    pub(crate) open spec fn new(vertices: Set<Vertex>, edges: Set<Edge>) -> Self {
        Self { vertices, edges }
    }

    /// Creates a new vertex-graph defined by the given vertex.
    pub(crate) open spec fn vertex_graph(v: Vertex) -> Self {
        Self { vertices: set![v], edges: Set::empty() }
    }

    /// Returns if a graph is a vertex-graph.
    ///
    /// [Tutte, Section I.1] A vertex-graph is an edgeless graph containing
    /// exactly one vertex.
    pub(crate) open spec fn is_vertex_graph(self) -> bool {
        &&& self.edges.is_empty()
        &&& self.vertices.is_singleton()
    }

    /// Returns if a graph is a vertex-graph defined by vertex x.
    pub(crate) open spec fn is_vertex_graph_defined_by(self, x: Vertex) -> bool {
        &&& self.is_vertex_graph()
        &&& self.vertices.contains(x)
    }

    /// Returns if a graph is a loop-graph.
    ///
    /// [Tutte, Section I.1] A loop-graph consists of a single loop with its one end.
    pub(crate) open spec fn is_loop_graph(self) -> bool {
        &&& self.edges.is_singleton()
        &&& self.edges.choose().is_loop()
        &&& {
            let a = self.edges.choose();
            self.vertices =~= set![a.tail]
        }
    }

    /// Returns if a graph is a link-graph.
    ///
    /// [Tutte, Section I.1] A link-graph consists of a single link with its two ends.
    pub(crate) open spec fn is_link_graph(self) -> bool {
        &&& self.edges.is_singleton()
        &&& self.edges.choose().is_link()
        &&& {
            let a = self.edges.choose();
            self.vertices =~= set![a.tail, a.head]
        }
    }

    /// Returns the set of edges incident with a vertex.
    pub(crate) open spec fn incident_edges(self, v: Vertex) -> Set<Edge>
        recommends
            self.vertices.contains(v),
    {
        self.edges.filter(|e: Edge| e.is_incident_to(v))
    }

    #[via_fn]
    proof fn incident_edges_to_valency_decreases(s: Set<Edge>) {
        assert(!s.is_empty() && s.finite() ==> s.len() > s.remove(s.choose()).len()) by {
            if !s.is_empty() && s.finite() {
                let e = s.choose();
                vstd::set::axiom_set_remove_len(s, e);
            }
        }
    }

    /// Computes the valency of a set of incident edges.
    pub(crate) open spec fn incident_edges_to_valency(s: Set<Edge>) -> nat
        decreases s.len(),
        when s.finite()
        via Self::incident_edges_to_valency_decreases
    {
        if s.is_empty() {
            0
        } else {
            let e = s.choose();
            if e.is_loop() {
                2 + Self::incident_edges_to_valency(s.remove(e))
            } else {
                1 + Self::incident_edges_to_valency(s.remove(e))
            }
        }
    }

    /// Returns the valency of a vertex.
    ///
    /// [Tutte, Section I.1] The valency of a vertex x in a graph G is the
    /// number of edges incident with x, loops being counted twice.
    pub(crate) open spec fn valency(self, v: Vertex) -> nat
        recommends
            self.vertices.contains(v),
    {
        Self::incident_edges_to_valency(self.incident_edges(v))
    }

    /// Returns if the graph is a subgraph of g.
    ///
    /// A graph S is a subgraph of a graph G if V(S) ⊆ V(G) and E(S) ⊆ E(G). We
    /// additionally require that a subgraph be well-formed due to the following
    /// rule on graph constructions:
    ///
    /// [Tutte, Rule I.4] Let G be a graph, P a subset of V(G) and Q a subset of
    /// E(G). Then the necessary and sufficient condition for the existence of a
    /// subgraph H of G such that V(H) = P and E(H) = Q is that P shall contain
    /// both ends of each member of Q.
    pub(crate) open spec fn is_subgraph_of(self, g: Self) -> bool {
        &&& self.vertices.subset_of(g.vertices)
        &&& self.edges.subset_of(g.edges)
        &&& forall|e: Edge|
            #![auto]
            self.edges.contains(e) ==> {
                &&& self.vertices.contains(e.tail)
                &&& self.vertices.contains(e.head)
            }
    }

    /// Returns the set of subgraphs in a graph.
    spec fn subgraphs(self) -> Set<Self> {
        Set::new(|h: Self| h.is_subgraph_of(self))
    }

    /// The `<=` operator, synonymous with [`Self::is_subgraph_of`].
    pub(crate) open spec fn spec_le(self, other: Self) -> bool {
        self.is_subgraph_of(other)
    }

    /// Returns if the graph is a proper subgraph of g.
    pub(crate) open spec fn is_proper_subgraph_of(self, g: Self) -> bool {
        &&& self <= g
        &&& !(self =~= g)
    }

    /// The `<` operator, synonymous with [`Self::is_proper_subgraph_of`].
    pub(crate) open spec fn spec_lt(self, other: Self) -> bool {
        self.is_proper_subgraph_of(other)
    }

    /// Returns if the graph is a spanning subgraph of g.
    ///
    /// A graph S is a spanning graph of a graph G if V(S) == V(G) and E(S) ⊆ E(G).
    pub(crate) open spec fn is_spanning_subgraph_of(self, g: Self) -> bool {
        &&& self.vertices =~= g.vertices
        &&& self.edges.subset_of(g.edges)
    }

    /// Returns the set of vertices v in the graph such that v is incident with
    /// a member of the given set of edges S.
    spec fn incident_vertices(self, s: Set<Edge>) -> Set<Vertex>
        recommends
            s.subset_of(self.edges),
    {
        self.vertices.filter(
            |v: Vertex|
                exists|e: Edge|
                    #![auto]
                    {
                        &&& s.contains(e)
                        &&& e.is_incident_to(v)
                    },
        )
    }

    /// Returns the reduction of a graph to the given set of edges S.
    spec fn reduction(self, s: Set<Edge>) -> Self
        recommends
            s.subset_of(self.edges),
    {
        Self { vertices: self.incident_vertices(s), edges: s }
    }

    /// Returns the subgraph induced by the given set of vertices.
    pub(crate) open spec fn induced_subgraph(self, s: Set<Vertex>) -> Self
        recommends
            s.subset_of(self.vertices),
    {
        Self {
            vertices: s,
            edges: self.edges.filter(
                |e: Edge|
                    {
                        &&& s.contains(e.tail)
                        &&& s.contains(e.head)
                    },
            ),
        }
    }

    /// Returns the null graph.
    pub(crate) open spec fn null() -> Self {
        Self { vertices: Set::empty(), edges: Set::empty() }
    }

    /// Returns the union of two graphs.
    pub closed spec fn union(self, other: Self) -> Self {
        Self { vertices: self.vertices + other.vertices, edges: self.edges + other.edges }
    }

    /// The `+` operator, synonymous with [`Self::union`].
    pub open spec fn spec_add(self, other: Self) -> Self {
        self.union(other)
    }

    /// Returns the intersection of two graphs.
    pub closed spec fn intersect(self, other: Self) -> Self {
        Self { vertices: self.vertices * other.vertices, edges: self.edges * other.edges }
    }

    /// The `*` operator, synonymous with [`Self::intersect`].
    pub open spec fn spec_mul(self, other: Self) -> Self {
        self.intersect(other)
    }

    /// Returns if the graph is disjoint from the other graph.
    pub(crate) open spec fn is_disjoint_from(self, other: Self) -> bool {
        &&& self.vertices.disjoint(other.vertices)
        &&& self.edges.disjoint(other.edges)
    }

    /// Returns if the graph is nonnull.
    pub(crate) open spec fn is_nonnull(self) -> bool {
        Self::null().is_proper_subgraph_of(self)
    }

    /// Returns if edge e is a edge of attachment of H in G.
    ///
    /// An edge of attachment of H in G is an edge of G that is incident to the
    /// given vertex v of H that is not an edge of H.
    pub(crate) open spec fn is_attachment_edge(self, h: Self, v: Vertex, e: Edge) -> bool
        recommends
            h.is_subgraph_of(self),
            h.vertices.contains(v),
    {
        &&& self.edges.contains(e)
        &&& e.is_incident_to(v)
        &&& !h.edges.contains(e)
    }

    /// Returns if vertex v is a vertex of attachment of H in G.
    ///
    /// A vertex of attachment of H in G is a vertex of H that is incident with
    /// some edge of G that is not an edge of H.
    pub(crate) open spec fn is_attachment_vertex(self, h: Self, v: Vertex) -> bool
        recommends
            h.is_subgraph_of(self),
            h.vertices.contains(v),
    {
        exists|e: Edge| self.is_attachment_edge(h, v, e)
    }

    /// Returns the set of vertices of attachment of the subgraph of H in G.
    ///
    /// The notation $$W(G, H)$$ indicates the set of vertices of attachment of H in G.
    pub(crate) open spec fn attachment_vertices(self, h: Self) -> Set<Vertex>
        recommends
            h.is_subgraph_of(self),
    {
        h.vertices.filter(|v: Vertex| self.is_attachment_vertex(h, v))
    }

    /// Returns the complement of a subgraph.
    ///
    /// [Tutte, Section I.4] Let H be a subgraph of a graph G. It follows from
    /// Rule I.4 that there is a subgraph $$H^c$$ of G such that
    ///
    ///     $$E(H^c) = E(G) - E(H)$$, and
    ///     $$V(H^c) = (V(G) - V(H)) \cup W(G, H)$$.
    spec fn subgraph_complement(self, h: Self) -> Self
        recommends
            h.is_subgraph_of(self),
    {
        Self {
            edges: self.edges - h.edges,
            vertices: (self.vertices - h.vertices) + self.attachment_vertices(h),
        }
    }

    /// Returns if a subgraph is detached.
    ///
    /// [Tutte, Section I.5] A subgraph H of a graph G is detached in G if it
    /// has no vertices of attachment in G.
    pub(crate) open spec fn is_detached_subgraph_of(self, g: Self) -> bool {
        &&& self.is_subgraph_of(g)
        &&& g.attachment_vertices(self).is_empty()
    }

    /// Returns if the graph is a nonnull and detached subgraph of G.
    pub(crate) open spec fn is_nonnull_detached_subgraph_of(self, g: Self) -> bool {
        &&& self.is_nonnull()
        &&& self.is_detached_subgraph_of(g)
    }

    /// Returns if a subgraph is a component.
    ///
    /// [Tutte, Section I.5] A component of G is a minimal nonnull detached
    /// subgraph of G, that is, a nonnull detached subgraph of G that contains
    /// no other nonnull detached subgraph of G.
    pub(crate) open spec fn is_component_of(self, g: Self) -> bool {
        &&& self.is_nonnull_detached_subgraph_of(g)
        &&& forall|s: Self|
            #![auto]
            {
                &&& !(s =~= self)
                &&& s.is_nonnull_detached_subgraph_of(g)
            } ==> !s.is_subgraph_of(self)
    }

    /// Returns a graph's set of components.
    pub(crate) open spec fn components(self) -> Set<Self> {
        Set::new(|c: Self| c.is_component_of(self))
    }

    /// Returns the component number of a graph.
    ///
    /// [Tutte, Section I.5] We denote the number of components of a graph G by
    /// $$p_0(G)$$. In the terminology of algebraic topology, it is "the Betti
    /// number of G of dimension 0".
    pub(crate) open spec fn component_number(self) -> nat {
        self.components().len()
    }

    /// Returns if a nonnull graph is connected.
    ///
    /// [Tutte, Section I.5] If $$p_0(G) = 1$$, we say that G is connected.
    pub(crate) open spec fn is_connected(self) -> bool {
        self.component_number() == 1
    }

    /// Returns if a nonnull graph is disconnected.
    ///
    /// [Tutte, Section I.5] If $$p_0(G) > 1$$, we say that G is disconnected.
    spec fn is_disconnected(self) -> bool {
        self.component_number() > 1
    }

    /// Removes edge A from graph G and returns the resulting graph.
    ///
    /// [Tutte, Section I.6] The [operation of deleting an edge A from a graph
    /// G] replaces G by its spanning subgraph G: (E(G) - {A}), which we denote
    /// also by the simpler symbol $$G'_A$$.
    pub(crate) open spec fn remove_edge(self, a: Edge) -> Self
        recommends
            self.edges.contains(a),
    {
        Self { vertices: self.vertices, edges: self.edges.remove(a) }
    }

    /// Returns if a graph is a forest.
    ///
    /// [Tutte, Section I.6] A graph in which every edge is an isthmus is called
    /// a forest.
    pub(crate) open spec fn is_forest(self) -> bool {
        forall|a: Edge| #![auto] self.edges.contains(a) ==> a.is_isthmus_of(self)
    }

    /// Returns if a graph is a tree.
    ///
    /// [Tutte, Section I.6] A connected forest is a tree.
    pub(crate) open spec fn is_tree(self) -> bool {
        &&& self.is_forest()
        &&& self.is_connected()
    }

    /// Returns if a graph is a spanning tree of G.
    pub(crate) open spec fn is_spanning_tree_of(self, g: Self) -> bool {
        &&& self.is_tree()
        &&& self.is_spanning_subgraph_of(g)
    }

    /// Returns the cyclomatic number of a graph.
    ///
    /// [Tutte, Section I.6] We define the cyclomatic number $$p_1(G)$$ of a
    /// graph G, also known as the Betti number of dimension 1, by the following
    /// equation:
    ///
    ///     $$p_1(G) = |E(G)| - |V(G)| + p_0(G)$$.
    ///
    /// This returns an `int` instead of a `nat` since Verus can't infer that
    /// $$p_1(G)$$ is nonnegative; that is shown by Theorem I.35.
    spec fn cyclomatic_number(self) -> int {
        self.edges.len() - self.vertices.len() + self.component_number()
    }

    /// The set of edges incident with a vertex in a finite graph is finite.
    proof fn lemma_incident_edges_finite(self, v: Vertex)
        requires
            self.well_formed(),
            self.vertices.contains(v),
        ensures
            self.incident_edges(v).finite(),
    {
    }

    /// A set of subgraphs in a finite graph G is finite.
    proof fn axiom_subgraphs_is_finite(self)
        requires
            self.well_formed(),
        ensures
            self.subgraphs().finite(),
    {
        admit()
    }

    /// The union of two subgraphs is a subgraph.
    proof fn lemma_subgraph_union_is_subgraph(self, h: Self, k: Self)
        requires
            h.is_subgraph_of(self),
            k.is_subgraph_of(self),
        ensures
            (h + k).is_subgraph_of(self),
    {
        // NOTE: Verus automatically proves this.
    }

    /// A finite graph G has a finite set of components.
    proof fn lemma_components_are_finite(self)
        requires
            self.well_formed(),
        ensures
            self.components().finite(),
    {
        // Let T be the set of subgraphs in G and S be the set of components in G.
        let t = self.subgraphs();
        let s = self.components();

        // By definition, S is a subset of T. Thus, S is finite since T is finite.
        assert(s.finite()) by {
            assert(s.subset_of(t));
            assert(t.finite()) by {
                self.axiom_subgraphs_is_finite();
            }
            vstd::set_lib::lemma_set_subset_finite(t, s);
        }
    }

    /// An isolated vertex v in graph G has no incident edges in G.
    proof fn lemma_isolation_implies_no_incident_edges(self, v: Vertex)
        requires
            self.well_formed(),
            self.vertices.contains(v),
            v.is_isolated_in(self),
        ensures
            self.incident_edges(v).is_empty(),
    {
        // Let S be the set of edges incident with v in G. Assume that S is not empty.
        let s = self.incident_edges(v);
        if !s.is_empty() {
            // Let T be a set containing a single edge from S. By construction, T is
            // a subset of S.
            let t = set![s.choose()];
            assert(t.subset_of(s));

            // By definition, the valency computed from T is greater than 0. This
            // contradicts the precondition that v is isolated in G.
            reveal_with_fuel(Graph::incident_edges_to_valency, 2);
            assert(Graph::incident_edges_to_valency(t) > 0);
            assert(!v.is_isolated_in(self));
            assert(false);
        }
    }

    /// A vertex v that is incident with an edge A in graph G is not isolated in G.
    proof fn lemma_incident_edge_implies_non_isolation(self, v: Vertex, a: Edge)
        requires
            self.well_formed(),
            self.vertices.contains(v),
            self.edges.contains(a),
            a.is_incident_to(v),
        ensures
            !v.is_isolated_in(self),
    {
        // Get the set of witness edges and incident edges.
        // Let S be the set of edges incident with v in G, and T be the set
        // containing A.
        let s = self.incident_edges(v);
        let t = set![a];

        // By construction, T is a subset of S. By definition, the valency computed
        // from T is greater than 0. Thus, the valency of v must be greater than 0,
        // which means that it is not isolated.
        assert(self.valency(v) > 0) by {
            assert(t.subset_of(s));
            reveal_with_fuel(Graph::incident_edges_to_valency, 2);
            assert(Graph::incident_edges_to_valency(t) > 0);
        }
    }

    /// A vertex v that is monovalent in graph G has one incident edge in G.
    proof fn lemma_monovalency_implies_one_incident_edge(self, v: Vertex)
        requires
            self.well_formed(),
            self.vertices.contains(v),
            v.is_monovalent_in(self),
        ensures
            self.incident_edges(v).len() == 1,
    {
        // Let S be the set of edges in H that are incident with x.
        let s = self.incident_edges(v);

        // There must be an edge A incident with v since v is monovalent.
        assert(s.len() > 0);
        let a = s.choose();

        // Assume that there isn't a single incident edge of v.
        if s.len() != 1 {
            // There must be another edge B incident with v.
            assert(s.len() >= 2);
            let b = s.remove(a).choose();

            // Let T be a set containing A and B. By definition, the valency of T is
            // greater than 1, which contradicts the precondition of v being
            // monovalent.
            let t = set![a, b];
            reveal_with_fuel(Graph::incident_edges_to_valency, 3);
            assert(Graph::incident_edges_to_valency(t) > 1);
            assert(!v.is_monovalent_in(self));
            assert(false);
        }
    }

    /// The incident edge of a monovalent vertex v in G is a link-edge.
    proof fn lemma_incident_edge_of_monovalent_vertex_is_link(self, v: Vertex, a: Edge)
        requires
            self.well_formed(),
            self.vertices.contains(v),
            self.edges.contains(a),
            v.is_monovalent_in(self),
            a.is_incident_to(v),
        ensures
            a.is_link(),
    {
        let s = self.incident_edges(v);

        // Since v is monovalent, A must be its only incident edge.
        assert(set![a] =~= s) by {
            assert(s.is_singleton()) by {
                self.lemma_monovalency_implies_one_incident_edge(v);
            }
            assert(s.contains(a));
        }

        // Assume that A is not a link (i.e., it is a loop).
        if a.is_loop() {
            // By definition, the valency of S is 2, which contradicts the
            // precondition of v being monovalent.
            reveal_with_fuel(Graph::incident_edges_to_valency, 2);
            assert(Graph::incident_edges_to_valency(s) == 2);
            assert(!v.is_monovalent_in(self));
            assert(false);
        }
    }

    /// The null graph is a subgraph of any graph G.
    proof fn lemma_graph_has_null_subgraph(self)
        ensures
            Self::null().is_subgraph_of(self),
    {
        // NOTE: Verus automatically proves this.
    }

    /// The intersection of two subgraphs is a subgraph.
    proof fn lemma_subgraph_intersection_exists(self, h: Self, k: Self)
        requires
            h.is_subgraph_of(self),
            k.is_subgraph_of(self),
        ensures
            (h * k).is_subgraph_of(self),
    {
        // NOTE: Verus automatically proves this.
    }

    /// [Tutte, Theorem I.5] Any subgraph of a subgraph of G is a subgraph of G.
    proof fn lemma_subgraph_transitivity(self, h: Self, k: Self)
        requires
            h.is_subgraph_of(self),
            k.is_subgraph_of(h),
        ensures
            k.is_subgraph_of(self),
    {
        // NOTE: Verus automatically proves this.
    }

    /// Any vertex of attachment of H in G is a vertex of G and H.
    proof fn lemma_attachment_vertex_membership(self, h: Self)
        requires
            h.is_subgraph_of(self),
        ensures
            forall|v: Vertex|
                #![auto]
                self.attachment_vertices(h).contains(v) ==> self.vertices.contains(v),
            forall|v: Vertex|
                #![auto]
                self.attachment_vertices(h).contains(v) ==> h.vertices.contains(v),
    {
        // NOTE: Verus automatically proves this.
    }

    /// The set of vertices of attachment is finite.
    proof fn lemma_attachment_vertices_finite(self, h: Self)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
        ensures
            self.attachment_vertices(h).finite(),
    {
        // The set of vertices of attachment of H is a subset of the vertices in
        // H. Since the set of vertices in H is finite, the set of vertices of
        // attachment of H must also be finite.
        let wh = self.attachment_vertices(h);
        assert(wh.finite()) by {
            assert(h.vertices.finite());
            assert(wh.subset_of(h.vertices));
            vstd::set_lib::lemma_set_subset_finite(h.vertices, wh);
        }
    }

    /// [Tutte, Theorem I.13] If H and K are detached subgraphs of G, then so
    /// are $$H \cup K$$ and $$H \cap K$$.
    proof fn lemma_h_and_k_detached_implies_huk_and_hnk_detached(self, h: Self, k: Self)
        requires
            self.well_formed(),
            h.is_detached_subgraph_of(self),
            k.is_detached_subgraph_of(self),
        ensures
            (h + k).is_detached_subgraph_of(self),
            (h * k).is_detached_subgraph_of(self),
    {
        assert((h + k).is_detached_subgraph_of(self)) by {
            self.lemma_wghuk_or_wghnk_contains_iff_wgh_or_wgk_contains(h, k);
        }

        assert((h * k).is_detached_subgraph_of(self)) by {
            self.lemma_wghuk_or_wghnk_contains_iff_wgh_or_wgk_contains(h, k);
        }
    }

    /// [Tutte, Theorem I.14] If H is a detached subgraph of G, then the
    /// complementary subgraph $$H^c$$ to H in G is detached in G. Moreover,
    /// $$H^c$$ is disjoint from H, and $$H^{cc} = H$$.
    proof fn lemma_complement_of_detached_subgraph_is_detached_and_disjoint(self, h: Self)
        requires
            self.well_formed(),
            h.is_detached_subgraph_of(self),
        ensures
            self.subgraph_complement(h).is_detached_subgraph_of(self),
            self.subgraph_complement(h).is_disjoint_from(h) ==> self.subgraph_complement(
                self.subgraph_complement(h),
            ) =~= h,
    {
        admit()
    }

    /// [Tutte, Theorem I.15] A detached subgraph of a detached subgraph of G is
    /// a detached subgraph of G.
    proof fn lemma_detached_subgraph_of_subgraph_is_subgraph_of(self, h: Self, k: Self)
        requires
            self.well_formed(),
            h.is_detached_subgraph_of(self),
            k.is_detached_subgraph_of(h),
        ensures
            k.is_detached_subgraph_of(self),
    {
        assert(k.is_detached_subgraph_of(self)) by {
            self.lemma_wkh_contains_implies_wgk_contains(h, k);
        }
    }

    /// [Tutte, Theorem I.16] If H is a nonnull detached subgraph of G, then
    /// there is a component C of G such that $$C \subseteq H$$.
    proof fn lemma_nonnull_detached_subgraph_implies_component(self, h: Self)
        requires
            self.well_formed(),
            h.is_nonnull_detached_subgraph_of(self),
        ensures
            exists|c: Self|
                #![auto]
                {
                    &&& c.is_component_of(self)
                    &&& c.is_subgraph_of(h)
                },
    {
        admit()
    }

    /// A vertex graph is nonnull.
    proof fn lemma_vertex_graph_is_nonnull(self, x: Vertex)
        requires
            self.well_formed(),
            self.vertices.contains(x),
        ensures
            Self::vertex_graph(x).is_nonnull(),
    {
        // Let H be the null graph and K be a vertex-graph defined by vertex x. We
        // show that K is nonnull by demonstrating that H is a proper subgraph of K.
        let h = Self::null();
        let k = Self::vertex_graph(x);

        // V(H) and E(H) are subsets of V(K) and V(H), respectively.
        assert(h.vertices.subset_of(k.vertices));
        assert(h.edges.subset_of(k.edges));

        // H is distinct from K since it has less vertices than K.
        assert(!(h =~= k)) by {
            assert(h.vertices.len() < k.vertices.len());
        }
    }

    /// The resulting graph of an edge deletion operation is well-formed.
    proof fn lemma_remove_edge_preserves_well_formedness(self, a: Edge)
        requires
            self.well_formed(),
            self.edges.contains(a),
        ensures
            self.remove_edge(a).well_formed(),
    {
        // NOTE: Verus automatically proves this.
    }

    /// [Tutte, Theorem I.21] A graph G is connected if and only if no nonnull
    /// proper subgraph of G is detached in G, provided that G itself is nonnull.
    proof fn lemma_connected_iff_no_nonnull_proper_subgraph_is_detached(self)
        requires
            self.well_formed(),
            self.is_nonnull(),
        ensures
            forall|h: Self|
                #![auto]
                {
                    &&& h.is_nonnull()
                    &&& h.is_proper_subgraph_of(self)
                } ==> !h.is_detached_subgraph_of(self),
    {
        admit()
    }

    /// [Tutte, Theorem I.35] The cyclomatic number of a graph G is nonnegative. It
    /// is zero if and only if G is a forest.
    proof fn lemma_cyclomatic_number_properties(self)
        requires
            self.well_formed(),
        ensures
            self.cyclomatic_number() >= 0,
            self.cyclomatic_number() == 0 <==> self.is_forest(),
    {
        admit()
    }

    /// [Tutte, Theorem I.6] Let H and K be subgraphs of a graph G. Then each
    /// vertex of attachment of $$H \cup K$$ or $$H \cap K$$ is a vertex of
    /// attachment of H or K. On the other hand, each vertex of attachment of H
    /// is a vertex of attachment of $$H \cup K$$ or $$H \cap K$$.
    proof fn lemma_wghuk_or_wghnk_contains_iff_wgh_or_wgk_contains(self, h: Self, k: Self)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
            k.is_subgraph_of(self),
        ensures
            forall|v: Vertex|
                #![auto]
                {
                    ||| self.attachment_vertices(h + k).contains(v)
                    ||| self.attachment_vertices(h * k).contains(v)
                } <==> {
                    ||| self.attachment_vertices(h).contains(v)
                    ||| self.attachment_vertices(k).contains(v)
                },
    {
        assert forall|v: Vertex| #![auto] self.attachment_vertices(h + k).contains(v) implies {
            ||| self.attachment_vertices(h).contains(v)
            ||| self.attachment_vertices(k).contains(v)
        } by {
            let wghuk = self.attachment_vertices(h + k);
            self.lemma_wghuk_implies_wgh_or_wgk_contains(h, k, wghuk);
        }

        assert forall|v: Vertex| #![auto] self.attachment_vertices(h * k).contains(v) implies {
            ||| self.attachment_vertices(h).contains(v)
            ||| self.attachment_vertices(k).contains(v)
        } by {
            let wghnk = self.attachment_vertices(h * k);
            self.lemma_wghnk_implies_wgh_or_wgk_contains(h, k, wghnk);
        }

        assert forall|v: Vertex| #![auto] self.attachment_vertices(h).contains(v) implies {
            ||| self.attachment_vertices(h + k).contains(v)
            ||| self.attachment_vertices(h * k).contains(v)
        } by {
            let wgh = self.attachment_vertices(h);
            self.lemma_wgh_implies_wghuk_or_wghnk_contains(h, k, wgh);
        }

        assert forall|v: Vertex| #![auto] self.attachment_vertices(k).contains(v) implies {
            ||| self.attachment_vertices(h + k).contains(v)
            ||| self.attachment_vertices(h * k).contains(v)
        } by {
            let wgk = self.attachment_vertices(k);
            self.lemma_wgk_implies_wghuk_or_wghnk_contains(h, k, wgk);
        }
    }

    /// [Tutte, Theorem I.8] Let K be a subgraph of a subgraph H of a graph G.
    /// Then each vertex of attachment of K in H is a vertex of attachment of K
    /// in G. Moreover, each vertex of attachment of K in G is either a vertex
    /// of attachment of K in H or a vertex of attachment of H in G.
    proof fn lemma_wkh_contains_implies_wgk_contains(self, h: Self, k: Self)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
            k.is_subgraph_of(h),
        ensures
            forall|v: Vertex|
                h.attachment_vertices(k).contains(v) ==> self.attachment_vertices(k).contains(v),
            forall|v: Vertex|
                self.attachment_vertices(k).contains(v) ==> {
                    ||| h.attachment_vertices(k).contains(v)
                    ||| self.attachment_vertices(h).contains(v)
                },
    {
        admit()
    }

    /// A isthmus A of finite graph G has a finite set of end-graphs.
    proof fn lemma_end_graphs_are_finite(self, a: Edge)
        requires
            self.well_formed(),
            a.is_isthmus_of(self),
        ensures
            a.end_graphs_in(self).finite(),
    {
        // Let H be the graph obtained by deleting A from G.
        let h = self.remove_edge(a);

        // By definition, H has a finite set of components.
        assert(h.components().finite()) by {
            h.lemma_components_are_finite();
        }

        // By definition, the set of end-graphs of A in G is the set of components of H.
        assert(a.end_graphs_in(self) =~= h.components());
    }

    /// The complementary subgraph of H in G is a well-formed subgraph of G.
    proof fn lemma_subgraph_complement_is_subgraph(self, h: Self)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
        ensures
            self.subgraph_complement(h).is_subgraph_of(self),
    {
        // Let $$H^c$$ be the complementary subgraph of H in G.
        let hc = self.subgraph_complement(h);

        // By definition, $$E(H^c) \subseteq E(G)$$ and $$V(H^c) \subseteq V(G)$$.
        // For Rule I.4, we need to demonstrate that $$H^c$$ is well-formed. We
        // start by assuming that $$H^c$$ is not well-formed.
        if !forall|e: Edge|
            #![auto]
            hc.edges.contains(e) ==> {
                &&& hc.vertices.contains(e.tail)
                &&& hc.vertices.contains(e.head)
            } {
            // There must exist an edge A in $$H^c$$ that is incident to a
            // vertex not in $$H^c$$.
            assert(exists|a: Edge|
                #![auto]
                {
                    &&& hc.edges.contains(a)
                    &&& {
                        ||| !hc.vertices.contains(a.tail)
                        ||| !hc.vertices.contains(a.head)
                    }
                });
            let a = choose|a: Edge|
                #![auto]
                {
                    &&& hc.edges.contains(a)
                    &&& {
                        ||| !hc.vertices.contains(a.tail)
                        ||| !hc.vertices.contains(a.head)
                    }
                };

            // We know that E(H) does not contain A since A is contained in $$E(H^c)$$.
            assert(!h.edges.contains(a));

            // Assume that tail(A) is not in $$V(H^c)$$.
            if !hc.vertices.contains(a.tail) {
                // By definition, tail(A) is neither in W(G, H) or in V(G) - V(H).
                assert(!self.attachment_vertices(h).contains(a.tail));
                assert(!(self.vertices - h.vertices).contains(a.tail));

                // Assume that tail(A) is not in W(G, H). In order for tail(A)
                // to not be in V(G) - V(H), tail(A) must be in V(H). Since A is
                // not in E(H), tail(A) is by definition a vertex of attachment
                // of H in G, which contradicts tail(A) not being in W(G, H).
                if !self.attachment_vertices(h).contains(a.tail) {
                    assert(h.vertices.contains(a.tail));
                    assert(self.is_attachment_edge(h, a.tail, a));
                    assert(false);
                }
            }
            // We know that head(A) is not in $$V(H^c)$$.

            if !hc.vertices.contains(a.head) {
                // By definition, head(A) is neither in W(G, H) or in V(G) - V(H).
                assert(!self.attachment_vertices(h).contains(a.head));
                assert(!(self.vertices - h.vertices).contains(a.head));

                // Assume that head(A) is not in W(G, H). In order for head(A)
                // to not be in V(G) - V(H), head(A) must be in V(H). Since A is
                // not in E(H), head(A) is by definition a vertex of attachment
                // of H in G, which contradicts head(A) not being in W(G, H).
                if !self.attachment_vertices(h).contains(a.head) {
                    assert(h.vertices.contains(a.head));
                    assert(self.is_attachment_edge(h, a.head, a));
                    assert(false);
                }
            }
        }
    }

    /// [Tutte, Theorem I.22] Each component of a graph G is a connected graph.
    pub(crate) proof fn lemma_components_are_connected(self)
        requires
            self.well_formed(),
        ensures
            forall|c: Self| #![auto] c.is_component_of(self) ==> c.is_connected(),
    {
        admit()
    }

    /// [Tutte, Theorem I.23] Let H be a subgraph of G. Then H is a component of G
    /// if and only if it is both detached in G and connected.
    proof fn lemma_component_iff_detached_and_connected(self, h: Self)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
        ensures
            h.is_component_of(self) <==> {
                &&& h.is_detached_subgraph_of(self)
                &&& h.is_connected()
            },
    {
        admit()
    }

    /// [Tutte, Theorem I.29] Let A be an edge of a graph G. If A is not an isthmus
    /// of G, then $$p_0(G'_A) = p_0(G)$$. But if A is an isthmus of G, then $$p_0(G'_A) = p_0(G) + 1$$.
    pub(crate) proof fn lemma_isthmus_increases_components(self, a: Edge)
        requires
            self.well_formed(),
            self.edges.contains(a),
        ensures
            if a.is_isthmus_of(self) {
                self.remove_edge(a).component_number() == self.component_number() + 1
            } else {
                self.remove_edge(a).component_number() == self.component_number()
            },
    {
        admit()
    }

    /// [Tutte, Section I.6] The single edge of a link-graph is an isthmus.
    pub(crate) proof fn lemma_link_graph_edge_is_isthmus(self, a: Edge)
        requires
            self.well_formed(),
            self.is_link_graph(),
            self.edges.contains(a),
        ensures
            a.is_isthmus_of(self),
    {
        // Let H be the resulting graph of removing A from G (i.e., $$H = C'_A$$).
        let h = self.remove_edge(a);

        // Both ends of A are in V(H) since they are both in V(G).
        assert(h.vertices.contains(a.tail));
        assert(h.vertices.contains(a.head));

        // Both ends of A are isolated in H since A is not in H.
        assert(a.tail.is_isolated_in(h));
        assert(a.head.is_isolated_in(h));

        // Let C and D be vertex-graphs defined by the ends of A.
        let c = Self::vertex_graph(a.tail);
        let d = Self::vertex_graph(a.head);

        // By Theorem I.19, C and D are both components of H.
        assert({
            &&& c.is_component_of(h)
            &&& d.is_component_of(h)
        }) by {
            h.lemma_isolated_vertex_graph_is_component(a.tail);
            h.lemma_isolated_vertex_graph_is_component(a.head);
        }

        // Since C and D are the only components of H, they must be contained in the
        // set of components of H. It is unclear why Verus needs this to be asserted
        // given that we've shown that both C and D are components.
        assert({
            &&& h.components().contains(c)
            &&& h.components().contains(d)
        }) by {
            assert(set![c, d] =~= h.components());
        }

        // By construction, each end of A is either in C or D.
        assert({
            &&& c.vertices.contains(a.tail)
            &&& !c.vertices.contains(a.head)
            &&& !d.vertices.contains(a.tail)
            &&& d.vertices.contains(a.head)
        });
    }

    /// [Tutte, Theorem I.37] If T is any tree, then $$|V(T)| = |E(T) + 1|$$.
    pub(crate) proof fn lemma_tree_vertices_exceed_edges_by_one(self)
        requires
            self.well_formed(),
            self.is_tree(),
        ensures
            self.vertices.len() == self.edges.len() + 1,
    {
        // Since T is connected, we have $$p_0(T) = 1$$.
        assert(self.component_number() == 1);

        // Since T is a forest, we have $$p_1(T) = 0$$ by Theorem I.35. Verus
        // completes the rest of the proof with the definition of a graph's
        // cyclomatic number.
        assert(self.cyclomatic_number() == 0) by {
            self.lemma_cyclomatic_number_properties();
        }
    }

    /// A vertex x that is contained in a graph G is contained in a component of G.
    proof fn lemma_vertex_contained_in_component(self, x: Vertex)
        requires
            self.well_formed(),
            self.vertices.contains(x),
        ensures
            exists|c: Self|
                #![auto]
                {
                    &&& c.is_component_of(self)
                    &&& c.vertices.contains(x)
                },
    {
        admit();
    }

    /// [Tutte, Theorem I.19] Let x be an isolated vertex of G. Then the
    /// corresponding vertex-graph is a component of G.
    pub(crate) proof fn lemma_isolated_vertex_graph_is_component(self, x: Vertex)
        requires
            self.well_formed(),
            self.vertices.contains(x),
            x.is_isolated_in(self),
        ensures
            Self::vertex_graph(x).is_component_of(self),
    {
        // Let H be a vertex-graph defined by vertex x.
        let h = Self::vertex_graph(x);

        // H is nonnull since vertex-graphs are nonnull.
        assert(h.is_nonnull()) by {
            self.lemma_vertex_graph_is_nonnull(x);
        }

        // H is a detached subgraph of G since x is isolated in G. Thus, there are
        // no vertices of attachment of H in G since there are no edges incident
        // with x in G.
        assert(h.is_detached_subgraph_of(self)) by {
            assert(h.is_subgraph_of(self));
            assert(self.attachment_vertices(h).is_empty()) by {
                assert(self.incident_edges(x).is_empty()) by {
                    self.lemma_isolation_implies_no_incident_edges(x);
                }
            }
        }

        // H doesn't contain any nonnull subgraphs since it is a vertex-graph.
        assert(forall|k: Self|
            {
                &&& !(k =~= h)
                &&& k.is_nonnull_detached_subgraph_of(h)
            } ==> !k.is_subgraph_of(h));
    }

    /// Any vertex graph G is well-formed.
    pub(crate) proof fn lemma_vertex_graph_is_well_formed(self)
        requires
            self.is_vertex_graph(),
        ensures
            self.well_formed(),
    {
        // By definition, E(G) is empty and thus finite.
        assert(self.edges.is_empty());

        // By definition, E(G) is a singleton containing just a vertex v.
        assert(self.vertices.is_singleton());
        assert(self.vertices.len() == 1) by {
            self.vertices.lemma_singleton_size();
        }

        // V(G) must be finite since it is equivalent to a finite set that only
        // contains v.
        let v = self.vertices.choose();
        assert(self.vertices.finite()) by {
            assert(set![v] =~= self.vertices);
        }
    }

    /// [Tutte, Theorem I.17] Distinct components of G are disjoint.
    pub(crate) proof fn lemma_distinct_components_are_disjoint(self, h: Self, k: Self)
        requires
            self.well_formed(),
            h.is_component_of(self),
            k.is_component_of(self),
            !(h =~= k),
        ensures
            h.is_disjoint_from(k),
    {
        // Assume that H and K are not disjoint.
        if !h.is_disjoint_from(k) {
            // There must be a vertex v in both V(H) and V(K).
            assert(exists|v: Vertex|
                #![auto]
                {
                    &&& h.vertices.contains(v)
                    &&& k.vertices.contains(v)
                });
            let v = choose|v: Vertex|
                #![auto]
                {
                    &&& h.vertices.contains(v)
                    &&& k.vertices.contains(v)
                };

            // By definition, v is contained in $$H \cap K$$.
            let hnk = h * k;
            assert(hnk.vertices.contains(v));

            // By Theorem I.13, $$H \cap K$$ is a nonnull detached subgraph of G,
            // which contradicts the minimality of H and K.
            assert(hnk.is_nonnull_detached_subgraph_of(self)) by {
                self.lemma_h_and_k_detached_implies_huk_and_hnk_detached(h, k);
            }
            assert(false);
        }
    }

    /// Let H and K be subgraphs of a graph G. Then,
    ///
    ///     $$\forall v \in W(G, H \cup K) \implies v \in W(G, H) \lor v \in W(G, K)$$.
    ///
    /// This is a recursive helper proof for
    /// [`Self::lemma_attachment_vertex_in_component_attachment_vertices`].
    proof fn lemma_wghuk_implies_wgh_or_wgk_contains(self, h: Self, k: Self, whuk: Set<Vertex>)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
            k.is_subgraph_of(self),
            whuk.subset_of(self.attachment_vertices(h + k)),
        ensures
            forall|v: Vertex|
                #![auto]
                whuk.contains(v) ==> {
                    ||| self.attachment_vertices(h).contains(v)
                    ||| self.attachment_vertices(k).contains(v)
                },
        decreases whuk.len(),
    {
        if whuk.is_empty() {
            // Base case: the set of attachment vertices is empty.
        } else {
            // Choose an arbitrary vertex v from W(G, H ∪ K).
            let v = whuk.choose();

            // There must be an edge A of G that is incident with v that is not
            // an edge of H or K.
            assert(exists|a: Edge|
                #![auto]
                {
                    &&& self.edges.contains(a)
                    &&& a.is_incident_to(v)
                    &&& !h.edges.contains(a)
                    &&& !k.edges.contains(a)
                });
            let a = choose|a: Edge|
                #![auto]
                {
                    &&& self.edges.contains(a)
                    &&& a.is_incident_to(v)
                    &&& !h.edges.contains(a)
                    &&& !k.edges.contains(a)
                };

            // We know that v must be a vertex of attachment for whichever
            // subgraph H or K it belongs to.
            if h.vertices.contains(v) {
                assert(self.attachment_vertices(h).contains(v)) by {
                    assert(self.is_attachment_edge(h, v, a));
                }
            } else {
                assert(self.attachment_vertices(k).contains(v)) by {
                    assert(self.is_attachment_edge(k, v, a));
                }
            }

            // The proof is completed inductively on the set of attachment
            // vertices without v.
            self.lemma_wghuk_implies_wgh_or_wgk_contains(h, k, whuk.remove(v));
        }
    }

    /// Let H and K be subgraphs of a graph G. Then,
    ///
    ///     $$\forall v \in V(G). v \in W(G, H \cap K) \implies v \in W(G, H) \lor W(G, K)$$.
    ///
    /// This is a recursive helper proof for
    /// [`g::lemma_attachment_vertex_in_component_attachment_vertices`].
    proof fn lemma_wghnk_implies_wgh_or_wgk_contains(self, h: Self, k: Self, whnk: Set<Vertex>)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
            k.is_subgraph_of(self),
            whnk.subset_of(self.attachment_vertices(h * k)),
        ensures
            forall|v: Vertex|
                #![auto]
                whnk.contains(v) ==> {
                    ||| self.attachment_vertices(h).contains(v)
                    ||| self.attachment_vertices(k).contains(v)
                },
        decreases whnk.len(),
    {
        if whnk.is_empty() {
            // Base case: the set of attachment vertices is empty.
        } else {
            // Choose an arbitrary vertex v from W(G, H ∩ K).
            let v = whnk.choose();

            // There must be an edge A in G that is incident with v that belongs
            // to one of H or K, but not to both.
            assert(exists|a: Edge|
                #![auto]
                {
                    &&& self.edges.contains(a)
                    &&& a.is_incident_to(v)
                    &&& {
                        ||| !h.edges.contains(a)
                        ||| !k.edges.contains(a)
                    }
                });
            let a = choose|a: Edge|
                #![auto]
                {
                    &&& self.edges.contains(a)
                    &&& a.is_incident_to(v)
                    &&& {
                        ||| !h.edges.contains(a)
                        ||| !k.edges.contains(a)
                    }
                };

            // We know that v is a vertex of attachment of whichever subgraph H
            // or K does not have A as an edge.
            if !h.edges.contains(a) {
                assert(self.attachment_vertices(h).contains(v)) by {
                    assert(self.is_attachment_edge(h, v, a));
                }
            } else {
                assert(self.attachment_vertices(k).contains(v)) by {
                    assert(self.is_attachment_edge(k, v, a));
                }
            }

            // The proof is completed inductively on the set of attachment
            // vertices without v.
            self.lemma_wghnk_implies_wgh_or_wgk_contains(h, k, whnk.remove(v));
        }
    }

    /// Let H and K be subgraphs of a graph G. Then,
    ///
    ///     $$\forall v \in V(G). v \in W(G, H) \implies v \in W(G, H \cup K) \lor v \in W(G, H \cap K)$$.
    ///
    /// This is a recursive helper proof for
    /// [`Self::lemma_attachment_vertex_in_component_attachment_vertices`].
    proof fn lemma_wgh_implies_wghuk_or_wghnk_contains(self, h: Self, k: Self, wgh: Set<Vertex>)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
            k.is_subgraph_of(self),
            wgh.subset_of(self.attachment_vertices(h)),
        ensures
            forall|v: Vertex|
                #![auto]
                wgh.contains(v) ==> {
                    ||| self.attachment_vertices(h + k).contains(v)
                    ||| self.attachment_vertices(h * k).contains(v)
                },
        decreases wgh.len(),
    {
        if wgh.is_empty() {
            // Base case: the set of attachment vertices is empty.
        } else {
            // Choose an arbitrary vertex from W(G, H).
            let v = wgh.choose();

            // There must be an edge A of G that is incident with v that is not
            // an edge of H.
            assert(exists|a: Edge|
                #![auto]
                {
                    &&& self.edges.contains(a)
                    &&& a.is_incident_to(v)
                    &&& !h.edges.contains(a)
                });
            let a = choose|a: Edge|
                #![auto]
                {
                    &&& self.edges.contains(a)
                    &&& a.is_incident_to(v)
                    &&& !h.edges.contains(a)
                };

            // If A is not in E(K), then v is a vertex of attachment of H ∪ K.
            // Otherwise, v is a vertex of attachment of H ∩ K.
            if !k.edges.contains(a) {
                assert(self.attachment_vertices(h + k).contains(v)) by {
                    assert(self.is_attachment_edge(h + k, v, a));
                }
            } else {
                assert(self.attachment_vertices(h * k).contains(v)) by {
                    assert(self.is_attachment_edge(h * k, v, a));
                }
            }

            // The proof is completed inductively on the set of attachment
            // vertices without v.
            self.lemma_wgh_implies_wghuk_or_wghnk_contains(h, k, wgh.remove(v));
        }
    }

    /// Let H and K be subgraphs of a graph G. Then,
    ///
    ///     $$\forall v \in V(G). v \in W(G, K) \implies v \in W(G, H \cup K) \lor v \in W(G, H \cap K)$$.
    ///
    /// This is a recursive helper proof for
    /// [`Self::lemma_attachment_vertex_in_component_attachment_vertices`].
    ///
    /// It isn't clear why Verus doesn't allow
    /// [`Self::lemma_wgh_implies_wghuk_or_wghnk_contains`] to be reused with H and
    /// K supplied in reverse order as inputs.
    proof fn lemma_wgk_implies_wghuk_or_wghnk_contains(self, h: Self, k: Self, wgk: Set<Vertex>)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
            k.is_subgraph_of(self),
            wgk.subset_of(self.attachment_vertices(k)),
        ensures
            forall|v: Vertex|
                #![auto]
                wgk.contains(v) ==> {
                    ||| self.attachment_vertices(h + k).contains(v)
                    ||| self.attachment_vertices(h * k).contains(v)
                },
        decreases wgk.len(),
    {
        if wgk.is_empty() {
            // Base case: the set of attachment vertices is empty.
        } else {
            // Choose an arbitrary vertex from W(G, K).
            let v = wgk.choose();

            // There must be an edge A of G that is incident with v that is not
            // an edge of K.
            assert(exists|a: Edge|
                #![auto]
                {
                    &&& self.edges.contains(a)
                    &&& a.is_incident_to(v)
                    &&& !k.edges.contains(a)
                });
            let a = choose|a: Edge|
                #![auto]
                {
                    &&& self.edges.contains(a)
                    &&& a.is_incident_to(v)
                    &&& !k.edges.contains(a)
                };

            // If A is not in E(H), then v is a vertex of attachment of H ∪ K.
            // Otherwise, v is a vertex of attachment of H ∩ K.
            if !h.edges.contains(a) {
                assert(self.attachment_vertices(h + k).contains(v)) by {
                    assert(self.is_attachment_edge(h + k, v, a));
                }
            } else {
                assert(self.attachment_vertices(h * k).contains(v)) by {
                    assert(self.is_attachment_edge(h * k, v, a));
                }
            }

            // The proof is completed inductively on the set of attachment
            // vertices without v.
            self.lemma_wgk_implies_wghuk_or_wghnk_contains(h, k, wgk.remove(v));
        }
    }

    /// The vertices of attachment of $$H^c$$ are those vertices of attachment
    /// of H that are not isolated vertices of H.
    ///
    /// This is a recursive helper proof for
    /// [`Self::lemma_wghc_contains_implies_wgh_contains_and_not_isolated`].
    proof fn lemma_wghc_contains_implies_wgh_contains_and_not_isolated_rec(
        self,
        h: Self,
        wghc: Set<Vertex>,
    )
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
            wghc.subset_of(self.attachment_vertices(self.subgraph_complement(h))),
        ensures
            forall|v: Vertex|
                #![auto]
                { wghc.contains(v) } ==> {
                    &&& self.attachment_vertices(h).contains(v)
                    &&& !v.is_isolated_in(h)
                },
        decreases wghc.len(),
    {
        if wghc.is_empty() {
            // Base case: the set of attachment vertices is empty.
        } else {
            // Let x be any vertex of attachment of $$H^c$$.
            let x = wghc.choose();

            // We know that x is incident with an edge of H and is therefore a
            // vertex of H.
            assert(exists|e: Edge|
                #![auto]
                {
                    &&& self.edges.contains(e)
                    &&& h.edges.contains(e)
                    &&& e.is_incident_to(x)
                });
            assert(h.vertices.contains(x));

            // By the definition of $$H^c$$, x is a vertex of attachment of H.
            assert(self.attachment_vertices(h).contains(x));

            // We know that x is not isolated in H since it is incident with an
            // edge of H; its valency must be non-zero.
            assert(!x.is_isolated_in(h)) by {
                let e = choose|e: Edge|
                    #![auto]
                    {
                        &&& self.edges.contains(e)
                        &&& h.edges.contains(e)
                        &&& e.is_incident_to(x)
                    };
                h.lemma_incident_edge_implies_non_isolation(x, e);
            }

            // The proof is completed inductively on the set of attachment
            // vertices without x.
            self.lemma_wghc_contains_implies_wgh_contains_and_not_isolated_rec(h, wghc.remove(x));
        }
    }

    /// The vertices of attachment of H that are not isolated are vertices of
    /// attachment in $$H^c$$.
    ///
    /// This is a recursive helper proof for
    /// [`Self::lemma_wghc_contains_implies_wgh_contains_and_not_isolated`].
    proof fn lemma_wgh_contains_and_not_isolated_implies_wghc_contains_rec(
        self,
        h: Self,
        wgh: Set<Vertex>,
    )
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
            wgh.subset_of(self.attachment_vertices(h)),
        ensures
            forall|v: Vertex|
                #![auto]
                {
                    &&& wgh.contains(v)
                    &&& !v.is_isolated_in(h)
                } ==> self.attachment_vertices(self.subgraph_complement(h)).contains(v),
        decreases wgh.len(),
    {
        if wgh.is_empty() {
            // Base case: the set of attachment vertices is empty.
        } else {
            // Let x be any vertex of attachment of H.
            let x = wgh.choose();

            // We know that x is a vertex of $$H^c$$.
            let hc = self.subgraph_complement(h);
            assert(hc.vertices.contains(x));

            // If x is not isolated in H, then it must be a vertex of attachment
            // of $$H^c$$.
            if !x.is_isolated_in(h) {
                // There must be an edge E in H that is incident to x since it
                // isn't isolated in H.
                assert(exists|e: Edge|
                    #![auto]
                    {
                        &&& self.edges.contains(e)
                        &&& h.edges.contains(e)
                        &&& e.is_incident_to(x)
                    }) by {
                    assert(!h.incident_edges(x).is_empty());
                }
                let e = choose|e: Edge|
                    #![auto]
                    {
                        &&& self.edges.contains(e)
                        &&& h.edges.contains(e)
                        &&& e.is_incident_to(x)
                    };

                // Since E is an edge in H, then it must not be an edge in
                // $$H^c$$. Thus, x must be a vertex of attachment of $$H^c$$.
                assert(self.attachment_vertices(hc).contains(x)) by {
                    assert(self.is_attachment_edge(hc, x, e));
                }
            }
            // The proof is completed inductively on the set of attachment
            // vertices without x.

            self.lemma_wgh_contains_and_not_isolated_implies_wghc_contains_rec(h, wgh.remove(x));
        }
    }

    /// [Tutte, Theorem I.9] The vertices of attachment of $$H^c$$ are those
    /// vertices of attachment of H that are not isolated vertices of H.
    proof fn lemma_wghc_contains_implies_wgh_contains_and_not_isolated(self, h: Self)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
        ensures
            forall|v: Vertex|
                #![auto]
                { self.attachment_vertices(self.subgraph_complement(h)).contains(v) } <==> {
                    &&& self.attachment_vertices(h).contains(v)
                    &&& !v.is_isolated_in(h)
                },
    {
        let wgh = self.attachment_vertices(h);
        let wghc = self.attachment_vertices(self.subgraph_complement(h));

        assert forall|v: Vertex| #![auto] wghc.contains(v) implies {
            &&& wgh.contains(v)
            &&& !v.is_isolated_in(h)
        } by {
            self.lemma_wghc_contains_implies_wgh_contains_and_not_isolated_rec(h, wghc);
        }

        assert forall|v: Vertex|
            #![auto]
            {
                &&& wgh.contains(v)
                &&& !v.is_isolated_in(h)
            } implies wghc.contains(v) by {
            self.lemma_wgh_contains_and_not_isolated_implies_wghc_contains_rec(h, wgh);
        }
    }

    /// There is no vertex of attachment of $$H^c$$ that is isolated in $$H^c$$.
    ///
    /// This is a recursive helper proof for
    /// [`g::lemma_wghc_contains_implies_not_isolated_in_hc`].
    proof fn lemma_wghc_contains_implies_not_isolated_in_hc_rec(self, h: Self, wghc: Set<Vertex>)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
            wghc.subset_of(self.attachment_vertices(self.subgraph_complement(h))),
        ensures
            forall|v: Vertex|
                #![auto]
                { wghc.contains(v) } ==> !v.is_isolated_in(self.subgraph_complement(h)),
        decreases wghc.len(),
    {
        if wghc.is_empty() {
            // Base case: the set of attachment vertices is empty.
        } else {
            // Let x be any vertex of attachment of H.
            let x = wghc.choose();

            // By definition, x must be a vertex of $$H^c$$.
            let hc = self.subgraph_complement(h);
            assert(hc.well_formed()) by {
                self.lemma_subgraph_complement_is_subgraph(h);
            }

            // We demonstrate that x is not isolated in $$H^c$$.
            assert(hc.vertices.contains(x));
            assert(!x.is_isolated_in(hc)) by {
                // Since x is a vertex of attachment of H, there must be an edge
                // A that is incident to x but isn't an edge in H.
                assert(exists|a: Edge|
                    #![auto]
                    {
                        &&& self.edges.contains(a)
                        &&& a.is_incident_to(x)
                        &&& !h.edges.contains(a)
                    });
                let a = choose|a: Edge|
                    #![auto]
                    {
                        &&& self.edges.contains(a)
                        &&& a.is_incident_to(x)
                        &&& !h.edges.contains(a)
                    };

                // By definition, A must be an edge of $$H^c$$ since it isn't an
                // edge of H. This means that the valency of x in $$H^c$$ is at
                // least 1; x is not isolated in $$H^c$$.
                assert(hc.edges.contains(a));
                hc.lemma_incident_edge_implies_non_isolation(x, a);
            }

            // The proof is completed inductively on the set of attachment
            // vertices without x.
            self.lemma_wghc_contains_implies_not_isolated_in_hc_rec(h, wghc.remove(x));
        }
    }

    /// [Tutte, Corollary I.10] No vertex of attachment of $$H^c$$ is isolated
    /// in $$H^c$$.
    proof fn lemma_wghc_contains_implies_not_isolated_in_hc(self, h: Self)
        requires
            self.well_formed(),
            h.is_subgraph_of(self),
        ensures
            forall|v: Vertex|
                #![auto]
                { self.attachment_vertices(self.subgraph_complement(h)).contains(v) }
                    ==> !v.is_isolated_in(self.subgraph_complement(h)),
    {
        let wghc = self.attachment_vertices(self.subgraph_complement(h));
        self.lemma_wghc_contains_implies_not_isolated_in_hc_rec(h, wghc);
    }

    /// [Tutte, Proposition I.28] Let A be an edge of a graph G, and let C be
    /// the component of G including A. Then the components of $$G'_A$$ are the
    /// components of G other than C, together with the components of $$C'_A$$.
    /// Moreover, each component of $$C'_A$$ includes at least one end of A.
    proof fn lemma_components_after_removed_edge_ensures(self, a: Edge, c: Self)
        requires
            self.well_formed(),
            self.edges.contains(a),
            c.is_component_of(self),
            c.edges.contains(a),
        ensures
            self.remove_edge(a).components() =~= self.components().remove(c) + (c.remove_edge(
                a,
            ).components()),
            forall|cta: Self|
                #![auto]
                c.remove_edge(a).components().contains(cta) ==> {
                    ||| cta.vertices.contains(a.tail)
                    ||| cta.vertices.contains(a.head)
                },
    {
        admit()
    }

    /// Let H be a subgraph of a graph G. Let x be a vertex in both H and G and A be
    /// an edge incident with x contained in both H and G. If x is monovalent in G,
    /// then x is monovalent in H.
    proof fn lemma_subgraph_monovalency_with_incident_edge(self, h: Self, x: Vertex, a: Edge)
        requires
            self.well_formed(),
            self.vertices.contains(x),
            self.edges.contains(a),
            h.is_subgraph_of(self),
            h.vertices.contains(x),
            h.edges.contains(a),
            x.is_monovalent_in(self),
            a.is_incident_to(x),
        ensures
            x.is_monovalent_in(h),
    {
        // A must be a link-edge since it is incident with x, which is monovalent.
        assert(a.is_link()) by {
            self.lemma_incident_edge_of_monovalent_vertex_is_link(x, a);
        }

        // Let S be the set of edges in H that are incident with x.
        let s = h.incident_edges(x);

        // Assume that x is not monovalent in H.
        if !x.is_monovalent_in(h) {
            // We know that S has at least two edges.
            assert(s.len() >= 2) by {
                // S cannot be empty since it must contain A.
                assert(s.len() != 0) by {
                    assert(s.contains(a));
                }
                // If S contains a single edge, it must be A. Since A is a
                // link-edge, the valency of x in H must be 1, which contradicts the
                // assumption that x is not monovalent in H.
                assert(s.len() != 1) by {
                    if s.len() == 1 {
                        assert(set![a] =~= s) by { assert(s.contains(a)) }
                        reveal_with_fuel(Graph::incident_edges_to_valency, 2);
                        assert(Self::incident_edges_to_valency(s) == 1);
                        assert(x.is_monovalent_in(h));
                        assert(false);
                    }
                }
            }

            // Let B be another edge incident with x in H. B must be an edge in G
            // since H is a subgraph of H.
            let b = s.remove(a).choose();
            assert(self.edges.contains(b)) by {
                assert(s.contains(b));
                assert(h.is_subgraph_of(self));
            }

            // Let T be the set of edges in G that are incident with x and R be a
            // set that contains A and B. Since R is a subset of T, T must contain
            // at least two edges. This means that x is not monovalent in G, which
            // contradicts the precondition.
            let t = self.incident_edges(x);
            let r = set![a, b];
            assert(r.subset_of(t));
            reveal_with_fuel(Graph::incident_edges_to_valency, 3);
            assert(Self::incident_edges_to_valency(r) >= 2);
            assert(self.valency(x) >= 2);
            assert(false);
        }
    }

    /// [Tutte, Theorem I.30] Let x be a monovalent vertex of a graph G, and let A
    /// be its incident edge. Let C be the component of G including x and A. Then A
    /// is an isthmus of G. One of its end-graphs is the vertex-graph X defined by
    /// x. The other is the graph obtained from C by deleting x and A.
    proof fn lemma_edge_in_component_with_monovalent_vertex_is_isthmus(
        self,
        x: Vertex,
        a: Edge,
        c: Self,
    )
        requires
            self.well_formed(),
            self.vertices.contains(x),
            self.edges.contains(a),
            x.is_monovalent_in(self),
            a.is_incident_to(x),
            c.is_component_of(self),
            c.vertices.contains(x),
            c.edges.contains(a),
        ensures
            a.is_isthmus_of(self),
            ({
                let end_graphs = a.end_graphs_in(self);
                &&& end_graphs.contains(Self::vertex_graph(x))
                &&& end_graphs.contains(
                    Self { vertices: c.vertices.remove(x), edges: c.edges.remove(a) },
                )
            }),
    {
        // Let H be a vertex-graph defined by x.
        let h = Self::vertex_graph(x);

        // H is a component of $$C'_A$$, by Theorem I.19.
        let cta = c.remove_edge(a);
        assert(h.is_component_of(cta)) by {
            // By definition, C is a subgraph of self. Since A is incident with x in G,
            // and is contained in both G and C, x must be monovalent in C.
            assert(x.is_monovalent_in(c)) by {
                self.lemma_subgraph_monovalency_with_incident_edge(c, x, a);
            }

            // Thus, x must be isolated in $$C'_A$$; it does not contain incident edge A.
            assert(cta.vertices.contains(x));
            assert(x.is_isolated_in(cta)) by {
                // Let S and T be the sets of edges incident with x in C and
                // $$C'_A$$, respectively.
                let s = c.incident_edges(x);
                let t = cta.incident_edges(x);

                // Since x is monovalent in C, S only contains A. This means that T
                // must be empty, since A is removed in $$C'_A$$. This means that x
                // is isolated in $$C'_A$$.
                assert(t.is_empty()) by {
                    assert(t =~= s.remove(a));
                    assert(set![a] =~= s) by {
                        assert(s.contains(a));
                        assert(s.is_singleton()) by {
                            c.lemma_monovalency_implies_one_incident_edge(x);
                        }
                    }
                }
            }

            // By Theorem I.19, a vertex-graph defined by an isolated vertex in G is
            // a component of self.
            cta.lemma_isolated_vertex_graph_is_component(x);
        }

        // TODO: Finish proving the rest.
        admit()
    }
}

} // verus!
