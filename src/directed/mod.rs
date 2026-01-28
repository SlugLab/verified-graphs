pub mod path;

use path::Path;
use vstd::prelude::*;

use crate::{
    undirected::{Edge, Graph, Vertex},
    vstd_specs,
};

verus! {

/// A finite, directed graph (digraph).
#[verifier::ext_equal]
pub struct DirectedGraph(pub(crate) Graph);

impl DirectedGraph {
    /// Returns the underlying graph of a digraph.
    ///
    /// [Tutte, Section VI.1] Each digraph has an underlying graph $$U(\Gamma)$$
    /// as follows: Its vertices are the vertices of $$\Gamma$$ and its edges
    /// are the darts of $$\Gamma$$.
    pub(crate) open spec fn underlying_graph(self) -> Graph {
        self.0
    }

    /// Well-formedness of a digraph.
    ///
    /// A digraph is well-formed if its underlying graph is well-formed.
    #[verifier::type_invariant]
    pub(crate) open spec fn well_formed(self) -> bool {
        self.underlying_graph().well_formed()
    }

    /// Returns the incoming edges of vertex v in the digraph.
    pub(crate) open spec fn incoming_edges(self, v: Vertex) -> Set<Edge>
        recommends
            self.underlying_graph().vertices.contains(v),
    {
        self.underlying_graph().edges.filter(|e: Edge| e.head == v)
    }

    /// Returns the invalency of vertex v in the digraph.
    pub(crate) open spec fn invalency(self, v: Vertex) -> nat
        recommends
            self.underlying_graph().vertices.contains(v),
    {
        self.incoming_edges(v).len()
    }

    /// Returns the outgoing edges of vertex v in a digraph.
    pub(crate) open spec fn outgoing_edges(self, v: Vertex) -> Set<Edge>
        recommends
            self.underlying_graph().vertices.contains(v),
    {
        self.underlying_graph().edges.filter(|e: Edge| e.tail == v)
    }

    /// Returns the outvalency of vertex v in the digraph.
    pub(crate) open spec fn outvalency(self, v: Vertex) -> nat
        recommends
            self.underlying_graph().vertices.contains(v),
    {
        self.outgoing_edges(v).len()
    }

    /// Returns if a digraph is Eulerian.
    ///
    /// [Tutte, Section VI.1] [A] digraph $$\Gamma$$ is Eulerian if, for every
    /// vertex, the invalency is equal to the outvalency.
    spec fn is_eulerian(self) -> bool {
        forall|v: Vertex|
            #![auto]
            { self.underlying_graph().vertices.contains(v) } ==> self.invalency(v)
                == self.outvalency(v)
    }

    /// Returns if the digraph is a subdigraph of G.
    ///
    /// This is defined using the digraph's underlying graph based on the
    /// following definition/observation:
    ///
    /// [Tutte, Section VI.1] Let $$\Gamma$$ and $$\Delta$$ be digraphs. We say
    /// that $$\Delta$$ is a subdigraph of $$\Gamma$$ if
    ///
    ///     $$V(\Delta) \subseteq V(\Gamma)$$, $$W(\Delta) \subseteq W(\Gamma)$$,
    ///
    /// and each dart of $$\Delta$$ has the same head and tail in $$\Delta$$ as
    /// in $$\Gamma$$. Clearly there is a 1-1 correspondence between the
    /// subdigraphs of $$\Gamma$$ and the subgraphs of $$U(\Gamma)$$ such that
    /// each subdigraph $$\Delta$$ of $$\Gamma$$ corresponds to its own
    /// underlying graph $$U(\Delta)$$.
    pub(crate) open spec fn is_subdigraph_of(self, g: Self) -> bool {
        self.underlying_graph().is_subgraph_of(g.underlying_graph())
    }

    /// Returns if a digraph is a spanning subdigraph of G.
    pub(crate) open spec fn is_spanning_subdigraph_of(self, g: Self) -> bool {
        self.underlying_graph().is_spanning_subgraph_of(g.underlying_graph())
    }

    /// Returns if the digraph is acyclic.
    ///
    /// A digraph $$\Gamma$$ is acyclic if it contains no circular paths.
    pub(crate) open spec fn is_acyclic(self) -> bool {
        forall|p: Path| #![auto] { p.is_nondegenerate_simple_path_of(self) } ==> !p.is_circular()
    }

    #[via_fn]
    proof fn arborescence_darts_decreases(self, r: Vertex, s: Set<Edge>) {
        assert(!s.is_empty() && s.finite() ==> s.len() > s.remove(s.choose()).len()) by {
            if !s.is_empty() {
                let a = s.choose();
                vstd::set::axiom_set_remove_len(s, a);
            }
        }
    }

    /// Returns the darts in the arborescence diverging from vertex r
    /// constructed from the given tree.
    ///
    /// [Tutte, Section VI.1] Suppose we are given a tree T in which one vertex
    /// r is distinguished. We can construct a digraph $$\Gamma$$ as follows: We put
    ///
    ///     $$V(\Gamma) = V(T)$$ and $$W(\Gamma) = E(T)$$.
    ///
    /// An edge A of T has two end-graphs H and K in T, the components of
    /// $$T'_A$$. We may suppose r to be in K. We define the head and tail of A
    /// in $$\Gamma$$ as the ends of the edge A of T in H and K, respectively.
    /// This completes the definition of $$\Gamma$$. A digraph $$\Gamma$$ so
    /// defined is called an arborescence diverging from r.
    pub(crate) open spec fn arborescence_darts(self, r: Vertex, s: Set<Edge>) -> Set<Edge>
        recommends
            self.underlying_graph().is_tree(),
            self.underlying_graph().vertices.contains(r),
            s.finite(),
            s.subset_of(self.underlying_graph().edges),
        decreases s.len(),
        when s.finite()
        via Self::arborescence_darts_decreases
    {
        if s.is_empty() {
            // Base case: the set of darts is empty.
            Set::empty()
        } else {
            // Consider any edge A of T.
            let a = s.choose();

            // Let X and Y be the end-graphs of A in T.
            let x = a.end_graphs_in(self.underlying_graph()).choose();
            let y = a.end_graphs_in(self.underlying_graph()).remove(x).choose();

            // Let H and K be the end-graphs of A in T, with r in K.
            let (h, k) = if y.vertices.contains(r) {
                (x, y)
            } else {
                (y, x)
            };

            // Let B be the edge of $$\Gamma$$ such that its head is the end of
            // A in H and its tail is the end of A in K.
            let b = if h.vertices.contains(a.head) {
                a
            } else {
                a.reverse()
            };

            // Recursively construct the rest of the darts.
            set![b] + self.arborescence_darts(r, s.remove(a))
        }
    }

    /// Creates an arborescence from a tree and a distinguished vertex r.
    ///
    /// [Tutte, Section VI.1] Suppose we are given a tree T in which one vertex
    /// r is distinguished. We can construct a digraph $$\Gamma$$ as follows: We put
    ///
    ///     $$V(\Gamma) = V(T)$$ and $$W(\Gamma) = E(T)$$.
    ///
    /// An edge A of T has two end-graphs H and K in T, the components of
    /// $$T'_A$$. We may suppose r to be in K. We define the head and tail of A
    /// in $$\Gamma$$ as the ends of the edge A of T in H and K, respectively.
    /// This completes the definition of $$\Gamma$$. A digraph $$\Gamma$$ so
    /// defined is called an arborescence diverging from r.
    pub(crate) open spec fn arborescence(self, r: Vertex) -> Self
        recommends
            self.underlying_graph().is_tree(),
            self.underlying_graph().vertices.contains(r),
    {
        Self(
            Graph::new(
                self.underlying_graph().vertices,
                self.arborescence_darts(r, self.underlying_graph().edges),
            ),
        )
    }

    /// Returns if the digraph is an arborescence diverging from vertex r.
    pub(crate) open spec fn is_arborescence_diverging_from(self, r: Vertex) -> bool {
        &&& self.underlying_graph().is_tree()
        &&& self.underlying_graph().vertices.contains(r)
        &&& self =~= self.arborescence(r)
    }

    /// Returns if the digraph is an arborescent tree.
    ///
    /// An arborescent tree is a digraph whose underlying graph is a tree in
    /// which no vertex is the head of more than one dart.
    ///
    /// NOTE: The label "arborescent tree" is not a standard term.
    pub(crate) open spec fn is_arborescent_tree(self) -> bool {
        &&& self.underlying_graph().is_tree()
        &&& forall|v: Vertex|
            #![auto]
            self.underlying_graph().vertices.contains(v) ==> { self.invalency(v) <= 1 }
    }

    /// Returns the vertex v of an arborescent tree G such that G is an
    /// arborescence diverging from v.
    ///
    /// The existence of such a vertex is given by Tutte, Theorem VI.2.
    pub(crate) open spec fn arborescent_tree_root(self) -> Vertex
        recommends
            self.is_arborescent_tree(),
    {
        choose|r: Vertex|
            #![auto]
            {
                &&& self.underlying_graph().vertices.contains(r)
                &&& self.is_arborescence_diverging_from(r)
            }
    }

    /// Returns if P is a path from vertex u to vertex v in the digraph.
    ///
    /// If u and v are the same vertex, then P is a degenerate path. Otherwise,
    /// P is a nondegenerate path whose origin is u and terminus is v.
    pub(crate) open spec fn is_connecting_path(self, p: Path, u: Vertex, v: Vertex) -> bool {
        if u == v {
            p.is_degenerate()
        } else {
            &&& p.is_nondegenerate_path_of(self)
            &&& p.origin() == u
            &&& p.terminus() == v
        }
    }

    /// Returns if vertex v is reachable from vertex u in the digraph.
    pub(crate) open spec fn reachable_from(self, v: Vertex, u: Vertex) -> bool
        recommends
            self.underlying_graph().vertices.contains(v),
            self.underlying_graph().vertices.contains(u),
    {
        exists|p: Path| self.is_connecting_path(p, u, v)
    }

    /// Returns if vertex v is uniquely reachable from vertex u in the digraph.
    pub(crate) open spec fn uniquely_reachable_from(self, v: Vertex, u: Vertex) -> bool
        recommends
            self.underlying_graph().vertices.contains(v),
            self.underlying_graph().vertices.contains(u),
    {
        &&& self.reachable_from(v, u)
        &&& {
            let p = choose|p: Path| self.is_connecting_path(p, u, v);
            forall|q: Path| #![auto] self.is_connecting_path(q, u, v) ==> q =~= p
        }
    }

    /// Returns the set of descendants of vertex v in the digraph.
    ///
    /// The set of descendants of a vertex v in a digraph $$\Gamma$$ is the set
    /// of vertices of $$\Gamma$$ that are reachable from v. Because of
    /// degenerate paths, v is considered its own descendant.
    pub(crate) open spec fn descendants(self, v: Vertex) -> Set<Vertex>
        recommends
            self.underlying_graph().vertices.contains(v),
    {
        Set::new(
            |u: Vertex|
                {
                    &&& self.underlying_graph().vertices.contains(u)
                    &&& self.reachable_from(u, v)
                },
        )
    }

    /// Any vertex v of digraph $$\Gamma$$ is reachable from itself.
    pub(crate) proof fn lemma_vertex_reachable_from_itself(self, v: Vertex)
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(v),
        ensures
            self.reachable_from(v, v),
    {
        // A vertex is reachable from itself through a degenerate path.
        let p = Path::degenerate();
        assert(self.is_connecting_path(p, v, v));
    }

    /// [Tutte, Theorem VI.2] Let $$\Gamma$$ be a digraph such that $$U(\Gamma)$$ is
    /// a tree and no vertex is the head of more than one dart. Then $$\Gamma$$ is
    /// an arborescence diverging from some vertex r.
    pub(crate) proof fn lemma_arborescent_tree_is_arborescence(self)
        requires
            self.well_formed(),
            self.is_arborescent_tree(),
        ensures
            exists|r: Vertex|
                #![auto]
                {
                    &&& self.underlying_graph().vertices.contains(r)
                    &&& self.is_arborescence_diverging_from(r)
                },
    {
        // Since $$U(\Gamma)$$ is a tree, the number of vertices of $$U(\Gamma)$$
        // exceeds the number of darts by 1, by Theorem I.37.
        let ut = self.underlying_graph();
        assert(ut.vertices.len() == ut.edges.len() + 1) by {
            ut.lemma_tree_vertices_exceed_edges_by_one();
        }

        // Thus, $$U(\Gamma)$$ has a vertex r that is the head of no dart, and each
        // other vertex has must be the head of exactly one dart.
        //
        // NOTE: The arborescence definition only requires the existence of a vertex
        // r; its valency and the valency of other vertices are not required.
        assert(exists|r: Vertex|
            {
                &&& ut.vertices.contains(r)
                &&& forall|a: Edge| #![auto] ut.edges.contains(a) ==> a.head != r
            }) by {
            // TODO: The general proof for this is that the number vertices without
            // r must be the same as the number of edges. By definition, the head of
            // each edge is unique. Thus, if every other vertex has a head, then r
            // must not have a head.
            admit();
        }
        let r = choose|r: Vertex|
            {
                &&& ut.vertices.contains(r)
                &&& forall|a: Edge| #![auto] ut.edges.contains(a) ==> a.head != r
            };

        if self.underlying_graph().edges.is_empty() {
            // If $$|E(U(\Gamma))| = 0$$, then $$V(U(\Gamma)) = \{r\}$$, by Theorem I.37.
            assert(set![r] =~= self.underlying_graph().vertices) by {
                assert(self.underlying_graph().vertices.len() == 1) by {
                    self.underlying_graph().lemma_tree_vertices_exceed_edges_by_one();
                }
                assert(self.underlying_graph().vertices.is_singleton()) by {
                    vstd_specs::set::lemma_set_with_single_element_is_singleton(
                        self.underlying_graph().vertices,
                    );
                }
            }

            // Thus, $$\Gamma$$ must be a vertex-graph defined by r, which trivially
            // is an arborescence diverging from r.
            assert(self.is_arborescence_diverging_from(r)) by {
                assert(self.underlying_graph() =~= Graph::vertex_graph(r));
            }
        } else {
            // TODO: Come back to this later.
            admit()
        }
    }

    pub(crate) proof fn lemma_arborescent_tree_root_is_contained_vertex(self)
        requires
            self.well_formed(),
            self.is_arborescent_tree(),
        ensures
            self.underlying_graph().vertices.contains(self.arborescent_tree_root()),
    {
        self.lemma_arborescent_tree_is_arborescence();
        let r = self.arborescent_tree_root();
    }

    /// [Tutte, Theorem VI.8 (modified)] Let $$\Gamma$$ be an arborescence diverging
    /// from a vertex r. Let v be any other vertex of $$\Gamma$$. Then there is just
    /// one nondegenerate path $$P_{rv}$$ in $$\Gamma$$ from r to v.
    pub(crate) proof fn lemma_arborescence_vertices_uniquely_reachable(self, r: Vertex)
        requires
            self.well_formed(),
            self.is_arborescence_diverging_from(r),
        ensures
            (forall|v: Vertex|
                #![auto]
                {
                    &&& v != r
                    &&& self.underlying_graph().vertices.contains(v)
                } ==> self.uniquely_reachable_from(v, r)),
    {
        admit()
    }

    /// [Tutte, Theorem VI.26] Let r be a vertex of a digraph $$\Gamma$$ and let
    /// $$\Delta$$ be a spanning subdigraph of $$\Gamma$$. Then in order that
    /// $$\Delta$$ shall be an arborescence diverging from r, it is necessary and
    /// sufficient that the following conditions shall be fulfilled: There must be
    /// no circular path in $$\Delta$$, the invalency of r in $$\Delta$$ must be 0,
    /// and the invalency of every other vertex in $$\Delta$$ must be 1.
    proof fn lemma_arborescence_requirements(self, r: Vertex, d: DirectedGraph)
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(r),
            d.is_spanning_subdigraph_of(self),
            d.is_acyclic(),
            d.invalency(r) == 0,
            forall|v: Vertex|
                #![auto]
                {
                    &&& v != r
                    &&& d.underlying_graph().vertices.contains(v)
                } ==> d.invalency(v) == 1,
        ensures
            d.is_arborescence_diverging_from(r),
    {
        admit()
    }

    /// A vertex-graph is a tree.
    pub(crate) proof fn lemma_vertex_graph_is_tree(self)
        requires
            self.well_formed(),
            self.underlying_graph().is_vertex_graph(),
        ensures
            self.underlying_graph().is_tree(),
    {
        // Since U(G) is a vertex graph, it must contain a single vertex v.
        assert(!self.underlying_graph().vertices.is_empty());
        let v = self.underlying_graph().vertices.choose();

        // U(G) must be a vertex-graph defined by v.
        assert(self.underlying_graph().is_vertex_graph_defined_by(v));

        // U(G) has a single component: the vertex-graph defined by v. Since G is
        // equivalent to this vertex-graph, and since an isolated vertex graph is by
        // definition a component, U(G) must be connected.
        assert(self.underlying_graph().is_connected()) by {
            assert(Graph::vertex_graph(v).is_component_of(self.underlying_graph())) by {
                self.underlying_graph().lemma_isolated_vertex_graph_is_component(v);
            }
            assert(self.underlying_graph() =~= Graph::vertex_graph(v));
            self.underlying_graph().lemma_components_are_connected();
        }
    }

    /// A vertex-graph is an arborescent tree.
    pub(crate) proof fn lemma_vertex_graph_is_arborescent_tree(self)
        requires
            self.well_formed(),
            self.underlying_graph().is_vertex_graph(),
        ensures
            self.is_arborescent_tree(),
    {
        // Since U(G) is a vertex graph, U(G) must be a tree.
        assert(self.underlying_graph().is_tree()) by {
            self.lemma_vertex_graph_is_tree();
        }

        // Since U(G) is a vertex graph, it must contain a single vertex v.
        assert(!self.underlying_graph().vertices.is_empty());
        let v = self.underlying_graph().vertices.choose();

        // The invalency of v in U(G) must be 0, since U(G) has no edges.
        assert(self.invalency(v) == 0) by {
            assert(self.incoming_edges(v).is_empty());
        }
    }

    /// A link-graph is an arborescent tree.
    pub(crate) proof fn lemma_link_graph_is_arborescent_tree(self)
        requires
            self.well_formed(),
            self.underlying_graph().is_link_graph(),
        ensures
            self.is_arborescent_tree(),
    {
        // Since U(G) is a link graph, it contains a single edge A.
        let a = self.underlying_graph().edges.choose();

        // Since U(G) is a link graph, A is an isthmus of U(G). Since A is the only
        // edge of U(G), U(G) must be a forest.
        assert(self.underlying_graph().is_forest()) by {
            assert(a.is_isthmus_of(self.underlying_graph())) by {
                self.underlying_graph().lemma_link_graph_edge_is_isthmus(a);
            }
        }

        // Let H be the graph U(G) with A removed. Since A is an isthmus of U(G), H
        // must have two components. This means that U(G) is connected, since
        // removing an isthmus from a graph increases the number of components by 1.
        assert(self.underlying_graph().is_connected()) by {
            let a = self.underlying_graph().edges.choose();
            let h = self.underlying_graph().remove_edge(a);
            assert(h.component_number() == 2) by {
                assert(a.is_isthmus_of(self.underlying_graph())) by {
                    self.underlying_graph().lemma_link_graph_edge_is_isthmus(a);
                }
            }
            assert(self.underlying_graph().component_number() == 1) by {
                self.underlying_graph().lemma_isthmus_increases_components(a);
            }
        }

        // U(G) contains two vertices: the tail and head of A. The invalency of the
        // tail of A must be 0, since it has no incoming edges. The invalency of the
        // head of A must be 1, since it has one incoming edge: A. Thus, each edge
        // of U(G) has an invalency of at most 1.
        assert forall|v: Vertex|
            #![auto]
            { self.underlying_graph().vertices.contains(v) } implies self.invalency(v) <= 1 by {
            assert(self.underlying_graph().vertices =~= set![a.tail, a.head]);
            assert(self.invalency(a.tail) == 0) by {
                assert(self.incoming_edges(a.tail).is_empty());
            }
            assert(self.invalency(a.head) == 1) by {
                assert(self.incoming_edges(a.head) =~= set![a]);
            }
        }
    }

    /// The set of descendants for a vertex is finite.
    proof fn lemma_descendants_finite(self, v: Vertex)
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(v),
        ensures
            self.descendants(v).finite(),
    {
        assert(self.descendants(v).subset_of(self.underlying_graph().vertices));
    }

    /// A vertex w is reachable from vertex v if and only if w is a descendant of v.
    proof fn lemma_reachable_vertices_are_descendants(self, v: Vertex)
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(v),
        ensures
            forall|w: Vertex|
                #![auto]
                {
                    &&& self.underlying_graph().vertices.contains(w)
                    &&& self.reachable_from(w, v)
                } <==> { self.descendants(v).contains(w) },
    {
        // NOTE: Verus proves this automatically.
    }

    /// The root of an arborescent tree is unique.
    pub(crate) proof fn lemma_arborescent_tree_root_is_unique(self)
        requires
            self.well_formed(),
            self.is_arborescent_tree(),
        ensures
            forall|r: Vertex|
                #![auto]
                {
                    &&& self.underlying_graph().vertices.contains(r)
                    &&& self.is_arborescence_diverging_from(r)
                } ==> { r =~= self.arborescent_tree_root() },
    {
        admit();
    }

    pub(crate) proof fn lemma_cannot_reach_non_descendant(self)
        requires
            self.well_formed(),
        ensures
            forall|v: Vertex|
                self.underlying_graph().vertices.contains(v) ==> {
                    forall|u: Vertex|
                        #![auto]
                        {
                            &&& self.underlying_graph().vertices.contains(u)
                            &&& !self.descendants(v).contains(u)
                        } ==> !self.reachable_from(u, v)
                },
    {
        // NOTE: Verus automatically proves this.
    }

    /// A digraph whose underlying graph is a vertex-graph defined by a vertex r is
    /// an arborescence diverging from r.
    pub(crate) proof fn lemma_vertex_graph_is_arborescence_diverging_from(self, r: Vertex)
        requires
            self.well_formed(),
            self.underlying_graph().is_vertex_graph_defined_by(r),
        ensures
            self.is_arborescence_diverging_from(r),
    {
        // U(G) has a single component: the vertex-graph defined by r. Since G is
        // equivalent to this vertex-graph, and since an isolated vertex graph is by
        // definition a component, U(G) must be connected.
        assert(self.underlying_graph().is_connected()) by {
            assert(Graph::vertex_graph(r).is_component_of(self.underlying_graph())) by {
                self.underlying_graph().lemma_isolated_vertex_graph_is_component(r);
            }
            assert(self.underlying_graph() =~= Graph::vertex_graph(r));
            self.underlying_graph().lemma_components_are_connected();
        }
    }

    pub(crate) proof fn lemma_edge_is_path_between_vertices(self, e: Edge)
        requires
            self.well_formed(),
            self.underlying_graph().edges.contains(e),
        ensures
            self.reachable_from(e.head, e.tail),
    {
        if e.tail =~= e.head {
            self.lemma_vertex_reachable_from_itself(e.tail);
        } else {
            let p = Path(seq![e]);
            assert(self.is_connecting_path(p, e.tail, e.head));
            assert(p.is_nondegenerate());
            assert(p.is_nondegenerate_path_of(self));
            assert(p.origin() == e.tail);
            assert(p.terminus() == e.head);
        }
    }

    /// Let r be a vertex in G. Then, for every vertex v that is reachable from r,
    /// there exists an outgoing edge a from r such that v is reachable from the
    /// head of a.
    ///
    /// TODO: Finish documenting the proof.
    proof fn lemma_vertex_reachable_through_outgoing_edge(self, r: Vertex)
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(r),
        ensures
            forall|v: Vertex|
                #![auto]
                {
                    &&& !(v =~= r)
                    &&& self.underlying_graph().vertices.contains(v)
                    &&& self.reachable_from(v, r)
                } ==> {
                    exists|a: Edge|
                        #![auto]
                        {
                            &&& a.tail =~= r
                            &&& self.underlying_graph().edges.contains(a)
                            &&& self.reachable_from(v, a.head)
                        }
                },
    {
        assert forall|v: Vertex|
            #![auto]
            {
                &&& !(v =~= r)
                &&& self.underlying_graph().vertices.contains(v)
                &&& self.reachable_from(v, r)
            } implies {
            exists|a: Edge|
                #![auto]
                {
                    &&& a.tail =~= r
                    &&& self.underlying_graph().edges.contains(a)
                    &&& self.reachable_from(v, a.head)
                }
        } by {
            assert(exists|p: Path| #![auto] self.is_connecting_path(p, r, v));
            let p = choose|p: Path| #![auto] self.is_connecting_path(p, r, v);

            assert(p.is_nondegenerate());
            let a = p.as_seq().first();
            assert(a.tail =~= r);
            assert(self.underlying_graph().edges.contains(a));

            let q = p.drop_first();
            if q.is_degenerate() {
                assert(a.head =~= v);
                assert(self.reachable_from(v, a.head)) by {
                    self.lemma_vertex_reachable_from_itself(v);
                };
            } else {
                if a.head =~= v {
                    assert(self.reachable_from(v, a.head)) by {
                        self.lemma_vertex_reachable_from_itself(v);
                    };
                } else {
                    assert(self.reachable_from(v, a.head)) by {
                        assert(self.is_connecting_path(q, a.head, v)) by {
                            assert(q.is_nondegenerate_path_of(self));
                            assert(q.origin() =~= a.head);
                            assert(q.terminus() =~= v);
                        }
                    };
                }
            }
        }
    }

    pub(crate) proof fn lemma_connected_vertices_in_subgraph_connected_in_graph(
        self,
        h: DirectedGraph,
        v: Vertex,
        u: Vertex,
    )
        requires
            self.well_formed(),
            h.well_formed(),
            h.is_subdigraph_of(self),
            h.underlying_graph().vertices.contains(u),
            h.underlying_graph().vertices.contains(v),
            h.reachable_from(v, u),
        ensures
            self.reachable_from(v, u),
    {
        assert(exists|p: Path| #![auto] h.is_connecting_path(p, u, v));
        let p = choose|p: Path| #![auto] h.is_connecting_path(p, u, v);
        if p.is_degenerate() {
            self.lemma_vertex_reachable_from_itself(v);
        } else {
            assert(self.is_connecting_path(p, u, v));
        }
    }

    /// A vertex with outdegree 0 has no other descendants than itself.
    pub(crate) proof fn lemma_vertex_with_outdegree0_has_no_other_descendants(self, v: Vertex)
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(v),
            self.outvalency(v) == 0,
        ensures
            self.descendants(v) =~= set![v],
    {
        // The set of descendants of v contains itself since vertices are reachable
        // from themselves through degenerate paths.
        assert(self.descendants(v).contains(v)) by {
            assert(self.reachable_from(v, v)) by {
                self.lemma_vertex_reachable_from_itself(v);
            }
        }

        // Assume that there are other descendants of v.
        if !(self.descendants(v) =~= set![v]) {
            // There must exist a vertex u that is a descendant of v and is not v.
            assert(exists|u: Vertex|
                #![auto]
                {
                    &&& self.underlying_graph().vertices.contains(u)
                    &&& self.descendants(v).contains(u)
                    &&& u != v
                });
            let u = choose|u: Vertex|
                #![auto]
                {
                    &&& self.underlying_graph().vertices.contains(u)
                    &&& self.descendants(v).contains(u)
                    &&& u != v
                };

            // Assume that there is a path P from v to u. If there isn't, then u
            // cannot be a descendant of v.
            if exists|p: Path| #![auto] self.is_connecting_path(p, v, u) {
                // Since u is not v, P must be a nondegenerate path.
                let p = choose|p: Path| #![auto] self.is_connecting_path(p, v, u);
                assert(p.is_nondegenerate());

                // P contains at least one edge A, since it is nondegenerate. The
                // tail of A must be v, since P's origin is v.
                let a = p.as_seq().first();
                assert(a.tail == v);

                // A's existence contradicts v having an outdegree of 0.
                assert(self.outgoing_edges(v).contains(a));
                assert(false);
            }
        }
    }

    /// Let r and v be distinct vertices in G. If v is not reachable from any
    /// outgoing edge A from r, then v is not reachable from r.
    ///
    /// This is the contrapositive of [`lemma_vertex_reachable_through_outgoing_edge`].
    ///
    /// TODO: Finish documenting the proof.
    pub(crate) proof fn lemma_vertex_reachable_through_outgoing_edge_contra(
        self,
        r: Vertex,
        v: Vertex,
    )
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(r),
            self.underlying_graph().vertices.contains(v),
            !(v =~= r),
            forall|a: Edge|
                #![auto]
                self.outgoing_edges(r).contains(a) ==> { !self.reachable_from(v, a.head) },
        ensures
            !self.reachable_from(v, r),
    {
        if self.reachable_from(v, r) {
            assert(exists|a: Edge|
                #![auto]
                {
                    &&& a.tail =~= r
                    &&& self.underlying_graph().edges.contains(a)
                    &&& self.reachable_from(v, a.head)
                }) by {
                self.lemma_vertex_reachable_through_outgoing_edge(r);
            }
            let a = choose|a: Edge|
                #![auto]
                {
                    &&& a.tail =~= r
                    &&& self.underlying_graph().edges.contains(a)
                    &&& self.reachable_from(v, a.head)
                };
            assert(self.outgoing_edges(r).contains(a));
            assert(false);
        }
    }

    pub(crate) proof fn lemma_subgraph_path_is_path(
        self,
        h: DirectedGraph,
        p: Path,
        u: Vertex,
        v: Vertex,
    )
        requires
            self.well_formed(),
            h.is_subdigraph_of(self),
            h.is_connecting_path(p, u, v),
        ensures
            self.is_connecting_path(p, u, v),
    {
        // NOTE: Verus automatically proves this.
    }

    pub(crate) proof fn lemma_paths_are_transitive(self, u: Vertex, v: Vertex, w: Vertex)
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(u),
            self.underlying_graph().vertices.contains(v),
            self.underlying_graph().vertices.contains(w),
            self.reachable_from(u, v),
            self.reachable_from(v, w),
        ensures
            self.reachable_from(u, w),
    {
        let p = choose|p: Path| #![auto] self.is_connecting_path(p, v, u);
        let q = choose|q: Path| #![auto] self.is_connecting_path(q, w, v);

        assert(self.reachable_from(u, w)) by {
            if v =~= u {
                assert(self.is_connecting_path(q, w, u));
            } else {
                if v =~= w {
                    assert(self.is_connecting_path(p, w, u));
                } else {
                    if u =~= w {
                        self.lemma_vertex_reachable_from_itself(u);
                    } else {
                        let qp = q.product(p);
                        assert(self.is_connecting_path(qp, w, u));
                    }
                }
            }
        }
    }

    pub(crate) proof fn lemma_path_vertices_are_contained(self, p: Path)
        requires
            self.well_formed(),
            p.is_nondegenerate_path_of(self),
        ensures
            forall|a: Edge|
                #![auto]
                p.as_seq().contains(a) ==> {
                    &&& self.underlying_graph().vertices.contains(a.tail)
                    &&& self.underlying_graph().vertices.contains(a.head)
                },
    {
        if !(forall|a: Edge|
            #![auto]
            p.as_seq().contains(a) ==> {
                &&& self.underlying_graph().vertices.contains(a.tail)
                &&& self.underlying_graph().vertices.contains(a.head)
            }) {
            assert(exists|a: Edge|
                #![auto]
                {
                    &&& p.as_seq().contains(a)
                    &&& {
                        ||| !self.underlying_graph().vertices.contains(a.tail)
                        ||| !self.underlying_graph().vertices.contains(a.head)
                    }
                });
            let a = choose|a: Edge|
                #![auto]
                {
                    &&& p.as_seq().contains(a)
                    &&& {
                        ||| !self.underlying_graph().vertices.contains(a.tail)
                        ||| !self.underlying_graph().vertices.contains(a.head)
                    }
                };

            assert(self.underlying_graph().edges.contains(a));
            assert(false);
        }
    }

    /// The descendants of a child vertex v are reachable from its parent vertex u.
    ///
    /// This is a recursive helper function for [`lemma_child_descendants_reachable_from_parent`].
    proof fn lemma_child_descendants_reachable_from_parent_recur(
        self,
        u: Vertex,
        v: Vertex,
        a: Edge,
        reachable: Set<Vertex>,
    )
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(u),
            self.underlying_graph().vertices.contains(v),
            self.underlying_graph().edges.contains(a),
            a.tail =~= u,
            a.head =~= v,
            reachable.all(|w: Vertex| self.reachable_from(w, v)),
            reachable.finite(),
        ensures
            reachable.all(|w: Vertex| self.reachable_from(w, u)),
        decreases reachable.len(),
    {
        // Base case: there are no more reachable vertices.
        if !reachable.is_empty() {
            // Let w be a reachable vertex from v.
            let w = reachable.choose();

            if u =~= w {
                // If w is the parent vertex u, then it is trivially reachable.
                assert(self.reachable_from(w, u)) by {
                    self.lemma_vertex_reachable_from_itself(w);
                };
            } else {
                // Otherwise, there must exist a path P that connects v to w.
                assert(exists|p: Path| #![auto] self.is_connecting_path(p, v, w));
                let p = choose|p: Path| #![auto] self.is_connecting_path(p, v, w);

                if p.is_degenerate() {
                    // If P is a degenerate path, then w must be v. Thus, w must be
                    // reachable from u since there is an edge from u to v.
                    assert(w =~= v);
                    assert(self.reachable_from(w, u)) by {
                        self.lemma_edge_is_path_between_vertices(a);
                    };
                } else {
                    // Let Q be the path constructed from A. The product of Q and P
                    // is a path from u to w.
                    let q = Path(seq![a]);
                    let qp = q.product(p);
                    assert(self.reachable_from(w, u)) by {
                        assert(self.is_connecting_path(qp, u, w));
                    }
                }
            }

            // Recurse on the remaining reachable vertices.
            self.lemma_child_descendants_reachable_from_parent_recur(u, v, a, reachable.remove(w));
        }
    }

    /// The descendants of a child vertex v are reachable from its parent vertex u.
    proof fn lemma_child_descendants_reachable_from_parent(self, u: Vertex, v: Vertex, a: Edge)
        requires
            self.well_formed(),
            self.underlying_graph().vertices.contains(u),
            self.underlying_graph().vertices.contains(v),
            self.underlying_graph().edges.contains(a),
            a.tail =~= u,
            a.head =~= v,
        ensures
            forall|w: Vertex|
                #![auto]
                {
                    &&& self.underlying_graph().vertices.contains(w)
                    &&& self.reachable_from(w, v)
                } ==> { self.reachable_from(w, u) },
    {
        self.lemma_descendants_finite(v);
        self.lemma_reachable_vertices_are_descendants(v);
        self.lemma_child_descendants_reachable_from_parent_recur(u, v, a, self.descendants(v));
    }
}

} // verus!
