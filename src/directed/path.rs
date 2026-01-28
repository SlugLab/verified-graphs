use vstd::prelude::*;

use crate::{
    directed::DirectedGraph,
    undirected::{Edge, Graph, Vertex},
    vstd_specs,
};

verus! {

/// A dart is a directed edge.
pub type Dart = Edge;

/// A directed path.
#[verifier::ext_equal]
pub struct Path(pub(crate) Seq<Dart>);

impl Path {
    /// Returns the underlying sequence of dart.
    pub(crate) open spec fn as_seq(self) -> Seq<Dart> {
        self.0
    }

    /// Returns the initial segment of a path.
    ///
    /// The initial segment of a path P is the prefix of P with all darts
    /// except the last.
    pub(crate) open spec fn init(self) -> Self
        recommends
            self.as_seq().len() > 0,
    {
        Self(self.as_seq().drop_last())
    }

    /// Returns the tail segment of a path.
    ///
    /// The tail segment of a path P is the suffix of P with all darts except
    /// the first.
    pub(crate) open spec fn drop_first(self) -> Self
        recommends
            self.as_seq().len() > 0,
    {
        Self(self.as_seq().drop_first())
    }

    /// Returns if a path is nondegenerate.
    ///
    /// [Tutte, Section VI.2] A nondegenerate path in a digraph G is a sequence
    ///
    ///     $$P = (D_1, D_2, ..., D_n)$$ [Tutte, Equation VI.2.1]
    ///
    /// of n >= 1 darts $$D_j$$ of $$\Gamma$$. not necessarily all distinct. It
    /// is required that the head of $$D_j$$ shall be the tail of $$D_{j+1}$$
    /// whenever $$1 \leq j < n$$. The first and last vertices of P, that is,
    /// the tail of $$D_1$$ and the head of $$D_n$$, are called the origin and
    /// terminus of P, respectively.
    pub(crate) open spec fn is_nondegenerate(self) -> bool {
        &&& self.as_seq().len() >= 1
        &&& forall|i: int|
            #![auto]
            1 <= i < self.as_seq().len() ==> { self.as_seq()[i - 1].head == self.as_seq()[i].tail }
    }

    /// Returns if a path is degenerate.
    ///
    /// [Tutte, Section VI.2] Is is convenient to recognize also certain
    /// denegerate paths in $$\Gamma$$. There is exactly one of these, denoted
    /// by $$P_v$$, associated with each vertex v of $$\Gamma$$; $$P_v$$ has no
    /// member darts. We say that its length $$s(P_v)$$ is zero, and v is both
    /// its origin and its terminus.
    pub(crate) open spec fn is_degenerate(self) -> bool {
        self.as_seq().len() == 0
    }

    /// Creates a degenerate path.
    pub(crate) open spec fn degenerate() -> Self {
        Self(Seq::empty())
    }

    /// Returns the sequence of vertices walked along a path.
    pub(crate) open spec fn walked_vertices(self) -> Seq<Vertex>
        recommends
            self.is_nondegenerate(),
    {
        seq![self.as_seq()[0].tail] + self.as_seq().map_values(|d: Dart| d.head)
    }

    /// Returns the origin of the path.
    pub(crate) open spec fn origin(self) -> Vertex
        recommends
            self.is_nondegenerate(),
    {
        self.as_seq().first().tail
    }

    /// Returns the terminus of the path.
    pub(crate) open spec fn terminus(self) -> Vertex
        recommends
            self.is_nondegenerate(),
    {
        self.as_seq().last().head
    }

    /// Returns the product of two paths.
    ///
    /// [Tutte, Section VI.2] Consider two paths P and Q in $$\Gamma$$. If the
    /// terminus of P is the origin of Q, there is a path PQ in $$\Gamma$$
    /// formed by writing down the terms of P, in their order in P, and
    /// continuing with the terms of Q, in their order in Q. Moreover, the
    /// origin of PQ is the origin of P, and the terminus of PQ is the
    /// terminus of Q.
    pub(crate) open spec fn product(self, other: Self) -> Self
        recommends
            self.terminus() == other.origin(),
    {
        Self(self.as_seq() + other.as_seq())
    }

    /// Returns a factor of a path.
    ///
    /// A factor is specified by a subrange.
    pub(crate) open spec fn factor(self, start: int, end: int) -> Self
        recommends
            0 <= start <= end <= self.as_seq().len(),
    {
        Self(self.as_seq().subrange(start, end))
    }

    /// Returns if a path is reentrant.
    ///
    /// [Tutte, Section VI.2] A path P of Eq. (VI.2.1) is reentrant if its
    /// origin and terminus coincide.
    pub(crate) open spec fn is_reentrant(self) -> bool
        recommends
            self.is_nondegenerate(),
    {
        self.origin() == self.terminus()
    }

    /// Returns if a path is dart-simple.
    ///
    /// [Tutte, Section VI.2] We say that P is dart-simple if no dart is
    /// repeated in it.
    pub(crate) open spec fn is_dart_simple(self) -> bool
        recommends
            self.is_nondegenerate(),
    {
        self.as_seq().no_duplicates()
    }

    /// Returns if a path is tail-simple.
    ///
    /// [Tutte, Section VI.2] [We say that] a path P is head-simple
    /// (tail-simple) if no vertex occurs twice as head (tail) of a term of P.
    pub(crate) open spec fn is_tail_simple(self) -> bool
        recommends
            self.is_nondegenerate(),
    {
        self.as_seq().map_values(|d: Dart| d.tail).no_duplicates()
    }

    /// Returns if a path is head-simple.
    ///
    /// [Tutte, Section VI.2] [We say that] a path P is head-simple
    /// (tail-simple) if no vertex occurs twice as head (tail) of a term of P.
    pub(crate) open spec fn is_head_simple(self) -> bool
        recommends
            self.is_nondegenerate(),
    {
        self.as_seq().map_values(|d: Dart| d.head).no_duplicates()
    }

    /// Returns if a path is simple.
    ///
    /// [Tutte, Section VI.2] [We say that] a path P is simple if it is both
    /// head-simple and tail-simple.
    pub(crate) open spec fn is_simple(self) -> bool
        recommends
            self.is_nondegenerate(),
    {
        &&& self.is_tail_simple()
        &&& self.is_head_simple()
    }

    /// Returns if a path is nondegenerate and simple.
    pub(crate) open spec fn is_nondegenerate_and_simple(self) -> bool {
        &&& self.is_nondegenerate()
        &&& self.is_simple()
    }

    /// Returns if a path is circular.
    ///
    /// [Tutte, Section VI.2] A nondegenerate simple path is called a circular
    /// path if it is reentrant.
    pub(crate) open spec fn is_circular(self) -> bool
        recommends
            self.is_nondegenerate(),
            self.is_simple(),
    {
        self.is_reentrant()
    }

    /// Returns if a path is linear.
    ///
    /// [Tutte, Section VI.2] [A nondegenerate simple path is called] a linear
    /// path if its origin and terminus are distinct.
    pub(crate) open spec fn is_linear(self) -> bool
        recommends
            self.is_nondegenerate(),
            self.is_simple(),
    {
        !self.is_reentrant()
    }

    /// Returns the digraph of a path.
    ///
    /// [Tutte, Section VI.2] The digraph $$\Gamma(P)$$ of a path P in
    /// $$\Gamma$$ is defined as the subdigraph of $$\Gamma$$ whose darts are
    /// those occurring in P and whose vertices are the heads and tails of these
    /// darts, if P is nondegenerate.
    pub(crate) open spec fn digraph(self) -> DirectedGraph
        recommends
            self.is_nondegenerate(),
    {
        let heads = self.as_seq().map_values(|d: Dart| d.head).to_set();
        let tails = self.as_seq().map_values(|d: Dart| d.tail).to_set();
        DirectedGraph(Graph { vertices: heads + tails, edges: self.as_seq().to_set() })
    }

    /// Returns the underlying graph of a path.
    ///
    /// [Tutte, Section VI.2] The underlying graph U(P) of a path P of
    /// $$\Gamma$$ is the underlying graph of its digraph $$\Gamma(P)$$.
    pub(crate) open spec fn underlying_graph(self) -> Graph
        recommends
            self.is_nondegenerate(),
    {
        self.digraph().underlying_graph()
    }

    /// Returns if P is a nondegenerate path of digraph G.
    pub(crate) open spec fn is_nondegenerate_path_of(self, g: DirectedGraph) -> bool {
        &&& self.is_nondegenerate()
        &&& self.as_seq().to_set().subset_of(g.underlying_graph().edges)
    }

    /// Returns if P is a nondegenerate, simple path of digraph G.
    pub(crate) open spec fn is_nondegenerate_simple_path_of(self, g: DirectedGraph) -> bool {
        &&& self.is_nondegenerate_path_of(g)
        &&& self.is_simple()
    }

    /// A nondegenerate path with a duplicate head vertex is not head-simple.
    proof fn lemma_duplicate_head_implies_non_head_simpleness(self, i: int, j: int)
        requires
            self.is_nondegenerate(),
            0 <= i < self.as_seq().len(),
            0 <= j < self.as_seq().len(),
            i != j,
            self.as_seq()[i].head == self.as_seq()[j].head,
        ensures
            !self.is_head_simple(),
    {
        let heads = self.as_seq().map_values(|d: Dart| d.head);
        assert(heads[i] == heads[j]);
    }

    /// A nondegenerate path with a duplicate tail vertex is not tail-simple.
    proof fn lemma_duplicate_tail_implies_non_tail_simpleness(self, i: int, j: int)
        requires
            self.is_nondegenerate(),
            0 <= i < self.as_seq().len(),
            0 <= j < self.as_seq().len(),
            i != j,
            self.as_seq()[i].tail == self.as_seq()[j].tail,
        ensures
            !self.is_tail_simple(),
    {
        let tails = self.as_seq().map_values(|d: Dart| d.tail);
        assert(tails[i] == tails[j]);
    }

    /// The initial segment of a simple path is also simple.
    proof fn lemma_init_preserves_simpleness(self)
        requires
            self.is_simple(),
            self.as_seq().len() > 1,
        ensures
            self.init().is_simple(),
    {
        // Get the initial segment of the path (i.e., init(P)).
        let p_init = self.init();

        // The init(P) is head-simple because its sequence of heads is a prefix
        // of P's sequence of heads; if no head vertex appears more than once in
        // P, then no head vertex appears more than once in init(P).
        assert(p_init.is_head_simple()) by {
            let p_heads = self.as_seq().map_values(|d: Dart| d.head);
            let p_init_heads = p_init.as_seq().map_values(|d: Dart| d.head);
            assert(p_init_heads.is_prefix_of(p_heads));
        }

        // The init(P) is tail-simple because its sequence of tails is a prefix
        // of P's sequence of tails; if no tail vertex appears more than once in
        // P, then no tail vertex appears more than once in init(P).
        assert(p_init.is_tail_simple()) by {
            let p_tails = self.as_seq().map_values(|d: Dart| d.tail);
            let p_init_tails = p_init.as_seq().map_values(|d: Dart| d.tail);
            assert(p_init_tails.is_prefix_of(p_tails));
        }
    }

    /// A tail-simple path is necessarily edge-simple.
    proof fn lemma_tail_simple_path_is_dart_simple(self)
        requires
            self.is_nondegenerate(),
            self.is_tail_simple(),
        ensures
            self.is_dart_simple(),
    {
        // Assume that the path is not edge-simple.
        if !self.is_dart_simple() {
            // The path must have duplicates if it isn't edge-simple.
            assert(!self.as_seq().no_duplicates());

            // There has to be an edge that appears more than once in the
            // multiset of path edges.
            assert(exists|d: Dart|
                #![auto]
                {
                    &&& self.as_seq().to_multiset().contains(d)
                    &&& self.as_seq().to_multiset().count(d) > 1
                }) by {
                vstd_specs::seq::lemma_multiset_has_no_duplicates_inv(self.as_seq());
            };

            // If there is an edge that appears more than once, then there must
            // exist two indices that contain the same edge; we select these as
            // our witnesses.
            assert(exists|i: int, j: int|
                {
                    &&& 0 <= i < j < self.as_seq().len()
                    &&& self.as_seq()[i] == self.as_seq()[j]
                });
            let (i, j) = choose|i: int, j: int|
                {
                    &&& 0 <= i < j < self.as_seq().len()
                    &&& self.as_seq()[i] == self.as_seq()[j]
                };

            // The tail vertices of the witness indices must be the same since
            // they are the same edge, which contradicts the precondition that
            // the path is tail-simple.
            assert(!self.is_tail_simple()) by {
                self.lemma_duplicate_tail_implies_non_tail_simpleness(i, j);
            }
            assert(false);
        }
    }

    /// A head-simple path is necessarily dart-simple.
    proof fn lemma_head_simple_path_is_dart_simple(self)
        requires
            self.is_nondegenerate(),
            self.is_head_simple(),
        ensures
            self.is_dart_simple(),
    {
        // Assume that the path is not edge-simple.
        if !self.is_dart_simple() {
            // The path must have duplicates if it isn't edge-simple.
            assert(!self.as_seq().no_duplicates());

            // There has to be an edge that appears more than once in the
            // multiset of path edges.
            assert(exists|d: Dart|
                #![auto]
                {
                    &&& self.as_seq().to_multiset().contains(d)
                    &&& self.as_seq().to_multiset().count(d) > 1
                }) by {
                vstd_specs::seq::lemma_multiset_has_no_duplicates_inv(self.as_seq());
            };

            // If there is an edge that appears more than once, then there must
            // exist two indices that contain the same edge; we select these as
            // our witnesses.
            assert(exists|i: int, j: int|
                {
                    &&& 0 <= i < j < self.as_seq().len()
                    &&& self.as_seq()[i] == self.as_seq()[j]
                });
            let (i, j) = choose|i: int, j: int|
                {
                    &&& 0 <= i < j < self.as_seq().len()
                    &&& self.as_seq()[i] == self.as_seq()[j]
                };

            // The head vertices of the witness indices must be the same since
            // they are the same edge, which contradicts the precondition that
            // the path is head-simple.
            assert(!self.is_head_simple()) by {
                self.lemma_duplicate_head_implies_non_head_simpleness(i, j);
            }
            assert(false);
        }
    }

    /// The digraph of a path is well-formed.
    proof fn axiom_digraph_is_well_formed(self)
        requires
            self.is_nondegenerate(),
        ensures
            self.digraph().well_formed(),
    {
        admit();
    }

    /// The product of two nondegenerate paths is nondegenerate.
    proof fn lemma_nondegenerate_product_is_nondegenerate(self, q: Self)
        requires
            self.is_nondegenerate(),
            q.is_nondegenerate(),
            self.terminus() == q.origin(),
        ensures
            self.product(q).is_nondegenerate(),
    {
        // NOTE: Verus automatically proves this.
    }
}

} // verus!
