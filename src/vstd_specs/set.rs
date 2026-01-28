use vstd::prelude::*;

verus! {

/// A set S that contains a single element contains an element.
pub proof fn lemma_set_with_single_element_contains_element<T>(s: Set<T>)
    requires
        s.finite(),
        s.len() == 1,
    ensures
        exists|x: T| s.contains(x),
{
    // If there is no element that is contained in set S, then S must be empty.
    // This contradicts the precondition that S contains one element.
    if !(exists|x: T| s.contains(x)) {
        assert(s.is_empty());
        assert(s.len() != 1);
        assert(false);
    }
}

/// A set S that contains a single element is a singleton.
pub proof fn lemma_set_with_single_element_is_singleton<T>(s: Set<T>)
    requires
        s.finite(),
        s.len() == 1,
    ensures
        s.is_singleton(),
{
    // Since S contains one element, it must contain some element x.
    assert(exists|x: T| s.contains(x)) by {
        lemma_set_with_single_element_contains_element(s);
    }
    let x = choose|x: T| s.contains(x);

    // Assume that S is not a singleton.
    if !s.is_singleton() {
        // Then S must contain another element y.
        assert(exists|y: T| y != x && s.contains(y));
        let y = choose|y: T| y != x && s.contains(y);

        // Let T be a set containing x and y. By construction, T is a subset of
        // S, which means that S contains more than one element. This
        // contradicts the precondition that S contains one element.
        let t = set![x, y];
        assert(t.subset_of(s));
        assert(s.len() > 1) by {
            assert(t.len() == 2);
            vstd::set_lib::lemma_len_subset(t, s);
        }
        assert(false);
    }
}

/// If an injective map is applied to each element of a set to construct another
/// set, the two sets have the same size.
///
/// This lemma is essentially the same as [`lemma_map_size`], but instead uses a
/// `Map` instead of a total injective function. The `Map` acts as a partial
/// injective function; its domain may not be full.
pub proof fn lemma_partial_map_size<A, B>(x: Set<A>, y: Set<B>, m: Map<A, B>)
    requires
        x.finite(),
        y.finite(),
        m.is_injective(),
        forall|a: A| #![auto] x.contains(a) ==> m.contains_key(a),
        forall|a: A| #![auto] x.contains(a) ==> y.contains(m[a]),
        forall|b: B|
            #![auto]
            y.contains(b) ==> exists|a: A|
                #![auto]
                {
                    &&& x.contains(a)
                    &&& m[a] == b
                },
    ensures
        x.len() == y.len(),
    decreases x.len(), y.len(),
{
    broadcast use vstd::set_lib::group_set_properties;

    if x.len() != 0 {
        let a = x.choose();
        lemma_partial_map_size(x.remove(a), y.remove(m[a]), m);
    }
}

/// Applying a partial map commutes with the union of two sets.
///
/// This lemma is essentially the same as [`Set::lemma_map_union_commute`], but
/// instead uses a `Map` instead of a total injective function. The `Map` acts as a partial
/// injective function; its domain may not be full.
pub proof fn lemma_partial_map_union_commute<A, B>(x: Set<A>, y: Set<A>, m: Map<A, B>)
    requires
        forall|a: A| #![auto] x.contains(a) ==> m.contains_key(a),
        forall|a: A| #![auto] y.contains(a) ==> m.contains_key(a),
    ensures
        x.union(y).map(|a: A| m[a]) == x.map(|a: A| m[a]).union(y.map(|a: A| m[a])),
{
    broadcast use vstd::set::group_set_axioms;

    let lhs = x.union(y).map(|a: A| m[a]);
    let rhs = x.map(|a: A| m[a]).union(y.map(|a: A| m[a]));

    assert forall|elem: B| rhs.contains(elem) implies lhs.contains(elem) by {
        if x.map(|a: A| m[a]).contains(elem) {
            let preimage = choose|preimage: A| #[trigger]
                x.contains(preimage) && m[preimage] == elem;
            assert(x.union(y).contains(preimage));
        } else {
            assert(y.map(|a: A| m[a]).contains(elem));
            let preimage = choose|preimage: A| #[trigger]
                y.contains(preimage) && m[preimage] == elem;
            assert(x.union(y).contains(preimage));
        }
    }
}

/// TODO: Properly document (or remove) this lemma.
pub proof fn lemma_disjoint_union_is_disjoint<T>(s: Set<T>, t: Set<T>, x: T, y: T)
    requires
        s.disjoint(t),
        !s.contains(y),
        !t.contains(x),
        x != y,
    ensures
        s.insert(x).disjoint(t.insert(y)),
{
    // NOTE: Verus automatically proves this.
}

/// Let T be a subset of S that contains all but one element x of S. Inserting x
/// into T yields a set that is equal to S.
pub proof fn lemma_insert_restores_missing<T>(s: Set<T>, t: Set<T>, x: T)
    requires
        s.finite(),
        t.finite(),
        t.subset_of(s),
        s.len() == t.len() + 1,
        s.contains(x),
        !t.contains(x),
    ensures
        s == t.insert(x),
{
    let u = t.insert(x);
    assert(u == s) by {
        assert(u.len() == s.len()) by {
            vstd::set::axiom_set_insert_len(t, x);
        }
        assert(u.subset_of(s));
        vstd::set_lib::lemma_subset_equality(u, s);
    }
}

pub proof fn lemma_composition_equal_to_chained_map<A, B, C>(
    s: Set<A>,
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> C,
)
    requires
        s.finite(),
    ensures
        s.map(|a: A| g(f(a))) == s.map(f).map(g),
{
    let lhs = s.map(|a: A| g(f(a)));
    let rhs = s.map(f).map(g);

    assert forall|x: C| #[trigger] lhs.contains(x) implies rhs.contains(x) by {
        if !lhs.is_empty() {
            assert(exists|a: A|
                {
                    &&& s.contains(a)
                    &&& g(f(a)) == x
                });
            let a = choose|a: A|
                {
                    &&& s.contains(a)
                    &&& g(f(a)) == x
                };
            assert(s.map(f).contains(f(a)));
            assert(rhs.contains(g(f(a))));
        }
    }
}

pub proof fn lemma_map_composition_equality<A, B, C>(
    s: Set<A>,
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> C,
    h: spec_fn(A) -> C,
)
    requires
        s.finite(),
        forall|a: A| #[trigger] g(f(a)) == h(a),
    ensures
        s.map(f).map(g) == s.map(h),
{
    assert(s.map(|a| g(f(a))) == s.map(f).map(g)) by {
        lemma_composition_equal_to_chained_map(s, f, g);
    }
    assert(s.map(|a| g(f(a))) == s.map(h));
}

pub proof fn lemma_application_map_equivalence<A, B>(x: A, f: spec_fn(A) -> B)
    ensures
        set![f(x)] == set![x].map(f),
{
    let s = set![x];
    let t = Set::new(
        |y: B|
            exists|z: A|
                {
                    &&& s.contains(z)
                    &&& y == #[trigger] f(z)
                },
    );
    assert(s.map(f) == t);
}

pub proof fn lemma_application_map_equivalence_composes<A, B>(x: A, y: A, f: spec_fn(A) -> B)
    ensures
        set![f(x), f(y)] == set![x, y].map(f),
{
    let s = set![x, y];
    let t = Set::new(
        |z: B|
            exists|w: A|
                {
                    &&& s.contains(w)
                    &&& z == #[trigger] f(w)
                },
    );
    assert(s.map(f) == t);
}

pub proof fn lemma_map_union_commute2<A, B>(s: Set<A>, t: Set<A>, u: Set<A>, f: spec_fn(A) -> B)
    ensures
        (s + t + u).map(f) == s.map(f) + t.map(f) + u.map(f),
{
    assert((s + t).map(f) + u.map(f) == (s + t + u).map(f)) by {
        (s + t).lemma_map_union_commute(u, f);
    }

    assert(s.map(f) + t.map(f) == (s + t).map(f)) by {
        s.lemma_map_union_commute(t, f);
    }
}

} // verus!
