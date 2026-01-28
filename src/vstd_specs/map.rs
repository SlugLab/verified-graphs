use vstd::prelude::*;

verus! {

/// The union of two injective maps with disjoint domains and values is injective.
pub proof fn lemma_disjoint_injective_map_union_is_injective<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        m1.is_injective(),
        m2.is_injective(),
        m1.dom().disjoint(m2.dom()),
        m1.values().disjoint(m2.values()),
    ensures
        m1.union_prefer_right(m2).is_injective(),
{
    // Assume that the union is not injective.
    let m = m1.union_prefer_right(m2);
    if !m.is_injective() {
        // There must exist two distinct keys x and y in the domain of the union
        // that have the same value.
        assert(exists|x: K, y: K|
            #![auto]
            {
                &&& x != y
                &&& m.dom().contains(x)
                &&& m.dom().contains(y)
                &&& m[x] == m[y]
            });
        let (x, y) = choose|x: K, y: K|
            #![auto]
            {
                &&& x != y
                &&& m.dom().contains(x)
                &&& m.dom().contains(y)
                &&& m[x] == m[y]
            };

        // Since both maps are injective, x and y must be keys in different maps.
        assert({
            ||| m1.dom().contains(x) && m2.dom().contains(y)
            ||| m1.dom().contains(y) && m2.dom().contains(x)
        });

        // Assume that x is in the first map and y is in the second map. Since
        // they map to the same in the union, their values must be equal in the
        // different maps. This contradicts the maps having disjoint values.
        if m1.dom().contains(x) && m2.dom().contains(y) {
            assert(m1[x] == m2[y]);
            assert(m1.values().contains(m1[x]));
            assert(m2.values().contains(m2[y]));
            assert(!(m1.values().disjoint(m2.values())));
            assert(false);
        }

        // The same contradiction occurs if we assume that y is in the first map
        // and x is in the second map.
        if m1.dom().contains(y) && m2.dom().contains(x) {
            assert(m1[y] == m2[x]);
            assert(m1.values().contains(m1[y]));
            assert(m2.values().contains(m2[x]));
            assert(!(m1.values().disjoint(m2.values())));
            assert(false);
        }
    }
}

/// A map with a finite domain has finite values.
pub proof fn lemma_finite_dom_has_finite_values<K, V>(m: Map<K, V>)
    requires
        m.dom().finite(),
    ensures
        m.values().finite(),
{
    // Let S be the set of values in the map constructed by mapping each key in
    // the map's domain to its corresponding value. By construction, S must be
    // equivalent to the set of values in the map.
    let s = m.dom().map(|k: K| m[k]);
    assert(m.values() == s);

    // S must be finite since the resulting set of a mapping over a finite set
    // is also finite.
    assert(s.finite()) by {
        m.dom().lemma_map_finite(|k: K| m[k]);
    }
}

/// TODO: Finish documentation or remove proof.
pub proof fn lemma_unique_insertion_preserves_injectivity<K, V>(m: Map<K, V>, k: K, v: V)
    requires
        m.is_injective(),
        !m.contains_key(k),
        forall|x: K| #![auto] m.dom().contains(x) ==> m[x] != v,
    ensures
        m.insert(k, v).is_injective(),
{
    // NOTE: Verus automatically proves this.
}

/// The cardinalities of the domain and values of an injective map are equal.
pub proof fn lemma_injective_map_values_len<K, V>(m: Map<K, V>)
    requires
        m.dom().finite(),
        m.is_injective(),
    ensures
        m.values().len() == m.dom().len(),
    decreases m.len(),
{
    if m.is_empty() {
        // Base case: the map is empty, so both the domain and values are empty.
        assert(m.dom().is_empty());
        assert(m.values().is_empty());
    } else {
        // Let K be a key in the map's domain, and N be the map with K removed.
        let k = m.dom().choose();
        let n = m.remove(k);

        // The cardinality of the domain of N is one less than that of M, since
        // it does not contain K.
        assert(m.dom().len() == n.dom().len() + 1) by {
            m.lemma_remove_key_len(k);
        }

        // The cardinality of the values of N is one less than that of M, since
        // it does not contain K's value.
        assert(m.values().len() == n.values().len() + 1) by {
            // Adding K's value to the values of N yields the values of M.
            assert(m.values() == n.values().insert(m[k]));

            // Since M's values are finite, N's values must also be finite.
            assert(n.values().finite()) by {
                assert(m.values().finite()) by {
                    vstd::map_lib::lemma_values_finite(m);
                }
                assert(n.values().subset_of(m.values()));
                vstd::set_lib::lemma_set_subset_finite(m.values(), n.values());
            }

            // K's value is not in N's values, so inserting it increases the
            // cardinality of N's values by one.
            assert(n.values().insert(m[k]).len() == n.values().len() + 1) by {
                assert(!n.values().contains(m[k]));
                vstd::set::axiom_set_insert_len(n.values(), m[k]);
            }
        }

        // Recurse until the map is empty.
        lemma_injective_map_values_len(n);
    }
}

/// If M1 is a submap of M2, then the values of M1 are a subset of the values of M2.
pub proof fn lemma_submap_values_is_subset<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        m1.submap_of(m2),
    ensures
        m1.values().subset_of(m2.values()),
{
    // If M1 is a submap of M2, then every key in M1's domain is also in M2's
    // domain, and the values of M1 are the same as those of M2 for those keys.
    assert(forall|k: K| #![auto] m1.dom().contains(k) ==> m2.dom().contains(k));
    assert(forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]);

    // Thus, the values of M1 must be a subset of the values of M2.
    assert(m1.values().subset_of(m2.values()));
}

pub proof fn lemma_mapped_value_in_values<K, V>(m: Map<K, V>, k: K, v: V)
    requires
        m.dom().contains(k),
        m[k] == v,
    ensures
        m.values().contains(m[k]),
{
    // NOTE: Verus automatically proves this.
}

pub proof fn lemma_insert_domain_finite<K, V>(m: Map<K, V>, k: K, v: V)
    requires
        m.dom().finite(),
    ensures
        m.insert(k, v).dom().finite(),
{
    // NOTE: Verus automatically proves this.
}

pub proof fn lemma_insert_values_finite<K, V>(m: Map<K, V>, k: K, v: V)
    requires
        m.dom().finite(),
    ensures
        m.insert(k, v).values().finite(),
{
    let n = m.insert(k, v);
    assert(n.dom().finite()) by {
        lemma_insert_domain_finite(m, k, v);
    };
    assert(n.values().finite()) by {
        lemma_finite_dom_has_finite_values(n);
    };
}

} // verus!
