use vstd::prelude::*;

verus! {

/// If, in a sequence's conversion to a multiset, there exists an element that
/// doesn't only appear a single time, then the sequence must contain a
/// duplicated element.
///
/// This is the contrapositive of [`Seq::lemma_multiset_has_no_duplicates`].
pub proof fn lemma_multiset_has_no_duplicates_contra<T>(s: Seq<T>)
    requires
        exists|elem: T|
            {
                &&& s.to_multiset().contains(elem)
                &&& s.to_multiset().count(elem) != 1
            },
    ensures
        !s.no_duplicates(),
{
    // We know that a witness element exists due to the preconditions.
    let elem = choose|elem: T|
        {
            &&& s.to_multiset().contains(elem)
            &&& s.to_multiset().count(elem) != 1
        };

    // The witness must have a count greater than 1 in the multiset since it
    // appears in the sequence and doesn't appear only a single time.
    assert(s.to_multiset().count(elem) > 1) by {
        assert(s.to_multiset().count(elem) != 0) by {
            s.to_multiset_ensures();
        };
    }

    // A sequence that has no duplicates implies that each element's count in
    // the multiset is 1. Since we have a witness that appears more than once,
    // the sequence cannot have no duplicates; there is at least one duplicate element.
    assert(!s.no_duplicates()) by {
        if s.no_duplicates() {
            assert(forall|elem: T|
                s.to_multiset().contains(elem) ==> s.to_multiset().count(elem) == 1) by {
                s.lemma_multiset_has_no_duplicates();
            }
            assert(false);
        }
    }
}

/// If a sequence contains duplicates, it is nonempty.
pub proof fn lemma_seq_with_duplicates_is_nonempty<T>(s: Seq<T>)
    requires
        !s.no_duplicates(),
    ensures
        !(s.len() == 0),
{
    // Assume that the sequence is empty. This means that it trivially contains
    // no duplicates, which contradicts the precondition.
    if s.len() == 0 {
        assert(forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]);
        assert(s.no_duplicates());
        assert(false);
    }
}

// If a sequence is nonempty, there exists an element that is in the sequence.
pub proof fn lemma_nonempty_seq_contains_elem<T>(s: Seq<T>)
    requires
        !(s.len() == 0),
    ensures
        exists|elem: T| s.contains(elem),
{
    // We know that the length of a nonempty is at greater than 0 since it
    // cannot be negative. From this, we know that sequence must at least
    // contain its first element, thus demonstrating that there exists an
    // element that is in the sequence.
    assert(s.len() > 0);
    assert(s.contains(s[0]));
}

/// If a sequence doesn't contain duplicates, there exists an element in the
/// sequence converted to a multiset with a count greater than 1.
///
/// This is the inverse of [`Seq::lemma_multiset_has_no_duplicates`].
pub proof fn lemma_multiset_has_no_duplicates_inv<T>(s: Seq<T>)
    requires
        !s.no_duplicates(),
    ensures
        exists|elem: T|
            #![auto]
            {
                &&& s.to_multiset().contains(elem)
                &&& s.to_multiset().count(elem) > 1
            },
{
    // If the sequence contains duplicates, there must be an element that is
    // contained in the sequence converted to a multiset.
    assert(exists|elem: T| #![auto] s.to_multiset().contains(elem)) by {
        // There must exist an element that is contained by the sequence since
        // the sequence contains duplicates and thus is nonempty.
        assert(exists|elem: T| #![auto] s.contains(elem)) by {
            lemma_seq_with_duplicates_is_nonempty(s);
            lemma_nonempty_seq_contains_elem(s);
        }

        // Any element contained in a sequence must also be contained in the
        // sequence converted to a multiset.
        let elem = choose|elem: T| #![auto] s.contains(elem);
        assert(s.to_multiset().contains(elem)) by {
            s.to_multiset_ensures();
        }
    }

    // We've now demonstrated that there exists at least one element in the
    // sequence converted to a multiset. We now assume that there is no element
    // in the sequence converted to a multiset that has a count greater than 1.
    if !(exists|elem: T|
        #![auto]
        {
            &&& s.to_multiset().contains(elem)
            &&& s.to_multiset().count(elem) > 1
        }) {
        // If no contained element has a count greater than 1, then all
        // contained elements must have a count equal to 1; an element's count
        // must be greater than 0 since it's contained, and less than or equal
        // to 1 due to our assumption.
        assert(forall|elem: T|
            #![auto]
            s.to_multiset().contains(elem) ==> s.to_multiset().count(elem) == 1) by {
            assert(!(forall|elem: T|
                #![auto]
                s.to_multiset().contains(elem) ==> s.to_multiset().count(elem) > 1));
            assert(forall|elem: T|
                #![auto]
                s.to_multiset().contains(elem) ==> s.to_multiset().count(elem) != 0) by {
                s.to_multiset_ensures();
            }
        }

        // If all contained elements have a count equal to 1, then the sequence
        // must contain no duplicates, which contradicts our precondition.
        assert(s.no_duplicates()) by {
            s.lemma_multiset_has_no_duplicates_conv();
        };
        assert(false);
    }
}

} // verus!
