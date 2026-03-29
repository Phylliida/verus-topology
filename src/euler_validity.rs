use vstd::prelude::*;
use crate::mesh::*;
use crate::invariants::*;
use crate::euler_ops::{
    fe_h0, fe_h1, fe_a, fe_b, fe_c, fe_d, fe_all_distinct, flip_edge_post,
};

verus! {

//  =============================================================================
//  flip_edge preserves structural invariants
//  =============================================================================
//  Strategy: flip_edge doesn't change counts and only modifies 6 HEs.
//  The 6 modified HEs form two self-contained 3-cycles (h0→b→c and h1→d→a).
//  All other HEs are completely unchanged.
//  Key frame fact: for unmodified h, next(h) and prev(h) are also unmodified
//  (follows from prev being the inverse of next in the old mesh).

//  =============================================================================
//  1. twin_involution preserved
//  =============================================================================

///  flip_edge preserves twin_involution.
///  h0↔h1 twin pair is explicitly maintained. Other twins unchanged.
pub proof fn lemma_flip_edge_preserves_twin_involution(
    old_m: &Mesh, new_m: &Mesh, e: int,
)
    requires
        structurally_valid(old_m),
        flip_edge_post(old_m, new_m, e),
        0 <= e < edge_count(old_m),
        fe_all_distinct(old_m, e),
    ensures
        twin_involution(new_m),
{
    let h0 = fe_h0(old_m, e);
    let h1 = fe_h1(old_m, e);
    let a = fe_a(old_m, e);
    let b = fe_b(old_m, e);
    let c = fe_c(old_m, e);
    let d = fe_d(old_m, e);
    let hcnt = half_edge_count(old_m);

    assert(twin_involution(old_m));

    assert forall|h: int| 0 <= h < half_edge_count(new_m)
    implies new_m.half_edges@[new_m.half_edges@[h].twin as int].twin as int == h
    by {
        if h == h0 {
            //  twin(h0) = h1, twin(h1) = h0
            assert(new_m.half_edges@[h0].twin as int == h1);
            assert(new_m.half_edges@[h1].twin as int == h0);
        } else if h == h1 {
            assert(new_m.half_edges@[h1].twin as int == h0);
            assert(new_m.half_edges@[h0].twin as int == h1);
        } else if h == a || h == b || h == c || h == d {
            //  twin(h) unchanged. Need: the HE at twin(h) also has twin unchanged.
            //  twin(h) is unchanged from old. In old mesh, twin(twin(h)) = h.
            //  If twin(h) ∉ {h0,h1,a,b,c,d}: twin field at twin(h) unchanged,
            //    so new twin(twin(h)) = old twin(twin(h)) = h. ✓
            //  If twin(h) ∈ {a,b,c,d}: twin field preserved for a,b,c,d,
            //    so new twin(twin(h)) = old twin(twin(h)) = h. ✓
            //  If twin(h) = h0: old twin(h0) = h1, so old twin(twin(h)) = twin(h0) = h1 = h.
            //    But h ∈ {a,b,c,d} and h = h1? Contradicts distinctness.
            //  Similarly twin(h) ≠ h1.
            let t = old_m.half_edges@[h].twin as int;
            assert(new_m.half_edges@[h].twin == old_m.half_edges@[h].twin);
            assert(old_m.half_edges@[old_m.half_edges@[h].twin as int].twin as int == h);

            //  Show t ≠ h0: if t = h0, then old twin(h0) = h1, and old twin(t) = old twin(h0) = h1.
            //  But old twin(twin(h)) = h, so h = h1. Contradicts h ∈ {a,b,c,d} and distinctness.
            if t == h0 {
                assert(old_m.half_edges@[t].twin as int == h1);
                assert(h == h1);
                assert(false);
            }
            if t == h1 {
                assert(old_m.half_edges@[t].twin as int == h0);
                assert(h == h0);
                assert(false);
            }
            //  t ∉ {h0,h1}, so twin field at t is preserved in new_m
            if t == a || t == b || t == c || t == d {
                assert(new_m.half_edges@[t].twin == old_m.half_edges@[t].twin);
            } else {
                assert(new_m.half_edges@[t] == old_m.half_edges@[t]);
            }
        } else {
            //  h ∉ {h0,h1,a,b,c,d}: twin unchanged
            assert(new_m.half_edges@[h] == old_m.half_edges@[h]);
            let t = old_m.half_edges@[h].twin as int;
            assert(old_m.half_edges@[t].twin as int == h);
            //  Show t ∉ {h0,h1}: same argument as above
            if t == h0 {
                assert(old_m.half_edges@[h0].twin as int == h1);
                assert(h == h1);
                assert(false);
            }
            if t == h1 {
                assert(old_m.half_edges@[h1].twin as int == h0);
                assert(h == h0);
                assert(false);
            }
            if t == a || t == b || t == c || t == d {
                assert(new_m.half_edges@[t].twin == old_m.half_edges@[t].twin);
            } else {
                assert(new_m.half_edges@[t] == old_m.half_edges@[t]);
            }
        }
    }
}

//  =============================================================================
//  2. prev_next_bidirectional preserved
//  =============================================================================

///  flip_edge preserves prev_next_bidirectional.
///  New cycles: h0→b→c→h0 and h1→d→a→h1, with consistent prev pointers.
pub proof fn lemma_flip_edge_preserves_prev_next(
    old_m: &Mesh, new_m: &Mesh, e: int,
)
    requires
        structurally_valid(old_m),
        flip_edge_post(old_m, new_m, e),
        0 <= e < edge_count(old_m),
        fe_all_distinct(old_m, e),
        //  Triangle conditions
        old_m.half_edges@[fe_b(old_m, e)].next as int == fe_h0(old_m, e),
        old_m.half_edges@[fe_d(old_m, e)].next as int == fe_h1(old_m, e),
    ensures
        prev_next_bidirectional(new_m),
{
    let h0 = fe_h0(old_m, e);
    let h1 = fe_h1(old_m, e);
    let a = fe_a(old_m, e);
    let b = fe_b(old_m, e);
    let c = fe_c(old_m, e);
    let d = fe_d(old_m, e);
    let hcnt = half_edge_count(old_m);

    assert(prev_next_bidirectional(old_m));

    //  Prove next_prev_inverse_only: prev(next(h)) = h
    assert forall|h: int| 0 <= h < half_edge_count(new_m)
    implies next_prev_inverse_at(new_m, h)
    by {
        if h == h0 {
            //  next(h0)=b, prev(b)=h0
            assert(new_m.half_edges@[new_m.half_edges@[h0].next as int].prev as int == h0);
        } else if h == h1 {
            assert(new_m.half_edges@[new_m.half_edges@[h1].next as int].prev as int == h1);
        } else if h == a {
            //  next(a)=h1, prev(h1)=a
            assert(new_m.half_edges@[new_m.half_edges@[a].next as int].prev as int == a);
        } else if h == b {
            //  next(b)=c, prev(c)=b
            assert(new_m.half_edges@[new_m.half_edges@[b].next as int].prev as int == b);
        } else if h == c {
            //  next(c)=h0, prev(h0)=c
            assert(new_m.half_edges@[new_m.half_edges@[c].next as int].prev as int == c);
        } else if h == d {
            //  next(d)=a, prev(a)=d
            assert(new_m.half_edges@[new_m.half_edges@[d].next as int].prev as int == d);
        } else {
            //  Unmodified h: next(h) and prev(h) unchanged.
            //  Show next(h) ∉ {h0,h1,a,b,c,d}: prev is inverse of next in old mesh,
            //  so next(h) = x means h = prev(x). For x in modified set, prev(x) is
            //  another modified HE. Since h ∉ modified set, next(h) ∉ modified set.
            assert(new_m.half_edges@[h] == old_m.half_edges@[h]);
            let nxt = old_m.half_edges@[h].next as int;
            assert(next_prev_inverse_at(old_m, h));

            //  nxt ∉ {h0,h1}: from triangle, prev(h0)=b, so next maps to h0 only from b.
            //  Since h ≠ b, nxt ≠ h0. Similarly nxt ≠ h1.
            if nxt == h0 {
                assert(next_prev_inverse_at(old_m, b));
                assert(old_m.half_edges@[old_m.half_edges@[b].next as int].prev as int == b as int);
                assert(old_m.half_edges@[h0].prev as int == b);
                assert(next_prev_inverse_at(old_m, h));
                assert(old_m.half_edges@[h0].prev as int == h);
                assert(h == b);
                assert(false);
            }
            if nxt == h1 {
                assert(next_prev_inverse_at(old_m, d));
                assert(old_m.half_edges@[old_m.half_edges@[d].next as int].prev as int == d as int);
                assert(old_m.half_edges@[h1].prev as int == d);
                assert(next_prev_inverse_at(old_m, h));
                assert(old_m.half_edges@[h1].prev as int == h);
                assert(h == d);
                assert(false);
            }
            //  nxt ∉ {a}: old next(h0)=a, so next maps to a only from h0. h≠h0 → nxt≠a.
            if nxt == a {
                assert(next_prev_inverse_at(old_m, h0));
                assert(old_m.half_edges@[a].prev as int == h0);
                assert(next_prev_inverse_at(old_m, h));
                assert(old_m.half_edges@[a].prev as int == h);
                assert(h == h0);
                assert(false);
            }
            if nxt == b {
                assert(next_prev_inverse_at(old_m, a));
                assert(old_m.half_edges@[b].prev as int == a);
                assert(next_prev_inverse_at(old_m, h));
                assert(old_m.half_edges@[b].prev as int == h);
                assert(h == a);
                assert(false);
            }
            if nxt == c {
                assert(next_prev_inverse_at(old_m, h1));
                assert(old_m.half_edges@[c].prev as int == h1);
                assert(next_prev_inverse_at(old_m, h));
                assert(old_m.half_edges@[c].prev as int == h);
                assert(h == h1);
                assert(false);
            }
            if nxt == d {
                assert(next_prev_inverse_at(old_m, c));
                assert(old_m.half_edges@[d].prev as int == c);
                assert(next_prev_inverse_at(old_m, h));
                assert(old_m.half_edges@[d].prev as int == h);
                assert(h == c);
                assert(false);
            }
            //  nxt ∉ modified set → prev(nxt) unchanged
            assert(new_m.half_edges@[nxt] == old_m.half_edges@[nxt]);
        }
    }

    //  Prove prev_next_inverse_only: next(prev(h)) = h
    assert forall|h: int| 0 <= h < half_edge_count(new_m)
    implies prev_next_inverse_at(new_m, h)
    by {
        if h == h0 {
            //  prev(h0)=c, next(c)=h0
            assert(new_m.half_edges@[new_m.half_edges@[h0].prev as int].next as int == h0);
        } else if h == h1 {
            assert(new_m.half_edges@[new_m.half_edges@[h1].prev as int].next as int == h1);
        } else if h == a {
            assert(new_m.half_edges@[new_m.half_edges@[a].prev as int].next as int == a);
        } else if h == b {
            assert(new_m.half_edges@[new_m.half_edges@[b].prev as int].next as int == b);
        } else if h == c {
            assert(new_m.half_edges@[new_m.half_edges@[c].prev as int].next as int == c);
        } else if h == d {
            assert(new_m.half_edges@[new_m.half_edges@[d].prev as int].next as int == d);
        } else {
            assert(new_m.half_edges@[h] == old_m.half_edges@[h]);
            let prv = old_m.half_edges@[h].prev as int;
            assert(prev_next_inverse_at(old_m, h));

            //  prv ∉ modified set (symmetric argument to above)
            if prv == h0 {
                assert(prev_next_inverse_at(old_m, c));
                assert(old_m.half_edges@[old_m.half_edges@[c].prev as int].next as int == c as int);
                //  old next(prev(c)) = c. old prev(c) = h1. old next(h1) = c.
                //  But here we need: if prv = h0, then h = old next(h0) = a.
                assert(prev_next_inverse_at(old_m, h));
                assert(old_m.half_edges@[old_m.half_edges@[h].prev as int].next as int == h);
                assert(old_m.half_edges@[h0].next as int == h);
                assert(h == a);
                assert(false);
            }
            if prv == h1 {
                assert(prev_next_inverse_at(old_m, h));
                assert(old_m.half_edges@[h1].next as int == h);
                assert(h == c);
                assert(false);
            }
            if prv == a {
                assert(prev_next_inverse_at(old_m, h));
                assert(old_m.half_edges@[a].next as int == h);
                assert(h == b);
                assert(false);
            }
            if prv == b {
                assert(prev_next_inverse_at(old_m, h));
                assert(old_m.half_edges@[b].next as int == h);
                assert(h == h0);
                assert(false);
            }
            if prv == c {
                assert(prev_next_inverse_at(old_m, h));
                assert(old_m.half_edges@[c].next as int == h);
                assert(h == d);
                assert(false);
            }
            if prv == d {
                assert(prev_next_inverse_at(old_m, h));
                assert(old_m.half_edges@[d].next as int == h);
                assert(h == h1);
                assert(false);
            }
            assert(new_m.half_edges@[prv] == old_m.half_edges@[prv]);
        }
    }
}

//  =============================================================================
//  3. Counting invariants (trivial — counts unchanged)
//  =============================================================================

pub proof fn lemma_flip_edge_preserves_he_edge_relation(
    old_m: &Mesh, new_m: &Mesh, e: int,
)
    requires
        half_edge_edge_count_relation(old_m),
        flip_edge_post(old_m, new_m, e),
    ensures
        half_edge_edge_count_relation(new_m),
{}

pub proof fn lemma_flip_edge_preserves_he_face_bound(
    old_m: &Mesh, new_m: &Mesh, e: int,
)
    requires
        half_edge_face_count_lower_bound(old_m),
        flip_edge_post(old_m, new_m, e),
    ensures
        half_edge_face_count_lower_bound(new_m),
{}

//  =============================================================================
//  4. index_bounds for half_edges preserved
//  =============================================================================

///  flip_edge preserves the half_edges part of index_bounds:
///  all field values in half_edges are valid indices.
pub proof fn lemma_flip_edge_preserves_he_index_bounds(
    old_m: &Mesh, new_m: &Mesh, e: int,
)
    requires
        structurally_valid(old_m),
        flip_edge_post(old_m, new_m, e),
        0 <= e < edge_count(old_m),
        fe_all_distinct(old_m, e),
    ensures
        forall|h: int| 0 <= h < half_edge_count(new_m) ==> {
            let he = #[trigger] new_m.half_edges@[h];
            &&& (he.twin as int) < half_edge_count(new_m)
            &&& (he.next as int) < half_edge_count(new_m)
            &&& (he.prev as int) < half_edge_count(new_m)
            &&& (he.vertex as int) < vertex_count(new_m)
            &&& (he.edge as int) < edge_count(new_m)
            &&& (he.face as int) < face_count(new_m)
        },
{
    let h0 = fe_h0(old_m, e);
    let h1 = fe_h1(old_m, e);
    let a = fe_a(old_m, e);
    let b = fe_b(old_m, e);
    let c = fe_c(old_m, e);
    let d = fe_d(old_m, e);
    let hcnt = half_edge_count(old_m);

    assert(index_bounds(old_m));

    assert forall|h: int| 0 <= h < half_edge_count(new_m)
    implies {
        let he = #[trigger] new_m.half_edges@[h];
        &&& (he.twin as int) < half_edge_count(new_m)
        &&& (he.next as int) < half_edge_count(new_m)
        &&& (he.prev as int) < half_edge_count(new_m)
        &&& (he.vertex as int) < vertex_count(new_m)
        &&& (he.edge as int) < edge_count(new_m)
        &&& (he.face as int) < face_count(new_m)
    }
    by {
        if h == h0 || h == h1 || h == a || h == b || h == c || h == d {
            //  All field values are existing valid indices from old mesh
            //  h0: twin=h1, next=b, prev=c, vertex=v_d, edge=edge_idx, face=f0
            //  h1: twin=h0, next=d, prev=a, vertex=v_b, edge=edge_idx, face=f1
            //  a,b,c,d: preserved fields from old mesh (valid by old index_bounds)
            let old_he = old_m.half_edges@[h];
            assert((old_he.twin as int) < hcnt);
            assert((old_he.next as int) < hcnt);
            assert((old_he.prev as int) < hcnt);
            assert((old_he.vertex as int) < vertex_count(old_m));
            assert((old_he.edge as int) < edge_count(old_m));
            assert((old_he.face as int) < face_count(old_m));
        } else {
            //  Unmodified: all fields equal to old mesh
            assert(new_m.half_edges@[h] == old_m.half_edges@[h]);
        }
    }
}

} //  verus!
