use vstd::prelude::*;
use crate::mesh::*;
use crate::iteration::*;
use crate::invariants::*;

verus! {

// =============================================================================
// Helper for check_edge_twin_duality: positive case
// =============================================================================

/// Proves edge_exactly_two_half_edges_at(m, e) from concrete witnesses.
pub(crate) proof fn lemma_prove_edge_exactly_two_at(
    m: &Mesh,
    e: int,
    w0: int,
    w1: int,
    hcnt: int,
)
    requires
        0 <= e < edge_count(m),
        hcnt == half_edge_count(m),
        0 <= w0 < hcnt,
        0 <= w1 < hcnt,
        w0 != w1,
        m.half_edges@[w0].edge as int == e,
        m.half_edges@[w1].edge as int == e,
        m.half_edges@[w0].twin as int == w1,
        m.half_edges@[w1].twin as int == w0,
        m.edge_half_edges@[e] as int == w0 || m.edge_half_edges@[e] as int == w1,
        forall|j: int|
            0 <= j < hcnt && (#[trigger] m.half_edges@[j].edge as int) == e
                ==> (j == w0 || j == w1),
    ensures
        edge_exactly_two_half_edges_at(m, e),
{
    // Z3 auto-closes: existential witnesses are directly in requires
}

// =============================================================================
// Helper for check_edge_twin_duality: negative case
// =============================================================================

/// Proves !edge_exactly_two_half_edges_at(m, e) by contradiction from failure evidence.
pub(crate) proof fn lemma_disprove_edge_exactly_two_at(
    m: &Mesh,
    e: int,
    h0: int,
    h1: int,
    h2: int,
    count: int,
    too_many: bool,
    count_two: bool,
    twins_ok: bool,
    rep_ok: bool,
    hcnt: int,
)
    requires
        index_bounds(m),
        0 <= e < edge_count(m),
        hcnt == half_edge_count(m),
        count_two == (!too_many && count == 2),
        0 <= count <= 2,
        // Inner loop postcondition:
        count == 0 ==> forall|j: int|
            0 <= j < hcnt ==> (#[trigger] m.half_edges@[j].edge as int) != e,
        count >= 1 ==> {
            &&& 0 <= h0 < hcnt
            &&& (#[trigger] m.half_edges@[h0 as int].edge as int) == e
        },
        count >= 2 ==> {
            &&& 0 <= h1 < hcnt
            &&& h0 != h1
            &&& (#[trigger] m.half_edges@[h1 as int].edge as int) == e
        },
        too_many ==> {
            &&& count == 2
            &&& 0 <= h2 < hcnt
            &&& h2 != h0
            &&& h2 != h1
            &&& (#[trigger] m.half_edges@[h2 as int].edge as int) == e
        },
        !too_many && count == 1 ==> forall|j: int|
            0 <= j < hcnt && (#[trigger] m.half_edges@[j].edge as int) == e
                ==> j == h0,
        !too_many && count == 2 ==> forall|j: int|
            0 <= j < hcnt && (#[trigger] m.half_edges@[j].edge as int) == e
                ==> (j == h0 || j == h1),
        // Twins/rep (only meaningful when count_two):
        count_two ==> {
            &&& 0 <= h0 < hcnt
            &&& 0 <= h1 < hcnt
        },
        twins_ok == (count_two && m.half_edges@[h0].twin as int == h1 && m.half_edges@[h1].twin as int == h0),
        rep_ok == (count_two && (m.edge_half_edges@[e] as int == h0 || m.edge_half_edges@[e] as int == h1)),
        // The edge check failed:
        !(count_two && twins_ok && rep_ok),
    ensures
        !edge_exactly_two_half_edges_at(m, e),
{
    if edge_exactly_two_half_edges_at(m, e) {
        let (w0, w1) = choose|w0: int, w1: int| {
            &&& 0 <= w0 < hcnt
            &&& 0 <= w1 < hcnt
            &&& w0 != w1
            &&& (#[trigger] m.half_edges@[w0].edge as int) == e
            &&& (#[trigger] m.half_edges@[w1].edge as int) == e
            &&& (m.half_edges@[w0].twin as int) == w1
            &&& (m.half_edges@[w1].twin as int) == w0
            &&& ((m.edge_half_edges@[e] as int) == w0 || (m.edge_half_edges@[e] as int) == w1)
            &&& forall|hh: int|
                0 <= hh < hcnt && (#[trigger] m.half_edges@[hh].edge as int) == e
                    ==> (hh == w0 || hh == w1)
        };

        if too_many {
            let i0 = h0;
            let i1 = h1;
            let i2 = h2;
            assert(count == 2);
            assert(0 <= i0 < hcnt);
            assert(0 <= i1 < hcnt);
            assert(0 <= i2 < hcnt);
            assert(i0 != i1);
            assert(i2 != i0);
            assert(i2 != i1);
            assert((m.half_edges@[i0].edge as int) == e);
            assert((m.half_edges@[i1].edge as int) == e);
            assert((m.half_edges@[i2].edge as int) == e);
            assert(i0 == w0 || i0 == w1);
            assert(i1 == w0 || i1 == w1);
            assert(i2 == w0 || i2 == w1);
            if i0 == w0 {
                assert(i1 == w1);
                assert(i2 == w0 || i2 == w1);
                assert(i2 == i0 || i2 == i1);
            } else {
                assert(i0 == w1);
                assert(i1 == w0);
                assert(i2 == w0 || i2 == w1);
                assert(i2 == i0 || i2 == i1);
            }
            assert(false);
        } else if count == 0 {
            assert(0 <= w0 < hcnt);
            assert((m.half_edges@[w0].edge as int) != e);
            assert(false);
        } else if count == 1 {
            let i0 = h0;
            assert(0 <= i0 < hcnt);
            assert((m.half_edges@[i0].edge as int) == e);
            assert(w0 == i0);
            assert(w1 == i0);
            assert(false);
        } else {
            assert(count == 2);
            assert(count_two);
            let i0 = h0;
            let i1 = h1;
            assert(0 <= i0 < hcnt);
            assert(0 <= i1 < hcnt);
            assert(i0 != i1);
            assert((m.half_edges@[i0].edge as int) == e);
            assert((m.half_edges@[i1].edge as int) == e);
            assert(w0 == i0 || w0 == i1);
            assert(w1 == i0 || w1 == i1);
            assert(w0 != w1);
            if w0 == i0 {
                assert(w1 == i1);
                assert((m.half_edges@[i0].twin as int) == i1);
                assert((m.half_edges@[i1].twin as int) == i0);
                assert((m.edge_half_edges@[e] as int) == i0 || (m.edge_half_edges@[e] as int) == i1);
            } else {
                assert(w0 == i1);
                assert(w1 == i0);
                assert((m.half_edges@[i0].twin as int) == i1);
                assert((m.half_edges@[i1].twin as int) == i0);
                assert((m.edge_half_edges@[e] as int) == i0 || (m.edge_half_edges@[e] as int) == i1);
            }
            assert(m.half_edges@[h0].twin as int == h1 && m.half_edges@[h1].twin as int == h0);
            assert(m.edge_half_edges@[e] as int == h0 || m.edge_half_edges@[e] as int == h1);
            assert(twins_ok);
            assert(rep_ok);
            assert(false);
        }
    }
}

// =============================================================================
// Helper for check_face_cycles: inner loop step
// =============================================================================

/// Proves all 7 loop invariant updates for one step of the face cycle traversal.
pub(crate) proof fn lemma_face_cycle_step(
    m: &Mesh,
    start: int,
    h_prev: int,
    steps_prev: int,
    steps: int,
    f: int,
    hcnt: int,
    local_seen_before: Seq<bool>,
    local_seen: Seq<bool>,
    global_seen_before: Seq<bool>,
    global_seen_before_iter: Seq<bool>,
    global_seen: Seq<bool>,
)
    requires
        index_bounds(m),
        hcnt == half_edge_count(m),
        steps == steps_prev + 1,
        0 <= start < hcnt,
        0 <= h_prev < hcnt,
        0 <= steps_prev < hcnt,
        0 <= f < face_count(m),
        h_prev == next_iter(m, start, steps_prev as nat),
        !local_seen_before[h_prev],
        m.half_edges@[h_prev].face as int == f,
        local_seen_before.len() == hcnt,
        local_seen.len() == hcnt,
        global_seen_before.len() == hcnt,
        global_seen_before_iter.len() == hcnt,
        global_seen.len() == hcnt,
        local_seen == local_seen_before.update(h_prev, true),
        global_seen == global_seen_before_iter.update(h_prev, true),
        // Old invariants:
        forall|i: int|
            0 <= i < steps_prev ==> #[trigger] m.half_edges@[next_iter(
                m, start, i as nat,
            )].face as int == f,
        forall|hp: int|
            0 <= hp < hcnt && #[trigger] local_seen_before[hp]
                ==> exists|i: int| {
                    &&& 0 <= i < steps_prev
                    &&& #[trigger] next_iter(m, start, i as nat) == hp
                },
        forall|hp: int|
            0 <= hp < hcnt && #[trigger] local_seen_before[hp]
                ==> #[trigger] global_seen_before_iter[hp],
        forall|hp: int|
            0 <= hp < hcnt && !local_seen_before[hp]
                ==> global_seen_before_iter[hp] == global_seen_before[hp],
        forall|i: int|
            0 <= i < steps_prev ==> #[trigger] local_seen_before[next_iter(
                m, start, i as nat,
            )],
        forall|i: int, j: int|
            #![trigger next_iter(m, start, i as nat), next_iter(m, start, j as nat)]
            0 <= i < j < steps_prev
                ==> next_iter(m, start, i as nat) != next_iter(m, start, j as nat),
    ensures
        // Updated h:
        next_or_self(m, h_prev) < hcnt,
        m.half_edges@[h_prev].next as int == next_iter(m, start, steps as nat),
        // 7 updated invariants:
        forall|i: int|
            0 <= i < steps ==> #[trigger] m.half_edges@[next_iter(
                m, start, i as nat,
            )].face as int == f,
        forall|hp: int|
            0 <= hp < hcnt && #[trigger] local_seen[hp]
                ==> exists|i: int| {
                    &&& 0 <= i < steps
                    &&& #[trigger] next_iter(m, start, i as nat) == hp
                },
        forall|hp: int|
            0 <= hp < hcnt && #[trigger] local_seen[hp]
                ==> #[trigger] global_seen[hp],
        forall|hp: int|
            0 <= hp < hcnt && !local_seen[hp]
                ==> global_seen[hp] == global_seen_before[hp],
        forall|i: int|
            0 <= i < steps ==> #[trigger] local_seen[next_iter(
                m, start, i as nat,
            )],
        forall|i: int, j: int|
            #![trigger next_iter(m, start, i as nat), next_iter(m, start, j as nat)]
            0 <= i < j < steps
                ==> next_iter(m, start, i as nat) != next_iter(m, start, j as nat),
{
    lemma_next_iter_step(m, start, steps_prev as nat);
    assert(0 <= h_prev);
    assert((h_prev) < (hcnt));
    assert((m.half_edges@[h_prev].next as int) < hcnt);
    assert(next_or_self(m, h_prev) == m.half_edges@[h_prev].next as int);
    assert(m.half_edges@[h_prev].next as int == next_iter(m, start, steps as nat));

    // Invariant 1: face membership
    assert forall|i: int|
        0 <= i < steps implies #[trigger] m.half_edges@[next_iter(
            m, start, i as nat,
        )].face as int == f by {
        if i < steps_prev {
        } else {
            assert(i == steps_prev);
            assert(next_iter(m, start, i as nat) == h_prev);
        }
    };

    // Invariant 2: local_seen → exists i
    assert forall|hp: int|
        0 <= hp < hcnt && #[trigger] local_seen[hp]
            implies exists|i: int| {
                &&& 0 <= i < steps
                &&& #[trigger] next_iter(m, start, i as nat) == hp
            } by {
        if hp == h_prev {
            let i = steps_prev;
            assert(0 <= i < steps);
            assert(next_iter(m, start, i as nat) == hp);
        } else {
            assert(local_seen[hp] == local_seen_before[hp]);
            assert(local_seen_before[hp]);
            let i = choose|i: int| {
                &&& 0 <= i < steps_prev
                &&& #[trigger] next_iter(m, start, i as nat) == hp
            };
            assert(0 <= i < steps);
        }
    };

    // Invariant 3: local_seen → global_seen
    assert forall|hp: int|
        0 <= hp < hcnt && #[trigger] local_seen[hp]
            implies #[trigger] global_seen[hp] by {
        if hp == h_prev {
        } else {
            assert(local_seen[hp] == local_seen_before[hp]);
            assert(global_seen[hp] == global_seen_before_iter[hp]);
            assert(local_seen_before[hp]);
            assert(global_seen_before_iter[hp]);
        }
    };

    // Invariant 4: non-local → unchanged from global_seen_before
    assert forall|hp: int|
        0 <= hp < hcnt && !local_seen[hp]
            implies global_seen[hp] == global_seen_before[hp] by {
        if hp == h_prev {
            assert(local_seen[hp]);
        } else {
            assert(local_seen[hp] == local_seen_before[hp]);
            assert(!local_seen_before[hp]);
            assert(global_seen[hp] == global_seen_before_iter[hp]);
            assert(global_seen_before_iter[hp] == global_seen_before[hp]);
        }
    };

    // Invariant 5: all iterates are locally seen
    assert forall|i: int|
        0 <= i < steps implies #[trigger] local_seen[next_iter(
            m, start, i as nat,
        )] by {
        if i < steps_prev {
            let hi = next_iter(m, start, i as nat);
            lemma_next_iter_in_bounds(m, start, i as nat);
            assert(0 <= hi < hcnt);
            assert(local_seen_before[hi]);
            if hi == h_prev {
                assert(local_seen[hi]);
            } else {
                assert(local_seen[hi] == local_seen_before[hi]);
            }
        } else {
            assert(i == steps_prev);
            assert(next_iter(m, start, i as nat) == h_prev);
            assert(local_seen[h_prev]);
        }
    };

    // Invariant 6: distinctness
    assert forall|i: int, j: int|
        #![trigger next_iter(m, start, i as nat), next_iter(m, start, j as nat)]
        0 <= i < j < steps
            implies next_iter(m, start, i as nat) != next_iter(m, start, j as nat) by {
        if j < steps_prev {
        } else {
            assert(j == steps_prev);
            assert(next_iter(m, start, j as nat) == h_prev);
            let hi = next_iter(m, start, i as nat);
            assert(local_seen_before[hi]);
            if hi == h_prev {
                assert(local_seen_before[h_prev]);
                assert(false);
            }
            assert(hi != h_prev);
        }
    };
}

// =============================================================================
// Helper for check_vertex_manifold: inner loop step
// =============================================================================

/// Proves all 4 loop invariant updates for one step of the vertex ring traversal.
pub(crate) proof fn lemma_vertex_ring_step(
    m: &Mesh,
    start: int,
    h_prev: int,
    steps_prev: int,
    steps: int,
    v: int,
    hcnt: int,
    local_seen_before: Seq<bool>,
    local_seen: Seq<bool>,
)
    requires
        index_bounds(m),
        hcnt == half_edge_count(m),
        steps == steps_prev + 1,
        0 <= start < hcnt,
        0 <= h_prev < hcnt,
        0 <= steps_prev,
        h_prev == vertex_ring_iter(m, start, steps_prev as nat),
        !local_seen_before[h_prev],
        m.half_edges@[h_prev].vertex as int == v,
        local_seen_before.len() == hcnt,
        local_seen.len() == hcnt,
        local_seen == local_seen_before.update(h_prev, true),
        // Old invariants:
        forall|hp: int|
            0 <= hp < hcnt && #[trigger] local_seen_before[hp]
                ==> exists|i: int| {
                    &&& 0 <= i < steps_prev
                    &&& #[trigger] vertex_ring_iter(m, start, i as nat) == hp
                },
        forall|i: int|
            0 <= i < steps_prev ==> #[trigger] local_seen_before[vertex_ring_iter(
                m, start, i as nat,
            )],
        forall|i: int|
            0 <= i < steps_prev ==> #[trigger] m.half_edges@[vertex_ring_iter(
                m, start, i as nat,
            )].vertex as int == v,
        forall|i: int, j: int|
            #![trigger vertex_ring_iter(m, start, i as nat), vertex_ring_iter(m, start, j as nat)]
            0 <= i < j < steps_prev
                ==> vertex_ring_iter(m, start, i as nat) != vertex_ring_iter(m, start, j as nat),
    ensures
        // Updated h:
        vertex_ring_succ_or_self(m, h_prev) < hcnt,
        m.half_edges@[m.half_edges@[h_prev].twin as int].next as int
            == vertex_ring_iter(m, start, steps as nat),
        // 4 updated invariants:
        forall|i: int|
            0 <= i < steps ==> #[trigger] m.half_edges@[vertex_ring_iter(
                m, start, i as nat,
            )].vertex as int == v,
        forall|i: int|
            0 <= i < steps ==> #[trigger] local_seen[vertex_ring_iter(
                m, start, i as nat,
            )],
        forall|hp: int|
            0 <= hp < hcnt && #[trigger] local_seen[hp]
                ==> exists|i: int| {
                    &&& 0 <= i < steps
                    &&& #[trigger] vertex_ring_iter(m, start, i as nat) == hp
                },
        forall|i: int, j: int|
            #![trigger vertex_ring_iter(m, start, i as nat), vertex_ring_iter(m, start, j as nat)]
            0 <= i < j < steps
                ==> vertex_ring_iter(m, start, i as nat) != vertex_ring_iter(m, start, j as nat),
{
    assert(0 <= h_prev);
    assert((h_prev) < (hcnt));
    assert((m.half_edges@[h_prev].twin as int) < hcnt);
    assert((m.half_edges@[m.half_edges@[h_prev].twin as int].next as int) < hcnt);
    assert(vertex_ring_succ_or_self(m, h_prev)
        == m.half_edges@[m.half_edges@[h_prev].twin as int].next as int);
    lemma_vertex_ring_iter_step(m, start, steps_prev as nat);
    assert(m.half_edges@[m.half_edges@[h_prev].twin as int].next as int
        == vertex_ring_iter(m, start, steps as nat));

    // Invariant 1: vertex membership
    assert forall|i: int|
        0 <= i < steps implies #[trigger] m.half_edges@[vertex_ring_iter(
            m, start, i as nat,
        )].vertex as int == v by {
        if i < steps_prev {
        } else {
            assert(i == steps_prev);
            assert(vertex_ring_iter(m, start, i as nat) == h_prev);
        }
    };

    // Invariant 2: all iterates are locally seen
    assert forall|i: int|
        0 <= i < steps implies #[trigger] local_seen[vertex_ring_iter(
            m, start, i as nat,
        )] by {
        if i < steps_prev {
            let hi = vertex_ring_iter(m, start, i as nat);
            lemma_vertex_ring_iter_in_bounds(m, start, i as nat);
            assert(0 <= hi < hcnt);
            assert(local_seen_before[hi]);
            if hi == h_prev {
                assert(local_seen[hi]);
            } else {
                assert(local_seen[hi]
                    == local_seen_before.update(h_prev, true)[hi]);
                assert(local_seen_before.update(h_prev, true)[hi]
                    == local_seen_before[hi]);
                assert(local_seen[hi]);
            }
        } else {
            assert(i == steps_prev);
            assert(vertex_ring_iter(m, start, i as nat) == h_prev);
            assert(local_seen[h_prev]);
        }
    };

    // Invariant 3: local_seen → exists i
    assert forall|hp: int|
        0 <= hp < hcnt && #[trigger] local_seen[hp]
            implies exists|i: int| {
                &&& 0 <= i < steps
                &&& #[trigger] vertex_ring_iter(m, start, i as nat) == hp
            } by {
        if hp == h_prev {
            let i = steps_prev;
            assert(0 <= i < steps);
            assert(vertex_ring_iter(m, start, i as nat) == hp);
        } else {
            assert(local_seen[hp] == local_seen_before[hp]);
            assert(local_seen_before[hp]);
            let i = choose|i: int| {
                &&& 0 <= i < steps_prev
                &&& #[trigger] vertex_ring_iter(m, start, i as nat) == hp
            };
            assert(0 <= i < steps);
        }
    };

    // Invariant 4: distinctness
    assert forall|i: int, j: int|
        #![trigger vertex_ring_iter(m, start, i as nat), vertex_ring_iter(m, start, j as nat)]
        0 <= i < j < steps
            implies vertex_ring_iter(m, start, i as nat) != vertex_ring_iter(m, start, j as nat) by {
        if j < steps_prev {
        } else {
            assert(j == steps_prev);
            assert(i < steps_prev);
            assert(local_seen_before[vertex_ring_iter(m, start, i as nat)]);
            assert(!local_seen_before[h_prev]);
            assert(vertex_ring_iter(m, start, j as nat) == h_prev);
            assert(vertex_ring_iter(m, start, i as nat) != vertex_ring_iter(m, start, j as nat));
        }
    };
}

} // verus!
