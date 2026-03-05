use vstd::prelude::*;
use crate::mesh::*;
use crate::iteration::*;
use crate::invariants::*;
use crate::checker_proofs::*;

verus! {

// =============================================================================
// Checker 1: Index bounds (iff)
// =============================================================================

pub fn check_index_bounds(m: &Mesh) -> (out: bool)
    ensures
        out == index_bounds(m),
{
    let mut ok = true;
    let mut i: usize = 0;
    while i < m.vertex_half_edges.len()
        invariant
            0 <= i <= m.vertex_half_edges.len(),
            ok == (forall|j: int|
                0 <= j < i as int
                    ==> (#[trigger] m.vertex_half_edges@[j] as int) < m.half_edges@.len() as int),
        decreases m.vertex_half_edges.len() - i,
    {
        if m.vertex_half_edges[i] >= m.half_edges.len() {
            ok = false;
        }
        i += 1;
    }

    let mut i: usize = 0;
    while i < m.edge_half_edges.len()
        invariant
            0 <= i <= m.edge_half_edges.len(),
            ok == (
                (forall|j: int|
                    0 <= j < m.vertex_half_edges@.len() as int
                        ==> (#[trigger] m.vertex_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < i as int
                        ==> (#[trigger] m.edge_half_edges@[j] as int) < m.half_edges@.len() as int)
            ),
        decreases m.edge_half_edges.len() - i,
    {
        if m.edge_half_edges[i] >= m.half_edges.len() {
            ok = false;
        }
        i += 1;
    }

    let mut i: usize = 0;
    while i < m.face_half_edges.len()
        invariant
            0 <= i <= m.face_half_edges.len(),
            ok == (
                (forall|j: int|
                    0 <= j < m.vertex_half_edges@.len() as int
                        ==> (#[trigger] m.vertex_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < m.edge_half_edges@.len() as int
                        ==> (#[trigger] m.edge_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < i as int
                        ==> (#[trigger] m.face_half_edges@[j] as int) < m.half_edges@.len() as int)
            ),
        decreases m.face_half_edges.len() - i,
    {
        if m.face_half_edges[i] >= m.half_edges.len() {
            ok = false;
        }
        i += 1;
    }

    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            0 <= i <= m.half_edges.len(),
            ok == (
                (forall|j: int|
                    0 <= j < m.vertex_half_edges@.len() as int
                        ==> (#[trigger] m.vertex_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < m.edge_half_edges@.len() as int
                        ==> (#[trigger] m.edge_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < m.face_half_edges@.len() as int
                        ==> (#[trigger] m.face_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int| 0 <= j < i as int ==> {
                    let he = #[trigger] m.half_edges@[j];
                    &&& (he.twin as int) < m.half_edges@.len() as int
                    &&& (he.next as int) < m.half_edges@.len() as int
                    &&& (he.prev as int) < m.half_edges@.len() as int
                    &&& (he.vertex as int) < m.vertex_half_edges@.len() as int
                    &&& (he.edge as int) < m.edge_half_edges@.len() as int
                    &&& (he.face as int) < m.face_half_edges@.len() as int
                })
            ),
        decreases m.half_edges.len() - i,
    {
        let he = m.half_edges[i];
        if he.twin >= m.half_edges.len()
            || he.next >= m.half_edges.len()
            || he.prev >= m.half_edges.len()
            || he.vertex >= m.vertex_half_edges.len()
            || he.edge >= m.edge_half_edges.len()
            || he.face >= m.face_half_edges.len()
        {
            ok = false;
        }
        i += 1;
    }

    ok
}

// =============================================================================
// Checker 2: Twin involution (iff)
// =============================================================================

pub fn check_twin_involution(m: &Mesh) -> (out: bool)
    ensures
        out == twin_involution_total(m),
{
    let bounds_ok = check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let mut ok = true;
    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            index_bounds(m),
            0 <= i <= m.half_edges.len(),
            ok == (forall|j: int|
                0 <= j < i as int
                    ==> (#[trigger] m.half_edges@[m.half_edges@[j].twin as int].twin as int) == j),
        decreases m.half_edges.len() - i,
    {
        let t = m.half_edges[i].twin;
        if t >= m.half_edges.len() {
            ok = false;
        } else if m.half_edges[t].twin != i {
            ok = false;
        }
        i += 1;
    }

    proof {
        assert(bounds_ok);
        assert(twin_involution_total(m) == (index_bounds(m) && twin_involution(m)));
    }
    ok
}

// =============================================================================
// Checker 3: Prev/next bidirectional (iff)
// =============================================================================

fn check_next_prev_inverse(m: &Mesh) -> (out: bool)
    ensures
        out == (index_bounds(m) && next_prev_inverse_only(m)),
{
    let bounds_ok = check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let mut ok = true;
    let mut bad_idx: usize = 0;
    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            index_bounds(m),
            0 <= i <= m.half_edges.len(),
            ok ==> (forall|j: int| 0 <= j < i as int ==> #[trigger] next_prev_inverse_at(m, j)),
            !ok ==> {
                &&& bad_idx < i
                &&& !next_prev_inverse_at(m, bad_idx as int)
            },
        decreases m.half_edges.len() - i,
    {
        let he = m.half_edges[i];
        if m.half_edges[he.next].prev != i {
            if ok {
                bad_idx = i;
            }
            ok = false;
        }
        i += 1;
    }
    let _ = bad_idx;

    proof {
        assert(bounds_ok);
        if ok {
            assert(next_prev_inverse_only(m));
        } else {
            assert(bad_idx < m.half_edges@.len());
            assert(!next_prev_inverse_at(m, bad_idx as int));
            if next_prev_inverse_only(m) {
                assert(next_prev_inverse_at(m, bad_idx as int));
                assert(false);
            }
            assert(!next_prev_inverse_only(m));
        }
    }
    ok
}

fn check_prev_next_inverse(m: &Mesh) -> (out: bool)
    ensures
        out == (index_bounds(m) && prev_next_inverse_only(m)),
{
    let bounds_ok = check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let mut ok = true;
    let mut bad_idx: usize = 0;
    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            index_bounds(m),
            0 <= i <= m.half_edges.len(),
            ok ==> (forall|j: int| 0 <= j < i as int ==> #[trigger] prev_next_inverse_at(m, j)),
            !ok ==> {
                &&& bad_idx < i
                &&& !prev_next_inverse_at(m, bad_idx as int)
            },
        decreases m.half_edges.len() - i,
    {
        let he = m.half_edges[i];
        if m.half_edges[he.prev].next != i {
            if ok {
                bad_idx = i;
            }
            ok = false;
        }
        i += 1;
    }
    let _ = bad_idx;

    proof {
        assert(bounds_ok);
        if ok {
            assert(prev_next_inverse_only(m));
        } else {
            assert(bad_idx < m.half_edges@.len());
            assert(!prev_next_inverse_at(m, bad_idx as int));
            if prev_next_inverse_only(m) {
                assert(prev_next_inverse_at(m, bad_idx as int));
                assert(false);
            }
            assert(!prev_next_inverse_only(m));
        }
    }
    ok
}

pub fn check_prev_inverse_of_next(m: &Mesh) -> (out: bool)
    ensures
        out == prev_next_bidirectional_total(m),
{
    let next_prev_ok = check_next_prev_inverse(m);
    let prev_next_ok = check_prev_next_inverse(m);
    let ok = next_prev_ok && prev_next_ok;
    proof {
        assert(prev_next_bidirectional_total(m) == (index_bounds(m) && prev_next_bidirectional(m)));
        assert(prev_next_bidirectional(m)
            == (next_prev_inverse_only(m) && prev_next_inverse_only(m)));
        assert(ok == (index_bounds(m) && prev_next_bidirectional(m)));
    }
    ok
}

// =============================================================================
// Checker 4: No degenerate edges (iff)
// =============================================================================

pub fn check_no_degenerate_edges(m: &Mesh) -> (out: bool)
    ensures
        out == no_degenerate_edges_total(m),
{
    let bounds_ok = check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let mut ok = true;
    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            index_bounds(m),
            0 <= i <= m.half_edges.len(),
            ok == (forall|j: int|
                0 <= j < i as int ==> {
                    &&& (#[trigger] m.half_edges@[j].vertex as int)
                        != (m.half_edges@[m.half_edges@[j].twin as int].vertex as int)
                    &&& (#[trigger] m.half_edges@[j].vertex as int)
                        != (m.half_edges@[m.half_edges@[j].next as int].vertex as int)
                }),
        decreases m.half_edges.len() - i,
    {
        let he = m.half_edges[i];
        let t = he.twin;
        let n = he.next;
        if t >= m.half_edges.len() || n >= m.half_edges.len() {
            ok = false;
        } else if he.vertex == m.half_edges[t].vertex || he.vertex == m.half_edges[n].vertex {
            ok = false;
        }
        i += 1;
    }

    proof {
        assert(bounds_ok);
        assert(no_degenerate_edges_total(m) == (index_bounds(m) && no_degenerate_edges(m)));
    }
    ok
}

// =============================================================================
// Checker 5: Shared edge orientation consistency (iff)
// =============================================================================

pub fn check_shared_edge_orientation_consistency(m: &Mesh) -> (out: bool)
    ensures
        out == shared_edge_orientation_consistency_total(m),
{
    let bounds_ok = check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let mut ok = true;
    let mut bad_idx: usize = 0;
    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            index_bounds(m),
            0 <= i <= m.half_edges.len(),
            ok ==> (forall|j: int|
                0 <= j < i as int ==> #[trigger] twin_faces_distinct_at(m, j)),
            ok ==> (forall|j: int|
                0 <= j < i as int ==> #[trigger] twin_endpoint_correspondence_at(m, j)),
            !ok ==> {
                &&& bad_idx < i
                &&& (
                    !twin_faces_distinct_at(m, bad_idx as int)
                        || !twin_endpoint_correspondence_at(m, bad_idx as int)
                )
            },
        decreases m.half_edges.len() - i,
    {
        let he = m.half_edges[i];
        let t = he.twin;
        let twin = m.half_edges[t];
        let n = he.next;
        let tn = twin.next;
        let from_h = he.vertex;
        let to_h = m.half_edges[n].vertex;
        let from_t = twin.vertex;
        let to_t = m.half_edges[tn].vertex;

        let face_distinct_ok = he.face != twin.face;
        let endpoint_ok = from_t == to_h && to_t == from_h;
        if !(face_distinct_ok && endpoint_ok) {
            if ok {
                bad_idx = i;
            }
            ok = false;
            proof {
                assert(0 <= i as int && (i as int) < half_edge_count(m));
                assert(0 <= t as int && (t as int) < half_edge_count(m));
                assert(0 <= n as int && (n as int) < half_edge_count(m));
                assert(0 <= tn as int && (tn as int) < half_edge_count(m));

                if !face_distinct_ok {
                    assert(he.face as int == twin.face as int);
                    assert(!twin_faces_distinct_at(m, i as int));
                }
                if !endpoint_ok {
                    if from_t != to_h {
                        assert((m.half_edges@[t as int].vertex as int)
                            != (m.half_edges@[n as int].vertex as int));
                        assert(half_edge_from_vertex(m, t as int)
                            != half_edge_to_vertex(m, i as int));
                    } else {
                        assert(to_t != from_h);
                        assert((m.half_edges@[tn as int].vertex as int)
                            != (m.half_edges@[i as int].vertex as int));
                        assert(half_edge_to_vertex(m, t as int)
                            != half_edge_from_vertex(m, i as int));
                    }
                    assert(!twin_endpoint_correspondence_at(m, i as int));
                }
            }
        } else {
            if ok {
                proof {
                    assert(0 <= i as int && (i as int) < half_edge_count(m));
                    assert(0 <= t as int && (t as int) < half_edge_count(m));
                    assert(0 <= n as int && (n as int) < half_edge_count(m));
                    assert(0 <= tn as int && (tn as int) < half_edge_count(m));
                    assert(he.face as int != twin.face as int);
                    assert(from_t as int == to_h as int);
                    assert(to_t as int == from_h as int);
                    assert(twin_faces_distinct_at(m, i as int));
                    assert(twin_endpoint_correspondence_at(m, i as int));

                    assert(forall|j: int|
                        0 <= j < (i + 1) as int ==> #[trigger] twin_faces_distinct_at(m, j)) by {
                        assert forall|j: int|
                            0 <= j < (i + 1) as int
                                implies #[trigger] twin_faces_distinct_at(m, j) by {
                            if j < i as int {
                            } else {
                                assert(j == i as int);
                                assert(twin_faces_distinct_at(m, j));
                            }
                        };
                    };
                    assert(forall|j: int|
                        0 <= j < (i + 1) as int
                            ==> #[trigger] twin_endpoint_correspondence_at(m, j)) by {
                        assert forall|j: int|
                            0 <= j < (i + 1) as int
                                implies #[trigger] twin_endpoint_correspondence_at(m, j) by {
                            if j < i as int {
                            } else {
                                assert(j == i as int);
                                assert(twin_endpoint_correspondence_at(m, j));
                            }
                        };
                    };
                }
            }
        }

        i += 1;
    }

    let _ = bad_idx;

    proof {
        assert(bounds_ok);
        if ok {
            assert(forall|j: int|
                0 <= j < half_edge_count(m) ==> #[trigger] twin_faces_distinct_at(m, j)) by {
                assert forall|j: int|
                    0 <= j < half_edge_count(m)
                        implies #[trigger] twin_faces_distinct_at(m, j) by {
                    assert(half_edge_count(m) == i as int);
                    assert(0 <= j < i as int);
                };
            };
            assert(forall|j: int|
                0 <= j < half_edge_count(m)
                    ==> #[trigger] twin_endpoint_correspondence_at(m, j)) by {
                assert forall|j: int|
                    0 <= j < half_edge_count(m)
                        implies #[trigger] twin_endpoint_correspondence_at(m, j) by {
                    assert(half_edge_count(m) == i as int);
                    assert(0 <= j < i as int);
                };
            };
            assert(twin_faces_distinct(m));
            assert(twin_endpoint_correspondence(m));
            assert(shared_edge_orientation_consistency(m));
            assert(shared_edge_orientation_consistency_total(m));
        } else {
            assert(bad_idx < m.half_edges@.len());
            assert(
                !twin_faces_distinct_at(m, bad_idx as int)
                    || !twin_endpoint_correspondence_at(m, bad_idx as int)
            );
            assert(!shared_edge_orientation_consistency(m)) by {
                if shared_edge_orientation_consistency(m) {
                    assert(twin_faces_distinct(m));
                    assert(twin_endpoint_correspondence(m));
                    assert(twin_faces_distinct_at(m, bad_idx as int));
                    assert(twin_endpoint_correspondence_at(m, bad_idx as int));
                    assert(false);
                }
            };
            assert(!shared_edge_orientation_consistency_total(m));
        }
    }

    ok
}

// =============================================================================
// Checker 6: Face cycles (sound, ==>)
// =============================================================================

pub fn check_face_cycles(m: &Mesh) -> (out: bool)
    ensures
        out ==> face_representative_cycles_cover_all_half_edges_total(m),
{
    let bounds_ok = check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let hcnt = m.half_edges.len();
    let fcnt = m.face_half_edges.len();
    let mut global_seen: Vec<bool> = vec![false; hcnt];
    let mut face_cycle_lens: Vec<usize> = Vec::new();
    let mut f: usize = 0;
    while f < fcnt
        invariant
            index_bounds(m),
            hcnt == m.half_edges.len(),
            fcnt == m.face_half_edges.len(),
            global_seen@.len() == hcnt as int,
            face_cycle_lens@.len() == f as int,
            0 <= f <= fcnt,
            forall|fp: int|
                #![trigger face_cycle_lens@[fp]]
                0 <= fp < f as int
                    ==> face_representative_cycle_witness(
                        m,
                        fp,
                        face_cycle_lens@[fp] as int,
                    ),
            forall|hp: int| 0 <= hp < hcnt as int && #[trigger] global_seen@[hp] ==> exists|fp: int, ip: int| {
                &&& 0 <= fp < f as int
                &&& 0 <= ip < face_cycle_lens@[fp] as int
                &&& #[trigger] next_iter(m, m.face_half_edges@[fp] as int, ip as nat) == hp
            },
        decreases fcnt - f,
    {
        let start = m.face_half_edges[f];
        if m.half_edges[start].face != f {
            return false;
        }
        assert(start < hcnt);
        proof {
            assert(0 <= start as int);
            assert((start as int) < (hcnt as int));
        }
        let ghost global_seen_before = global_seen@;
        proof {
            assert(forall|hp: int|
                #![trigger hp + 0]
                0 <= hp < hcnt as int && #[trigger] global_seen_before[hp] ==> exists|fp: int, ip: int| {
                    &&& 0 <= fp < f as int
                    &&& 0 <= ip < face_cycle_lens@[fp] as int
                    &&& #[trigger] next_iter(m, m.face_half_edges@[fp] as int, ip as nat) == hp
                }) by {
                assert forall|hp: int|
                    #![trigger hp + 0]
                    0 <= hp < hcnt as int && #[trigger] global_seen_before[hp]
                        implies exists|fp: int, ip: int| {
                            &&& 0 <= fp < f as int
                            &&& 0 <= ip < face_cycle_lens@[fp] as int
                            &&& #[trigger] next_iter(m, m.face_half_edges@[fp] as int, ip as nat) == hp
                        } by {
                    assert(global_seen_before[hp] == global_seen@[hp]);
                };
            }
        }
        let mut local_seen: Vec<bool> = vec![false; hcnt];
        let mut h = start;
        let mut steps: usize = 0;
        let mut closed = false;
        while steps < hcnt && !closed
            invariant
                index_bounds(m),
                hcnt == m.half_edges.len(),
                0 <= steps <= hcnt,
                global_seen@.len() == hcnt as int,
                local_seen@.len() == hcnt as int,
                global_seen_before.len() == hcnt as int,
                start < hcnt,
                0 <= h < hcnt,
                h as int == next_iter(m, start as int, steps as nat),
                closed ==> h == start,
                forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] local_seen@[hp]
                        ==> exists|i: int| {
                            &&& 0 <= i < steps as int
                            &&& #[trigger] next_iter(m, start as int, i as nat) == hp
                        },
                forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] local_seen@[hp] ==> #[trigger] global_seen@[hp],
                forall|hp: int|
                    0 <= hp < hcnt as int && !local_seen@[hp] ==> global_seen@[hp] == global_seen_before[hp],
                forall|i: int|
                    0 <= i < steps as int ==> #[trigger] m.half_edges@[next_iter(
                        m,
                        start as int,
                        i as nat,
                    )].face as int == f as int,
                forall|i: int|
                    0 <= i < steps as int ==> #[trigger] local_seen@[next_iter(
                        m,
                        start as int,
                        i as nat,
                    )],
                forall|i: int, j: int|
                    #![trigger next_iter(m, start as int, i as nat), next_iter(m, start as int, j as nat)]
                    0 <= i < j < steps as int
                        ==> next_iter(m, start as int, i as nat)
                            != next_iter(m, start as int, j as nat),
            decreases hcnt - steps,
        {
            let h_prev = h;
            let steps_prev = steps;
            let ghost local_seen_before = local_seen@;
            let ghost global_seen_before_iter = global_seen@;

            if local_seen[h] {
                return false;
            }
            if global_seen[h] {
                return false;
            }
            local_seen[h] = true;
            global_seen[h] = true;
            let he = m.half_edges[h];
            if he.face != f {
                return false;
            }
            h = he.next;
            if steps == usize::MAX {
                return false;
            }
            steps += 1;
            let _ = (h_prev, steps_prev);

            proof {
                assert(0 <= h_prev as int && (h_prev as int) < local_seen_before.len());
                assert(local_seen_before.len() == hcnt as int);
                assert(global_seen_before.len() == hcnt as int);
                assert(global_seen_before_iter.len() == hcnt as int);
                assert(local_seen@ == local_seen_before.update(h_prev as int, true));
                assert(global_seen@ == global_seen_before_iter.update(h_prev as int, true));
                lemma_face_cycle_step(
                    m,
                    start as int, h_prev as int,
                    steps_prev as int, steps as int,
                    f as int, hcnt as int,
                    local_seen_before, local_seen@,
                    global_seen_before, global_seen_before_iter, global_seen@,
                );
                assert(h as int == m.half_edges@[h_prev as int].next as int);
                assert(h as int == next_iter(m, start as int, steps as nat));
            }

            if h == start {
                closed = true;
            }
        }

        if !closed {
            return false;
        }
        if h != start {
            return false;
        }
        if steps < 3 {
            return false;
        }
        face_cycle_lens.push(steps);

        proof {
            assert(forall|fp: int|
                #![trigger face_cycle_lens@[fp]]
                0 <= fp < (f + 1) as int
                    ==> face_representative_cycle_witness(
                        m,
                        fp,
                        face_cycle_lens@[fp] as int,
                    )) by {
                assert forall|fp: int|
                    #![trigger face_cycle_lens@[fp]]
                    0 <= fp < (f + 1) as int
                        implies face_representative_cycle_witness(
                            m,
                            fp,
                            face_cycle_lens@[fp] as int,
                        ) by {
                    if fp < f as int {
                        assert(face_representative_cycle_witness(
                            m,
                            fp,
                            face_cycle_lens@[fp] as int,
                        ));
                    } else {
                        assert(fp == f as int);
                        assert((face_cycle_lens@[fp] as int) == steps as int);
                        assert(steps as int <= hcnt as int);
                        assert(3 <= steps as int);
                        assert(h as int == start as int);
                        assert(h as int == next_iter(m, start as int, steps as nat));
                        assert(next_iter(m, start as int, steps as nat) == start as int);
                        let s = m.face_half_edges@[f as int] as int;
                        assert(s == start as int);
                        assert(forall|i: int|
                            0 <= i < steps as int ==> #[trigger] m.half_edges@[next_iter(
                                m,
                                s,
                                i as nat,
                            )].face as int == f as int) by {
                            assert forall|i: int|
                                0 <= i < steps as int implies #[trigger] m.half_edges@[next_iter(
                                    m,
                                    s,
                                    i as nat,
                                )].face as int == f as int by {
                                assert((#[trigger] m.half_edges@[next_iter(
                                    m,
                                    start as int,
                                    i as nat,
                                )].face as int) == f as int);
                                assert(next_iter(m, s, i as nat)
                                    == next_iter(m, start as int, i as nat));
                            };
                        }
                        assert(face_representative_cycle_witness(m, f as int, steps as int)) by {
                            assert(3 <= steps as int <= half_edge_count(m));
                            assert(next_iter(m, s, steps as nat) == s);
                            assert(forall|i: int|
                                0 <= i < steps as int ==> #[trigger] m.half_edges@[next_iter(
                                    m,
                                    s,
                                    i as nat,
                                )].face as int == f as int);
                            assert(forall|i: int, j: int|
                                #![trigger next_iter(m, s, i as nat), next_iter(m, s, j as nat)]
                                0 <= i < j < steps as int
                                    ==> next_iter(m, s, i as nat)
                                        != next_iter(m, s, j as nat)) by {
                                assert forall|i: int, j: int|
                                    #![trigger next_iter(m, s, i as nat), next_iter(m, s, j as nat)]
                                    0 <= i < j < steps as int
                                        implies next_iter(m, s, i as nat)
                                            != next_iter(m, s, j as nat) by {
                                    assert(next_iter(m, s, i as nat)
                                        == next_iter(m, start as int, i as nat));
                                    assert(next_iter(m, s, j as nat)
                                        == next_iter(m, start as int, j as nat));
                                    assert(next_iter(m, start as int, i as nat)
                                        != next_iter(m, start as int, j as nat));
                                };
                            };
                        }
                        assert(face_representative_cycle_witness(
                            m,
                            fp,
                            face_cycle_lens@[fp] as int,
                        ));
                    }
                };
            }
            assert(forall|hp: int| 0 <= hp < hcnt as int && #[trigger] global_seen@[hp] ==> exists|fp: int, ip: int| {
                &&& 0 <= fp < (f + 1) as int
                &&& 0 <= ip < face_cycle_lens@[fp] as int
                &&& #[trigger] next_iter(m, m.face_half_edges@[fp] as int, ip as nat) == hp
            }) by {
                assert forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] global_seen@[hp]
                        implies exists|fp: int, ip: int| {
                            &&& 0 <= fp < (f + 1) as int
                            &&& 0 <= ip < face_cycle_lens@[fp] as int
                            &&& #[trigger] next_iter(m, m.face_half_edges@[fp] as int, ip as nat) == hp
                        } by {
                    if local_seen@[hp] {
                        assert(exists|i: int| {
                            &&& 0 <= i < steps as int
                            &&& #[trigger] next_iter(m, start as int, i as nat) == hp
                        });
                        let i = choose|i: int| {
                            &&& 0 <= i < steps as int
                            &&& #[trigger] next_iter(m, start as int, i as nat) == hp
                        };
                        assert(0 <= i < face_cycle_lens@[f as int] as int);
                        assert(m.face_half_edges@[f as int] as int == start as int);
                        assert(next_iter(m, m.face_half_edges@[f as int] as int, i as nat)
                            == next_iter(m, start as int, i as nat));
                    } else {
                        assert(global_seen@[hp] == global_seen_before[hp]);
                        assert(global_seen_before[hp]);
                        assert(exists|fp: int, ip: int| {
                            &&& 0 <= fp < f as int
                            &&& 0 <= ip < face_cycle_lens@[fp] as int
                            &&& #[trigger] next_iter(m, m.face_half_edges@[fp] as int, ip as nat) == hp
                        });
                    }
                };
            };
        }

        f += 1;
    }

    let mut h: usize = 0;
    while h < hcnt
        invariant
            index_bounds(m),
            hcnt == m.half_edges.len(),
            f == fcnt,
            global_seen@.len() == hcnt as int,
            face_cycle_lens@.len() == f as int,
            forall|fp: int|
                #![trigger face_cycle_lens@[fp]]
                0 <= fp < f as int
                    ==> face_representative_cycle_witness(
                        m,
                        fp,
                        face_cycle_lens@[fp] as int,
                    ),
            forall|hp: int| 0 <= hp < hcnt as int && #[trigger] global_seen@[hp] ==> exists|fp: int, ip: int| {
                &&& 0 <= fp < f as int
                &&& 0 <= ip < face_cycle_lens@[fp] as int
                &&& #[trigger] next_iter(m, m.face_half_edges@[fp] as int, ip as nat) == hp
            },
            0 <= h <= hcnt,
            forall|j: int| 0 <= j < h as int ==> #[trigger] global_seen@[j],
        decreases hcnt - h,
    {
        if !global_seen[h] {
            return false;
        }
        h += 1;
    }

    proof {
        assert(bounds_ok);
        assert(f == fcnt);
        assert(face_cycle_lens@.len() == f as int);
        assert(forall|hp: int| 0 <= hp < hcnt as int ==> #[trigger] global_seen@[hp]) by {
            assert forall|hp: int| 0 <= hp < hcnt as int implies #[trigger] global_seen@[hp] by {
                assert(h == hcnt);
                assert(0 <= hp < h as int);
            };
        }
        assert(face_representative_cycles(m)) by {
            let cycle_lens = face_cycle_lens@;
            assert(cycle_lens.len() == face_count(m)) by {
                assert(cycle_lens.len() == f as int);
                assert(face_count(m) == fcnt as int);
                assert(f == fcnt);
            }
            assert(forall|fp: int|
                #![trigger cycle_lens[fp]]
                0 <= fp < face_count(m)
                    ==> face_representative_cycle_witness(
                        m,
                        fp,
                        cycle_lens[fp] as int,
                    )) by {
                assert forall|fp: int|
                    #![trigger cycle_lens[fp]]
                    0 <= fp < face_count(m)
                        implies face_representative_cycle_witness(
                            m,
                            fp,
                            cycle_lens[fp] as int,
                        ) by {
                    assert(face_count(m) == fcnt as int);
                    assert(fp < fcnt as int);
                    assert(fp < f as int);
                    assert(cycle_lens[fp] == face_cycle_lens@[fp]);
                    assert(face_representative_cycle_witness(
                        m,
                        fp,
                        face_cycle_lens@[fp] as int,
                    ));
                    assert(face_representative_cycle_witness(
                        m,
                        fp,
                        cycle_lens[fp] as int,
                    ));
                };
            }
            assert(exists|cycle_lens: Seq<usize>| {
                &&& cycle_lens.len() == face_count(m)
                &&& forall|fp: int|
                    #![trigger cycle_lens[fp]]
                    0 <= fp < face_count(m)
                        ==> face_representative_cycle_witness(
                            m,
                            fp,
                            cycle_lens[fp] as int,
                        )
            }) by {
                let cycle_lens = face_cycle_lens@;
                assert(cycle_lens.len() == face_count(m));
                assert(forall|fp: int|
                    #![trigger cycle_lens[fp]]
                    0 <= fp < face_count(m)
                        ==> face_representative_cycle_witness(
                            m,
                            fp,
                            cycle_lens[fp] as int,
                        ));
            };
        }
        assert(face_representative_cycles_total(m));
        assert(face_representative_cycles_cover_all_half_edges(m)) by {
            let cycle_lens = face_cycle_lens@;
            let covered = global_seen@;
            assert(cycle_lens.len() == face_count(m)) by {
                assert(cycle_lens.len() == f as int);
                assert(face_count(m) == fcnt as int);
                assert(f == fcnt);
            }
            assert(covered.len() == half_edge_count(m)) by {
                assert(covered.len() == hcnt as int);
                assert(half_edge_count(m) == hcnt as int);
            }
            assert(forall|fp: int|
                #![trigger cycle_lens[fp]]
                0 <= fp < face_count(m)
                    ==> face_representative_cycle_witness(
                        m,
                        fp,
                        cycle_lens[fp] as int,
                    )) by {
                assert forall|fp: int|
                    #![trigger cycle_lens[fp]]
                    0 <= fp < face_count(m)
                        implies face_representative_cycle_witness(
                            m,
                            fp,
                            cycle_lens[fp] as int,
                        ) by {
                    assert(face_count(m) == fcnt as int);
                    assert(fp < fcnt as int);
                    assert(fp < f as int);
                    assert(cycle_lens[fp] == face_cycle_lens@[fp]);
                    assert(face_representative_cycle_witness(
                        m,
                        fp,
                        face_cycle_lens@[fp] as int,
                    ));
                    assert(face_representative_cycle_witness(
                        m,
                        fp,
                        cycle_lens[fp] as int,
                    ));
                };
            }
            assert(forall|hp: int|
                #![trigger hp + 0]
                0 <= hp < half_edge_count(m) && #[trigger] covered[hp]
                    ==> exists|fp: int, ip: int| {
                        &&& 0 <= fp < face_count(m)
                        &&& 0 <= ip < cycle_lens[fp] as int
                        &&& #[trigger] next_iter(
                            m,
                            m.face_half_edges@[fp] as int,
                            ip as nat,
                        ) == hp
                    }) by {
                assert forall|hp: int|
                    #![trigger hp + 0]
                    0 <= hp < half_edge_count(m) && #[trigger] covered[hp]
                        implies exists|fp: int, ip: int| {
                            &&& 0 <= fp < face_count(m)
                            &&& 0 <= ip < cycle_lens[fp] as int
                            &&& #[trigger] next_iter(
                                m,
                                m.face_half_edges@[fp] as int,
                                ip as nat,
                            ) == hp
                        } by {
                    assert(half_edge_count(m) == hcnt as int);
                    assert(0 <= hp < hcnt as int);
                    assert(covered[hp] == global_seen@[hp]);
                    assert(global_seen@[hp]);
                    assert(exists|fp: int, ip: int| {
                        &&& 0 <= fp < f as int
                        &&& 0 <= ip < face_cycle_lens@[fp] as int
                        &&& #[trigger] next_iter(
                            m,
                            m.face_half_edges@[fp] as int,
                            ip as nat,
                        ) == hp
                    }) by {
                        assert(forall|hp2: int|
                            0 <= hp2 < hcnt as int && #[trigger] global_seen@[hp2]
                                ==> exists|fp: int, ip: int| {
                                    &&& 0 <= fp < f as int
                                    &&& 0 <= ip < face_cycle_lens@[fp] as int
                                    &&& #[trigger] next_iter(
                                        m,
                                        m.face_half_edges@[fp] as int,
                                        ip as nat,
                                    ) == hp2
                                });
                        assert(0 <= hp < hcnt as int && global_seen@[hp]);
                    };
                    let (fp, ip) = choose|fp: int, ip: int| {
                        &&& 0 <= fp < f as int
                        &&& 0 <= ip < face_cycle_lens@[fp] as int
                        &&& #[trigger] next_iter(
                            m,
                            m.face_half_edges@[fp] as int,
                            ip as nat,
                        ) == hp
                    };
                    assert(f == fcnt);
                    assert(face_count(m) == fcnt as int);
                    assert(0 <= fp < face_count(m));
                    assert(cycle_lens[fp] == face_cycle_lens@[fp]);
                    assert(0 <= ip < cycle_lens[fp] as int);
                    assert(next_iter(m, m.face_half_edges@[fp] as int, ip as nat) == hp);
                };
            }
            assert(forall|h: int| 0 <= h < half_edge_count(m) ==> #[trigger] covered[h]) by {
                assert forall|h: int| 0 <= h < half_edge_count(m) implies #[trigger] covered[h] by {
                    assert(half_edge_count(m) == hcnt as int);
                    assert(0 <= h < hcnt as int);
                    assert(covered[h] == global_seen@[h]);
                    assert(global_seen@[h]);
                };
            }
            assert(forall|fp1: int, ip1: int, fp2: int, ip2: int|
                #![trigger next_iter(m, m.face_half_edges@[fp1] as int, ip1 as nat), next_iter(m, m.face_half_edges@[fp2] as int, ip2 as nat)]
                0 <= fp1 < face_count(m)
                    && 0 <= fp2 < face_count(m)
                    && 0 <= ip1 < cycle_lens[fp1] as int
                    && 0 <= ip2 < cycle_lens[fp2] as int
                    && next_iter(m, m.face_half_edges@[fp1] as int, ip1 as nat)
                        == next_iter(m, m.face_half_edges@[fp2] as int, ip2 as nat)
                    ==> fp1 == fp2) by {
                assert forall|fp1: int, ip1: int, fp2: int, ip2: int|
                    #![trigger next_iter(m, m.face_half_edges@[fp1] as int, ip1 as nat), next_iter(m, m.face_half_edges@[fp2] as int, ip2 as nat)]
                    0 <= fp1 < face_count(m)
                        && 0 <= fp2 < face_count(m)
                        && 0 <= ip1 < cycle_lens[fp1] as int
                        && 0 <= ip2 < cycle_lens[fp2] as int
                        && next_iter(m, m.face_half_edges@[fp1] as int, ip1 as nat)
                            == next_iter(m, m.face_half_edges@[fp2] as int, ip2 as nat)
                        implies fp1 == fp2 by {
                    assert(face_representative_cycle_witness(m, fp1, cycle_lens[fp1] as int));
                    assert(face_representative_cycle_witness(m, fp2, cycle_lens[fp2] as int));
                    assert(m.half_edges@[next_iter(
                        m,
                        m.face_half_edges@[fp1] as int,
                        ip1 as nat,
                    )].face as int == fp1);
                    assert(m.half_edges@[next_iter(
                        m,
                        m.face_half_edges@[fp2] as int,
                        ip2 as nat,
                    )].face as int == fp2);
                    assert(next_iter(m, m.face_half_edges@[fp1] as int, ip1 as nat)
                        == next_iter(m, m.face_half_edges@[fp2] as int, ip2 as nat));
                    assert(m.half_edges@[next_iter(
                        m,
                        m.face_half_edges@[fp1] as int,
                        ip1 as nat,
                    )].face as int == fp2);
                };
            }
            let cycle_lens = face_cycle_lens@;
            let covered = global_seen@;
            assert(face_representative_cycles_cover_all_half_edges_witness(
                m,
                cycle_lens,
                covered,
            )) by {
                assert(cycle_lens.len() == face_count(m)) by {
                    assert(cycle_lens.len() == f as int);
                    assert(face_count(m) == fcnt as int);
                    assert(f == fcnt);
                }
                assert(covered.len() == half_edge_count(m)) by {
                    assert(covered.len() == hcnt as int);
                    assert(half_edge_count(m) == hcnt as int);
                }
                assert(forall|fp: int|
                    #![trigger cycle_lens[fp]]
                    0 <= fp < face_count(m)
                        ==> face_representative_cycle_witness(
                            m,
                            fp,
                            cycle_lens[fp] as int,
                        ));
                assert(forall|h: int|
                    #![trigger h + 0]
                    0 <= h < half_edge_count(m) && #[trigger] covered[h]
                        ==> exists|fp: int, ip: int| {
                            &&& 0 <= fp < face_count(m)
                            &&& 0 <= ip < cycle_lens[fp] as int
                            &&& #[trigger] next_iter(
                                m,
                                m.face_half_edges@[fp] as int,
                                ip as nat,
                            ) == h
                        });
                assert(forall|h: int| 0 <= h < half_edge_count(m) ==> #[trigger] covered[h]);
                assert(forall|fp1: int, ip1: int, fp2: int, ip2: int|
                    #![trigger next_iter(m, m.face_half_edges@[fp1] as int, ip1 as nat), next_iter(m, m.face_half_edges@[fp2] as int, ip2 as nat)]
                    0 <= fp1 < face_count(m)
                        && 0 <= fp2 < face_count(m)
                        && 0 <= ip1 < cycle_lens[fp1] as int
                        && 0 <= ip2 < cycle_lens[fp2] as int
                        && next_iter(m, m.face_half_edges@[fp1] as int, ip1 as nat)
                            == next_iter(m, m.face_half_edges@[fp2] as int, ip2 as nat)
                        ==> fp1 == fp2);
            };
            assert(exists|cycle_lens2: Seq<usize>, covered2: Seq<bool>| {
                face_representative_cycles_cover_all_half_edges_witness(
                    m,
                    cycle_lens2,
                    covered2,
                )
            });
        }
        assert(face_representative_cycles_cover_all_half_edges_total(m));
    }
    true
}

// =============================================================================
// Checker 7: Vertex manifold (sound, ==>)
// =============================================================================

pub fn check_vertex_manifold(m: &Mesh) -> (out: bool)
    ensures
        out ==> vertex_manifold_total(m),
{
    let bounds_ok = check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let hcnt = m.half_edges.len();
    let vcnt = m.vertex_half_edges.len();
    let mut vertex_cycle_lens: Vec<usize> = Vec::new();

    let mut v: usize = 0;
    while v < vcnt
        invariant
            index_bounds(m),
            hcnt == m.half_edges.len(),
            vcnt == m.vertex_half_edges.len(),
            vertex_cycle_lens@.len() == v as int,
            0 <= v <= vcnt,
            forall|vp: int|
                #![trigger m.vertex_half_edges@[vp]]
                0 <= vp < v as int
                    ==> (#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp,
            forall|vp: int|
                #![trigger vertex_cycle_lens@[vp]]
                0 <= vp < v as int
                    ==> vertex_representative_cycle_witness(
                        m,
                        vp,
                        vertex_cycle_lens@[vp] as int,
                    ),
        decreases vcnt - v,
    {
        let mut expected: usize = 0;
        let mut hh: usize = 0;
        while hh < hcnt
            invariant
                index_bounds(m),
                hcnt == m.half_edges.len(),
                0 <= hh <= hcnt,
                0 <= expected <= hh,
            decreases hcnt - hh,
        {
            if m.half_edges[hh].vertex == v {
                expected += 1;
            }
            hh += 1;
        }
        proof {
            assert(hh == hcnt);
            assert(expected <= hcnt);
        }
        if expected == 0 {
            return false;
        }

        let start = m.vertex_half_edges[v];
        if m.half_edges[start].vertex != v {
            return false;
        }

        let mut local_seen: Vec<bool> = vec![false; hcnt];
        let mut h = start;
        let mut steps: usize = 0;
        let mut closed = false;
        while steps <= expected && !closed
            invariant
                index_bounds(m),
                hcnt == m.half_edges.len(),
                start < hcnt,
                0 <= steps <= expected + 1,
                local_seen@.len() == hcnt as int,
                0 <= h < hcnt,
                h as int == vertex_ring_iter(m, start as int, steps as nat),
                closed ==> h == start,
                forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] local_seen@[hp]
                        ==> exists|i: int| {
                            &&& 0 <= i < steps as int
                            &&& #[trigger] vertex_ring_iter(m, start as int, i as nat) == hp
                        },
                forall|i: int|
                    0 <= i < steps as int ==> #[trigger] local_seen@[vertex_ring_iter(
                        m,
                        start as int,
                        i as nat,
                    )],
                forall|i: int|
                    0 <= i < steps as int ==> #[trigger] m.half_edges@[vertex_ring_iter(
                        m,
                        start as int,
                        i as nat,
                    )].vertex as int == v as int,
                forall|i: int, j: int|
                    #![trigger vertex_ring_iter(m, start as int, i as nat), vertex_ring_iter(m, start as int, j as nat)]
                    0 <= i < j < steps as int
                        ==> vertex_ring_iter(m, start as int, i as nat)
                            != vertex_ring_iter(m, start as int, j as nat),
            decreases expected + 1 - steps,
        {
            let h_prev = h;
            let steps_prev = steps;
            let ghost local_seen_before = local_seen@;

            if local_seen[h] {
                return false;
            }
            local_seen[h] = true;
            if m.half_edges[h].vertex != v {
                return false;
            }
            h = m.half_edges[m.half_edges[h].twin].next;
            if steps == usize::MAX {
                return false;
            }
            steps += 1;
            let _ = (h_prev, steps_prev);

            proof {
                assert(0 <= h_prev as int && (h_prev as int) < local_seen_before.len());
                assert(local_seen@ == local_seen_before.update(h_prev as int, true));
                lemma_vertex_ring_step(
                    m,
                    start as int, h_prev as int,
                    steps_prev as int, steps as int,
                    v as int, hcnt as int,
                    local_seen_before, local_seen@,
                );
                assert(h as int == m.half_edges@[m.half_edges@[h_prev as int].twin as int].next as int);
                assert(h as int == vertex_ring_iter(m, start as int, steps as nat));
            }

            if h == start {
                closed = true;
            }
        }

        if !closed {
            return false;
        }
        if h != start {
            return false;
        }
        if steps != expected {
            return false;
        }

        let mut scan_h: usize = 0;
        while scan_h < hcnt
            invariant
                index_bounds(m),
                hcnt == m.half_edges.len(),
                start < hcnt,
                0 <= scan_h <= hcnt,
                local_seen@.len() == hcnt as int,
                forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] local_seen@[hp]
                        ==> exists|i: int| {
                            &&& 0 <= i < steps as int
                            &&& #[trigger] vertex_ring_iter(m, start as int, i as nat) == hp
                        },
                forall|i: int|
                    0 <= i < steps as int ==> #[trigger] local_seen@[vertex_ring_iter(
                        m,
                        start as int,
                        i as nat,
                    )],
                forall|i: int|
                    0 <= i < steps as int ==> #[trigger] m.half_edges@[vertex_ring_iter(
                        m,
                        start as int,
                        i as nat,
                    )].vertex as int == v as int,
                forall|i: int, j: int|
                    #![trigger vertex_ring_iter(m, start as int, i as nat), vertex_ring_iter(m, start as int, j as nat)]
                    0 <= i < j < steps as int
                        ==> vertex_ring_iter(m, start as int, i as nat)
                            != vertex_ring_iter(m, start as int, j as nat),
                forall|hp: int|
                    #![trigger hp + 0]
                    0 <= hp < scan_h as int
                        && #[trigger] m.half_edges@[hp].vertex as int == v as int ==> local_seen@[hp],
            decreases hcnt - scan_h,
        {
            if m.half_edges[scan_h].vertex == v && !local_seen[scan_h] {
                return false;
            }
            scan_h += 1;
        }

        vertex_cycle_lens.push(steps);

        proof {
            assert(start as int == m.vertex_half_edges@[v as int] as int);
            assert((m.half_edges@[start as int].vertex as int) == v as int);
            assert(forall|vp: int|
                #![trigger m.vertex_half_edges@[vp]]
                0 <= vp < (v + 1) as int
                    ==> (#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp) by {
                assert forall|vp: int|
                    #![trigger m.vertex_half_edges@[vp]]
                    0 <= vp < (v + 1) as int
                        implies (#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp by {
                    if vp < v as int {
                        assert((#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp);
                    } else {
                        assert(vp == v as int);
                        assert((#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == v as int);
                    }
                };
            }
            assert(forall|vp: int|
                #![trigger vertex_cycle_lens@[vp]]
                0 <= vp < (v + 1) as int
                    ==> vertex_representative_cycle_witness(
                        m,
                        vp,
                        vertex_cycle_lens@[vp] as int,
                    )) by {
                assert forall|vp: int|
                    #![trigger vertex_cycle_lens@[vp]]
                    0 <= vp < (v + 1) as int
                        implies vertex_representative_cycle_witness(
                            m,
                            vp,
                            vertex_cycle_lens@[vp] as int,
                        ) by {
                    if vp < v as int {
                        assert(vertex_representative_cycle_witness(
                            m,
                            vp,
                            vertex_cycle_lens@[vp] as int,
                        ));
                    } else {
                        assert(vp == v as int);
                        assert((vertex_cycle_lens@[vp] as int) == steps as int);
                        assert(steps <= expected);
                        assert(expected <= hcnt);
                        assert(steps as int <= hcnt as int);
                        assert(expected > 0);
                        assert(1 <= steps as int);
                        assert(h as int == start as int);
                        assert(h as int == vertex_ring_iter(m, start as int, steps as nat));
                        assert(vertex_ring_iter(m, start as int, steps as nat) == start as int);
                        let s = m.vertex_half_edges@[v as int] as int;
                        assert(s == start as int);
                        assert(half_edge_count(m) == hcnt as int);
                        assert(0 <= s < half_edge_count(m));
                        assert(forall|i: int|
                            0 <= i < steps as int ==> #[trigger] m.half_edges@[vertex_ring_iter(
                                m,
                                s,
                                i as nat,
                            )].vertex as int == v as int) by {
                            assert forall|i: int|
                                0 <= i < steps as int implies #[trigger] m.half_edges@[vertex_ring_iter(
                                    m,
                                    s,
                                    i as nat,
                                )].vertex as int == v as int by {
                                assert(s == start as int);
                                assert((#[trigger] m.half_edges@[vertex_ring_iter(
                                    m,
                                    start as int,
                                    i as nat,
                                )].vertex as int) == v as int);
                            };
                        }
                        assert(vertex_representative_cycle_witness(
                            m,
                            v as int,
                            steps as int,
                        )) by {
                            assert(1 <= steps as int <= half_edge_count(m));
                            assert(vertex_ring_iter(m, s, steps as nat) == s);
                            assert(forall|i: int|
                                0 <= i < steps as int ==> #[trigger] m.half_edges@[vertex_ring_iter(
                                    m,
                                    s,
                                    i as nat,
                                )].vertex as int == v as int);
                            assert(forall|i: int, j: int|
                                #![trigger vertex_ring_iter(m, s, i as nat), vertex_ring_iter(m, s, j as nat)]
                                0 <= i < j < steps as int
                                    ==> vertex_ring_iter(m, s, i as nat)
                                        != vertex_ring_iter(m, s, j as nat));
                            assert(scan_h == hcnt);
                            assert(forall|h0: int|
                                0 <= h0 < half_edge_count(m)
                                    && #[trigger] m.half_edges@[h0].vertex as int == v as int
                                    ==> exists|i: int|
                                        #![trigger vertex_ring_iter(m, s, i as nat)]
                                        0 <= i < steps as int
                                            && vertex_ring_iter(m, s, i as nat) == h0) by {
                                assert forall|h0: int|
                                    0 <= h0 < half_edge_count(m)
                                        && #[trigger] m.half_edges@[h0].vertex as int == v as int
                                        implies exists|i: int|
                                            #![trigger vertex_ring_iter(m, s, i as nat)]
                                            0 <= i < steps as int
                                                && vertex_ring_iter(m, s, i as nat) == h0
                                        by {
                                    assert(half_edge_count(m) == hcnt as int);
                                    assert(0 <= h0 < scan_h as int);
                                    assert(local_seen@[h0]);
                                    assert(exists|i: int| {
                                        &&& 0 <= i < steps as int
                                        &&& #[trigger] vertex_ring_iter(
                                            m,
                                            start as int,
                                            i as nat,
                                        ) == h0
                                    });
                                    let i0 = choose|i: int| {
                                        &&& 0 <= i < steps as int
                                        &&& #[trigger] vertex_ring_iter(
                                            m,
                                            start as int,
                                            i as nat,
                                        ) == h0
                                    };
                                    assert(0 <= i0 < steps as int);
                                    assert(vertex_ring_iter(m, start as int, i0 as nat) == h0);
                                    assert(vertex_ring_iter(m, s, i0 as nat)
                                        == vertex_ring_iter(m, start as int, i0 as nat));
                                    assert(vertex_ring_iter(m, s, i0 as nat) == h0);
                                };
                            };
                        }
                        assert(vertex_representative_cycle_witness(
                            m,
                            vp,
                            vertex_cycle_lens@[vp] as int,
                        ));
                    }
                };
            }
        }
        v += 1;
    }

    proof {
        assert(bounds_ok);
        assert(v == vcnt);
        assert(vertex_cycle_lens@.len() == v as int);
        assert(vertex_cycle_lens@.len() == vertex_count(m));
        assert(vertex_has_incident_half_edge(m)) by {
            assert forall|vp: int|
                #![trigger m.vertex_half_edges@[vp]]
                0 <= vp < vertex_count(m) implies {
                    &&& (m.vertex_half_edges@[vp] as int) < half_edge_count(m)
                    &&& #[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int == vp
                } by {
                assert(vertex_count(m) == vcnt as int);
                assert(half_edge_count(m) == hcnt as int);
                assert(vp < (vcnt as int));
                assert(vp < v as int);
                assert((m.vertex_half_edges@[vp] as int) < half_edge_count(m));
                assert((#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp);
            };
        }
        assert(vertex_manifold(m)) by {
            let cycle_lens = vertex_cycle_lens@;
            assert(cycle_lens.len() == vertex_count(m));
            assert(forall|vp: int|
                #![trigger cycle_lens[vp]]
                0 <= vp < vertex_count(m)
                    ==> vertex_representative_cycle_witness(
                        m,
                        vp,
                        cycle_lens[vp] as int,
                    )) by {
                assert forall|vp: int|
                    #![trigger cycle_lens[vp]]
                    0 <= vp < vertex_count(m)
                        implies vertex_representative_cycle_witness(
                            m,
                            vp,
                            cycle_lens[vp] as int,
                        ) by {
                    assert(vertex_count(m) == vcnt as int);
                    assert(vp < vcnt as int);
                    assert(vp < v as int);
                    assert(vp < cycle_lens.len());
                    assert(cycle_lens[vp] == vertex_cycle_lens@[vp]);
                    assert(vertex_representative_cycle_witness(
                        m,
                        vp,
                        vertex_cycle_lens@[vp] as int,
                    ));
                    assert(vertex_representative_cycle_witness(
                        m,
                        vp,
                        cycle_lens[vp] as int,
                    ));
                };
            }
            assert(exists|cycle_lens: Seq<usize>| {
                &&& cycle_lens.len() == vertex_count(m)
                &&& forall|vp: int|
                    #![trigger cycle_lens[vp]]
                    0 <= vp < vertex_count(m)
                        ==> vertex_representative_cycle_witness(
                            m,
                            vp,
                            cycle_lens[vp] as int,
                        )
            }) by {
                let cycle_lens = vertex_cycle_lens@;
                assert(cycle_lens.len() == vertex_count(m));
                assert(forall|vp: int|
                    #![trigger cycle_lens[vp]]
                    0 <= vp < vertex_count(m)
                        ==> vertex_representative_cycle_witness(
                            m,
                            vp,
                            cycle_lens[vp] as int,
                        ));
            };
        }
        assert(vertex_manifold_total(m));
    }
    true
}

// =============================================================================
// Checker 8: Edge twin duality (iff)
// =============================================================================

pub fn check_edge_twin_duality(m: &Mesh) -> (out: bool)
    ensures
        out == edge_exactly_two_half_edges_total(m),
{
    let bounds_ok = check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let ecnt = m.edge_half_edges.len();
    let hcnt = m.half_edges.len();

    let mut ok = true;
    let mut bad_e: usize = 0;
    let mut e: usize = 0;
    while e < ecnt
        invariant
            index_bounds(m),
            ecnt == m.edge_half_edges.len(),
            hcnt == m.half_edges.len(),
            0 <= e <= ecnt,
            ok ==> forall|ep: int| 0 <= ep < e as int ==> edge_exactly_two_half_edges_at(m, ep),
            !ok ==> {
                &&& bad_e < e
                &&& !edge_exactly_two_half_edges_at(m, bad_e as int)
            },
        decreases ecnt - e,
    {
        let mut count: usize = 0;
        let mut h0: usize = 0;
        let mut h1: usize = 0;
        let mut h2: usize = 0;
        let mut too_many = false;
        let mut h: usize = 0;
        while h < hcnt
            invariant
                index_bounds(m),
                hcnt == m.half_edges.len(),
                0 <= h <= hcnt,
                count <= 2,
                count == 0 ==> forall|j: int|
                    0 <= j < h as int ==> (#[trigger] m.half_edges@[j].edge as int) != e as int,
                count >= 1 ==> {
                    &&& 0 <= h0 < h
                    &&& (#[trigger] m.half_edges@[h0 as int].edge as int) == e as int
                },
                count >= 2 ==> {
                    &&& 0 <= h1 < h
                    &&& h0 != h1
                    &&& (#[trigger] m.half_edges@[h1 as int].edge as int) == e as int
                },
                too_many ==> {
                    &&& count == 2
                    &&& 0 <= h2 < h
                    &&& h2 != h0
                    &&& h2 != h1
                    &&& (#[trigger] m.half_edges@[h2 as int].edge as int) == e as int
                },
                !too_many && count == 1 ==> forall|j: int|
                    0 <= j < h as int && (#[trigger] m.half_edges@[j].edge as int) == e as int
                        ==> j == h0 as int,
                !too_many && count == 2 ==> forall|j: int|
                    0 <= j < h as int && (#[trigger] m.half_edges@[j].edge as int) == e as int
                        ==> (j == h0 as int || j == h1 as int),
            decreases hcnt - h,
        {
            assert(h < m.half_edges.len());
            if m.half_edges[h].edge == e {
                if count == 0 {
                    h0 = h;
                    count = 1;
                } else if count == 1 {
                    h1 = h;
                    count = 2;
                } else {
                    if !too_many {
                        h2 = h;
                    }
                    too_many = true;
                }
            }
            h += 1;
        }

        let count_two = !too_many && count == 2;
        let mut twins_ok = false;
        let mut rep_ok = false;
        let mut twin0: usize = 0;
        let mut twin1: usize = 0;
        let mut rep: usize = 0;
        if count_two {
            assert(0 <= h0 < hcnt);
            assert(0 <= h1 < hcnt);
            twin0 = m.half_edges[h0].twin;
            twin1 = m.half_edges[h1].twin;
            twins_ok = twin0 == h1 && twin1 == h0;
            assert(e < m.edge_half_edges.len());
            rep = m.edge_half_edges[e];
            rep_ok = rep == h0 || rep == h1;
        }
        let edge_ok = count_two && twins_ok && rep_ok;

        if ok && edge_ok {
            proof {
                lemma_prove_edge_exactly_two_at(
                    m, e as int, h0 as int, h1 as int, hcnt as int,
                );
            }
        } else {
            if ok {
                bad_e = e;
                proof {
                    assert(h == hcnt);
                    lemma_disprove_edge_exactly_two_at(
                        m, e as int,
                        h0 as int, h1 as int, h2 as int,
                        count as int, too_many, count_two, twins_ok, rep_ok,
                        hcnt as int,
                    );
                }
            }
            ok = false;
        }

        e += 1;
        let _ = (h2, twin0, twin1, rep);
    }
    let _ = bad_e;

    proof {
        if ok {
            assert(forall|ep: int| 0 <= ep < ecnt as int ==> edge_exactly_two_half_edges_at(m, ep));
            assert(edge_exactly_two_half_edges(m));
            assert(edge_exactly_two_half_edges_total(m));
        } else {
            assert(bad_e < ecnt);
            assert(!edge_exactly_two_half_edges_at(m, bad_e as int));
            if edge_exactly_two_half_edges(m) {
                assert(edge_exactly_two_half_edges_at(m, bad_e as int));
                assert(false);
            }
            assert(!edge_exactly_two_half_edges(m));
            assert(!edge_exactly_two_half_edges_total(m));
        }
    }
    ok
}

// =============================================================================
// Composite: check_structurally_valid (sound, ==>)
// =============================================================================

pub fn check_structurally_valid(m: &Mesh) -> (out: bool)
    ensures
        out ==> structurally_valid(m),
{
    let bounds_ok = check_index_bounds(m);
    if !bounds_ok {
        return false;
    }
    let twin_ok = check_twin_involution(m);
    if !twin_ok {
        return false;
    }
    let prev_next_ok = check_prev_inverse_of_next(m);
    if !prev_next_ok {
        return false;
    }
    let degen_ok = check_no_degenerate_edges(m);
    if !degen_ok {
        return false;
    }
    let orient_ok = check_shared_edge_orientation_consistency(m);
    if !orient_ok {
        return false;
    }
    let face_ok = check_face_cycles(m);
    if !face_ok {
        return false;
    }
    let vertex_ok = check_vertex_manifold(m);
    if !vertex_ok {
        return false;
    }
    let edge_ok = check_edge_twin_duality(m);
    if !edge_ok {
        return false;
    }
    // Check counting invariant: 2E == HE
    let ecnt = m.edge_half_edges.len();
    let hcnt = m.half_edges.len();
    if ecnt > usize::MAX / 2 {
        return false;
    }
    if 2 * ecnt != hcnt {
        return false;
    }
    // Check counting invariant: HE >= 3F
    let fcnt = m.face_half_edges.len();
    if fcnt > usize::MAX / 3 {
        return false;
    }
    if hcnt < 3 * fcnt {
        return false;
    }
    true
}

} // verus!
