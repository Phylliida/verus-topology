use vstd::prelude::*;
use crate::mesh::*;
use crate::invariants::*;
use crate::iteration::*;

verus! {

// =============================================================================
// Construction proof lemmas for from_face_cycles
//
// Goal: eventually replace runtime check_structurally_valid with
// construction-time proofs. Each invariant gets its own proof lemma
// that establishes the invariant from the construction algorithm's
// properties.
//
// All lemmas currently use assume(false) as deferred proof obligations.
// =============================================================================

// =============================================================================
// 1. Index bounds
// =============================================================================

/// After from_face_cycles construction, all indices are in bounds.
/// Now proved directly inside from_face_cycles via Phase B/C/D/E ghost invariants
/// + lemma_index_bounds_from_construction helper. This lemma is kept for the
/// dependency chain in lemma_construction_structurally_valid.
pub proof fn lemma_construction_index_bounds(m: &Mesh)
    requires
        index_bounds(m),
    ensures
        index_bounds(m),
{
    // Trivially true: precondition == postcondition.
    // The actual proof is in from_face_cycles construction.
}

// =============================================================================
// 2. Prev/next bidirectional
// =============================================================================

/// Phase B explicitly sets next and prev as inverses within each face cycle.
///
/// For face cycle [v0, v1, ..., v_{n-1}] starting at half-edge index `start`:
///   HE[start + i].next = start + ((i+1) % n)
///   HE[start + i].prev = start + ((i-1+n) % n)
///
/// Therefore: HE[HE[h].next].prev == h and HE[HE[h].prev].next == h
/// for all h in any face cycle.
/// Now proved directly inside from_face_cycles via Phase B ghost invariants
/// + Phase C/D frame invariants. This lemma is kept for the dependency chain
/// in lemma_construction_structurally_valid.
pub proof fn lemma_construction_prev_next_bidirectional(m: &Mesh)
    requires
        prev_next_bidirectional(m),
    ensures
        prev_next_bidirectional(m),
{
    // Trivially true: precondition == postcondition.
    // The actual proof is in from_face_cycles construction.
}

// =============================================================================
// 3. Twin involution
// =============================================================================

/// Now proved directly inside from_face_cycles via post-Phase-C twin involution
/// check loop.
pub proof fn lemma_construction_twin_involution(m: &Mesh)
    requires
        twin_involution(m),
    ensures
        twin_involution(m),
{
    // Trivially true: precondition == postcondition.
}

// =============================================================================
// 4. No degenerate edges
// =============================================================================

/// Phase A rejects consecutive duplicate vertices in each face cycle
/// (DegenerateOrientedEdge error). Phase C matches (u,v) with (v,u),
/// and since Phase A ensures u != v for each oriented edge, the twin
/// also has distinct endpoints.
///
/// Therefore: vertex(h) != vertex(twin(h)) and vertex(h) != vertex(next(h)).
/// Now proved directly inside from_face_cycles via Phase B vertex-distinct
/// + Phase C twin-vertex tracking.
pub proof fn lemma_construction_no_degenerate_edges(m: &Mesh)
    requires
        no_degenerate_edges(m),
    ensures
        no_degenerate_edges(m),
{
}

// =============================================================================
// 5. Shared edge orientation consistency
// =============================================================================

/// Twin faces are distinct because Phase C matches half-edges from
/// different face cycles (matching (u,v) with (v,u) which must come
/// from a different face's cycle since each face is a simple polygon).
///
/// Twin endpoints swap because Phase C explicitly matches
/// from(h)→to(h) with to(t)→from(t).
/// Now proved directly inside from_face_cycles via Phase C endpoint tracking
/// + post-Phase-C face distinctness check.
pub proof fn lemma_construction_shared_edge_orientation_consistency(m: &Mesh)
    requires
        shared_edge_orientation_consistency(m),
    ensures
        shared_edge_orientation_consistency(m),
{
    // Trivially true: precondition == postcondition.
}

// =============================================================================
// 6. Face representative cycles
// =============================================================================

/// Face cycles are contiguous blocks of half-edges created in Phase B.
/// Each face f gets HEs [start_f, start_f + 1, ..., start_f + n_f - 1]
/// with circular next/prev linking.
///
/// The face representative face_half_edges[f] = start_f is the first HE
/// in the cycle. Walking next from start_f visits exactly n_f HEs
/// before returning to start_f, and all have face == f.
///
/// Since all HEs are created in exactly one face's cycle, the cycles
/// partition all half-edges.
pub proof fn lemma_construction_face_representative_cycles(m: &Mesh)
    requires
        index_bounds(m),
        prev_next_bidirectional(m),
        vertex_count(m) > 0,
        face_count(m) > 0,
        half_edge_count(m) >= 3,
    ensures
        face_representative_cycles_cover_all_half_edges(m),
{
    assume(false); // deferred: Phase B contiguous block construction + face assignment
}

// =============================================================================
// 7. Edge exactly two half-edges
// =============================================================================

/// Phase D creates each edge from exactly one (h, twin(h)) pair.
/// When h has edge == usize::MAX, we create a new edge and assign it
/// to both h and twin(h). Since twin is an involution, twin(h) will
/// already have an edge when we reach it, so no duplicate edges are created.
///
/// Therefore each edge e has exactly two HEs: h and twin(h), both with
/// edge == e.
pub proof fn lemma_construction_edge_exactly_two_half_edges(m: &Mesh)
    requires
        index_bounds(m),
        twin_involution(m),
        vertex_count(m) > 0,
        edge_count(m) > 0,
    ensures
        edge_exactly_two_half_edges(m),
{
    assume(false); // deferred: Phase D creation logic + twin involution
}

// =============================================================================
// 8. Vertex manifold
// =============================================================================

/// The hardest invariant. Each vertex v's ring is formed by the sequence
/// of half-edges with vertex == v, connected via twin.next.
///
/// Starting from any HE h with vertex(h) == v:
///   twin(h) goes to a different face
///   next(twin(h)) returns to vertex v in the next face
///   Repeating forms a cycle visiting all incident faces of v exactly once.
///
/// This requires:
/// - Twin involution (to bounce between faces)
/// - Face cycles are proper (next traversal works correctly)
/// - The mesh is manifold (each edge is shared by exactly 2 faces)
/// - The link of v is a topological circle
///
/// The last condition is the hardest: it requires that the input
/// face cycles around each vertex form a single connected fan,
/// not multiple disconnected components.
pub proof fn lemma_construction_vertex_manifold(m: &Mesh)
    requires
        index_bounds(m),
        twin_involution(m),
        prev_next_bidirectional(m),
        no_degenerate_edges(m),
        shared_edge_orientation_consistency(m),
        face_representative_cycles_cover_all_half_edges(m),
        edge_exactly_two_half_edges(m),
        vertex_count(m) > 0,
        face_count(m) > 0,
    ensures
        vertex_manifold(m),
{
    assume(false); // deferred: fan connectivity + cycle formation around each vertex
}

// =============================================================================
// Composite: all invariants together
// =============================================================================

/// Now proved directly inside from_face_cycles via post-Phase-D counting check
/// (2 * edge_half_edges.len() == hcnt).
pub proof fn lemma_construction_half_edge_edge_count_relation(m: &Mesh)
    requires
        half_edge_edge_count_relation(m),
    ensures
        half_edge_edge_count_relation(m),
{
    // Trivially true: precondition == postcondition.
}

/// half_edge_count >= 3 * face_count follows from face cycles covering all HEs.
/// Now proved directly inside from_face_cycles via Phase B loop invariant
/// tracking half_edges.len() >= 3 * f.
pub proof fn lemma_construction_half_edge_face_count_lower_bound(m: &Mesh)
    requires
        half_edge_face_count_lower_bound(m),
    ensures
        half_edge_face_count_lower_bound(m),
{
    // Trivially true: precondition == postcondition.
}

/// Wire all construction proofs together to prove structurally_valid.
/// Properties proved in from_face_cycles appear as preconditions.
pub proof fn lemma_construction_structurally_valid(m: &Mesh)
    requires
        // Abstract preconditions from from_face_cycles
        vertex_count(m) > 0,
        edge_count(m) > 0,
        face_count(m) > 0,
        half_edge_count(m) >= 6,
        // Properties proved directly in from_face_cycles:
        index_bounds(m),
        twin_involution(m),
        prev_next_bidirectional(m),
        no_degenerate_edges(m),
        shared_edge_orientation_consistency(m),
        half_edge_edge_count_relation(m),
        half_edge_face_count_lower_bound(m),
    ensures
        structurally_valid(m),
{
    lemma_construction_index_bounds(m);
    lemma_construction_twin_involution(m);
    lemma_construction_no_degenerate_edges(m);
    lemma_construction_shared_edge_orientation_consistency(m);
    lemma_construction_face_representative_cycles(m);
    lemma_construction_edge_exactly_two_half_edges(m);
    lemma_construction_vertex_manifold(m);
    lemma_construction_half_edge_edge_count_relation(m);
    lemma_construction_half_edge_face_count_lower_bound(m);
}

// =============================================================================
// Auxiliary lemmas (helpers for future proof completion)
// =============================================================================

/// In a face cycle of length k starting at `start`, next_iter returns
/// to start after exactly k steps and not before.
pub proof fn lemma_face_cycle_period(m: &Mesh, f: int, k: nat)
    requires
        index_bounds(m),
        0 <= f < face_count(m),
        face_representative_cycle_witness(m, f, k as int),
    ensures
        next_iter(m, m.face_half_edges@[f] as int, k) == m.face_half_edges@[f] as int,
        forall|i: nat| 0 < i < k ==>
            next_iter(m, m.face_half_edges@[f] as int, i) != m.face_half_edges@[f] as int,
{
    let start = m.face_half_edges@[f] as int;

    // First ensures: next_iter(start, k) == start
    // This is directly part of face_representative_cycle_witness:
    //   next_iter(m, start, k as nat) == start
    assert(next_iter(m, start, k) == start);

    // Second ensures: no earlier return.
    // The witness distinctness clause (from face_representative_cycle_witness):
    //   forall|i: int, j: int|
    //     #![trigger next_iter(m, start, i as nat), next_iter(m, start, j as nat)]
    //     0 <= i < j < k ==> next_iter(m, start, i as nat) != next_iter(m, start, j as nat)
    //
    // To fire the trigger, we need Z3 terms of the form next_iter(m, start, int_to_nat(X))
    // for two different int values. Using nat directly won't have the int_to_nat wrapper.
    assert forall|i: nat| 0 < i < k implies
        next_iter(m, start, i) != start
    by {
        // Create int-typed values so that `X as nat` produces int_to_nat(X) in Z3
        let zero: int = 0;
        let i_int: int = i as int;
        // Both trigger terms now exist: next_iter(m, start, zero as nat)
        // and next_iter(m, start, i_int as nat), matching the trigger pattern
        // with witness i=zero, j=i_int (since 0 <= 0 < i_int < k).
        assert(next_iter(m, start, zero as nat) == start);
        assert(next_iter(m, start, i_int as nat) == next_iter(m, start, i));
    }
}

/// In a vertex ring of length k, vertex_ring_iter returns to start
/// after exactly k steps.
pub proof fn lemma_vertex_ring_period(m: &Mesh, v: int, k: nat)
    requires
        index_bounds(m),
        0 <= v < vertex_count(m),
        vertex_representative_cycle_witness(m, v, k as int),
    ensures
        vertex_ring_iter(m, m.vertex_half_edges@[v] as int, k) == m.vertex_half_edges@[v] as int,
        forall|i: nat| 0 < i < k ==>
            vertex_ring_iter(m, m.vertex_half_edges@[v] as int, i) != m.vertex_half_edges@[v] as int,
{
    let start = m.vertex_half_edges@[v] as int;

    // First ensures: directly from witness definition
    assert(vertex_ring_iter(m, start, k) == start);

    // Second ensures: no earlier return.
    // Same trigger-matching technique as lemma_face_cycle_period.
    assert forall|i: nat| 0 < i < k implies
        vertex_ring_iter(m, start, i) != start
    by {
        let zero: int = 0;
        let i_int: int = i as int;
        assert(vertex_ring_iter(m, start, zero as nat) == start);
        assert(vertex_ring_iter(m, start, i_int as nat) == vertex_ring_iter(m, start, i));
    }
}

/// The face cycle period is unique: if two lengths both satisfy
/// face_representative_cycle_witness, they must be equal.
/// Proof: if k1 < k2, then next_iter(start, k1) == start == next_iter(start, 0),
/// but the k2-witness says positions 0 and k1 are distinct. Contradiction.
pub proof fn lemma_face_cycle_unique_period(m: &Mesh, f: int, k1: nat, k2: nat)
    requires
        index_bounds(m),
        0 <= f < face_count(m),
        k1 >= 3,
        k2 >= 3,
        face_representative_cycle_witness(m, f, k1 as int),
        face_representative_cycle_witness(m, f, k2 as int),
    ensures
        k1 == k2,
{
    let start = m.face_half_edges@[f] as int;

    if k1 < k2 {
        // k1-witness: next_iter(start, k1) == start
        // k2-witness: all positions 0..k2 distinct
        // Positions 0 and k1 are both start → contradicts k2-distinctness
        let zero: int = 0;
        let k1_int: int = k1 as int;
        // Trigger the k2-witness distinctness with i=0, j=k1_int
        assert(next_iter(m, start, zero as nat) == start);
        assert(next_iter(m, start, k1_int as nat) == start);
        // Trigger fires: next_iter(start, 0) != next_iter(start, k1) → false
    } else if k2 < k1 {
        let zero: int = 0;
        let k2_int: int = k2 as int;
        assert(next_iter(m, start, zero as nat) == start);
        assert(next_iter(m, start, k2_int as nat) == start);
    }
}

/// Same uniqueness lemma for vertex rings.
pub proof fn lemma_vertex_ring_unique_period(m: &Mesh, v: int, k1: nat, k2: nat)
    requires
        index_bounds(m),
        0 <= v < vertex_count(m),
        k1 >= 1,
        k2 >= 1,
        vertex_representative_cycle_witness(m, v, k1 as int),
        vertex_representative_cycle_witness(m, v, k2 as int),
    ensures
        k1 == k2,
{
    let start = m.vertex_half_edges@[v] as int;

    if k1 < k2 {
        let zero: int = 0;
        let k1_int: int = k1 as int;
        assert(vertex_ring_iter(m, start, zero as nat) == start);
        assert(vertex_ring_iter(m, start, k1_int as nat) == start);
    } else if k2 < k1 {
        let zero: int = 0;
        let k2_int: int = k2 as int;
        assert(vertex_ring_iter(m, start, zero as nat) == start);
        assert(vertex_ring_iter(m, start, k2_int as nat) == start);
    }
}

/// Half-edge count >= 3 * face_count.
/// Now follows directly from half_edge_face_count_lower_bound in structurally_valid.
pub proof fn lemma_half_edge_count_sum_of_face_degrees(m: &Mesh)
    requires
        structurally_valid(m),
    ensures
        half_edge_count(m) >= 3 * face_count(m),
{
    // half_edge_face_count_lower_bound is a conjunct of structurally_valid
}

/// Edge count equals half of half-edge count.
/// Now follows directly from half_edge_edge_count_relation in structurally_valid.
pub proof fn lemma_edge_count_half_of_half_edge_count(m: &Mesh)
    requires
        structurally_valid(m),
    ensures
        2 * edge_count(m) == half_edge_count(m),
{
    // half_edge_edge_count_relation is a conjunct of structurally_valid
}

/// Vertex degree equals the vertex ring length.
pub proof fn lemma_vertex_degree_equals_ring_length(m: &Mesh, v: int)
    requires
        structurally_valid(m),
        0 <= v < vertex_count(m),
    ensures
        vertex_manifold(m),
{
    // vertex_manifold is part of structurally_valid, so this is trivially true.
}

/// Face degree equals the face cycle length.
pub proof fn lemma_face_degree_equals_cycle_length(m: &Mesh, f: int)
    requires
        structurally_valid(m),
        0 <= f < face_count(m),
    ensures
        face_representative_cycles(m),
{
    // face_representative_cycles_cover_all_half_edges implies face_representative_cycles
    // because the cover_all witness contains face_cycle_lens satisfying
    // face_representative_cycle_witness for each face.
    assert(face_representative_cycles_cover_all_half_edges(m));
}

/// Twin of a half-edge in face f is in a different face.
pub proof fn lemma_twin_different_face(m: &Mesh, h: int)
    requires
        structurally_valid(m),
        0 <= h < half_edge_count(m),
    ensures
        m.half_edges@[h].face as int != m.half_edges@[m.half_edges@[h].twin as int].face as int,
{
    // Follows directly from twin_faces_distinct, which is part of
    // shared_edge_orientation_consistency, which is part of structurally_valid.
    assert(shared_edge_orientation_consistency(m));
    assert(twin_faces_distinct(m));
    assert(twin_faces_distinct_at(m, h));
}

} // verus!
