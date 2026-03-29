use vstd::prelude::*;
use crate::mesh::*;
use crate::iteration::*;

verus! {

//  --- Twin involution ---

pub open spec fn twin_involution(m: &Mesh) -> bool {
    forall|h: int|
        0 <= h < half_edge_count(m)
            ==> (#[trigger] m.half_edges@[m.half_edges@[h].twin as int].twin as int) == h
}

pub open spec fn twin_involution_total(m: &Mesh) -> bool {
    index_bounds(m) && twin_involution(m)
}

//  --- Prev/next bidirectional ---

pub open spec fn next_prev_inverse_at(m: &Mesh, h: int) -> bool {
    let hcnt = half_edge_count(m);
    if 0 <= h < hcnt {
        (m.half_edges@[m.half_edges@[h].next as int].prev as int) == h
    } else {
        false
    }
}

pub open spec fn prev_next_inverse_at(m: &Mesh, h: int) -> bool {
    let hcnt = half_edge_count(m);
    if 0 <= h < hcnt {
        (m.half_edges@[m.half_edges@[h].prev as int].next as int) == h
    } else {
        false
    }
}

pub open spec fn next_prev_inverse_only(m: &Mesh) -> bool {
    forall|h: int| 0 <= h < half_edge_count(m) ==> next_prev_inverse_at(m, h)
}

pub open spec fn prev_next_inverse_only(m: &Mesh) -> bool {
    forall|h: int| 0 <= h < half_edge_count(m) ==> prev_next_inverse_at(m, h)
}

pub open spec fn prev_next_bidirectional(m: &Mesh) -> bool {
    next_prev_inverse_only(m) && prev_next_inverse_only(m)
}

pub open spec fn prev_next_bidirectional_total(m: &Mesh) -> bool {
    index_bounds(m) && prev_next_bidirectional(m)
}

//  --- No degenerate edges ---

pub open spec fn no_degenerate_edges(m: &Mesh) -> bool {
    forall|h: int| 0 <= h < half_edge_count(m) ==> {
        &&& (#[trigger] m.half_edges@[h].vertex as int)
            != (m.half_edges@[m.half_edges@[h].twin as int].vertex as int)
        &&& (#[trigger] m.half_edges@[h].vertex as int)
            != (m.half_edges@[m.half_edges@[h].next as int].vertex as int)
    }
}

pub open spec fn no_degenerate_edges_total(m: &Mesh) -> bool {
    index_bounds(m) && no_degenerate_edges(m)
}

//  --- Shared edge orientation consistency ---

pub open spec fn twin_faces_distinct_at(m: &Mesh, h: int) -> bool {
    let hcnt = half_edge_count(m);
    let t = m.half_edges@[h].twin as int;
    &&& 0 <= h < hcnt
    &&& 0 <= t < hcnt
    &&& m.half_edges@[h].face as int != m.half_edges@[t].face as int
}

pub open spec fn twin_faces_distinct(m: &Mesh) -> bool {
    forall|h: int|
        0 <= h < half_edge_count(m)
            ==> #[trigger] twin_faces_distinct_at(m, h)
}

pub open spec fn half_edge_from_vertex(m: &Mesh, h: int) -> int {
    m.half_edges@[h].vertex as int
}

pub open spec fn half_edge_to_vertex(m: &Mesh, h: int) -> int {
    m.half_edges@[m.half_edges@[h].next as int].vertex as int
}

pub open spec fn twin_endpoint_correspondence_at(m: &Mesh, h: int) -> bool {
    let hcnt = half_edge_count(m);
    let t = m.half_edges@[h].twin as int;
    &&& 0 <= h < hcnt
    &&& 0 <= t < hcnt
    &&& half_edge_from_vertex(m, t) == half_edge_to_vertex(m, h)
    &&& half_edge_to_vertex(m, t) == half_edge_from_vertex(m, h)
}

pub open spec fn twin_endpoint_correspondence(m: &Mesh) -> bool {
    forall|h: int|
        0 <= h < half_edge_count(m)
            ==> #[trigger] twin_endpoint_correspondence_at(m, h)
}

pub open spec fn shared_edge_orientation_consistency(m: &Mesh) -> bool {
    &&& twin_faces_distinct(m)
    &&& twin_endpoint_correspondence(m)
}

pub open spec fn shared_edge_orientation_consistency_total(m: &Mesh) -> bool {
    index_bounds(m) && shared_edge_orientation_consistency(m)
}

//  --- Face cycles cover ---

pub open spec fn face_representative_cycle_witness(m: &Mesh, f: int, k: int) -> bool {
    let hcnt = half_edge_count(m);
    let start = m.face_half_edges@[f] as int;
    &&& 3 <= k <= hcnt
    &&& next_iter(m, start, k as nat) == start
    &&& forall|i: int|
        0 <= i < k ==> #[trigger] m.half_edges@[next_iter(m, start, i as nat)].face as int
            == f
    &&& forall|i: int, j: int|
        #![trigger next_iter(m, start, i as nat), next_iter(m, start, j as nat)]
        0 <= i < j < k
            ==> next_iter(m, start, i as nat) != next_iter(m, start, j as nat)
}

pub open spec fn face_representative_cycles(m: &Mesh) -> bool {
    exists|face_cycle_lens: Seq<usize>| {
        &&& face_cycle_lens.len() == face_count(m)
        &&& forall|f: int|
            #![trigger face_cycle_lens[f]]
            0 <= f < face_count(m)
                ==> face_representative_cycle_witness(m, f, face_cycle_lens[f] as int)
    }
}

pub open spec fn face_representative_cycles_total(m: &Mesh) -> bool {
    index_bounds(m) && face_representative_cycles(m)
}

pub open spec fn face_representative_cycles_cover_all_half_edges_witness(
    m: &Mesh,
    face_cycle_lens: Seq<usize>,
    covered: Seq<bool>,
) -> bool {
    &&& face_cycle_lens.len() == face_count(m)
    &&& covered.len() == half_edge_count(m)
    &&& forall|f: int|
        #![trigger face_cycle_lens[f]]
        0 <= f < face_count(m)
            ==> face_representative_cycle_witness(m, f, face_cycle_lens[f] as int)
    &&& forall|h: int|
        #![trigger h + 0]
        0 <= h < half_edge_count(m) && #[trigger] covered[h]
            ==> exists|f: int, i: int| {
                &&& 0 <= f < face_count(m)
                &&& 0 <= i < face_cycle_lens[f] as int
                &&& #[trigger] next_iter(m, m.face_half_edges@[f] as int, i as nat) == h
            }
    &&& forall|h: int| 0 <= h < half_edge_count(m) ==> #[trigger] covered[h]
    &&& forall|f1: int, i1: int, f2: int, i2: int|
        #![trigger next_iter(m, m.face_half_edges@[f1] as int, i1 as nat), next_iter(m, m.face_half_edges@[f2] as int, i2 as nat)]
        0 <= f1 < face_count(m)
            && 0 <= f2 < face_count(m)
            && 0 <= i1 < face_cycle_lens[f1] as int
            && 0 <= i2 < face_cycle_lens[f2] as int
            && next_iter(m, m.face_half_edges@[f1] as int, i1 as nat)
                == next_iter(m, m.face_half_edges@[f2] as int, i2 as nat)
            ==> f1 == f2
}

pub open spec fn face_representative_cycles_cover_all_half_edges(m: &Mesh) -> bool {
    exists|face_cycle_lens: Seq<usize>, covered: Seq<bool>| {
        face_representative_cycles_cover_all_half_edges_witness(
            m,
            face_cycle_lens,
            covered,
        )
    }
}

pub open spec fn face_representative_cycles_cover_all_half_edges_total(m: &Mesh) -> bool {
    index_bounds(m) && face_representative_cycles_cover_all_half_edges(m)
}

pub open spec fn face_has_incident_half_edge(m: &Mesh) -> bool {
    forall|f: int|
        #![trigger m.face_half_edges@[f]]
        0 <= f < face_count(m) ==> {
            &&& (m.face_half_edges@[f] as int) < half_edge_count(m)
            &&& #[trigger] m.half_edges@[m.face_half_edges@[f] as int].face as int == f
        }
}

//  --- Vertex manifold ---

pub open spec fn vertex_representative_cycle_witness(m: &Mesh, v: int, k: int) -> bool {
    let hcnt = half_edge_count(m);
    let start = m.vertex_half_edges@[v] as int;
    &&& 1 <= k <= hcnt
    &&& vertex_ring_iter(m, start, k as nat) == start
    &&& forall|i: int|
        0 <= i < k ==> {
            #[trigger] m.half_edges@[vertex_ring_iter(m, start, i as nat)].vertex as int == v
        }
    &&& forall|i: int, j: int|
        #![trigger vertex_ring_iter(m, start, i as nat), vertex_ring_iter(m, start, j as nat)]
        0 <= i < j < k
            ==> vertex_ring_iter(m, start, i as nat)
                != vertex_ring_iter(m, start, j as nat)
    &&& forall|h: int|
        0 <= h < hcnt && #[trigger] m.half_edges@[h].vertex as int == v ==> exists|i: int|
            #![trigger vertex_ring_iter(m, start, i as nat)]
            0 <= i < k && vertex_ring_iter(m, start, i as nat) == h
}

pub open spec fn vertex_manifold(m: &Mesh) -> bool {
    exists|vertex_cycle_lens: Seq<usize>| {
        &&& vertex_cycle_lens.len() == vertex_count(m)
        &&& forall|v: int|
            #![trigger vertex_cycle_lens[v]]
            0 <= v < vertex_count(m)
                ==> vertex_representative_cycle_witness(
                    m,
                    v,
                    vertex_cycle_lens[v] as int,
                )
    }
}

pub open spec fn vertex_manifold_total(m: &Mesh) -> bool {
    index_bounds(m) && vertex_manifold(m)
}

pub open spec fn vertex_has_incident_half_edge(m: &Mesh) -> bool {
    forall|v: int|
        #![trigger m.vertex_half_edges@[v]]
        0 <= v < vertex_count(m) ==> {
            &&& (m.vertex_half_edges@[v] as int) < half_edge_count(m)
            &&& #[trigger] m.half_edges@[m.vertex_half_edges@[v] as int].vertex as int == v
        }
}

//  --- Edge twin duality ---

pub open spec fn edge_exactly_two_half_edges_at(m: &Mesh, e: int) -> bool {
    let hcnt = half_edge_count(m);
    &&& 0 <= e < edge_count(m)
    &&& exists|h0: int, h1: int| {
        &&& 0 <= h0 < hcnt
        &&& 0 <= h1 < hcnt
        &&& h0 != h1
        &&& (#[trigger] m.half_edges@[h0].edge as int) == e
        &&& (#[trigger] m.half_edges@[h1].edge as int) == e
        &&& (m.half_edges@[h0].twin as int) == h1
        &&& (m.half_edges@[h1].twin as int) == h0
        &&& ((m.edge_half_edges@[e] as int) == h0 || (m.edge_half_edges@[e] as int) == h1)
        &&& forall|h: int|
            0 <= h < hcnt && (#[trigger] m.half_edges@[h].edge as int) == e ==> (h == h0 || h == h1)
    }
}

pub open spec fn edge_exactly_two_half_edges(m: &Mesh) -> bool {
    forall|e: int| 0 <= e < edge_count(m) ==> edge_exactly_two_half_edges_at(m, e)
}

pub open spec fn edge_exactly_two_half_edges_total(m: &Mesh) -> bool {
    index_bounds(m) && edge_exactly_two_half_edges(m)
}

//  --- Composite ---

///  2 * edge_count == half_edge_count (each edge has exactly 2 half-edges).
///  This is the counting consequence of edge_exactly_two_half_edges.
pub open spec fn half_edge_edge_count_relation(m: &Mesh) -> bool {
    2 * edge_count(m) == half_edge_count(m)
}

///  half_edge_count >= 3 * face_count (each face has at least 3 half-edges).
///  This is the counting consequence of face cycles covering all half-edges.
pub open spec fn half_edge_face_count_lower_bound(m: &Mesh) -> bool {
    half_edge_count(m) >= 3 * face_count(m)
}

pub open spec fn structurally_valid(m: &Mesh) -> bool {
    &&& index_bounds(m)
    &&& twin_involution(m)
    &&& prev_next_bidirectional(m)
    &&& no_degenerate_edges(m)
    &&& shared_edge_orientation_consistency(m)
    &&& face_representative_cycles_cover_all_half_edges(m)
    &&& vertex_manifold(m)
    &&& edge_exactly_two_half_edges(m)
    &&& half_edge_edge_count_relation(m)
    &&& half_edge_face_count_lower_bound(m)
}

//  --- Closedness ---

///  A mesh is closed iff every edge has exactly two half-edges
///  and twin half-edges belong to distinct faces.
pub open spec fn is_closed(m: &Mesh) -> bool {
    edge_exactly_two_half_edges(m) && twin_faces_distinct(m)
}

///  structurally_valid implies is_closed.
pub proof fn lemma_structurally_valid_is_closed(m: &Mesh)
    requires
        structurally_valid(m),
    ensures
        is_closed(m),
{
}

} //  verus!
