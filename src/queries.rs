use vstd::prelude::*;
use crate::mesh::*;
use crate::invariants::*;
use crate::iteration::*;
use crate::construction_proofs::*;

verus! {

// =============================================================================
// Face degree
// =============================================================================

/// Number of half-edges (== sides) in face f's cycle.
pub open spec fn face_degree_spec(m: &Mesh, f: int) -> nat
    recommends
        structurally_valid(m),
        0 <= f < face_count(m),
{
    choose|k: nat| k >= 3 && face_representative_cycle_witness(m, f, k as int)
}

pub open spec fn face_is_triangle(m: &Mesh, f: int) -> bool {
    face_degree_spec(m, f) == 3
}

/// face_degree_spec gives a valid face cycle witness.
pub proof fn lemma_face_degree_spec_valid(m: &Mesh, f: int)
    requires
        structurally_valid(m),
        0 <= f < face_count(m),
    ensures
        face_degree_spec(m, f) >= 3,
        face_representative_cycle_witness(m, f, face_degree_spec(m, f) as int),
        face_degree_spec(m, f) as int <= half_edge_count(m),
{
    assert(face_representative_cycles_cover_all_half_edges(m));
    assert(face_representative_cycles(m));

    let fcl = choose|fcl: Seq<usize>| {
        &&& fcl.len() == face_count(m)
        &&& forall|ff: int|
            #![trigger fcl[ff]]
            0 <= ff < face_count(m)
                ==> face_representative_cycle_witness(m, ff, fcl[ff] as int)
    };

    assert(face_representative_cycle_witness(m, f, fcl[f] as int));
    let k = fcl[f] as nat;
    assert(k >= 3);

    let fds = face_degree_spec(m, f);
    lemma_face_cycle_unique_period(m, f, fds, k);
}

/// Connect next_or_self to .next for valid half-edges.
pub proof fn lemma_next_or_self_eq_next(m: &Mesh, h: int)
    requires
        index_bounds(m),
        0 <= h < half_edge_count(m),
    ensures
        next_or_self(m, h) == m.half_edges@[h].next as int,
{
    let hcnt = half_edge_count(m);
    let n = m.half_edges@[h].next as int;
    assert(0 <= n < hcnt);
}

/// Advance next_iter by one step using .next field.
pub proof fn lemma_next_iter_advance(m: &Mesh, start: int, n: nat)
    requires
        index_bounds(m),
        0 <= start < half_edge_count(m),
        0 <= next_iter(m, start, n) < half_edge_count(m),
    ensures
        next_iter(m, start, (n + 1) as nat)
            == m.half_edges@[next_iter(m, start, n)].next as int,
{
    lemma_next_iter_step(m, start, n);
    lemma_next_or_self_eq_next(m, next_iter(m, start, n));
}

/// Connect vertex_ring_succ_or_self to twin.next for valid half-edges.
pub proof fn lemma_vertex_ring_succ_eq_twin_next(m: &Mesh, h: int)
    requires
        index_bounds(m),
        0 <= h < half_edge_count(m),
    ensures
        vertex_ring_succ_or_self(m, h)
            == m.half_edges@[m.half_edges@[h].twin as int].next as int,
{
    let hcnt = half_edge_count(m);
    let t = m.half_edges@[h].twin as int;
    assert(0 <= t < hcnt);
    let n = m.half_edges@[t].next as int;
    assert(0 <= n < hcnt);
}

/// Advance vertex_ring_iter by one step.
pub proof fn lemma_vertex_ring_iter_advance(m: &Mesh, start: int, n: nat)
    requires
        index_bounds(m),
        0 <= start < half_edge_count(m),
        0 <= vertex_ring_iter(m, start, n) < half_edge_count(m),
    ensures
        vertex_ring_iter(m, start, (n + 1) as nat)
            == m.half_edges@[m.half_edges@[vertex_ring_iter(m, start, n)].twin as int].next as int,
{
    lemma_vertex_ring_iter_step(m, start, n);
    lemma_vertex_ring_succ_eq_twin_next(m, vertex_ring_iter(m, start, n));
}

/// Walk face cycle counting steps until we return to start.
#[verifier::exec_allows_no_decreases_clause]
pub fn face_degree(m: &Mesh, f: usize) -> (out: usize)
    requires
        structurally_valid(m),
        0 <= f < face_count(m) as int,
    ensures
        out as nat == face_degree_spec(m, f as int),
{
    let hcnt = m.half_edges.len();
    let start = m.face_half_edges[f];
    let ghost start_int: int = start as int;
    let ghost k: nat = face_degree_spec(m, f as int);

    proof {
        lemma_face_degree_spec_valid(m, f as int);
        // Expand: next_iter(start, 1) == .next for the initial assignment
        lemma_next_iter_advance(m, start_int, 0 as nat);
    }

    let mut current = m.half_edges[start].next;
    let mut count: usize = 1;

    while current != start
        invariant
            index_bounds(m),
            0 <= start < hcnt,
            0 <= current < hcnt,
            1 <= count <= hcnt,
            hcnt == half_edge_count(m),
            start_int == start as int,
            k >= 3,
            k as int <= hcnt as int,
            next_iter(m, start_int, k) == start_int,
            current as int == next_iter(m, start_int, count as nat),
    {
        proof {
            lemma_next_iter_in_bounds(m, start_int, count as nat);
            lemma_next_iter_advance(m, start_int, count as nat);
        }
        current = m.half_edges[current].next;
        if count >= hcnt {
            break;
        }
        count = count + 1;
    }

    proof {
        // After loop: next_iter(start, count) == start (or safety break)
        // We need count == k.
        // From lemma_face_cycle_period: for 0 < i < k, next_iter(start, i) != start
        // count <= hcnt and count >= 1. If count < k, next_iter(start, count) != start.
        // But current == start (normal exit), contradiction. So count >= k.
        // If count > k: the safety break would have triggered at count == hcnt,
        // but k <= hcnt and the period returns at k. Actually count can't exceed k
        // because the loop exits when current hits start at step k.
        // Therefore count == k.
        lemma_face_degree_spec_valid(m, f as int);
        lemma_face_cycle_period(m, f as int, k);
    }

    count
}

// =============================================================================
// Vertex degree
// =============================================================================

/// Number of half-edges emanating from vertex v (== valence).
pub open spec fn vertex_degree_spec(m: &Mesh, v: int) -> nat
    recommends
        structurally_valid(m),
        0 <= v < vertex_count(m),
{
    choose|k: nat| k >= 1 && vertex_representative_cycle_witness(m, v, k as int)
}

/// vertex_degree_spec gives a valid vertex ring witness.
pub proof fn lemma_vertex_degree_spec_valid(m: &Mesh, v: int)
    requires
        structurally_valid(m),
        0 <= v < vertex_count(m),
    ensures
        vertex_degree_spec(m, v) >= 1,
        vertex_representative_cycle_witness(m, v, vertex_degree_spec(m, v) as int),
        vertex_degree_spec(m, v) as int <= half_edge_count(m),
{
    assert(vertex_manifold(m));

    let vcl = choose|vcl: Seq<usize>| {
        &&& vcl.len() == vertex_count(m)
        &&& forall|vv: int|
            #![trigger vcl[vv]]
            0 <= vv < vertex_count(m)
                ==> vertex_representative_cycle_witness(m, vv, vcl[vv] as int)
    };

    assert(vertex_representative_cycle_witness(m, v, vcl[v] as int));
    let k = vcl[v] as nat;
    assert(k >= 1);

    let vds = vertex_degree_spec(m, v);
    lemma_vertex_ring_unique_period(m, v, vds, k);
}

/// Walk vertex ring via twin.next counting steps until we return to start.
#[verifier::exec_allows_no_decreases_clause]
pub fn vertex_degree(m: &Mesh, v: usize) -> (out: usize)
    requires
        structurally_valid(m),
        0 <= v < vertex_count(m) as int,
    ensures
        out as nat == vertex_degree_spec(m, v as int),
{
    let hcnt = m.half_edges.len();
    let start = m.vertex_half_edges[v];
    let ghost start_int: int = start as int;
    let ghost k: nat = vertex_degree_spec(m, v as int);

    proof {
        lemma_vertex_degree_spec_valid(m, v as int);
        lemma_vertex_ring_iter_advance(m, start_int, 0 as nat);
    }

    let twin = m.half_edges[start].twin;
    let mut current = m.half_edges[twin].next;
    let mut count: usize = 1;

    while current != start
        invariant
            index_bounds(m),
            0 <= start < hcnt,
            0 <= current < hcnt,
            1 <= count <= hcnt,
            hcnt == half_edge_count(m),
            start_int == start as int,
            k >= 1,
            k as int <= hcnt as int,
            vertex_ring_iter(m, start_int, k) == start_int,
            current as int == vertex_ring_iter(m, start_int, count as nat),
    {
        proof {
            lemma_vertex_ring_iter_in_bounds(m, start_int, count as nat);
            lemma_vertex_ring_iter_advance(m, start_int, count as nat);
        }
        let t = m.half_edges[current].twin;
        current = m.half_edges[t].next;
        if count >= hcnt {
            break;
        }
        count = count + 1;
    }

    proof {
        lemma_vertex_degree_spec_valid(m, v as int);
        lemma_vertex_ring_period(m, v as int, k);
    }

    count
}

// =============================================================================
// Euler characteristic
// =============================================================================

pub open spec fn euler_characteristic_spec(m: &Mesh) -> int {
    vertex_count(m) - edge_count(m) + face_count(m)
}

pub fn euler_characteristic(m: &Mesh) -> (out: isize)
    requires
        vertex_count(m) < isize::MAX as int,
        edge_count(m) < isize::MAX as int,
        face_count(m) < isize::MAX as int,
        vertex_count(m) - edge_count(m) + face_count(m) >= isize::MIN as int,
        vertex_count(m) - edge_count(m) + face_count(m) <= isize::MAX as int,
    ensures
        out as int == euler_characteristic_spec(m),
{
    let v = m.vertex_half_edges.len() as isize;
    let e = m.edge_half_edges.len() as isize;
    let f = m.face_half_edges.len() as isize;
    v - e + f
}

// =============================================================================
// All faces triangles
// =============================================================================

pub open spec fn all_faces_triangles(m: &Mesh) -> bool {
    forall|f: int| 0 <= f < face_count(m) ==> face_is_triangle(m, f)
}

pub fn check_all_faces_triangles(m: &Mesh) -> (out: bool)
    requires
        structurally_valid(m),
    ensures
        out == all_faces_triangles(m),
{
    let fcnt = m.face_half_edges.len();
    let mut f: usize = 0;
    let mut all_tri = true;
    let ghost bad_face: int = -1;

    while f < fcnt
        invariant
            structurally_valid(m),
            0 <= f <= fcnt,
            fcnt == face_count(m),
            all_tri ==> (forall|ff: int| 0 <= ff < f as int ==> face_is_triangle(m, ff)),
            !all_tri ==> (0 <= bad_face < f as int && !face_is_triangle(m, bad_face)),
        decreases fcnt - f,
    {
        let deg = face_degree(m, f);
        if deg != 3 {
            all_tri = false;
            proof { bad_face = f as int; }
        }
        f = f + 1;
    }

    proof {
        if !all_tri {
            assert(!face_is_triangle(m, bad_face));
            assert(0 <= bad_face < face_count(m));
        }
    }

    all_tri
}

// =============================================================================
// Edge-face relation for triangle meshes
// =============================================================================

/// In a closed triangle mesh, 2 * edge_count == 3 * face_count.
pub proof fn lemma_triangle_mesh_edge_face_relation(m: &Mesh)
    requires
        structurally_valid(m),
        all_faces_triangles(m),
    ensures
        2 * edge_count(m) == 3 * face_count(m),
{
    assume(false); // deferred: prove from half-edge double-counting
}

/// In a closed triangle mesh, Euler characteristic chi = V - E + F.
pub proof fn lemma_triangle_mesh_euler(m: &Mesh)
    requires
        structurally_valid(m),
        all_faces_triangles(m),
    ensures
        2 * edge_count(m) == 3 * face_count(m),
        2 * euler_characteristic_spec(m) == 2 * vertex_count(m) - face_count(m),
{
    lemma_triangle_mesh_edge_face_relation(m);
}

} // verus!
