use vstd::prelude::*;
use crate::mesh::*;
use crate::invariants::*;
use crate::iteration::*;
use crate::construction_proofs::*;
use crate::refinement::*;
use crate::connectivity::*;

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
pub fn face_degree(m: &Mesh, f: usize) -> (out: usize)
    requires
        structurally_valid(m),
        0 <= f < face_count(m) as int,
    ensures
        out as nat == face_degree_spec(m, f as int),
{
    proof {
        // Focus solver on relevant conjuncts
        assert(index_bounds(m));
        assert(face_representative_cycles_cover_all_half_edges(m));
    }
    let hcnt = m.half_edges.len();
    let start = m.face_half_edges[f];
    let ghost start_int: int = start as int;
    let ghost k: nat = face_degree_spec(m, f as int);

    proof {
        lemma_face_degree_spec_valid(m, f as int);
        lemma_next_iter_advance(m, start_int, 0 as nat);
    }

    let mut current = m.half_edges[start].next;
    let mut count: usize = 1;

    while current != start
        invariant
            index_bounds(m),
            0 <= start < hcnt,
            0 <= current < hcnt,
            1 <= count <= k,
            hcnt == half_edge_count(m),
            start_int == start as int,
            k >= 3,
            k as int <= hcnt as int,
            next_iter(m, start_int, k) == start_int,
            current as int == next_iter(m, start_int, count as nat),
        decreases k - count,
    {
        // count < k: if count == k, current == next_iter(start, k) == start,
        // contradicting loop condition current != start.
        proof {
            lemma_next_iter_in_bounds(m, start_int, count as nat);
            lemma_next_iter_advance(m, start_int, count as nat);
        }
        current = m.half_edges[current].next;
        count = count + 1;
    }

    proof {
        // After loop: current == start, so next_iter(start, count) == start.
        // count <= k and for 0 < i < k: next_iter(start, i) != start.
        // So count cannot be less than k. Therefore count == k.
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

/// One iteration of the vertex ring walk loop:
/// proves that vertex_ring_iter(start, count+1) == twin.next of current.
pub proof fn lemma_vertex_degree_loop_step(m: &Mesh, start: int, count: nat)
    requires
        index_bounds(m),
        0 <= start < half_edge_count(m),
        0 <= vertex_ring_iter(m, start, count) < half_edge_count(m),
    ensures
        ({
            let cur = vertex_ring_iter(m, start, count);
            let t = m.half_edges@[cur].twin as int;
            let nxt = m.half_edges@[t].next as int;
            vertex_ring_iter(m, start, (count + 1) as nat) == nxt
        }),
        0 <= vertex_ring_iter(m, start, (count + 1) as nat) < half_edge_count(m),
{
    let cur = vertex_ring_iter(m, start, count);
    // Step 1: vertex_ring_iter(start, count+1) == vertex_ring_succ_or_self(m, cur)
    lemma_vertex_ring_iter_step(m, start, count);
    // Step 2: vertex_ring_succ_or_self(m, cur) == m.half_edges@[twin(cur)].next
    lemma_vertex_ring_succ_eq_twin_next(m, cur);
    // Step 3: result is in bounds
    let t = m.half_edges@[cur].twin as int;
    assert(0 <= t < half_edge_count(m));
    let nxt = m.half_edges@[t].next as int;
    assert(0 <= nxt < half_edge_count(m));
}

/// Walk vertex ring via twin.next counting steps until we return to start.
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
        // Expand: vertex_ring_iter(start, 1) == twin.next(start)
        lemma_vertex_degree_loop_step(m, start_int, 0 as nat);
    }

    let twin = m.half_edges[start].twin;
    let mut current = m.half_edges[twin].next;
    let mut count: usize = 1;

    while current != start
        invariant
            index_bounds(m),
            0 <= start < hcnt,
            0 <= current < hcnt,
            1 <= count <= k,
            hcnt == half_edge_count(m),
            start_int == start as int,
            k >= 1,
            k as int <= hcnt as int,
            vertex_ring_iter(m, start_int, k) == start_int,
            current as int == vertex_ring_iter(m, start_int, count as nat),
        decreases k - count,
    {
        proof {
            lemma_vertex_degree_loop_step(m, start_int, count as nat);
        }
        let t = m.half_edges[current].twin;
        current = m.half_edges[t].next;
        count = count + 1;
    }

    proof {
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
    &&& forall|f: int| 0 <= f < face_count(m) ==> face_is_triangle(m, f)
    &&& half_edge_count(m) == 3 * face_count(m)
}

pub fn check_all_faces_triangles(m: &Mesh) -> (out: bool)
    requires
        structurally_valid(m),
    ensures
        out == all_faces_triangles(m),
{
    let fcnt = m.face_half_edges.len();
    let hcnt = m.half_edges.len();
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

    if !all_tri {
        proof {
            assert(!face_is_triangle(m, bad_face));
            assert(0 <= bad_face < face_count(m));
        }
        return false;
    }

    // Check counting invariant: HE == 3F
    if fcnt > usize::MAX / 3 {
        return false;
    }
    if hcnt != 3 * fcnt {
        return false;
    }

    true
}

// =============================================================================
// Edge-face relation for triangle meshes
// =============================================================================

/// In a closed triangle mesh, 2 * edge_count == 3 * face_count.
/// Follows from 2E == HE (structurally_valid) and HE == 3F (all_faces_triangles).
pub proof fn lemma_triangle_mesh_edge_face_relation(m: &Mesh)
    requires
        structurally_valid(m),
        all_faces_triangles(m),
    ensures
        2 * edge_count(m) == 3 * face_count(m),
{
    // 2E == HE from half_edge_edge_count_relation in structurally_valid
    // HE == 3F from all_faces_triangles
    // Therefore 2E == 3F
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

// =============================================================================
// Euler characteristic preservation lemmas
// =============================================================================

/// Splitting an edge preserves Euler characteristic: V+1, E+1, F unchanged.
pub proof fn lemma_split_edge_preserves_euler(m: &Mesh, r: &Mesh)
    requires
        vertex_count(r) == vertex_count(m) + 1,
        edge_count(r) == edge_count(m) + 1,
        face_count(r) == face_count(m),
    ensures
        euler_characteristic_spec(r) == euler_characteristic_spec(m),
{
}

/// Splitting a face preserves Euler characteristic: V unchanged, E+1, F+1.
pub proof fn lemma_split_face_preserves_euler(m: &Mesh, r: &Mesh)
    requires
        vertex_count(r) == vertex_count(m),
        edge_count(r) == edge_count(m) + 1,
        face_count(r) == face_count(m) + 1,
    ensures
        euler_characteristic_spec(r) == euler_characteristic_spec(m),
{
}

/// Flipping an edge preserves Euler characteristic: all counts unchanged.
pub proof fn lemma_flip_edge_preserves_euler(m: &Mesh, r: &Mesh)
    requires
        vertex_count(r) == vertex_count(m),
        edge_count(r) == edge_count(m),
        face_count(r) == face_count(m),
    ensures
        euler_characteristic_spec(r) == euler_characteristic_spec(m),
{
}

// =============================================================================
// Concrete mesh chi = 2 lemmas
// =============================================================================

/// A tetrahedron has Euler characteristic 2: V=4, E=6, F=4 → 4-6+4=2.
pub proof fn lemma_tetrahedron_euler(m: &Mesh)
    requires
        vertex_count(m) == 4,
        edge_count(m) == 6,
        face_count(m) == 4,
    ensures
        euler_characteristic_spec(m) == 2,
{
}

/// A cube has Euler characteristic 2: V=8, E=12, F=6 → 8-12+6=2.
pub proof fn lemma_cube_euler(m: &Mesh)
    requires
        vertex_count(m) == 8,
        edge_count(m) == 12,
        face_count(m) == 6,
    ensures
        euler_characteristic_spec(m) == 2,
{
}

// =============================================================================
// Genus (Tier 3b)
// =============================================================================

/// Genus of a closed orientable surface: g = (2 - chi) / 2.
pub open spec fn genus_spec(m: &Mesh) -> int {
    (2 - euler_characteristic_spec(m)) / 2
}

/// Genus from raw V, E, F counts (for subdivision where counts are formulas, not a Mesh).
pub open spec fn genus_from_counts_spec(v: int, e: int, f: int) -> int {
    (2 - (v - e + f)) / 2
}

/// A tetrahedron has genus 0: chi = 2 → g = 0.
pub proof fn lemma_tetrahedron_genus_zero(m: &Mesh)
    requires
        vertex_count(m) == 4,
        edge_count(m) == 6,
        face_count(m) == 4,
    ensures
        genus_spec(m) == 0,
{
}

/// A cube has genus 0: chi = 2 → g = 0.
pub proof fn lemma_cube_genus_zero(m: &Mesh)
    requires
        vertex_count(m) == 8,
        edge_count(m) == 12,
        face_count(m) == 6,
    ensures
        genus_spec(m) == 0,
{
}

/// Midpoint subdivision preserves genus: sub counts give the same chi.
pub proof fn lemma_subdivision_preserves_genus(m: &Mesh)
    requires
        structurally_valid(m),
        all_faces_triangles(m),
    ensures
        genus_from_counts_spec(
            subdivision_vertex_count(m),
            subdivision_edge_count(m),
            subdivision_face_count(m),
        ) == genus_spec(m),
{
    lemma_subdivision_preserves_euler(m);
}

// =============================================================================
// Concrete Euler preservation (Tier 3c)
// =============================================================================

/// Splitting an edge preserves chi (concrete version for use after exec Euler ops).
pub proof fn lemma_split_edge_preserves_euler_concrete(m: &Mesh, r: &Mesh)
    requires
        vertex_count(r) == vertex_count(m) + 1,
        edge_count(r) == edge_count(m) + 1,
        face_count(r) == face_count(m),
    ensures
        euler_characteristic_spec(r) == euler_characteristic_spec(m),
{
    lemma_split_edge_preserves_euler(m, r);
}

/// Splitting a face preserves chi (concrete version for use after exec Euler ops).
pub proof fn lemma_split_face_preserves_euler_concrete(m: &Mesh, r: &Mesh)
    requires
        vertex_count(r) == vertex_count(m),
        edge_count(r) == edge_count(m) + 1,
        face_count(r) == face_count(m) + 1,
    ensures
        euler_characteristic_spec(r) == euler_characteristic_spec(m),
{
    lemma_split_face_preserves_euler(m, r);
}

/// Flipping an edge preserves chi (concrete version for use after exec Euler ops).
pub proof fn lemma_flip_edge_preserves_euler_concrete(m: &Mesh, r: &Mesh)
    requires
        vertex_count(r) == vertex_count(m),
        edge_count(r) == edge_count(m),
        face_count(r) == face_count(m),
    ensures
        euler_characteristic_spec(r) == euler_characteristic_spec(m),
{
    lemma_flip_edge_preserves_euler(m, r);
}

// =============================================================================
// Topological sphere (Tier 4a)
// =============================================================================

/// A mesh is a topological sphere: structurally valid, closed, connected, chi = 2.
pub open spec fn is_topological_sphere(m: &Mesh) -> bool {
    &&& structurally_valid(m)
    &&& is_closed(m)
    &&& is_connected(m)
    &&& euler_characteristic_spec(m) == 2
}

/// Runtime checker for topological sphere classification.
pub fn check_topological_sphere(m: &Mesh) -> (out: bool)
    requires
        structurally_valid(m),
    ensures
        out ==> is_topological_sphere(m),
{
    proof { lemma_structurally_valid_is_closed(m); }
    let connected = check_connected(m);
    if !connected {
        return false;
    }

    let vcnt = m.vertex_half_edges.len();
    let ecnt = m.edge_half_edges.len();
    let fcnt = m.face_half_edges.len();

    // Overflow guards for euler_characteristic
    if vcnt >= isize::MAX as usize {
        return false;
    }
    if ecnt >= isize::MAX as usize {
        return false;
    }
    if fcnt >= isize::MAX as usize {
        return false;
    }

    let v = vcnt as isize;
    let e = ecnt as isize;
    let f = fcnt as isize;

    // v - e is safe: both < MAX, so v - e > -(MAX-1) > MIN
    let ve = v - e;
    // Overflow guard for ve + f
    if ve > 0 && f > isize::MAX - ve {
        return false;
    }

    let chi = euler_characteristic(m);
    chi == 2
}

/// A tetrahedron is a topological sphere.
pub proof fn lemma_tetrahedron_is_sphere(m: &Mesh)
    requires
        structurally_valid(m),
        is_connected(m),
        vertex_count(m) == 4,
        edge_count(m) == 6,
        face_count(m) == 4,
    ensures
        is_topological_sphere(m),
{
    lemma_structurally_valid_is_closed(m);
    lemma_tetrahedron_euler(m);
}

/// A cube is a topological sphere.
pub proof fn lemma_cube_is_sphere(m: &Mesh)
    requires
        structurally_valid(m),
        is_connected(m),
        vertex_count(m) == 8,
        edge_count(m) == 12,
        face_count(m) == 6,
    ensures
        is_topological_sphere(m),
{
    lemma_structurally_valid_is_closed(m);
    lemma_cube_euler(m);
}

/// Midpoint subdivision preserves sphere topology.
pub proof fn lemma_subdivision_preserves_sphere(m: &Mesh, r: &Mesh)
    requires
        is_topological_sphere(m),
        all_faces_triangles(m),
        structurally_valid(r),
        is_connected(r),
        vertex_count(r) == subdivision_vertex_count(m),
        edge_count(r) == subdivision_edge_count(m),
        face_count(r) == subdivision_face_count(m),
    ensures
        is_topological_sphere(r),
{
    lemma_structurally_valid_is_closed(r);
    lemma_subdivision_preserves_euler(m);
}

} // verus!
