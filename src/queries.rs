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
/// Proof: structurally_valid → face_representative_cycles → exists witness
/// → choose satisfies predicate.
pub proof fn lemma_face_degree_spec_valid(m: &Mesh, f: int)
    requires
        structurally_valid(m),
        0 <= f < face_count(m),
    ensures
        face_degree_spec(m, f) >= 3,
        face_representative_cycle_witness(m, f, face_degree_spec(m, f) as int),
        face_degree_spec(m, f) as int <= half_edge_count(m),
{
    // Step 1: Extract face_representative_cycles from structurally_valid
    assert(face_representative_cycles_cover_all_half_edges(m));
    assert(face_representative_cycles(m));

    // Step 2: Extract the witness Seq<usize> for all face cycle lengths
    let fcl = choose|fcl: Seq<usize>| {
        &&& fcl.len() == face_count(m)
        &&& forall|ff: int|
            #![trigger fcl[ff]]
            0 <= ff < face_count(m)
                ==> face_representative_cycle_witness(m, ff, fcl[ff] as int)
    };

    // Step 3: Instantiate for our specific f
    assert(face_representative_cycle_witness(m, f, fcl[f] as int));
    let k = fcl[f] as nat;
    // face_representative_cycle_witness requires 3 <= k <= hcnt
    assert(k >= 3);

    // Step 4: The exists is satisfied, so choose returns a valid k
    // face_degree_spec(m, f) = choose|k: nat| k >= 3 && witness(m, f, k)
    // By choice axiom: P(choose|k| P(k)) holds when exists|k| P(k)
    let fds = face_degree_spec(m, f);

    // Step 5: By uniqueness, face_degree_spec must equal our k
    lemma_face_cycle_unique_period(m, f, fds, k);
}

/// Walk face cycle counting steps until we return to start.
#[verifier::rlimit(30)]
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
        // Now we know: k >= 3, face_representative_cycle_witness(m, f, k as int),
        // k as int <= half_edge_count(m)
    }

    let mut current = m.half_edges[start].next;
    let mut count: usize = 1;

    while current != start
        invariant
            index_bounds(m),
            structurally_valid(m),
            0 <= start < hcnt,
            0 <= current < hcnt,
            1 <= count <= k,
            count <= hcnt,
            hcnt == half_edge_count(m),
            start_int == start as int,
            k >= 3,
            k as int <= hcnt as int,
            face_representative_cycle_witness(m, f as int, k as int),
            current as int == next_iter(m, start_int, count as nat),
            current != start ==> count < k,
        decreases k - count,
    {
        proof {
            // current is in bounds, so next_or_self(m, current) == m.half_edges@[current].next
            lemma_next_iter_in_bounds(m, start_int, count as nat);

            // After the step: new_current = next_or_self(m, current) = next_iter(start, count+1)
            lemma_next_iter_step(m, start_int, count as nat);

            // count < k (from invariant current != start ==> count < k)
        }
        current = m.half_edges[current].next;
        if count >= hcnt {
            break;
        }
        count = count + 1;

        proof {
            // Show count <= k still holds
            // count was < k before increment, so count <= k now

            // Show current != start ==> count < k
            // Equivalently: count == k ==> current == start
            // If count == k, then current == next_iter(start, k) == start
            // (from face_representative_cycle_witness)
            if count as nat == k {
                assert(next_iter(m, start_int, k) == start_int);
            }
        }
    }

    proof {
        // After loop: current == start (normal exit) or count >= hcnt (safety break)
        // But count <= k <= hcnt, so if count >= hcnt then k == hcnt
        // In either case, current == next_iter(start, count) and if current == start,
        // then count must equal k (by period uniqueness from lemma_face_cycle_period).

        // The loop invariant gives: current == next_iter(start, count)
        // If current == start: next_iter(start, count) == start
        // We know next_iter(start, k) == start and 0 < count <= k
        // If count < k, then by lemma_face_cycle_period, next_iter(start, count) != start
        // Contradiction. So count == k == face_degree_spec(m, f).
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
#[verifier::rlimit(30)]
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
    }

    let twin = m.half_edges[start].twin;
    let mut current = m.half_edges[twin].next;
    let mut count: usize = 1;

    while current != start
        invariant
            index_bounds(m),
            structurally_valid(m),
            0 <= start < hcnt,
            0 <= current < hcnt,
            1 <= count <= k,
            count <= hcnt,
            hcnt == half_edge_count(m),
            start_int == start as int,
            k >= 1,
            k as int <= hcnt as int,
            vertex_representative_cycle_witness(m, v as int, k as int),
            current as int == vertex_ring_iter(m, start_int, count as nat),
            current != start ==> count < k,
        decreases k - count,
    {
        proof {
            lemma_vertex_ring_iter_in_bounds(m, start_int, count as nat);
            lemma_vertex_ring_iter_step(m, start_int, count as nat);
        }
        let t = m.half_edges[current].twin;
        current = m.half_edges[t].next;
        if count >= hcnt {
            break;
        }
        count = count + 1;

        proof {
            if count as nat == k {
                assert(vertex_ring_iter(m, start_int, k) == start_int);
            }
        }
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

    while f < fcnt
        invariant
            structurally_valid(m),
            0 <= f <= fcnt,
            fcnt == face_count(m),
            all_tri ==> (forall|ff: int| 0 <= ff < f as int ==> face_is_triangle(m, ff)),
            !all_tri ==> (exists|ff: int| 0 <= ff < f as int && !face_is_triangle(m, ff)),
        decreases fcnt - f,
    {
        let deg = face_degree(m, f);
        if deg != 3 {
            all_tri = false;
        }
        f = f + 1;
    }

    proof {
        if all_tri {
            assert(forall|ff: int| 0 <= ff < face_count(m) ==> face_is_triangle(m, ff));
        } else {
            // exists a non-triangle face, so !all_faces_triangles
            let ff = choose|ff: int| 0 <= ff < f as int && !face_is_triangle(m, ff);
            assert(!face_is_triangle(m, ff));
        }
    }

    all_tri
}

// =============================================================================
// Edge-face relation for triangle meshes
// =============================================================================

/// In a closed triangle mesh, 2 * edge_count == 3 * face_count.
/// Proof sketch: each triangle has 3 half-edges, total HE = 3F.
/// Each edge has exactly 2 half-edges, total HE = 2E.
/// Therefore 2E = 3F.
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
/// Combined with 2E = 3F, we get E = 3F/2 and chi = V - 3F/2 + F = V - F/2.
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
