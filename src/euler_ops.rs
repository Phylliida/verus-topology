use vstd::prelude::*;
use crate::mesh::*;
use crate::invariants::*;
use crate::checkers::*;
use crate::queries::*;

verus! {

// =============================================================================
// Error type
// =============================================================================

#[derive(Structural, PartialEq, Eq)]
pub enum EulerError {
    InvalidIndex,
    NotTriangleFace { face: usize },
    WouldCreateDegeneracy,
    ValidationFailed,
    Overflow,
}

// =============================================================================
// Helper: rebuild a HalfEdge with one field changed
// =============================================================================

spec fn he_with_twin(he: HalfEdge, new_twin: usize) -> HalfEdge {
    HalfEdge { twin: new_twin, next: he.next, prev: he.prev, vertex: he.vertex, edge: he.edge, face: he.face }
}

spec fn he_with_next(he: HalfEdge, new_next: usize) -> HalfEdge {
    HalfEdge { twin: he.twin, next: new_next, prev: he.prev, vertex: he.vertex, edge: he.edge, face: he.face }
}

spec fn he_with_prev(he: HalfEdge, new_prev: usize) -> HalfEdge {
    HalfEdge { twin: he.twin, next: he.next, prev: new_prev, vertex: he.vertex, edge: he.edge, face: he.face }
}

spec fn he_with_vertex(he: HalfEdge, new_vertex: usize) -> HalfEdge {
    HalfEdge { twin: he.twin, next: he.next, prev: he.prev, vertex: new_vertex, edge: he.edge, face: he.face }
}

spec fn he_with_edge(he: HalfEdge, new_edge: usize) -> HalfEdge {
    HalfEdge { twin: he.twin, next: he.next, prev: he.prev, vertex: he.vertex, edge: new_edge, face: he.face }
}

pub open spec fn he_with_face(he: HalfEdge, new_face: usize) -> HalfEdge {
    HalfEdge { twin: he.twin, next: he.next, prev: he.prev, vertex: he.vertex, edge: he.edge, face: new_face }
}

proof fn lemma_he_with_face_fields(he: HalfEdge, f: usize)
    ensures
        he_with_face(he, f).vertex == he.vertex,
        he_with_face(he, f).next == he.next,
        he_with_face(he, f).twin == he.twin,
        he_with_face(he, f).prev == he.prev,
        he_with_face(he, f).edge == he.edge,
{}

// =============================================================================
// Exec helper: set one field of a half-edge in the vector
// =============================================================================

fn set_he_twin(half_edges: &mut Vec<HalfEdge>, idx: usize, val: usize)
    requires
        0 <= idx < old(half_edges).len(),
    ensures
        half_edges.len() == old(half_edges).len(),
        half_edges@[idx as int] == he_with_twin(old(half_edges)@[idx as int], val),
        forall|i: int| 0 <= i < half_edges.len() && i != idx as int
            ==> half_edges@[i] == old(half_edges)@[i],
{
    let he = half_edges[idx];
    half_edges.set(idx, HalfEdge { twin: val, next: he.next, prev: he.prev, vertex: he.vertex, edge: he.edge, face: he.face });
}

fn set_he_next(half_edges: &mut Vec<HalfEdge>, idx: usize, val: usize)
    requires
        0 <= idx < old(half_edges).len(),
    ensures
        half_edges.len() == old(half_edges).len(),
        half_edges@[idx as int] == he_with_next(old(half_edges)@[idx as int], val),
        forall|i: int| 0 <= i < half_edges.len() && i != idx as int
            ==> half_edges@[i] == old(half_edges)@[i],
{
    let he = half_edges[idx];
    half_edges.set(idx, HalfEdge { twin: he.twin, next: val, prev: he.prev, vertex: he.vertex, edge: he.edge, face: he.face });
}

fn set_he_prev(half_edges: &mut Vec<HalfEdge>, idx: usize, val: usize)
    requires
        0 <= idx < old(half_edges).len(),
    ensures
        half_edges.len() == old(half_edges).len(),
        half_edges@[idx as int] == he_with_prev(old(half_edges)@[idx as int], val),
        forall|i: int| 0 <= i < half_edges.len() && i != idx as int
            ==> half_edges@[i] == old(half_edges)@[i],
{
    let he = half_edges[idx];
    half_edges.set(idx, HalfEdge { twin: he.twin, next: he.next, prev: val, vertex: he.vertex, edge: he.edge, face: he.face });
}

fn set_he_vertex(half_edges: &mut Vec<HalfEdge>, idx: usize, val: usize)
    requires
        0 <= idx < old(half_edges).len(),
    ensures
        half_edges.len() == old(half_edges).len(),
        half_edges@[idx as int] == he_with_vertex(old(half_edges)@[idx as int], val),
        forall|i: int| 0 <= i < half_edges.len() && i != idx as int
            ==> half_edges@[i] == old(half_edges)@[i],
{
    let he = half_edges[idx];
    half_edges.set(idx, HalfEdge { twin: he.twin, next: he.next, prev: he.prev, vertex: val, edge: he.edge, face: he.face });
}

fn set_he_edge(half_edges: &mut Vec<HalfEdge>, idx: usize, val: usize)
    requires
        0 <= idx < old(half_edges).len(),
    ensures
        half_edges.len() == old(half_edges).len(),
        half_edges@[idx as int] == he_with_edge(old(half_edges)@[idx as int], val),
        forall|i: int| 0 <= i < half_edges.len() && i != idx as int
            ==> half_edges@[i] == old(half_edges)@[i],
{
    let he = half_edges[idx];
    half_edges.set(idx, HalfEdge { twin: he.twin, next: he.next, prev: he.prev, vertex: he.vertex, edge: val, face: he.face });
}

fn set_he_face(half_edges: &mut Vec<HalfEdge>, idx: usize, val: usize)
    requires
        0 <= idx < old(half_edges).len(),
    ensures
        half_edges.len() == old(half_edges).len(),
        half_edges@[idx as int] == he_with_face(old(half_edges)@[idx as int], val),
        forall|i: int| 0 <= i < half_edges.len() && i != idx as int
            ==> half_edges@[i] == old(half_edges)@[i],
{
    let he = half_edges[idx];
    half_edges.set(idx, HalfEdge { twin: he.twin, next: he.next, prev: he.prev, vertex: he.vertex, edge: he.edge, face: val });
}

// =============================================================================
// 5.1 split_edge — spec helpers
// =============================================================================

/// The half-edge on edge e (h0).
pub open spec fn se_h0(m: &Mesh, e: int) -> int {
    m.edge_half_edges@[e] as int
}

/// The twin of h0 (h1).
pub open spec fn se_h1(m: &Mesh, e: int) -> int {
    m.half_edges@[se_h0(m, e)].twin as int
}

/// Structural postcondition of split_edge_build: captures how the new mesh
/// relates to the old mesh for connectivity and other proofs.
pub open spec fn split_edge_post(old_m: &Mesh, new_m: &Mesh, e: int) -> bool {
    let h0 = se_h0(old_m, e);
    let h1 = se_h1(old_m, e);
    let hcnt = half_edge_count(old_m);
    let vcnt = vertex_count(old_m);
    // Counts
    &&& vertex_count(new_m) == vcnt + 1
    &&& edge_count(new_m) == edge_count(old_m) + 1
    &&& face_count(new_m) == face_count(old_m)
    &&& half_edge_count(new_m) == hcnt + 2
    // All old HE vertices preserved
    &&& forall|h: int| 0 <= h < hcnt
        ==> new_m.half_edges@[h].vertex == old_m.half_edges@[h].vertex
    // Old HE next preserved (except h0, h1)
    &&& forall|h: int| 0 <= h < hcnt && h != h0 && h != h1
        ==> new_m.half_edges@[h].next == old_m.half_edges@[h].next
    // h0 rewired: next -> hcnt (new HE h2)
    &&& new_m.half_edges@[h0].next as int == hcnt
    // h1 rewired: next -> hcnt+1 (new HE h3)
    &&& new_m.half_edges@[h1].next as int == hcnt + 1
    // New HE at hcnt (h2): vertex = v_new, next = old h0.next
    &&& new_m.half_edges@[hcnt].vertex as int == vcnt
    &&& new_m.half_edges@[hcnt].next == old_m.half_edges@[h0].next
    // New HE at hcnt+1 (h3): vertex = v_new, next = old h1.next
    &&& new_m.half_edges@[hcnt + 1].vertex as int == vcnt
    &&& new_m.half_edges@[hcnt + 1].next == old_m.half_edges@[h1].next
}

// =============================================================================
// 5.1 split_edge
// =============================================================================

/// Helper: perform the split_edge mutation and return the new mesh.
pub fn split_edge_build(mesh: Mesh, e: usize) -> (result_mesh: Mesh)
    requires
        index_bounds(&mesh),
        0 <= e < edge_count(&mesh) as int,
        vertex_count(&mesh) < usize::MAX - 1,
        edge_count(&mesh) < usize::MAX - 1,
        half_edge_count(&mesh) < usize::MAX - 2,
        // h0 != h1 (guaranteed by twin_faces_distinct in structurally_valid meshes)
        se_h0(&mesh, e as int) != se_h1(&mesh, e as int),
    ensures
        split_edge_post(&mesh, &result_mesh, e as int),
{
    let vcnt = mesh.vertex_half_edges.len();
    let ecnt = mesh.edge_half_edges.len();
    let hcnt = mesh.half_edges.len();

    let h0 = mesh.edge_half_edges[e];
    let h1 = mesh.half_edges[h0].twin;

    let v0 = mesh.half_edges[h0].vertex;
    let v1 = mesh.half_edges[h1].vertex;
    let f0 = mesh.half_edges[h0].face;
    let f1 = mesh.half_edges[h1].face;

    let old_h0_next = mesh.half_edges[h0].next;
    let old_h1_next = mesh.half_edges[h1].next;

    let v_new = vcnt;
    let e_new = ecnt;
    let h2 = hcnt;
    let h3 = hcnt + 1;

    let mut half_edges = mesh.half_edges;
    let ghost old_hes = half_edges@;

    set_he_next(&mut half_edges, h0, h2);
    set_he_next(&mut half_edges, h1, h3);
    set_he_prev(&mut half_edges, old_h0_next, h2);
    set_he_prev(&mut half_edges, old_h1_next, h3);

    half_edges.push(HalfEdge { twin: h1, next: old_h0_next, prev: h0, vertex: v_new, edge: e_new, face: f0 });
    half_edges.push(HalfEdge { twin: h0, next: old_h1_next, prev: h1, vertex: v_new, edge: e_new, face: f1 });

    set_he_twin(&mut half_edges, h0, h3);
    set_he_twin(&mut half_edges, h1, h2);

    proof {
        // Help Z3: vertex preserved for all old HEs
        assert forall|h: int| 0 <= h < hcnt as int
        implies half_edges@[h].vertex == old_hes[h].vertex
        by {}

        // Help Z3: next preserved for old HEs except h0, h1
        assert forall|h: int| 0 <= h < hcnt as int
            && h != h0 as int && h != h1 as int
        implies half_edges@[h].next == old_hes[h].next
        by {}
    }

    let mut vertex_half_edges = mesh.vertex_half_edges;
    vertex_half_edges.push(h2);

    let mut edge_half_edges = mesh.edge_half_edges;
    edge_half_edges.push(h2);

    Mesh {
        vertex_half_edges,
        edge_half_edges,
        face_half_edges: mesh.face_half_edges,
        half_edges,
    }
}

/// Insert new vertex on edge e. +1V, +1E, +2HE, 0F.
///
/// Before:
///   h0: v0 ---> v1   (face f0)
///   h1: v1 ---> v0   (face f1, twin of h0)
///
/// After:
///   h0: v0 ---> v_new (face f0)
///   h2: v_new ---> v1 (face f0, new HE)
///   h1: v1 ---> v_new (face f1)
///   h3: v_new ---> v0 (face f1, new HE)
pub fn split_edge(mesh: Mesh, e: usize) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
        0 <= e < edge_count(&mesh) as int,
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
        result is Ok ==> split_edge_post(&mesh, &result->Ok_0, e as int),
{
    let vcnt = mesh.vertex_half_edges.len();
    let ecnt = mesh.edge_half_edges.len();
    let hcnt = mesh.half_edges.len();

    if vcnt >= usize::MAX - 1 || ecnt >= usize::MAX - 1 || hcnt >= usize::MAX - 2 {
        return Err(EulerError::Overflow);
    }

    // Check h0 != h1 (self-twin is degenerate)
    let h0_check = mesh.edge_half_edges[e];
    let h1_check = mesh.half_edges[h0_check].twin;
    if h0_check == h1_check {
        return Err(EulerError::WouldCreateDegeneracy);
    }

    let result_mesh = split_edge_build(mesh, e);

    if check_structurally_valid(&result_mesh) {
        Ok(result_mesh)
    } else {
        Err(EulerError::ValidationFailed)
    }
}

// =============================================================================
// 5.2 split_face — spec helpers
// =============================================================================

/// Structural postcondition of split_face_build: captures how the new mesh
/// relates to the old mesh for connectivity proofs.
pub open spec fn split_face_post(old_m: &Mesh, new_m: &Mesh, h_start: int, h_end: int) -> bool {
    let hcnt = half_edge_count(old_m);
    let prev_s = old_m.half_edges@[h_start].prev as int;
    let prev_e = old_m.half_edges@[h_end].prev as int;
    let v_start = old_m.half_edges@[h_start].vertex as int;
    let v_end = old_m.half_edges@[h_end].vertex as int;
    // Counts
    &&& vertex_count(new_m) == vertex_count(old_m)
    &&& half_edge_count(new_m) == hcnt + 2
    // All old HE vertices preserved
    &&& forall|h: int| 0 <= h < hcnt
        ==> new_m.half_edges@[h].vertex == old_m.half_edges@[h].vertex
    // Next preserved (except prev_of_h_start and prev_of_h_end)
    &&& forall|h: int| 0 <= h < hcnt && h != prev_s && h != prev_e
        ==> new_m.half_edges@[h].next == old_m.half_edges@[h].next
    // prev_of_h_start.next -> hcnt, vertex(hcnt) = v_start
    &&& new_m.half_edges@[prev_s].next as int == hcnt
    &&& new_m.half_edges@[hcnt].vertex as int == v_start
    // prev_of_h_end.next -> hcnt+1, vertex(hcnt+1) = v_end
    &&& new_m.half_edges@[prev_e].next as int == hcnt + 1
    &&& new_m.half_edges@[hcnt + 1].vertex as int == v_end
}

// =============================================================================
// 5.2 split_face
// =============================================================================

/// Helper: perform the split_face mutation and return the new mesh.
pub fn split_face_build(mesh: Mesh, h_start: usize, h_end: usize) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
        0 <= h_start < half_edge_count(&mesh) as int,
        0 <= h_end < half_edge_count(&mesh) as int,
        edge_count(&mesh) < usize::MAX - 1,
        face_count(&mesh) < usize::MAX - 1,
        half_edge_count(&mesh) < usize::MAX - 2,
        // prev_of_h_start != prev_of_h_end (guaranteed by prev_next + h_start != h_end)
        mesh.half_edges@[h_start as int].prev as int
            != mesh.half_edges@[h_end as int].prev as int,
    ensures
        result is Ok ==> vertex_count(&result->Ok_0) == vertex_count(&mesh),
        result is Ok ==> edge_count(&result->Ok_0) == edge_count(&mesh) + 1,
        result is Ok ==> face_count(&result->Ok_0) == face_count(&mesh) + 1,
        result is Ok ==> split_face_post(&mesh, &result->Ok_0, h_start as int, h_end as int),
{
    let ecnt = mesh.edge_half_edges.len();
    let fcnt = mesh.face_half_edges.len();
    let hcnt = mesh.half_edges.len();

    let f_old = mesh.half_edges[h_start].face;
    if mesh.half_edges[h_end].face != f_old {
        return Err(EulerError::InvalidIndex);
    }
    if mesh.half_edges[h_start].next == h_end || mesh.half_edges[h_end].next == h_start {
        return Err(EulerError::WouldCreateDegeneracy);
    }
    if h_start == h_end {
        return Err(EulerError::WouldCreateDegeneracy);
    }

    let v_start = mesh.half_edges[h_start].vertex;
    let v_end = mesh.half_edges[h_end].vertex;

    let e_new = ecnt;
    let f_new = fcnt;
    let h_new_a = hcnt;
    let h_new_b = hcnt + 1;

    let prev_of_h_start = mesh.half_edges[h_start].prev;
    let prev_of_h_end = mesh.half_edges[h_end].prev;

    let mut half_edges = mesh.half_edges;
    let ghost old_hes = half_edges@;

    half_edges.push(HalfEdge {
        twin: h_new_b,
        next: h_end,
        prev: prev_of_h_start,
        vertex: v_start,
        edge: e_new,
        face: f_old,
    });

    half_edges.push(HalfEdge {
        twin: h_new_a,
        next: h_start,
        prev: prev_of_h_end,
        vertex: v_end,
        edge: e_new,
        face: f_new,
    });

    set_he_next(&mut half_edges, prev_of_h_start, h_new_a);
    set_he_prev(&mut half_edges, h_end, h_new_a);
    set_he_next(&mut half_edges, prev_of_h_end, h_new_b);
    set_he_prev(&mut half_edges, h_start, h_new_b);

    {
        let new_hcnt = hcnt + 2;
        let mut cur = h_start;
        let mut steps: usize = 0;

        proof {
            assert forall|h: int| 0 <= h < hcnt as int
            implies half_edges@[h].vertex == old_hes[h].vertex
            by {}

            assert forall|h: int| 0 <= h < hcnt as int
                && h != prev_of_h_start as int && h != prev_of_h_end as int
            implies half_edges@[h].next == old_hes[h].next
            by {}

            assert(half_edges@[prev_of_h_start as int].next == h_new_a);
            assert(half_edges@[prev_of_h_end as int].next == h_new_b);
            assert(half_edges@[h_new_a as int].vertex == v_start);
            assert(half_edges@[h_new_b as int].vertex == v_end);
        }

        while cur != h_new_b && steps < new_hcnt
            invariant
                half_edges.len() == new_hcnt,
                0 <= cur < new_hcnt,
                steps <= new_hcnt,
                new_hcnt == hcnt + 2,
                h_new_a as int == hcnt as int,
                h_new_b as int == hcnt as int + 1,
                0 <= prev_of_h_start < hcnt,
                0 <= prev_of_h_end < hcnt,
                prev_of_h_start != prev_of_h_end,
                forall|h: int| 0 <= h < hcnt as int
                    ==> half_edges@[h].vertex == old_hes[h].vertex,
                forall|h: int| 0 <= h < hcnt as int
                    && h != prev_of_h_start as int && h != prev_of_h_end as int
                    ==> half_edges@[h].next == old_hes[h].next,
                half_edges@[prev_of_h_start as int].next == h_new_a,
                half_edges@[prev_of_h_end as int].next == h_new_b,
                half_edges@[h_new_a as int].vertex == v_start,
                half_edges@[h_new_b as int].vertex == v_end,
            decreases new_hcnt - steps,
        {
            set_he_face(&mut half_edges, cur, f_new);
            let nxt = half_edges[cur].next;
            if nxt >= new_hcnt {
                break;
            }
            cur = nxt;
            steps = steps + 1;
        }
    }

    let mut edge_half_edges = mesh.edge_half_edges;
    edge_half_edges.push(h_new_a);

    let mut face_half_edges = mesh.face_half_edges;
    face_half_edges.set(f_old, h_new_a);
    face_half_edges.push(h_new_b);

    Ok(Mesh {
        vertex_half_edges: mesh.vertex_half_edges,
        edge_half_edges,
        face_half_edges,
        half_edges,
    })
}

/// Add edge between two non-adjacent vertices on a face boundary.
/// 0V, +1E, +1F, +2HE.
pub fn split_face(mesh: Mesh, h_start: usize, h_end: usize) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
        0 <= h_start < half_edge_count(&mesh) as int,
        0 <= h_end < half_edge_count(&mesh) as int,
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
        result is Ok ==> split_face_post(&mesh, &result->Ok_0, h_start as int, h_end as int),
{
    let ecnt = mesh.edge_half_edges.len();
    let fcnt = mesh.face_half_edges.len();
    let hcnt = mesh.half_edges.len();

    if ecnt >= usize::MAX - 1 || fcnt >= usize::MAX - 1 || hcnt >= usize::MAX - 2 {
        return Err(EulerError::Overflow);
    }

    // Check prev_of_h_start != prev_of_h_end
    if mesh.half_edges[h_start].prev == mesh.half_edges[h_end].prev {
        return Err(EulerError::WouldCreateDegeneracy);
    }

    match split_face_build(mesh, h_start, h_end) {
        Ok(result_mesh) => {
            if check_structurally_valid(&result_mesh) {
                Ok(result_mesh)
            } else {
                Err(EulerError::ValidationFailed)
            }
        }
        Err(err) => Err(err),
    }
}

// =============================================================================
// 5.3 flip_edge
// =============================================================================

/// Rotate edge 90° within quad formed by two adjacent triangles. 0V, 0E, 0F.
///
/// Before:           After:
///     c                 c
///    / \               /|\
///   /   \             / | \
///  d--h0->b          d  |  b
///   \   /             \ | /
///    \ /               \|/
///     a                 a
///
/// Helper: perform the flip_edge mutation and return the new mesh.
fn flip_edge_build(mesh: Mesh, e: usize) -> (result_mesh: Mesh)
    requires
        index_bounds(&mesh),
        0 <= e < edge_count(&mesh) as int,
    ensures
        vertex_count(&result_mesh) == vertex_count(&mesh),
        edge_count(&result_mesh) == edge_count(&mesh),
        face_count(&result_mesh) == face_count(&mesh),
{
    let h0 = mesh.edge_half_edges[e];
    let h1 = mesh.half_edges[h0].twin;

    let f0 = mesh.half_edges[h0].face;
    let f1 = mesh.half_edges[h1].face;

    let a = mesh.half_edges[h0].next;
    let b = mesh.half_edges[a].next;
    let c = mesh.half_edges[h1].next;
    let d = mesh.half_edges[c].next;

    let v_b = mesh.half_edges[b].vertex;
    let v_d = mesh.half_edges[d].vertex;
    let edge_idx = mesh.half_edges[h0].edge;

    let mut half_edges = mesh.half_edges;

    half_edges.set(h0, HalfEdge { twin: h1, next: b, prev: c, vertex: v_d, edge: edge_idx, face: f0 });
    half_edges.set(h1, HalfEdge { twin: h0, next: d, prev: a, vertex: v_b, edge: edge_idx, face: f1 });

    set_he_prev(&mut half_edges, b, h0);
    set_he_next(&mut half_edges, b, c);

    set_he_prev(&mut half_edges, c, b);
    set_he_next(&mut half_edges, c, h0);
    set_he_face(&mut half_edges, c, f0);

    set_he_prev(&mut half_edges, d, h1);
    set_he_next(&mut half_edges, d, a);

    set_he_prev(&mut half_edges, a, d);
    set_he_next(&mut half_edges, a, h1);
    set_he_face(&mut half_edges, a, f1);

    let mut face_half_edges = mesh.face_half_edges;
    face_half_edges.set(f0, h0);
    face_half_edges.set(f1, h1);

    let mut vertex_half_edges = mesh.vertex_half_edges;
    vertex_half_edges.set(v_d, h0);
    vertex_half_edges.set(v_b, h1);

    Mesh {
        vertex_half_edges,
        edge_half_edges: mesh.edge_half_edges,
        face_half_edges,
        half_edges,
    }
}

/// Rotate edge 90° within quad formed by two adjacent triangles. 0V, 0E, 0F.
pub fn flip_edge(mesh: Mesh, e: usize) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
        0 <= e < edge_count(&mesh) as int,
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
        result is Ok ==> vertex_count(&result->Ok_0) == vertex_count(&mesh),
        result is Ok ==> edge_count(&result->Ok_0) == edge_count(&mesh),
        result is Ok ==> face_count(&result->Ok_0) == face_count(&mesh),
{
    let h0 = mesh.edge_half_edges[e];
    let h1 = mesh.half_edges[h0].twin;
    let f0 = mesh.half_edges[h0].face;
    let f1 = mesh.half_edges[h1].face;
    let a = mesh.half_edges[h0].next;
    let b = mesh.half_edges[a].next;
    let c = mesh.half_edges[h1].next;
    let d = mesh.half_edges[c].next;

    if mesh.half_edges[b].next != h0 {
        return Err(EulerError::NotTriangleFace { face: f0 });
    }
    if mesh.half_edges[d].next != h1 {
        return Err(EulerError::NotTriangleFace { face: f1 });
    }

    let result_mesh = flip_edge_build(mesh, e);

    if check_structurally_valid(&result_mesh) {
        Ok(result_mesh)
    } else {
        Err(EulerError::ValidationFailed)
    }
}

// =============================================================================
// 5.4 collapse_edge
// =============================================================================

/// Helper: perform the collapse_edge mutation and return the mesh.
/// All validation and compaction logic; structural validity checked by caller.
#[verifier::exec_allows_no_decreases_clause]
fn collapse_edge_build(mesh: Mesh, e: usize) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
        0 <= e < edge_count(&mesh) as int,
{
    let vcnt = mesh.vertex_half_edges.len();
    let ecnt = mesh.edge_half_edges.len();
    let fcnt = mesh.face_half_edges.len();
    let hcnt = mesh.half_edges.len();

    if vcnt < 4 || ecnt < 4 || fcnt < 3 || hcnt < 8 {
        return Err(EulerError::WouldCreateDegeneracy);
    }

    let h0 = mesh.edge_half_edges[e];
    let h1 = mesh.half_edges[h0].twin;

    let v0 = mesh.half_edges[h0].vertex;
    let v1 = mesh.half_edges[h1].vertex;

    let f0 = mesh.half_edges[h0].face;
    let f1 = mesh.half_edges[h1].face;

    let a0 = mesh.half_edges[h0].next;
    let b0 = mesh.half_edges[a0].next;
    if mesh.half_edges[b0].next != h0 {
        return Err(EulerError::NotTriangleFace { face: f0 });
    }

    let a1 = mesh.half_edges[h1].next;
    let b1 = mesh.half_edges[a1].next;
    if mesh.half_edges[b1].next != h1 {
        return Err(EulerError::NotTriangleFace { face: f1 });
    }

    let e_a0 = mesh.half_edges[a0].edge;
    let e_a1 = mesh.half_edges[a1].edge;

    let old_vertex_half_edges = mesh.vertex_half_edges;
    let old_edge_half_edges = mesh.edge_half_edges;
    let old_face_half_edges = mesh.face_half_edges;

    let mut half_edges = mesh.half_edges;
    let ghost orig = half_edges@;

    let mut i: usize = 0;
    while i < hcnt
        invariant
            half_edges.len() == hcnt,
            0 <= i <= hcnt,
            forall|h: int| 0 <= h < hcnt ==> {
                &&& (#[trigger] half_edges@[h]).twin == orig[h].twin
                &&& half_edges@[h].edge == orig[h].edge
            },
    {
        if half_edges[i].vertex == v1 {
            set_he_vertex(&mut half_edges, i, v0);
        }
        i = i + 1;
    }

    let a0_twin = half_edges[a0].twin;
    let b0_twin = half_edges[b0].twin;
    set_he_twin(&mut half_edges, a0_twin, b0_twin);
    set_he_twin(&mut half_edges, b0_twin, a0_twin);

    let kept_edge_0 = half_edges[a0_twin].edge;
    set_he_edge(&mut half_edges, b0_twin, kept_edge_0);

    let a1_twin = half_edges[a1].twin;
    let b1_twin = half_edges[b1].twin;
    set_he_twin(&mut half_edges, a1_twin, b1_twin);
    set_he_twin(&mut half_edges, b1_twin, a1_twin);

    let kept_edge_1 = half_edges[a1_twin].edge;
    set_he_edge(&mut half_edges, b1_twin, kept_edge_1);

    let mut he_keep: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < hcnt
        invariant
            he_keep.len() == j,
            0 <= j <= hcnt,
    {
        he_keep.push(true);
        j = j + 1;
    }
    he_keep.set(h0, false);
    he_keep.set(h1, false);
    he_keep.set(a0, false);
    he_keep.set(b0, false);
    he_keep.set(a1, false);
    he_keep.set(b1, false);

    let new_hcnt = hcnt - 6;
    let mut he_old_to_new: Vec<usize> = Vec::new();
    let mut new_idx: usize = 0;
    let mut k: usize = 0;
    while k < hcnt
        invariant
            he_old_to_new.len() == k,
            he_keep.len() == hcnt,
            0 <= k <= hcnt,
            new_idx <= k,
    {
        if he_keep[k] {
            he_old_to_new.push(new_idx);
            new_idx = new_idx + 1;
        } else {
            he_old_to_new.push(usize::MAX);
        }
        k = k + 1;
    }

    let mut new_half_edges: Vec<HalfEdge> = Vec::new();
    let mut k2: usize = 0;
    while k2 < hcnt
        invariant
            half_edges.len() == hcnt,
            he_keep.len() == hcnt,
            he_old_to_new.len() == hcnt,
            0 <= k2 <= hcnt,
    {
        if he_keep[k2] {
            let he = half_edges[k2];
            if he.twin >= hcnt || he.next >= hcnt || he.prev >= hcnt {
                return Err(EulerError::ValidationFailed);
            }
            let new_twin = he_old_to_new[he.twin];
            let new_next = he_old_to_new[he.next];
            let new_prev = he_old_to_new[he.prev];
            let new_v = if he.vertex > v1 && v1 < he.vertex { he.vertex - 1 } else { he.vertex };
            let smaller_f = if f0 < f1 { f0 } else { f1 };
            let larger_f = if f0 < f1 { f1 } else { f0 };
            let new_f = if he.face > larger_f && he.face >= 2 {
                he.face - 2
            } else if he.face > smaller_f && he.face >= 1 {
                he.face - 1
            } else {
                he.face
            };
            let mut removed_edges: [usize; 3] = [e, e_a0, e_a1];
            if removed_edges[0] > removed_edges[1] {
                let tmp = removed_edges[0];
                removed_edges[0] = removed_edges[1];
                removed_edges[1] = tmp;
            }
            if removed_edges[1] > removed_edges[2] {
                let tmp = removed_edges[1];
                removed_edges[1] = removed_edges[2];
                removed_edges[2] = tmp;
            }
            if removed_edges[0] > removed_edges[1] {
                let tmp = removed_edges[0];
                removed_edges[0] = removed_edges[1];
                removed_edges[1] = tmp;
            }
            let new_e = if he.edge > removed_edges[2] && he.edge >= 3 {
                he.edge - 3
            } else if he.edge > removed_edges[1] && he.edge >= 2 {
                he.edge - 2
            } else if he.edge > removed_edges[0] && he.edge >= 1 {
                he.edge - 1
            } else {
                he.edge
            };

            new_half_edges.push(HalfEdge {
                twin: new_twin,
                next: new_next,
                prev: new_prev,
                vertex: new_v,
                edge: new_e,
                face: new_f,
            });
        }
        k2 = k2 + 1;
    }

    let new_vcnt = vcnt - 1;
    let mut new_vertex_half_edges: Vec<usize> = Vec::new();
    let mut vi: usize = 0;
    while vi < vcnt
        invariant
            old_vertex_half_edges.len() == vcnt,
            half_edges.len() == hcnt,
            he_keep.len() == hcnt,
            he_old_to_new.len() == hcnt,
            0 <= vi <= vcnt,
    {
        if vi != v1 {
            let old_he = old_vertex_half_edges[vi];
            if old_he >= hcnt {
                return Err(EulerError::ValidationFailed);
            }
            if he_keep[old_he] {
                new_vertex_half_edges.push(he_old_to_new[old_he]);
            } else {
                let remapped_v = new_vertex_half_edges.len();
                let mut found: usize = usize::MAX;
                let mut s: usize = 0;
                while s < hcnt
                    invariant
                        half_edges.len() == hcnt,
                        he_keep.len() == hcnt,
                        he_old_to_new.len() == hcnt,
                        0 <= s <= hcnt,
                {
                    if he_keep[s] && half_edges[s].vertex == vi {
                        found = he_old_to_new[s];
                        break;
                    }
                    s = s + 1;
                }
                if found == usize::MAX {
                    return Err(EulerError::WouldCreateDegeneracy);
                }
                new_vertex_half_edges.push(found);
            }
        }
        vi = vi + 1;
    }

    let mut new_edge_half_edges: Vec<usize> = Vec::new();
    let mut ei: usize = 0;
    while ei < ecnt
        invariant
            old_edge_half_edges.len() == ecnt,
            half_edges.len() == hcnt,
            he_keep.len() == hcnt,
            he_old_to_new.len() == hcnt,
            0 <= ei <= ecnt,
    {
        if ei != e && ei != e_a0 && ei != e_a1 {
            let old_he = old_edge_half_edges[ei];
            if old_he >= hcnt {
                return Err(EulerError::ValidationFailed);
            }
            if he_keep[old_he] {
                new_edge_half_edges.push(he_old_to_new[old_he]);
            } else {
                let tw = half_edges[old_he].twin;
                if tw >= hcnt {
                    return Err(EulerError::ValidationFailed);
                }
                if he_keep[tw] {
                    new_edge_half_edges.push(he_old_to_new[tw]);
                } else {
                    return Err(EulerError::WouldCreateDegeneracy);
                }
            }
        }
        ei = ei + 1;
    }

    let mut new_face_half_edges: Vec<usize> = Vec::new();
    let mut fi: usize = 0;
    while fi < fcnt
        invariant
            old_face_half_edges.len() == fcnt,
            he_keep.len() == hcnt,
            he_old_to_new.len() == hcnt,
            0 <= fi <= fcnt,
    {
        if fi != f0 && fi != f1 {
            let old_he = old_face_half_edges[fi];
            if old_he >= hcnt {
                return Err(EulerError::ValidationFailed);
            }
            if he_keep[old_he] {
                new_face_half_edges.push(he_old_to_new[old_he]);
            } else {
                return Err(EulerError::WouldCreateDegeneracy);
            }
        }
        fi = fi + 1;
    }

    Ok(Mesh {
        vertex_half_edges: new_vertex_half_edges,
        edge_half_edges: new_edge_half_edges,
        face_half_edges: new_face_half_edges,
        half_edges: new_half_edges,
    })
}

/// Merge two endpoints of edge e into one vertex.
/// For triangle-adjacent case: −1V, −3E, −2F, −6HE.
pub fn collapse_edge(mesh: Mesh, e: usize) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
        0 <= e < edge_count(&mesh) as int,
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
{
    match collapse_edge_build(mesh, e) {
        Ok(result_mesh) => {
            if check_structurally_valid(&result_mesh) {
                Ok(result_mesh)
            } else {
                Err(EulerError::ValidationFailed)
            }
        }
        Err(err) => Err(err),
    }
}

} // verus!
