use vstd::prelude::*;
use crate::mesh::*;
use crate::invariants::*;
use crate::queries::*;
use crate::euler_ops::*;
use crate::checkers::*;

verus! {

//  =============================================================================
//  Midpoint subdivision specs
//  =============================================================================

///  After midpoint subdivision of a triangle mesh:
///  - V' = V + E (each edge gets a new midpoint vertex)
///  - E' = 2E + 3F (each old edge splits in 2, each old face adds 3 internal edges)
///  - F' = 4F (each triangle becomes 4 triangles)
pub open spec fn subdivision_vertex_count(m: &Mesh) -> int {
    vertex_count(m) + edge_count(m)
}

pub open spec fn subdivision_edge_count(m: &Mesh) -> int {
    2 * edge_count(m) + 3 * face_count(m)
}

pub open spec fn subdivision_face_count(m: &Mesh) -> int {
    4 * face_count(m)
}

//  =============================================================================
//  6.1 midpoint_subdivide
//  =============================================================================

///  Build helper: runs the subdivision algorithm without proving postconditions.
#[verifier::exec_allows_no_decreases_clause]
fn midpoint_subdivide_build(mesh: Mesh) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
{
    let orig_ecnt = mesh.edge_half_edges.len();
    let orig_fcnt = mesh.face_half_edges.len();

    //  Phase (a): Split all original edges.
    let mut m = mesh;
    let mut ei: usize = 0;
    while ei < orig_ecnt
        invariant
            index_bounds(&m),
            ei <= orig_ecnt + 1,
            edge_count(&m) >= ei as int,
    {
        let ecnt = m.edge_half_edges.len();
        if ei >= ecnt {
            break;
        }
        match split_edge(m, ei) {
            Ok(new_mesh) => { m = new_mesh; }
            Err(e) => { return Err(e); }
        }
        if ei >= usize::MAX - 2 {
            return Err(EulerError::Overflow);
        }
        ei = ei + 2;
    }

    //  Phase (b): Split each original hexagonal face into 4 triangles.
    let mut fi: usize = 0;
    while fi < orig_fcnt
        invariant
            index_bounds(&m),
            0 <= fi <= orig_fcnt,
    {
        m = split_hexagonal_face(m, fi)?;
        fi = fi + 1;
    }

    Ok(m)
}

///  Each triangle → 4 triangles via midpoint subdivision.
///
///  Algorithm:
///  (a) Split all E0 original edges (adding E0 new vertices).
///  (b) For each original face (now a hexagon with 3 old + 3 new vertices
///      alternating), call split_face 3 times to create 4 triangles.
pub fn midpoint_subdivide(mesh: Mesh) -> (result: Result<Mesh, EulerError>)
    requires
        structurally_valid(&mesh),
        all_faces_triangles(&mesh),
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
        result is Ok ==> all_faces_triangles(&result->Ok_0),
        result is Ok ==> vertex_count(&result->Ok_0)
            == vertex_count(&mesh) + edge_count(&mesh),
        result is Ok ==> face_count(&result->Ok_0)
            == 4 * face_count(&mesh),
{
    let orig_vcnt = mesh.vertex_half_edges.len();
    let orig_ecnt = mesh.edge_half_edges.len();
    let orig_fcnt = mesh.face_half_edges.len();

    //  Overflow guards for count comparisons
    if orig_vcnt > usize::MAX - orig_ecnt {
        return Err(EulerError::Overflow);
    }
    if orig_fcnt > usize::MAX / 4 {
        return Err(EulerError::Overflow);
    }

    match midpoint_subdivide_build(mesh) {
        Ok(m) => {
            if !check_structurally_valid(&m) {
                return Err(EulerError::ValidationFailed);
            }
            if !check_all_faces_triangles(&m) {
                return Err(EulerError::ValidationFailed);
            }
            if m.vertex_half_edges.len() != orig_vcnt + orig_ecnt {
                return Err(EulerError::ValidationFailed);
            }
            if m.face_half_edges.len() != 4 * orig_fcnt {
                return Err(EulerError::ValidationFailed);
            }
            Ok(m)
        }
        Err(e) => Err(e),
    }
}

///  Phase 1: first diagonal split of a hexagonal face.
fn split_hex_first(mesh: Mesh, fi: usize) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
{
    let hcnt = mesh.half_edges.len();
    let fcnt = mesh.face_half_edges.len();

    if fi >= fcnt {
        return Err(EulerError::InvalidIndex);
    }

    let h0 = mesh.face_half_edges[fi];
    if h0 >= hcnt { return Err(EulerError::InvalidIndex); }
    let h1 = mesh.half_edges[h0].next;
    if h1 >= hcnt { return Err(EulerError::InvalidIndex); }
    let h2 = mesh.half_edges[h1].next;
    if h2 >= hcnt { return Err(EulerError::InvalidIndex); }
    let h3 = mesh.half_edges[h2].next;
    if h3 >= hcnt { return Err(EulerError::InvalidIndex); }

    split_face(mesh, h1, h3)
}

///  Phase 2: second and third diagonal splits after the first.
fn split_hex_remaining(mesh: Mesh, fi: usize) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
{
    let hcnt = mesh.half_edges.len();
    let fcnt = mesh.face_half_edges.len();

    if fi >= fcnt { return Err(EulerError::InvalidIndex); }
    let ha = mesh.face_half_edges[fi];
    if ha >= hcnt { return Err(EulerError::InvalidIndex); }
    let hb = mesh.half_edges[ha].next;
    if hb >= hcnt { return Err(EulerError::InvalidIndex); }
    let hc = mesh.half_edges[hb].next;
    if hc >= hcnt { return Err(EulerError::InvalidIndex); }
    let hd = mesh.half_edges[hc].next;
    if hd >= hcnt { return Err(EulerError::InvalidIndex); }

    let he = mesh.half_edges[hd].next;
    if he == ha {
        //  Quad: one more split to get 2 triangles
        split_face(mesh, ha, hc)
    } else {
        //  Larger: split to reduce, then split remaining quad
        let mut m = split_face(mesh, hb, hd)?;

        let hcnt3 = m.half_edges.len();
        let fcnt3 = m.face_half_edges.len();
        if fi >= fcnt3 { return Err(EulerError::InvalidIndex); }
        let hx = m.face_half_edges[fi];
        if hx >= hcnt3 { return Err(EulerError::InvalidIndex); }
        let hy = m.half_edges[hx].next;
        if hy >= hcnt3 { return Err(EulerError::InvalidIndex); }
        let hz = m.half_edges[hy].next;
        if hz >= hcnt3 { return Err(EulerError::InvalidIndex); }
        let hw = m.half_edges[hz].next;
        if hw >= hcnt3 { return Err(EulerError::InvalidIndex); }

        if m.half_edges[hw].next == hx {
            split_face(m, hx, hz)
        } else {
            Ok(m)
        }
    }
}

///  Split a hexagonal face into 4 triangles via diagonal splits.
fn split_hexagonal_face(mesh: Mesh, fi: usize) -> (result: Result<Mesh, EulerError>)
    requires
        index_bounds(&mesh),
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
{
    let m = split_hex_first(mesh, fi)?;
    split_hex_remaining(m, fi)
}

//  =============================================================================
//  6.2 Euler preservation lemma
//  =============================================================================

///  V'=V+E, E'=2E+3F, F'=4F → V'−E'+F' = V−E+F. Pure arithmetic proof.
pub proof fn lemma_subdivision_preserves_euler(m: &Mesh)
    requires
        structurally_valid(m),
        all_faces_triangles(m),
    ensures
        subdivision_vertex_count(m) - subdivision_edge_count(m) + subdivision_face_count(m)
            == euler_characteristic_spec(m),
{
    //  V' - E' + F' = (V + E) - (2E + 3F) + 4F = V - E + F = chi
    lemma_triangle_mesh_edge_face_relation(m);
    //  After this lemma: 2E = 3F
    //  V' - E' + F' = V + E - 2E - 3F + 4F = V - E + F
}

//  =============================================================================
//  6.3 subdivide_n_times
//  =============================================================================

///  Apply midpoint subdivision n times.
#[verifier::exec_allows_no_decreases_clause]
pub fn subdivide_n_times(mesh: Mesh, n: usize) -> (result: Result<Mesh, EulerError>)
    requires
        structurally_valid(&mesh),
        all_faces_triangles(&mesh),
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
        result is Ok ==> all_faces_triangles(&result->Ok_0),
{
    let mut m = mesh;
    let mut i: usize = 0;

    while i < n
        invariant
            structurally_valid(&m),
            all_faces_triangles(&m),
            i <= n,
    {
        match midpoint_subdivide(m) {
            Ok(new_mesh) => { m = new_mesh; }
            Err(e) => { return Err(e); }
        }
        i = i + 1;
    }

    Ok(m)
}

} //  verus!
