use vstd::prelude::*;
use crate::mesh::*;
use crate::invariants::*;
use crate::checkers::*;

verus! {

#[derive(Structural, PartialEq, Eq)]
pub enum MeshBuildError {
    EmptyVertexSet,
    EmptyFaceSet,
    FaceTooSmall { face: usize, len: usize },
    VertexOutOfBounds { face: usize, vertex: usize, index: usize },
    DegenerateOrientedEdge { face: usize, index: usize, vertex: usize },
    DuplicateOrientedEdge { from_v: usize, to_v: usize },
    MissingTwin { half_edge: usize, from_v: usize, to_v: usize },
    IsolatedVertex { vertex: usize },
    ValidationFailed,
    Overflow,
}

#[verifier::exec_allows_no_decreases_clause]
pub fn from_face_cycles(
    vertex_count: usize,
    face_cycles: &[Vec<usize>],
) -> (result: Result<Mesh, MeshBuildError>)
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
{
    // Phase A: Input validation
    if vertex_count == 0 {
        return Err(MeshBuildError::EmptyVertexSet);
    }
    if face_cycles.len() == 0 {
        return Err(MeshBuildError::EmptyFaceSet);
    }

    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            0 <= f <= face_cycles.len(),
    {
        let cycle = vstd::slice::slice_index_get(face_cycles, f);
        let n = cycle.len();
        if n < 3 {
            return Err(MeshBuildError::FaceTooSmall { face: f, len: n });
        }
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == cycle.len(),
        {
            let v = cycle[i];
            if v >= vertex_count {
                return Err(MeshBuildError::VertexOutOfBounds {
                    face: f,
                    vertex: v,
                    index: i,
                });
            }
            i += 1;
        }
        f += 1;
    }

    // Phase B: Create half-edges from face cycles
    let mut half_edges: Vec<HalfEdge> = Vec::new();
    let mut face_half_edges: Vec<usize> = Vec::with_capacity(face_cycles.len());

    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            0 <= f <= face_cycles.len(),
            face_half_edges.len() == f,
    {
        let cycle = vstd::slice::slice_index_get(face_cycles, f);
        let n = cycle.len();

        let start = half_edges.len();
        face_half_edges.push(start);

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == cycle.len(),
                face_half_edges.len() == f + 1,
        {
            let v = cycle[i];

            let i_plus_one = match i.checked_add(1) {
                Some(val) => val,
                None => return Err(MeshBuildError::Overflow),
            };
            let next_idx = if i_plus_one < n { i_plus_one } else { 0 };
            let to = cycle[next_idx];

            if v == to {
                return Err(MeshBuildError::DegenerateOrientedEdge {
                    face: f,
                    index: i,
                    vertex: v,
                });
            }

            let next = match start.checked_add(next_idx) {
                Some(val) => val,
                None => return Err(MeshBuildError::Overflow),
            };
            let prev_idx = if i == 0 { n - 1 } else { i - 1 };
            let prev = match start.checked_add(prev_idx) {
                Some(val) => val,
                None => return Err(MeshBuildError::Overflow),
            };

            half_edges.push(HalfEdge {
                twin: usize::MAX,
                next,
                prev,
                vertex: v,
                edge: usize::MAX,
                face: f,
            });
            i += 1;
        }

        f += 1;
    }

    // Phase C: Match twins (O(H²) scan)
    let hcnt = half_edges.len();

    let mut h: usize = 0;
    while h < hcnt
        invariant
            half_edges.len() == hcnt,
            0 <= h <= hcnt,
    {
        let from = half_edges[h].vertex;
        let next_h = half_edges[h].next;
        if next_h >= hcnt {
            return Err(MeshBuildError::Overflow);
        }
        let to = half_edges[next_h].vertex;

        let mut twin_opt: Option<usize> = None;
        let mut t: usize = 0;
        while t < hcnt
            invariant
                half_edges.len() == hcnt,
                0 <= t <= hcnt,
        {
            let t_next = half_edges[t].next;
            if t_next >= hcnt {
                return Err(MeshBuildError::Overflow);
            }
            let t_from = half_edges[t].vertex;
            let t_to = half_edges[t_next].vertex;
            if t_from == to && t_to == from {
                twin_opt = Some(t);
                break;
            }
            t += 1;
        }

        match twin_opt {
            Some(twin) => {
                let next_val = half_edges[h].next;
                let prev_val = half_edges[h].prev;
                let vertex_val = half_edges[h].vertex;
                let edge_val = half_edges[h].edge;
                let face_val = half_edges[h].face;
                half_edges.set(h, HalfEdge {
                    twin,
                    next: next_val,
                    prev: prev_val,
                    vertex: vertex_val,
                    edge: edge_val,
                    face: face_val,
                });
            }
            None => {
                return Err(MeshBuildError::MissingTwin {
                    half_edge: h,
                    from_v: from,
                    to_v: to,
                });
            }
        }

        h += 1;
    }

    // Phase D: Create edges
    let mut edge_half_edges: Vec<usize> = Vec::new();

    let mut h: usize = 0;
    while h < hcnt
        invariant
            half_edges.len() == hcnt,
            0 <= h <= hcnt,
    {
        if half_edges[h].edge == usize::MAX {
            let edge_idx = edge_half_edges.len();
            edge_half_edges.push(h);

            let twin = half_edges[h].twin;

            // Update h's edge
            let twin_val = half_edges[h].twin;
            let next_val = half_edges[h].next;
            let prev_val = half_edges[h].prev;
            let vertex_val = half_edges[h].vertex;
            let face_val = half_edges[h].face;
            half_edges.set(h, HalfEdge {
                twin: twin_val,
                next: next_val,
                prev: prev_val,
                vertex: vertex_val,
                edge: edge_idx,
                face: face_val,
            });

            // Update twin's edge
            if twin >= hcnt {
                return Err(MeshBuildError::Overflow);
            }
            let twin_twin_val = half_edges[twin].twin;
            let twin_next_val = half_edges[twin].next;
            let twin_prev_val = half_edges[twin].prev;
            let twin_vertex_val = half_edges[twin].vertex;
            let twin_face_val = half_edges[twin].face;
            half_edges.set(twin, HalfEdge {
                twin: twin_twin_val,
                next: twin_next_val,
                prev: twin_prev_val,
                vertex: twin_vertex_val,
                edge: edge_idx,
                face: twin_face_val,
            });
        }
        h += 1;
    }

    // Phase E: Vertex representatives + validate
    let mut vertex_half_edges: Vec<usize> = vec![usize::MAX; vertex_count];

    let mut h: usize = 0;
    while h < hcnt
        invariant
            half_edges.len() == hcnt,
            vertex_half_edges.len() == vertex_count,
            0 <= h <= hcnt,
    {
        let v = half_edges[h].vertex;
        if v < vertex_count && vertex_half_edges[v] == usize::MAX {
            vertex_half_edges.set(v, h);
        }
        h += 1;
    }

    // Check no isolated vertices
    let mut v: usize = 0;
    while v < vertex_count
        invariant
            vertex_half_edges.len() == vertex_count,
            0 <= v <= vertex_count,
    {
        if vertex_half_edges[v] == usize::MAX {
            return Err(MeshBuildError::IsolatedVertex { vertex: v });
        }
        v += 1;
    }

    // Assemble and validate
    let mesh = Mesh {
        vertex_half_edges,
        edge_half_edges,
        face_half_edges,
        half_edges,
    };

    if check_structurally_valid(&mesh) {
        Ok(mesh)
    } else {
        Err(MeshBuildError::ValidationFailed)
    }
}

// =============================================================================
// Reference constructors
// =============================================================================

pub fn tetrahedron() -> (result: Result<Mesh, MeshBuildError>)
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
{
    let f0: Vec<usize> = vec![0, 1, 2];
    let f1: Vec<usize> = vec![0, 3, 1];
    let f2: Vec<usize> = vec![1, 3, 2];
    let f3: Vec<usize> = vec![2, 3, 0];
    let faces: Vec<Vec<usize>> = vec![f0, f1, f2, f3];
    from_face_cycles(4, faces.as_slice())
}

pub fn cube() -> (result: Result<Mesh, MeshBuildError>)
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0),
{
    // Vertices: 0-7 for unit cube
    // Faces (outward-facing, CCW from outside):
    let f0: Vec<usize> = vec![0, 1, 2, 3]; // front
    let f1: Vec<usize> = vec![4, 7, 6, 5]; // back
    let f2: Vec<usize> = vec![0, 3, 7, 4]; // left
    let f3: Vec<usize> = vec![1, 5, 6, 2]; // right
    let f4: Vec<usize> = vec![0, 4, 5, 1]; // bottom
    let f5: Vec<usize> = vec![3, 2, 6, 7]; // top
    let faces: Vec<Vec<usize>> = vec![f0, f1, f2, f3, f4, f5];
    from_face_cycles(8, faces.as_slice())
}

} // verus!
