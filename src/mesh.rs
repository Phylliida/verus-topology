use vstd::prelude::*;

verus! {

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct HalfEdge {
    pub twin: usize,
    pub next: usize,
    pub prev: usize,
    pub vertex: usize,
    pub edge: usize,
    pub face: usize,
}

pub struct Mesh {
    pub vertex_half_edges: Vec<usize>,
    pub edge_half_edges: Vec<usize>,
    pub face_half_edges: Vec<usize>,
    pub half_edges: Vec<HalfEdge>,
}

pub open spec fn vertex_count(m: &Mesh) -> int {
    m.vertex_half_edges@.len() as int
}

pub open spec fn edge_count(m: &Mesh) -> int {
    m.edge_half_edges@.len() as int
}

pub open spec fn face_count(m: &Mesh) -> int {
    m.face_half_edges@.len() as int
}

pub open spec fn half_edge_count(m: &Mesh) -> int {
    m.half_edges@.len() as int
}

pub open spec fn index_bounds(m: &Mesh) -> bool {
    &&& forall|v: int|
        0 <= v < vertex_count(m)
            ==> (#[trigger] m.vertex_half_edges@[v] as int) < half_edge_count(m)
    &&& forall|e: int|
        0 <= e < edge_count(m)
            ==> (#[trigger] m.edge_half_edges@[e] as int) < half_edge_count(m)
    &&& forall|f: int|
        0 <= f < face_count(m)
            ==> (#[trigger] m.face_half_edges@[f] as int) < half_edge_count(m)
    &&& forall|h: int| 0 <= h < half_edge_count(m) ==> {
        let he = #[trigger] m.half_edges@[h];
        &&& (he.twin as int) < half_edge_count(m)
        &&& (he.next as int) < half_edge_count(m)
        &&& (he.prev as int) < half_edge_count(m)
        &&& (he.vertex as int) < vertex_count(m)
        &&& (he.edge as int) < edge_count(m)
        &&& (he.face as int) < face_count(m)
    }
}

} //  verus!
