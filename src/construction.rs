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

/// Post-Phase-D helper: verify edge properties.
/// Extracted to give Z3 a separate verification context.
#[verifier::exec_allows_no_decreases_clause]
fn verify_edge_properties(
    half_edges: &Vec<HalfEdge>,
    edge_half_edges: &Vec<usize>,
) -> (result: Result<(), MeshBuildError>)
    requires
        half_edges@.len() > 0,
        // All twins valid
        forall|k: int| 0 <= k < half_edges@.len() ==>
            ((#[trigger] half_edges@[k]).twin as int) < half_edges@.len(),
        // All edges valid
        forall|k: int| 0 <= k < half_edges@.len() ==>
            ((#[trigger] half_edges@[k]).edge as int) < edge_half_edges@.len(),
        // edge_half_edges valid
        forall|e: int| 0 <= e < edge_half_edges@.len() ==>
            (#[trigger] edge_half_edges@[e] as int) < half_edges@.len(),
    ensures
        result is Ok ==> {
            // Edge(h) == edge(twin(h)) for all h
            &&& forall|k: int| 0 <= k < half_edges@.len() ==>
                (#[trigger] half_edges@[k]).edge
                    == half_edges@[half_edges@[k].twin as int].edge
            // edge_half_edges[edge(h)] is h or twin(h)
            &&& forall|k: int| 0 <= k < half_edges@.len() ==> {
                let e = (#[trigger] half_edges@[k]).edge as int;
                let t = half_edges@[k].twin as int;
                (edge_half_edges@[e] as int == k || edge_half_edges@[e] as int == t)
            }
            // h != twin(h) for all h
            &&& forall|k: int| 0 <= k < half_edges@.len() ==>
                k != (#[trigger] half_edges@[k]).twin as int
            // edge(edge_half_edges[e]) == e for all e
            &&& forall|e: int| 0 <= e < edge_half_edges@.len() ==>
                (#[trigger] half_edges@[edge_half_edges@[e] as int]).edge as int == e
        },
{
    let hcnt = half_edges.len();
    let ecnt = edge_half_edges.len();

    // Check edge(edge_half_edges[e]) == e for all e
    let mut e_check: usize = 0;
    while e_check < ecnt
        invariant
            half_edges@.len() == hcnt,
            edge_half_edges@.len() == ecnt,
            0 <= e_check <= ecnt,
            forall|e: int| 0 <= e < ecnt as int ==>
                (#[trigger] edge_half_edges@[e] as int) < hcnt as int,
            forall|e: int| 0 <= e < e_check as int ==>
                (#[trigger] half_edges@[edge_half_edges@[e] as int]).edge as int == e,
    {
        let rep = edge_half_edges[e_check];
        if half_edges[rep].edge != e_check {
            return Err(MeshBuildError::Overflow);
        }
        e_check += 1;
    }

    let mut check: usize = 0;
    while check < hcnt
        invariant
            half_edges@.len() == hcnt,
            edge_half_edges@.len() == ecnt,
            0 <= check <= hcnt,
            forall|k: int| 0 <= k < hcnt as int ==>
                ((#[trigger] half_edges@[k]).twin as int) < (hcnt as int),
            forall|k: int| 0 <= k < hcnt as int ==>
                ((#[trigger] half_edges@[k]).edge as int) < ecnt as int,
            forall|e: int| 0 <= e < ecnt as int ==>
                (#[trigger] edge_half_edges@[e] as int) < hcnt as int,
            forall|k: int| 0 <= k < check as int ==>
                (#[trigger] half_edges@[k]).edge
                    == half_edges@[half_edges@[k].twin as int].edge,
            forall|k: int| 0 <= k < check as int ==> {
                let e = (#[trigger] half_edges@[k]).edge as int;
                let t = half_edges@[k].twin as int;
                (edge_half_edges@[e] as int == k || edge_half_edges@[e] as int == t)
            },
            forall|k: int| 0 <= k < check as int ==>
                k != (#[trigger] half_edges@[k]).twin as int,
    {
        let t = half_edges[check].twin;
        if half_edges[check].edge != half_edges[t].edge {
            return Err(MeshBuildError::Overflow);
        }
        let e = half_edges[check].edge;
        if edge_half_edges[e] != check && edge_half_edges[e] != t {
            return Err(MeshBuildError::Overflow);
        }
        if t == check {
            return Err(MeshBuildError::Overflow);
        }
        check += 1;
    }
    Ok(())
}

/// Prove edge_exactly_two_half_edges from verified edge properties.
proof fn lemma_edge_exactly_two_from_properties(mesh: &Mesh)
    requires
        // twin involution
        forall|h: int| 0 <= h < half_edge_count(mesh) ==>
            (#[trigger] mesh.half_edges@[mesh.half_edges@[h].twin as int].twin as int) == h,
        // All twins valid
        forall|h: int| 0 <= h < half_edge_count(mesh) ==>
            ((#[trigger] mesh.half_edges@[h]).twin as int) < half_edge_count(mesh),
        // edge(h) == edge(twin(h))
        forall|k: int| 0 <= k < half_edge_count(mesh) ==>
            (#[trigger] mesh.half_edges@[k]).edge
                == mesh.half_edges@[mesh.half_edges@[k].twin as int].edge,
        // edge_half_edges[edge(h)] is h or twin(h)
        forall|k: int| 0 <= k < half_edge_count(mesh) ==> {
            let e = (#[trigger] mesh.half_edges@[k]).edge as int;
            let t = mesh.half_edges@[k].twin as int;
            (mesh.edge_half_edges@[e] as int == k || mesh.edge_half_edges@[e] as int == t)
        },
        // h != twin(h)
        forall|k: int| 0 <= k < half_edge_count(mesh) ==>
            k != (#[trigger] mesh.half_edges@[k]).twin as int,
        // All edges valid
        forall|h: int| 0 <= h < half_edge_count(mesh) ==>
            ((#[trigger] mesh.half_edges@[h]).edge as int) < edge_count(mesh),
        // edge_half_edges valid
        forall|e: int| 0 <= e < edge_count(mesh) ==>
            (#[trigger] mesh.edge_half_edges@[e] as int) < half_edge_count(mesh),
        // edge(edge_half_edges[e]) == e
        forall|e: int| 0 <= e < edge_count(mesh) ==>
            (#[trigger] mesh.half_edges@[mesh.edge_half_edges@[e] as int]).edge as int == e,
    ensures
        edge_exactly_two_half_edges(mesh),
{
    assert forall|e: int| 0 <= e < edge_count(mesh) implies
        edge_exactly_two_half_edges_at(mesh, e)
    by {
        let h0 = mesh.edge_half_edges@[e] as int;
        let h1 = mesh.half_edges@[h0].twin as int;

        // h0 is in bounds and edge(h0) == e
        assert(0 <= h0 < half_edge_count(mesh));
        assert(mesh.half_edges@[h0].edge as int == e);

        // h1 is in bounds (twin valid)
        assert(0 <= h1 < half_edge_count(mesh));

        // edge(h1) == e (edge(twin(h0)) == edge(h0) == e)
        assert(mesh.half_edges@[h1].edge == mesh.half_edges@[h0].edge);

        // h0 != h1
        assert(h0 != h1);

        // twin(h0) == h1 (by definition)
        // twin(h1) == h0 (by twin involution)
        assert(mesh.half_edges@[h0].twin as int == h1);
        assert(mesh.half_edges@[h1].twin as int == h0);

        // edge_half_edges[e] is h0 (by definition)
        assert(mesh.edge_half_edges@[e] as int == h0);

        // For all h with edge(h) == e: h == h0 or h == h1
        // Uses: edge_half_edges[edge(h)] == h or twin(h)
        // edge(h) == e, so edge_half_edges[e] == h or twin(h)
        // edge_half_edges[e] == h0, so h == h0 or twin(h) == h0
        // If twin(h) == h0, then h == twin(twin(h)) == twin(h0) == h1
        assert forall|h: int|
            0 <= h < half_edge_count(mesh)
            && (#[trigger] mesh.half_edges@[h].edge as int) == e
        implies h == h0 || h == h1
        by {
            // edge_half_edges[edge(h)] == h or twin(h)
            // edge(h) == e, edge_half_edges[e] == h0
            // So h0 == h or h0 == twin(h)
            if mesh.edge_half_edges@[e] as int == h {
                // h == h0
            } else {
                // h0 == twin(h), so h == twin(h0) == h1
                assert(mesh.edge_half_edges@[e] as int == mesh.half_edges@[h].twin as int);
                assert(mesh.half_edges@[h].twin as int == h0);
                // twin(twin(h)) == h, twin(h) == h0, so twin(h0) == h
                // But twin(h0) == h1, so h == h1
            }
        }
    }
}

/// Phase D helper: create edges from twin pairs.
/// Extracted to give Z3 a separate verification context.
#[verifier::exec_allows_no_decreases_clause]
fn phase_d_create_edges(
    half_edges: &mut Vec<HalfEdge>,
) -> (result: Result<Vec<usize>, MeshBuildError>)
    requires
        old(half_edges)@.len() > 0,
        // All edges start as MAX (set by Phase B, preserved through Phase C)
        forall|k: int| 0 <= k < old(half_edges)@.len() ==>
            (#[trigger] old(half_edges)@[k]).edge == usize::MAX,
    ensures
        half_edges@.len() == old(half_edges)@.len(),
        // Frame: non-edge fields preserved
        forall|k: int| #![trigger half_edges@[k]]
            0 <= k < half_edges@.len() as int ==> {
                &&& half_edges@[k].next == old(half_edges)@[k].next
                &&& half_edges@[k].prev == old(half_edges)@[k].prev
                &&& half_edges@[k].vertex == old(half_edges)@[k].vertex
                &&& half_edges@[k].face == old(half_edges)@[k].face
                &&& half_edges@[k].twin == old(half_edges)@[k].twin
            },
        result is Ok ==> {
            // edge_half_edges entries are valid HE indices
            &&& forall|e: int| 0 <= e < result->Ok_0@.len() ==>
                (#[trigger] result->Ok_0@[e] as int) < half_edges@.len()
            // All HEs have edge assigned (not MAX)
            &&& forall|k: int| 0 <= k < half_edges@.len() as int ==>
                (#[trigger] half_edges@[k]).edge as int != usize::MAX as int
            // All assigned edges are valid edge indices
            &&& forall|k: int| 0 <= k < half_edges@.len() as int
                && (#[trigger] half_edges@[k]).edge as int != usize::MAX as int ==>
                (half_edges@[k].edge as int) < result->Ok_0@.len()
        },
{
    let hcnt = half_edges.len();
    let mut edge_half_edges: Vec<usize> = Vec::new();

    let mut h: usize = 0;
    while h < hcnt
        invariant
            half_edges@.len() == hcnt,
            hcnt as int == old(half_edges)@.len(),
            0 <= h <= hcnt,
            hcnt > 0,
            // Frame + edge validity combined
            forall|k: int| #![trigger half_edges@[k]]
                0 <= k < hcnt as int ==> {
                    &&& half_edges@[k].next == old(half_edges)@[k].next
                    &&& half_edges@[k].prev == old(half_edges)@[k].prev
                    &&& half_edges@[k].vertex == old(half_edges)@[k].vertex
                    &&& half_edges@[k].face == old(half_edges)@[k].face
                    &&& half_edges@[k].twin == old(half_edges)@[k].twin
                    &&& (half_edges@[k].edge as int != usize::MAX as int ==>
                        (half_edges@[k].edge as int) < edge_half_edges@.len())
                },
            // At most one edge created per iteration
            edge_half_edges@.len() <= h as int,
            // All HEs before h have edge assigned
            forall|k: int| 0 <= k < h as int ==>
                (#[trigger] half_edges@[k]).edge as int != usize::MAX as int,
            // edge_half_edges entries are valid HE indices
            forall|e: int| 0 <= e < edge_half_edges@.len() ==>
                (#[trigger] edge_half_edges@[e] as int) < hcnt as int,
    {
        if half_edges[h].edge == usize::MAX {
            let edge_idx = edge_half_edges.len();
            proof {
                // edge_idx <= h < hcnt, so edge_idx < usize::MAX
                assert(edge_idx as int <= h as int);
                assert((edge_idx as int) < hcnt as int);
                assert(edge_idx as int != usize::MAX as int);
            }
            edge_half_edges.push(h);

            let twin = half_edges[h].twin;

            // Update h's edge
            let twin_val = half_edges[h].twin;
            let next_val = half_edges[h].next;
            let prev_val = half_edges[h].prev;
            let vertex_val = half_edges[h].vertex;
            let face_val = half_edges[h].face;
            let ghost pre_set_h = half_edges@;
            half_edges.set(h, HalfEdge {
                twin: twin_val,
                next: next_val,
                prev: prev_val,
                vertex: vertex_val,
                edge: edge_idx,
                face: face_val,
            });
            proof {
                assert forall|k: int| #![trigger half_edges@[k]]
                    0 <= k < hcnt as int implies {
                        &&& half_edges@[k].next == old(half_edges)@[k].next
                        &&& half_edges@[k].prev == old(half_edges)@[k].prev
                        &&& half_edges@[k].vertex == old(half_edges)@[k].vertex
                        &&& half_edges@[k].face == old(half_edges)@[k].face
                        &&& half_edges@[k].twin == old(half_edges)@[k].twin
                        &&& (half_edges@[k].edge as int != usize::MAX as int ==>
                            (half_edges@[k].edge as int) < edge_half_edges@.len())
                    }
                by {
                    if k == h as int {
                    } else {
                        assert(half_edges@[k] == pre_set_h[k]);
                    }
                }
                // All k < h still have edge assigned (unchanged by set on h)
                assert forall|k: int| 0 <= k < h as int implies
                    (#[trigger] half_edges@[k]).edge as int != usize::MAX as int
                by {
                    assert(half_edges@[k] == pre_set_h[k]);
                }
            }

            // Update twin's edge
            if twin >= hcnt {
                return Err(MeshBuildError::Overflow);
            }
            let twin_twin_val = half_edges[twin].twin;
            let twin_next_val = half_edges[twin].next;
            let twin_prev_val = half_edges[twin].prev;
            let twin_vertex_val = half_edges[twin].vertex;
            let twin_face_val = half_edges[twin].face;
            let ghost pre_set_twin = half_edges@;
            half_edges.set(twin, HalfEdge {
                twin: twin_twin_val,
                next: twin_next_val,
                prev: twin_prev_val,
                vertex: twin_vertex_val,
                edge: edge_idx,
                face: twin_face_val,
            });
            proof {
                assert forall|k: int| #![trigger half_edges@[k]]
                    0 <= k < hcnt as int implies {
                        &&& half_edges@[k].next == old(half_edges)@[k].next
                        &&& half_edges@[k].prev == old(half_edges)@[k].prev
                        &&& half_edges@[k].vertex == old(half_edges)@[k].vertex
                        &&& half_edges@[k].face == old(half_edges)@[k].face
                        &&& half_edges@[k].twin == old(half_edges)@[k].twin
                        &&& (half_edges@[k].edge as int != usize::MAX as int ==>
                            (half_edges@[k].edge as int) < edge_half_edges@.len())
                    }
                by {
                    if k == twin as int {
                    } else {
                        assert(half_edges@[k] == pre_set_twin[k]);
                    }
                }
                // All k < h still have edge assigned
                assert forall|k: int| 0 <= k < h as int implies
                    (#[trigger] half_edges@[k]).edge as int != usize::MAX as int
                by {
                    if k == twin as int {
                        // twin was just assigned edge_idx != MAX
                    } else {
                        assert(half_edges@[k] == pre_set_twin[k]);
                    }
                }
                // h was assigned edge_idx by the first set, preserved by second set
                if h != twin {
                    assert(half_edges@[h as int] == pre_set_twin[h as int]);
                }
                assert(half_edges@[h as int].edge as int != usize::MAX as int);
            }
        }
        h += 1;
    }

    proof {
        // Help Z3 connect hcnt to old(half_edges)@.len()
        assert(half_edges@.len() == hcnt);
    }

    Ok(edge_half_edges)
}

/// Prove index_bounds from Phase B/C/D/E ghost state.
/// Extracted as separate proof to avoid rlimit in from_face_cycles.
proof fn lemma_index_bounds_from_construction(
    mesh: &Mesh,
    post_phase_b: Seq<HalfEdge>,
    pre_phase_d: Seq<HalfEdge>,
)
    requires
        half_edge_count(mesh) > 0,
        post_phase_b.len() == half_edge_count(mesh),
        pre_phase_d.len() == half_edge_count(mesh),
        // Phase D frame: mesh fields == pre_phase_d (non-edge)
        forall|k: int| #![trigger mesh.half_edges@[k]]
            0 <= k < half_edge_count(mesh) ==> {
                &&& mesh.half_edges@[k].next == pre_phase_d[k].next
                &&& mesh.half_edges@[k].prev == pre_phase_d[k].prev
                &&& mesh.half_edges@[k].vertex == pre_phase_d[k].vertex
                &&& mesh.half_edges@[k].face == pre_phase_d[k].face
                &&& mesh.half_edges@[k].twin == pre_phase_d[k].twin
            },
        // Phase C frame: pre_phase_d non-twin fields == post_phase_b
        forall|k: int| #![trigger pre_phase_d[k]]
            0 <= k < half_edge_count(mesh) ==> {
                &&& pre_phase_d[k].next == post_phase_b[k].next
                &&& pre_phase_d[k].prev == post_phase_b[k].prev
                &&& pre_phase_d[k].vertex == post_phase_b[k].vertex
                &&& pre_phase_d[k].face == post_phase_b[k].face
            },
        // Phase B bounds on post_phase_b
        forall|h: int| #![trigger post_phase_b[h]]
            0 <= h < half_edge_count(mesh) ==> {
                &&& 0 <= post_phase_b[h].next as int
                &&& (post_phase_b[h].next as int) < half_edge_count(mesh)
                &&& 0 <= post_phase_b[h].prev as int
                &&& (post_phase_b[h].prev as int) < half_edge_count(mesh)
                &&& (post_phase_b[h].vertex as int) < vertex_count(mesh)
                &&& (post_phase_b[h].face as int) < face_count(mesh)
            },
        // Phase C twin bounds
        forall|k: int| 0 <= k < half_edge_count(mesh) ==>
            ((#[trigger] pre_phase_d[k]).twin as int) < half_edge_count(mesh),
        // Phase D: all edges assigned and valid
        forall|k: int| 0 <= k < half_edge_count(mesh) ==> {
            &&& (#[trigger] mesh.half_edges@[k]).edge as int != usize::MAX as int
            &&& (mesh.half_edges@[k].edge as int) < edge_count(mesh)
        },
        // edge_half_edges valid
        forall|e: int| 0 <= e < edge_count(mesh) ==>
            (#[trigger] mesh.edge_half_edges@[e] as int) < half_edge_count(mesh),
        // face_half_edges valid
        forall|f: int| 0 <= f < face_count(mesh) ==>
            (#[trigger] mesh.face_half_edges@[f] as int) < half_edge_count(mesh),
        // vertex_half_edges valid
        forall|v: int| 0 <= v < vertex_count(mesh) ==>
            (#[trigger] mesh.vertex_half_edges@[v] as int) < half_edge_count(mesh),
    ensures
        index_bounds(mesh),
{
    // Prove HE field bounds
    assert forall|h: int| 0 <= h < half_edge_count(mesh) implies {
        let he = #[trigger] mesh.half_edges@[h];
        &&& (he.twin as int) < half_edge_count(mesh)
        &&& (he.next as int) < half_edge_count(mesh)
        &&& (he.prev as int) < half_edge_count(mesh)
        &&& (he.vertex as int) < vertex_count(mesh)
        &&& (he.edge as int) < edge_count(mesh)
        &&& (he.face as int) < face_count(mesh)
    }
    by {
        // Chain: mesh → pre_phase_d → post_phase_b
        let _ = pre_phase_d[h];
        let _ = post_phase_b[h];
    }
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
            // Bidirectional + vertex/face bounds + no degenerate for all existing HEs
            forall|h: int| #![trigger half_edges@[h]]
                0 <= h < half_edges@.len() ==> {
                    &&& 0 <= half_edges@[h].next as int
                    &&& (half_edges@[h].next as int) < half_edges@.len()
                    &&& 0 <= half_edges@[h].prev as int
                    &&& (half_edges@[h].prev as int) < half_edges@.len()
                    &&& half_edges@[half_edges@[h].next as int].prev as int == h
                    &&& half_edges@[half_edges@[h].prev as int].next as int == h
                    // vertex in bounds and consecutive vertices distinct
                    &&& (half_edges@[h].vertex as int) < vertex_count as int
                    &&& half_edges@[h].vertex != half_edges@[half_edges@[h].next as int].vertex
                    // face in bounds
                    &&& (half_edges@[h].face as int) < f as int
                    // twin/edge set to MAX (will be filled by Phases C/D)
                    &&& half_edges@[h].twin == usize::MAX
                    &&& half_edges@[h].edge == usize::MAX
                },
            // face_half_edges entries point to valid HE indices
            forall|ff: int| 0 <= ff < f as int ==>
                (#[trigger] face_half_edges@[ff] as int) < half_edges@.len(),
            // HE count >= 3 * face count (each face has >= 3 HEs)
            half_edges@.len() >= 3 * f as int,
    {
        let cycle = vstd::slice::slice_index_get(face_cycles, f);
        let n = cycle.len();

        let start = half_edges.len();
        face_half_edges.push(start);

        // Re-check face size (already validated in Phase A, but needed by verifier)
        if n < 3 {
            return Err(MeshBuildError::FaceTooSmall { face: f, len: n });
        }

        let ghost pre_inner_hes = half_edges@;

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == cycle.len(),
                n >= 3,
                face_half_edges.len() == f + 1,
                half_edges@.len() == start as int + i as int,
                // Field values of created HEs
                forall|j: int| #![trigger half_edges@[start as int + j]]
                    0 <= j < i as int ==> {
                    &&& half_edges@[start as int + j].next as int
                        == start as int + (if j + 1 < n as int { j + 1 } else { 0 })
                    &&& half_edges@[start as int + j].prev as int
                        == start as int + (if j == 0 { n as int - 1 } else { j - 1 })
                    &&& half_edges@[start as int + j].vertex == cycle@[j]
                    &&& half_edges@[start as int + j].face == f
                    &&& half_edges@[start as int + j].twin == usize::MAX
                    &&& half_edges@[start as int + j].edge == usize::MAX
                    // vertex bounds
                    &&& (cycle@[j] as int) < vertex_count as int
                    // consecutive vertices distinct
                    &&& cycle@[j] != cycle@[if j + 1 < n as int { j + 1 } else { 0int }]
                },
                // Old HEs preserved
                pre_inner_hes.len() == start as int,
                forall|h: int| 0 <= h < start as int ==>
                    (#[trigger] half_edges@[h]) == pre_inner_hes[h],
        {
            let v = cycle[i];

            // Re-check vertex bounds (validated in Phase A, needed by verifier)
            if v >= vertex_count {
                return Err(MeshBuildError::VertexOutOfBounds { face: f, vertex: v, index: i });
            }

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

            let ghost old_hes = half_edges@;
            half_edges.push(HalfEdge {
                twin: usize::MAX,
                next,
                prev,
                vertex: v,
                edge: usize::MAX,
                face: f,
            });

            proof {
                // The pushed element is at index start + i
                let pushed_idx = start as int + i as int;
                assert(half_edges@[pushed_idx].next == next);
                assert(half_edges@[pushed_idx].prev == prev);
                assert(half_edges@[pushed_idx].vertex == v);
                assert(half_edges@[pushed_idx].face == f);
                assert(half_edges@[pushed_idx].twin == usize::MAX);
                assert(half_edges@[pushed_idx].edge == usize::MAX);

                // next matches the if-else in invariant
                assert(next as int == start as int + next_idx as int);
                assert(next as int == start as int
                    + (if i as int + 1 < n as int { i as int + 1 } else { 0int }));

                // prev matches the if-else in invariant
                assert(prev as int == start as int + prev_idx as int);
                assert(prev as int == start as int
                    + (if i as int == 0 { n as int - 1 } else { i as int - 1 }));

                // vertex bounds: v < vertex_count (from re-check)
                assert((cycle@[i as int] as int) < vertex_count as int);
                // vertex distinct: cycle[i] != cycle[next_idx] (from degenerate check)
                assert(cycle@[i as int] != cycle@[next_idx as int]);
                assert(cycle@[i as int] != cycle@[if i as int + 1 < n as int { i as int + 1 } else { 0int }]);

                // Push preserves old elements
                assert forall|j: int| #![trigger half_edges@[start as int + j]]
                    0 <= j < i as int implies
                    half_edges@[start as int + j] == old_hes[start as int + j]
                by {
                    assert(start as int + j < old_hes.len());
                }

                // Old HEs before start preserved
                assert forall|h: int| 0 <= h < start as int implies
                    (#[trigger] half_edges@[h]) == pre_inner_hes[h]
                by {
                    assert(h < old_hes.len());
                    assert(half_edges@[h] == old_hes[h]);
                    assert(old_hes[h] == pre_inner_hes[h]);
                }
            }

            i += 1;
        }

        // Prove bidirectional for all HEs [0, start + n)
        proof {
            let hlen = half_edges@.len();
            assert(hlen == start as int + n as int);

            assert forall|h: int| #![trigger half_edges@[h]]
                0 <= h < hlen implies {
                    &&& 0 <= half_edges@[h].next as int
                    &&& (half_edges@[h].next as int) < hlen
                    &&& 0 <= half_edges@[h].prev as int
                    &&& (half_edges@[h].prev as int) < hlen
                    &&& half_edges@[half_edges@[h].next as int].prev as int == h
                    &&& half_edges@[half_edges@[h].prev as int].next as int == h
                    &&& (half_edges@[h].vertex as int) < vertex_count as int
                    &&& half_edges@[h].vertex != half_edges@[half_edges@[h].next as int].vertex
                    &&& (half_edges@[h].face as int) < f as int + 1
                    &&& half_edges@[h].twin == usize::MAX
                    &&& half_edges@[h].edge == usize::MAX
                }
            by {
                if h < start as int {
                    // Old HE: unchanged from pre_inner_hes
                    assert(half_edges@[h] == pre_inner_hes[h]);
                    let nh = half_edges@[h].next as int;
                    let ph = half_edges@[h].prev as int;
                    assert(nh < start as int);
                    assert(ph < start as int);
                    assert(half_edges@[nh] == pre_inner_hes[nh]);
                    assert(half_edges@[ph] == pre_inner_hes[ph]);
                    assert(0 <= nh < hlen);
                    assert(0 <= ph < hlen);
                    assert(pre_inner_hes[nh].prev as int == h);
                    assert(half_edges@[nh].prev as int == h);
                    assert(pre_inner_hes[ph].next as int == h);
                    assert(half_edges@[ph].next as int == h);
                    // vertex/face bounds preserved from old invariant
                    // (face < f < f+1)
                    assert((half_edges@[h].vertex as int) < vertex_count as int);
                    assert((half_edges@[h].face as int) < f as int);
                    // vertex distinct: next is also < start, so unchanged
                    assert(half_edges@[h].vertex != half_edges@[nh].vertex);
                } else {
                    // New HE in current face block
                    let j = h - start as int;
                    assert(0 <= j < n as int);
                    // Trigger inner loop's quantifier: half_edges@[start + j]
                    assert(h == start as int + j);
                    let _ = half_edges@[start as int + j];

                    // next and prev from inner loop invariant
                    let nj = if j + 1 < n as int { j + 1 } else { 0int };
                    let pj = if j == 0 { n as int - 1 } else { j - 1 };

                    assert(half_edges@[start as int + j].next as int
                        == start as int + (if j + 1 < n as int { j + 1 } else { 0int }));
                    assert(half_edges@[start as int + j].prev as int
                        == start as int + (if j == 0 { n as int - 1 } else { j - 1 }));
                    assert(half_edges@[h].next as int == start as int + nj);
                    assert(half_edges@[h].prev as int == start as int + pj);

                    // Both in bounds
                    assert(0 <= start as int + nj < hlen);
                    assert(0 <= start as int + pj < hlen);

                    // Verify next(prev(h)) == h:
                    // prev(h) = start + pj, need next(start + pj) == h
                    let prev_h = start as int + pj;
                    // What is next(start + pj)?
                    // next(start + pj) = start + (if pj+1 < n { pj+1 } else { 0 })
                    if j == 0 {
                        // pj = n-1
                        // next(start + n-1) = start + (if n-1+1 < n { n } else { 0 })
                        //                   = start + 0 = start = start + j = h
                        assert(half_edges@[prev_h].next as int == start as int + 0);
                    } else {
                        // pj = j-1
                        // next(start + j-1) = start + (if j-1+1 < n { j } else { 0 })
                        //                   = start + j = h  (since j < n)
                        assert(half_edges@[prev_h].next as int == start as int + j);
                    }
                    assert(half_edges@[prev_h].next as int == h);

                    // Verify prev(next(h)) == h:
                    // next(h) = start + nj, need prev(start + nj) == h
                    let next_h = start as int + nj;
                    // prev(start + nj) = start + (if nj == 0 { n-1 } else { nj-1 })
                    if j + 1 < n as int {
                        // nj = j+1
                        // prev(start + j+1) = start + (if j+1 == 0 { n-1 } else { j })
                        //                   = start + j = h  (since j+1 > 0)
                        assert(half_edges@[next_h].prev as int == start as int + j);
                    } else {
                        // nj = 0, j = n-1
                        // prev(start + 0) = start + (n-1) = start + j = h
                        assert(half_edges@[next_h].prev as int == start as int + (n as int - 1));
                    }
                    assert(half_edges@[next_h].prev as int == h);

                    // vertex bounds: from inner loop invariant
                    assert((cycle@[j] as int) < vertex_count as int);
                    assert(half_edges@[h].vertex == cycle@[j]);
                    assert((half_edges@[h].vertex as int) < vertex_count as int);

                    // vertex distinct: cycle[j] != cycle[nj] from inner loop
                    assert(cycle@[j] != cycle@[if j + 1 < n as int { j + 1 } else { 0int }]);
                    assert(cycle@[j] != cycle@[nj]);
                    // next(h) is at start + nj, vertex(start+nj) = cycle[nj]
                    assert(half_edges@[start as int + nj].vertex == cycle@[nj]);
                    assert(half_edges@[h].vertex != half_edges@[half_edges@[h].next as int].vertex);

                    // face bounds: face == f, and f < f+1
                    assert(half_edges@[h].face == f);
                    assert((half_edges@[h].face as int) < f as int + 1);
                }
            }

            // face_half_edges entries valid: ff < f from entry, ff == f: start < start + n
            assert forall|ff: int| 0 <= ff < f as int + 1 implies
                (#[trigger] face_half_edges@[ff] as int) < half_edges@.len()
            by {
                if ff < f as int {
                    // entry invariant + half_edges only grew
                } else {
                    // ff == f: face_half_edges[f] = start, half_edges.len() = start + n
                    assert(face_half_edges@[f as int] == start);
                }
            }
        }

        f += 1;
    }

    // Phase C: Match twins (O(H²) scan)
    let hcnt = half_edges.len();

    let ghost post_phase_b = half_edges@;

    let mut h: usize = 0;
    while h < hcnt
        invariant
            half_edges.len() == hcnt,
            0 <= h <= hcnt,
            post_phase_b.len() == hcnt as int,
            // Frame: next/prev/vertex/face/edge fields unchanged from Phase B
            forall|k: int| #![trigger half_edges@[k]]
                0 <= k < hcnt as int ==> {
                    &&& half_edges@[k].next == post_phase_b[k].next
                    &&& half_edges@[k].prev == post_phase_b[k].prev
                    &&& half_edges@[k].vertex == post_phase_b[k].vertex
                    &&& half_edges@[k].face == post_phase_b[k].face
                    &&& half_edges@[k].edge == post_phase_b[k].edge
                },
            // Phase B bidirectional: next/prev are valid indices
            forall|k: int| #![trigger post_phase_b[k]]
                0 <= k < hcnt as int ==> {
                    &&& 0 <= post_phase_b[k].next as int
                    &&& (post_phase_b[k].next as int) < hcnt as int
                    &&& 0 <= post_phase_b[k].prev as int
                    &&& (post_phase_b[k].prev as int) < hcnt as int
                },
            // Twin valid for processed HEs
            forall|k: int| 0 <= k < h as int ==>
                (((#[trigger] half_edges@[k]).twin) as int) < (hcnt as int),
            // Twin endpoint correspondence for processed HEs
            // from(twin(k)) == to(k): vertex(twin) == vertex(next)
            forall|k: int| 0 <= k < h as int ==> {
                let tw = (#[trigger] half_edges@[k]).twin as int;
                let nx = half_edges@[k].next as int;
                half_edges@[tw].vertex == half_edges@[nx].vertex
            },
            // to(twin(k)) == from(k): vertex(next(twin)) == vertex(k)
            forall|k: int| 0 <= k < h as int ==> {
                let tw = (#[trigger] half_edges@[k]).twin as int;
                let tw_nx = half_edges@[tw].next as int;
                half_edges@[tw_nx].vertex == half_edges@[k].vertex
            },
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
                twin_opt is Some ==> {
                    &&& (twin_opt->Some_0 as int) < hcnt as int
                    &&& half_edges@[twin_opt->Some_0 as int].vertex == to
                    &&& half_edges@[half_edges@[twin_opt->Some_0 as int].next as int].vertex == from
                },
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
                let ghost pre_set = half_edges@;
                half_edges.set(h, HalfEdge {
                    twin,
                    next: next_val,
                    prev: prev_val,
                    vertex: vertex_val,
                    edge: edge_val,
                    face: face_val,
                });
                proof {
                    // Frame preserved (including edge)
                    assert forall|k: int| #![trigger half_edges@[k]]
                        0 <= k < hcnt as int implies {
                            &&& half_edges@[k].next == post_phase_b[k].next
                            &&& half_edges@[k].prev == post_phase_b[k].prev
                            &&& half_edges@[k].vertex == post_phase_b[k].vertex
                            &&& half_edges@[k].face == post_phase_b[k].face
                            &&& half_edges@[k].edge == post_phase_b[k].edge
                        }
                    by {
                        if k == h as int {} // written back same values (edge_val == old edge)
                    }

                    // Twin valid: new h + preserved for k < h
                    assert forall|k: int| 0 <= k < h as int + 1 implies
                        (((#[trigger] half_edges@[k]).twin) as int) < (hcnt as int)
                    by {
                        if k == h as int {
                            assert(half_edges@[h as int].twin == twin);
                        }
                        // k < h: half_edges@[k] unchanged by set(h), entry invariant applies
                    }

                    // from(twin(k)) == to(k): vertex(twin) == vertex(next)
                    assert forall|k: int| 0 <= k < h as int + 1 implies {
                        let tw = (#[trigger] half_edges@[k]).twin as int;
                        let nx = half_edges@[k].next as int;
                        half_edges@[tw].vertex == half_edges@[nx].vertex
                    }
                    by {
                        if k == h as int {
                            assert(half_edges@[h as int].twin == twin);
                            assert(half_edges@[h as int].next == next_val);
                            assert(next_val == next_h);
                        }
                    }

                    // to(twin(k)) == from(k): vertex(next(twin)) == vertex(k)
                    assert forall|k: int| 0 <= k < h as int + 1 implies {
                        let tw = (#[trigger] half_edges@[k]).twin as int;
                        let tw_nx = half_edges@[tw].next as int;
                        half_edges@[tw_nx].vertex == half_edges@[k].vertex
                    }
                    by {
                        if k == h as int {
                            assert(half_edges@[h as int].twin == twin);
                            let twin_next = half_edges@[twin as int].next as int;
                            // vertex(next(twin)) == from == vertex(h)
                            assert(half_edges@[twin_next].vertex == from);
                            assert(from == vertex_val);
                            assert(half_edges@[h as int].vertex == vertex_val);
                        }
                    }
                }
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

    // Post-Phase-C: Verify twin involution
    let mut check: usize = 0;
    while check < hcnt
        invariant
            half_edges.len() == hcnt,
            0 <= check <= hcnt,
            // All twins are valid indices (from Phase C)
            forall|k: int| 0 <= k < hcnt as int ==>
                ((#[trigger] half_edges@[k]).twin as int) < (hcnt as int),
            // Twin involution for all checked so far
            forall|k: int| 0 <= k < check as int ==>
                (#[trigger] half_edges@[half_edges@[k].twin as int].twin as int) == k,
            // Twin faces distinct for all checked so far
            forall|k: int| 0 <= k < check as int ==>
                (#[trigger] half_edges@[k]).face
                    != half_edges@[half_edges@[k].twin as int].face,
            // Frame preserved (Phase C only changed twin field)
            forall|k: int| #![trigger half_edges@[k]]
                0 <= k < hcnt as int ==> {
                    &&& half_edges@[k].next == post_phase_b[k].next
                    &&& half_edges@[k].prev == post_phase_b[k].prev
                    &&& half_edges@[k].vertex == post_phase_b[k].vertex
                    &&& half_edges@[k].face == post_phase_b[k].face
                    &&& half_edges@[k].edge == post_phase_b[k].edge
                },
    {
        let t = half_edges[check].twin;
        if half_edges[t].twin != check {
            return Err(MeshBuildError::Overflow);
        }
        if half_edges[check].face == half_edges[t].face {
            return Err(MeshBuildError::Overflow);
        }
        check += 1;
    }

    // Phase D: Create edges (extracted to helper for Z3 partitioning)
    let ghost pre_phase_d = half_edges@;
    if hcnt == 0 {
        return Err(MeshBuildError::Overflow);
    }
    proof {
        // Establish all-edges-MAX precondition for Phase D
        // Phase B set all edge to MAX, Phase C preserved edge via frame
        assert forall|k: int| 0 <= k < half_edges@.len() implies
            (#[trigger] half_edges@[k]).edge == usize::MAX
        by {
            assert(half_edges@[k].edge == post_phase_b[k].edge);
        }
    }
    let edge_half_edges = match phase_d_create_edges(&mut half_edges) {
        Ok(ehs) => ehs,
        Err(e) => return Err(e),
    };

    // Post-Phase-D: Verify 2 * edge_count == half_edge_count
    let ecnt = edge_half_edges.len();
    if ecnt > usize::MAX / 2 {
        return Err(MeshBuildError::Overflow);
    }
    if 2 * ecnt != hcnt {
        return Err(MeshBuildError::Overflow);
    }

    // Post-Phase-D: Verify edge properties (extracted to helper for Z3)
    match verify_edge_properties(&half_edges, &edge_half_edges) {
        Ok(()) => {},
        Err(e) => return Err(e),
    }

    // Phase E: Vertex representatives + validate
    let mut vertex_half_edges: Vec<usize> = vec![usize::MAX; vertex_count];

    let mut h: usize = 0;
    while h < hcnt
        invariant
            half_edges.len() == hcnt,
            vertex_half_edges.len() == vertex_count,
            0 <= h <= hcnt,
            // vertex_half_edges entries: either MAX or valid HE index
            forall|vv: int| 0 <= vv < vertex_count as int ==>
                (#[trigger] vertex_half_edges@[vv]) == usize::MAX
                || (vertex_half_edges@[vv] as int) < hcnt as int,
    {
        let v = half_edges[h].vertex;
        if v < vertex_count && vertex_half_edges[v] == usize::MAX {
            vertex_half_edges.set(v, h);
            proof {
                assert forall|vv: int| 0 <= vv < vertex_count as int implies
                    (#[trigger] vertex_half_edges@[vv]) == usize::MAX
                    || (vertex_half_edges@[vv] as int) < hcnt as int
                by {
                    if vv == v as int {} // v was set to h < hcnt
                }
            }
        }
        h += 1;
    }

    // Check no isolated vertices
    let mut v: usize = 0;
    while v < vertex_count
        invariant
            vertex_half_edges.len() == vertex_count,
            0 <= v <= vertex_count,
            // All checked vertices have valid HE indices
            forall|vv: int| 0 <= vv < v as int ==>
                (#[trigger] vertex_half_edges@[vv] as int) < hcnt as int,
            // All entries: MAX or valid
            forall|vv: int| 0 <= vv < vertex_count as int ==>
                (#[trigger] vertex_half_edges@[vv]) == usize::MAX
                || (vertex_half_edges@[vv] as int) < hcnt as int,
            half_edges.len() == hcnt,
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

    proof {
        // Chain: mesh.half_edges == half_edges (moved into struct)
        // Phase D ensures: half_edges@[k].field == pre_phase_d[k].field (non-edge)
        // pre_phase_d was captured after Phase C, so pre_phase_d[k].next == post_phase_b[k].next etc.

        // Derive prev_next_bidirectional
        assert forall|h: int| #![trigger mesh.half_edges@[h]]
            0 <= h < half_edge_count(&mesh) implies
                next_prev_inverse_at(&mesh, h)
        by {
            // Chain: mesh → pre_phase_d → post_phase_b
            assert(mesh.half_edges@[h].next == pre_phase_d[h].next);
            assert(pre_phase_d[h].next == post_phase_b[h].next);
            assert(mesh.half_edges@[h].prev == pre_phase_d[h].prev);
            assert(pre_phase_d[h].prev == post_phase_b[h].prev);
            let nh = mesh.half_edges@[h].next as int;
            assert(mesh.half_edges@[nh].prev == pre_phase_d[nh].prev);
            assert(pre_phase_d[nh].prev == post_phase_b[nh].prev);
        }
        assert(next_prev_inverse_only(&mesh));

        assert forall|h: int| #![trigger mesh.half_edges@[h]]
            0 <= h < half_edge_count(&mesh) implies
                prev_next_inverse_at(&mesh, h)
        by {
            assert(mesh.half_edges@[h].next == pre_phase_d[h].next);
            assert(pre_phase_d[h].next == post_phase_b[h].next);
            assert(mesh.half_edges@[h].prev == pre_phase_d[h].prev);
            assert(pre_phase_d[h].prev == post_phase_b[h].prev);
            let ph = mesh.half_edges@[h].prev as int;
            assert(mesh.half_edges@[ph].next == pre_phase_d[ph].next);
            assert(pre_phase_d[ph].next == post_phase_b[ph].next);
        }
        assert(prev_next_inverse_only(&mesh));

        assert(prev_next_bidirectional(&mesh));

        // Derive no_degenerate_edges
        assert forall|h: int| #![trigger mesh.half_edges@[h]]
            0 <= h < half_edge_count(&mesh) implies {
                &&& (mesh.half_edges@[h].vertex as int)
                    != (mesh.half_edges@[mesh.half_edges@[h].twin as int].vertex as int)
                &&& (mesh.half_edges@[h].vertex as int)
                    != (mesh.half_edges@[mesh.half_edges@[h].next as int].vertex as int)
            }
        by {
            // vertex/next/twin all go through pre_phase_d to their Phase B/C values
            assert(mesh.half_edges@[h].vertex == pre_phase_d[h].vertex);
            assert(pre_phase_d[h].vertex == post_phase_b[h].vertex);
            assert(mesh.half_edges@[h].next == pre_phase_d[h].next);
            assert(pre_phase_d[h].next == post_phase_b[h].next);
            let nh = mesh.half_edges@[h].next as int;
            assert(mesh.half_edges@[nh].vertex == pre_phase_d[nh].vertex);
            assert(pre_phase_d[nh].vertex == post_phase_b[nh].vertex);
            // vertex(h) != vertex(next(h)) from Phase B
            // twin preserved through Phase D
            assert(mesh.half_edges@[h].twin == pre_phase_d[h].twin);
            let tw = mesh.half_edges@[h].twin as int;
            assert(mesh.half_edges@[tw].vertex == pre_phase_d[tw].vertex);
            assert(pre_phase_d[tw].vertex == post_phase_b[tw].vertex);
            // vertex(twin) from Phase C: pre_phase_d[tw].vertex == pre_phase_d[nh].vertex
        }
        assert(no_degenerate_edges(&mesh));

        // Derive twin_involution (from post-Phase-C check loop)
        assert forall|h: int| 0 <= h < half_edge_count(&mesh) implies
            (#[trigger] mesh.half_edges@[mesh.half_edges@[h].twin as int].twin as int) == h
        by {
            assert(mesh.half_edges@[h].twin == pre_phase_d[h].twin);
            let t = mesh.half_edges@[h].twin as int;
            assert(mesh.half_edges@[t].twin == pre_phase_d[t].twin);
        }
        assert(twin_involution(&mesh));

        // Derive twin_faces_distinct (from post-Phase-C check loop)
        assert forall|h: int| 0 <= h < half_edge_count(&mesh) implies
            #[trigger] twin_faces_distinct_at(&mesh, h)
        by {
            assert(mesh.half_edges@[h].twin == pre_phase_d[h].twin);
            assert(mesh.half_edges@[h].face == pre_phase_d[h].face);
            let t = mesh.half_edges@[h].twin as int;
            assert(mesh.half_edges@[t].face == pre_phase_d[t].face);
        }
        assert(twin_faces_distinct(&mesh));

        // Derive twin_endpoint_correspondence (from Phase C invariants)
        assert forall|h: int| 0 <= h < half_edge_count(&mesh) implies
            #[trigger] twin_endpoint_correspondence_at(&mesh, h)
        by {
            // Chain through pre_phase_d to get vertex/next/twin
            assert(mesh.half_edges@[h].twin == pre_phase_d[h].twin);
            assert(mesh.half_edges@[h].next == pre_phase_d[h].next);
            assert(pre_phase_d[h].next == post_phase_b[h].next);
            assert(mesh.half_edges@[h].vertex == pre_phase_d[h].vertex);
            assert(pre_phase_d[h].vertex == post_phase_b[h].vertex);
            let t = mesh.half_edges@[h].twin as int;
            assert(mesh.half_edges@[t].vertex == pre_phase_d[t].vertex);
            assert(pre_phase_d[t].vertex == post_phase_b[t].vertex);
            assert(mesh.half_edges@[t].next == pre_phase_d[t].next);
            assert(pre_phase_d[t].next == post_phase_b[t].next);
            let t_nx = mesh.half_edges@[t].next as int;
            assert(mesh.half_edges@[t_nx].vertex == pre_phase_d[t_nx].vertex);
            let h_nx = mesh.half_edges@[h].next as int;
            assert(mesh.half_edges@[h_nx].vertex == pre_phase_d[h_nx].vertex);
        }
        assert(twin_endpoint_correspondence(&mesh));

        assert(shared_edge_orientation_consistency(&mesh));

        // Derive index_bounds via helper lemma (avoids rlimit)
        lemma_index_bounds_from_construction(&mesh, post_phase_b, pre_phase_d);
        assert(index_bounds(&mesh));

        // Derive edge_exactly_two_half_edges
        lemma_edge_exactly_two_from_properties(&mesh);
        assert(edge_exactly_two_half_edges(&mesh));

        // Derive half_edge_edge_count_relation (from post-Phase-D counting check)
        assert(2 * edge_count(&mesh) == half_edge_count(&mesh));

        // Derive half_edge_face_count_lower_bound
        // Phase B invariant: half_edges.len() >= 3 * f, and f == face_cycles.len()
        assert(half_edge_count(&mesh) >= 3 * face_count(&mesh));
    }

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
