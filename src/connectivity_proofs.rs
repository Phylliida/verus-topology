use vstd::prelude::*;
use crate::mesh::*;
use crate::invariants::*;
use crate::connectivity::*;
use crate::euler_ops::{se_h0, se_h1, split_edge_post, split_face_post};

verus! {

// =============================================================================
// 1. Single adjacency transfer: old adjacent → new reachable
// =============================================================================

/// If u→v is adjacent in old_m, then u and v are reachable in new_m.
proof fn lemma_old_adj_new_reachable(
    old_m: &Mesh, new_m: &Mesh, e: int, u: int, v: int,
)
    requires
        structurally_valid(old_m),
        split_edge_post(old_m, new_m, e),
        0 <= e < edge_count(old_m),
        adjacent_vertices(old_m, u, v),
    ensures
        vertices_reachable(new_m, u, v),
{
    let h0 = se_h0(old_m, e);
    let h1 = se_h1(old_m, e);
    let hcnt = half_edge_count(old_m);
    let vcnt = vertex_count(old_m);
    let v_new = vcnt;

    // Get witness h for adjacency u→v in old_m
    let hw = choose|h: int| 0 <= h < hcnt
        && old_m.half_edges@[h].vertex as int == u
        && old_m.half_edges@[old_m.half_edges@[h].next as int].vertex as int == v;

    // u and v are old vertices, hence < vertex_count(new_m) = vcnt + 1
    assert(0 <= u < vcnt);
    assert(0 <= v < vcnt);

    if hw != h0 && hw != h1 {
        // --- Case 1: witness is not h0 or h1 → adjacency preserved directly ---
        // vertex(hw) preserved, next(hw) preserved, vertex(next(hw)) preserved
        assert(0 <= hw < half_edge_count(new_m));
        assert(new_m.half_edges@[hw].vertex as int == u);
        let nxt = old_m.half_edges@[hw].next as int;
        assert(new_m.half_edges@[hw].next == old_m.half_edges@[hw].next);
        assert(0 <= nxt < hcnt);
        assert(new_m.half_edges@[nxt].vertex == old_m.half_edges@[nxt].vertex);
        assert(new_m.half_edges@[new_m.half_edges@[hw].next as int].vertex as int == v);
        // hw witnesses adjacent_vertices(new_m, u, v)
        assert(adjacent_vertices(new_m, u, v));

        // Build 2-vertex path
        lemma_trivial_path(new_m, u);
        lemma_extend_path(new_m, u, u, v);
    } else if hw == h0 {
        // --- Case 2: hw == h0, so u = v0, v = vertex(old_h0_next) ---
        // In new_m: h0 witnesses u → v_new, hcnt witnesses v_new → v

        // h0 witnesses u → v_new in new_m
        assert(0 <= h0 < half_edge_count(new_m));
        assert(new_m.half_edges@[h0].vertex as int == u);
        assert(new_m.half_edges@[h0].next as int == hcnt);
        assert(new_m.half_edges@[hcnt].vertex as int == v_new);
        assert(adjacent_vertices(new_m, u, v_new));

        // hcnt witnesses v_new → v in new_m
        assert(0 <= hcnt < half_edge_count(new_m));
        assert(new_m.half_edges@[hcnt].vertex as int == v_new);
        let old_h0_next = old_m.half_edges@[h0].next as int;
        assert(new_m.half_edges@[hcnt].next as int == old_h0_next);
        assert(0 <= old_h0_next < hcnt);
        assert(new_m.half_edges@[old_h0_next].vertex == old_m.half_edges@[old_h0_next].vertex);
        // vertex(old_h0_next) = v from the choose witness
        assert(old_m.half_edges@[old_h0_next].vertex as int == v);
        assert(new_m.half_edges@[new_m.half_edges@[hcnt as int].next as int].vertex as int == v);
        assert(adjacent_vertices(new_m, v_new, v));

        // Path: u → v_new → v
        assert(0 <= v_new < vertex_count(new_m));
        lemma_trivial_path(new_m, u);
        lemma_extend_path(new_m, u, u, v_new);
        lemma_extend_path(new_m, u, v_new, v);
    } else {
        // --- Case 3: hw == h1, so u = v1, v = vertex(old_h1_next) ---
        assert(hw == h1);

        // h1 witnesses u → v_new in new_m
        assert(0 <= h1 < half_edge_count(new_m));
        assert(new_m.half_edges@[h1].vertex as int == u);
        assert(new_m.half_edges@[h1].next as int == hcnt + 1);
        assert(new_m.half_edges@[hcnt + 1].vertex as int == v_new);
        assert(adjacent_vertices(new_m, u, v_new));

        // hcnt+1 witnesses v_new → v in new_m
        assert(0 <= hcnt + 1 < half_edge_count(new_m));
        assert(new_m.half_edges@[hcnt + 1].vertex as int == v_new);
        let old_h1_next = old_m.half_edges@[h1].next as int;
        assert(new_m.half_edges@[hcnt + 1].next as int == old_h1_next);
        assert(0 <= old_h1_next < hcnt);
        assert(new_m.half_edges@[old_h1_next].vertex == old_m.half_edges@[old_h1_next].vertex);
        assert(old_m.half_edges@[old_h1_next].vertex as int == v);
        assert(new_m.half_edges@[new_m.half_edges@[(hcnt + 1) as int].next as int].vertex as int == v);
        assert(adjacent_vertices(new_m, v_new, v));

        // Path: u → v_new → v
        assert(0 <= v_new < vertex_count(new_m));
        lemma_trivial_path(new_m, u);
        lemma_extend_path(new_m, u, u, v_new);
        lemma_extend_path(new_m, u, v_new, v);
    }
}

// =============================================================================
// 2. Path transfer: old path → endpoints reachable in new mesh
// =============================================================================

/// If path is a valid path in old_m, then its endpoints are reachable in new_m.
proof fn lemma_old_path_new_reachable(
    old_m: &Mesh, new_m: &Mesh, e: int, path: Seq<int>,
)
    requires
        structurally_valid(old_m),
        split_edge_post(old_m, new_m, e),
        0 <= e < edge_count(old_m),
        vertex_path(old_m, path),
    ensures
        vertices_reachable(new_m, path[0], path[path.len() - 1]),
    decreases path.len(),
{
    if path.len() <= 1 {
        // Single vertex: trivial self-path in new_m
        // path[0] < vertex_count(old_m) < vertex_count(new_m)
        assert(0 <= path[0] < vertex_count(new_m));
        lemma_trivial_path(new_m, path[0]);
    } else {
        let n = path.len();
        let prefix = path.subrange(0, n - 1);

        // Prove prefix is a valid path in old_m
        assert(prefix.len() >= 1);
        assert forall|i: int| 0 <= i < prefix.len()
        implies 0 <= #[trigger] prefix[i] < vertex_count(old_m)
        by { assert(prefix[i] == path[i]); }

        assert forall|i: int| 0 <= i < prefix.len() - 1
        implies adjacent_vertices(old_m, #[trigger] prefix[i], prefix[i + 1])
        by {
            assert(prefix[i] == path[i]);
            assert(prefix[i + 1] == path[i + 1]);
        }

        // Induction: prefix endpoints reachable in new_m
        lemma_old_path_new_reachable(old_m, new_m, e, prefix);
        // vertices_reachable(new_m, path[0], path[n-2])

        // Last step: path[n-2] → path[n-1] adjacent in old_m
        assert(adjacent_vertices(old_m, path[n - 2], path[n - 1]));
        lemma_old_adj_new_reachable(old_m, new_m, e, path[n - 2], path[n - 1]);
        // vertices_reachable(new_m, path[n-2], path[n-1])

        // Transitivity
        lemma_reachable_transitive(new_m, path[0], path[n - 2], path[n - 1]);
    }
}

// =============================================================================
// 3. New vertex reachability
// =============================================================================

/// v_new (= vertex_count(old_m)) is reachable from/to any old vertex.
proof fn lemma_vnew_reachable_from_old(
    old_m: &Mesh, new_m: &Mesh, e: int, v: int,
)
    requires
        structurally_valid(old_m),
        is_connected(old_m),
        split_edge_post(old_m, new_m, e),
        0 <= e < edge_count(old_m),
        0 <= v < vertex_count(old_m),
    ensures
        vertices_reachable(new_m, v, vertex_count(old_m)),
        vertices_reachable(new_m, vertex_count(old_m), v),
{
    let h0 = se_h0(old_m, e);
    let h1 = se_h1(old_m, e);
    let hcnt = half_edge_count(old_m);
    let vcnt = vertex_count(old_m);
    let v_new = vcnt;
    let v0 = old_m.half_edges@[h0].vertex as int;

    // --- Show v0 → v_new adjacent in new_m (via h0) ---
    assert(0 <= h0 < half_edge_count(new_m));
    assert(new_m.half_edges@[h0].vertex as int == v0);
    assert(new_m.half_edges@[h0].next as int == hcnt);
    assert(new_m.half_edges@[hcnt].vertex as int == v_new);
    assert(adjacent_vertices(new_m, v0, v_new));

    // --- Show v_new → v0 adjacent in new_m (via hcnt+1) ---
    // Need: vertex(old_h1_next) = v0 in old_m
    // From twin_involution at h0: twin(h1) = h0
    assert(shared_edge_orientation_consistency(old_m));
    assert(twin_involution(old_m));
    assert(old_m.half_edges@[old_m.half_edges@[h0 as int].twin as int].twin as int == h0);
    // So twin(h1) = h0, i.e., old_m.half_edges@[h1].twin == h0

    // From twin_endpoint_correspondence at h1:
    // half_edge_to_vertex(old_m, h1) = half_edge_from_vertex(old_m, h0) = v0
    // i.e., vertex(next(h1)) = vertex(h0) = v0
    assert(twin_endpoint_correspondence(old_m));
    assert(twin_endpoint_correspondence_at(old_m, h1));
    let old_h1_next = old_m.half_edges@[h1].next as int;
    assert(old_m.half_edges@[old_h1_next].vertex as int == v0);

    // In new_m: vertex(old_h1_next) preserved
    assert(0 <= old_h1_next < hcnt);
    assert(new_m.half_edges@[old_h1_next].vertex == old_m.half_edges@[old_h1_next].vertex);

    // hcnt+1 witnesses v_new → v0
    assert(0 <= hcnt + 1 < half_edge_count(new_m));
    assert(new_m.half_edges@[hcnt + 1].vertex as int == v_new);
    assert(new_m.half_edges@[hcnt + 1].next as int == old_h1_next);
    assert(new_m.half_edges@[new_m.half_edges@[(hcnt + 1) as int].next as int].vertex as int == v0);
    assert(adjacent_vertices(new_m, v_new, v0));

    // --- v → v_new: transfer old path v→v0, then extend with v0→v_new ---
    assert(vertices_reachable(old_m, v, v0));
    let path_v_v0 = choose|p: Seq<int>| vertex_path(old_m, p) && p[0] == v && p[p.len() - 1] == v0;
    lemma_old_path_new_reachable(old_m, new_m, e, path_v_v0);
    // vertices_reachable(new_m, v, v0)

    assert(0 <= v0 < vertex_count(new_m));
    assert(0 <= v_new < vertex_count(new_m));
    lemma_trivial_path(new_m, v0);
    lemma_extend_path(new_m, v0, v0, v_new);
    // vertices_reachable(new_m, v0, v_new)
    lemma_reachable_transitive(new_m, v, v0, v_new);

    // --- v_new → v: v_new → v0 adjacent, then transfer old path v0→v ---
    assert(vertices_reachable(old_m, v0, v));
    let path_v0_v = choose|p: Seq<int>| vertex_path(old_m, p) && p[0] == v0 && p[p.len() - 1] == v;
    lemma_old_path_new_reachable(old_m, new_m, e, path_v0_v);
    // vertices_reachable(new_m, v0, v)

    lemma_trivial_path(new_m, v_new);
    lemma_extend_path(new_m, v_new, v_new, v0);
    // vertices_reachable(new_m, v_new, v0)
    lemma_reachable_transitive(new_m, v_new, v0, v);
}

// =============================================================================
// 4. Master lemma: split_edge preserves connectivity
// =============================================================================

/// If old_m is structurally valid, connected, and new_m is the result of
/// split_edge_build (satisfying split_edge_post), then new_m is connected.
pub proof fn lemma_split_edge_preserves_connected(
    old_m: &Mesh, new_m: &Mesh, e: int,
)
    requires
        structurally_valid(old_m),
        is_connected(old_m),
        split_edge_post(old_m, new_m, e),
        0 <= e < edge_count(old_m),
        vertex_count(old_m) > 0,
    ensures
        is_connected(new_m),
{
    let vcnt = vertex_count(old_m);
    let v_new = vcnt;

    assert forall|u: int, v: int|
        0 <= u < vertex_count(new_m) && 0 <= v < vertex_count(new_m)
    implies vertices_reachable(new_m, u, v)
    by {
        if u < vcnt && v < vcnt {
            // Both old vertices: transfer old path
            assert(vertices_reachable(old_m, u, v));
            let path = choose|p: Seq<int>| vertex_path(old_m, p) && p[0] == u && p[p.len() - 1] == v;
            lemma_old_path_new_reachable(old_m, new_m, e, path);
        } else if u == v_new && v == v_new {
            lemma_trivial_path(new_m, v_new);
        } else if u == v_new {
            // v < vcnt (since v < vcnt+1 and v != v_new)
            lemma_vnew_reachable_from_old(old_m, new_m, e, v);
        } else {
            // u < vcnt, v == v_new
            lemma_vnew_reachable_from_old(old_m, new_m, e, u);
        }
    }
}

// =============================================================================
// 5. split_face adjacency preservation
// =============================================================================

/// If u→v is adjacent in old_m, then u→v is adjacent in new_m after split_face.
/// split_face only rewires next at prev_s and prev_e, but the destination vertex
/// is the same (v_start, v_end) thanks to prev_next_bidirectional.
proof fn lemma_split_face_adj_preserved(
    old_m: &Mesh, new_m: &Mesh, h_start: int, h_end: int, u: int, v: int,
)
    requires
        structurally_valid(old_m),
        split_face_post(old_m, new_m, h_start, h_end),
        0 <= h_start < half_edge_count(old_m),
        0 <= h_end < half_edge_count(old_m),
        adjacent_vertices(old_m, u, v),
    ensures
        adjacent_vertices(new_m, u, v),
{
    let hcnt = half_edge_count(old_m);
    let prev_s = old_m.half_edges@[h_start].prev as int;
    let prev_e = old_m.half_edges@[h_end].prev as int;
    let v_start = old_m.half_edges@[h_start].vertex as int;
    let v_end = old_m.half_edges@[h_end].vertex as int;

    // Get witness h for adjacency u→v in old_m
    let hw = choose|h: int| 0 <= h < hcnt
        && old_m.half_edges@[h].vertex as int == u
        && old_m.half_edges@[old_m.half_edges@[h].next as int].vertex as int == v;

    if hw != prev_s && hw != prev_e {
        // Case 1: next(hw) preserved directly
        assert(0 <= hw < half_edge_count(new_m));
        assert(new_m.half_edges@[hw].vertex == old_m.half_edges@[hw].vertex);
        assert(new_m.half_edges@[hw].next == old_m.half_edges@[hw].next);
        let nxt = old_m.half_edges@[hw].next as int;
        assert(0 <= nxt < hcnt);
        assert(new_m.half_edges@[nxt].vertex == old_m.half_edges@[nxt].vertex);
        assert(adjacent_vertices(new_m, u, v));
    } else if hw == prev_s {
        // Case 2: hw == prev_s
        // From prev_next_bidirectional: next(prev(h_start)) = h_start
        assert(prev_next_inverse_at(old_m, h_start));
        assert(old_m.half_edges@[prev_s].next as int == h_start);
        // So v = vertex(h_start) = v_start
        assert(v == v_start);

        // In new_m: vertex(prev_s) preserved, next(prev_s) = hcnt, vertex(hcnt) = v_start
        assert(0 <= prev_s < half_edge_count(new_m));
        assert(new_m.half_edges@[prev_s].vertex == old_m.half_edges@[prev_s].vertex);
        assert(new_m.half_edges@[prev_s].next as int == hcnt);
        assert(0 <= hcnt < half_edge_count(new_m));
        assert(new_m.half_edges@[hcnt].vertex as int == v_start);
        assert(adjacent_vertices(new_m, u, v));
    } else {
        // Case 3: hw == prev_e
        assert(hw == prev_e);
        assert(prev_next_inverse_at(old_m, h_end));
        assert(old_m.half_edges@[prev_e].next as int == h_end);
        assert(v == v_end);

        assert(0 <= prev_e < half_edge_count(new_m));
        assert(new_m.half_edges@[prev_e].vertex == old_m.half_edges@[prev_e].vertex);
        assert(new_m.half_edges@[prev_e].next as int == hcnt + 1);
        assert(0 <= hcnt + 1 < half_edge_count(new_m));
        assert(new_m.half_edges@[hcnt + 1].vertex as int == v_end);
        assert(adjacent_vertices(new_m, u, v));
    }
}

// =============================================================================
// 6. split_face path transfer
// =============================================================================

/// An old vertex path is directly valid in new_m (vertex count unchanged,
/// all adjacencies preserved).
proof fn lemma_split_face_path_valid(
    old_m: &Mesh, new_m: &Mesh, h_start: int, h_end: int, path: Seq<int>,
)
    requires
        structurally_valid(old_m),
        split_face_post(old_m, new_m, h_start, h_end),
        0 <= h_start < half_edge_count(old_m),
        0 <= h_end < half_edge_count(old_m),
        vertex_path(old_m, path),
    ensures
        vertex_path(new_m, path),
{
    // Vertices in bounds (vertex count unchanged)
    assert forall|i: int| 0 <= i < path.len()
    implies 0 <= #[trigger] path[i] < vertex_count(new_m)
    by {}

    // Consecutive pairs adjacent in new_m
    assert forall|i: int| 0 <= i < path.len() - 1
    implies adjacent_vertices(new_m, #[trigger] path[i], path[i + 1])
    by {
        assert(adjacent_vertices(old_m, path[i], path[i + 1]));
        lemma_split_face_adj_preserved(old_m, new_m, h_start, h_end, path[i], path[i + 1]);
    }
}

// =============================================================================
// 7. Master lemma: split_face preserves connectivity
// =============================================================================

/// If old_m is structurally valid, connected, and new_m is the result of
/// split_face (satisfying split_face_post), then new_m is connected.
pub proof fn lemma_split_face_preserves_connected(
    old_m: &Mesh, new_m: &Mesh, h_start: int, h_end: int,
)
    requires
        structurally_valid(old_m),
        is_connected(old_m),
        split_face_post(old_m, new_m, h_start, h_end),
        0 <= h_start < half_edge_count(old_m),
        0 <= h_end < half_edge_count(old_m),
        vertex_count(old_m) > 0,
    ensures
        is_connected(new_m),
{
    assert forall|u: int, v: int|
        0 <= u < vertex_count(new_m) && 0 <= v < vertex_count(new_m)
    implies vertices_reachable(new_m, u, v)
    by {
        // vertex count unchanged, so u and v are old vertices
        assert(vertices_reachable(old_m, u, v));
        let path = choose|p: Seq<int>| vertex_path(old_m, p) && p[0] == u && p[p.len() - 1] == v;
        lemma_split_face_path_valid(old_m, new_m, h_start, h_end, path);
    }
}

} // verus!
