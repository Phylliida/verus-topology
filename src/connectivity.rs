use vstd::prelude::*;
use crate::mesh::*;
use crate::invariants::*;

verus! {

// =============================================================================
// 1. Adjacency and path specs
// =============================================================================

/// Half-edge h witnesses directed edge u→v.
pub open spec fn adjacent_vertices(m: &Mesh, u: int, v: int) -> bool {
    exists|h: int| 0 <= h < half_edge_count(m)
        && m.half_edges@[h].vertex as int == u
        && m.half_edges@[m.half_edges@[h].next as int].vertex as int == v
}

/// Valid vertex path: vertices in bounds, consecutive pairs adjacent.
pub open spec fn vertex_path(m: &Mesh, path: Seq<int>) -> bool {
    &&& path.len() >= 1
    &&& forall|i: int| 0 <= i < path.len() ==> 0 <= #[trigger] path[i] < vertex_count(m)
    &&& forall|i: int| 0 <= i < path.len() - 1
        ==> adjacent_vertices(m, #[trigger] path[i], path[i + 1])
}

/// Exists a path from u to v.
pub open spec fn vertices_reachable(m: &Mesh, u: int, v: int) -> bool {
    exists|path: Seq<int>| vertex_path(m, path) && path[0] == u && path[path.len() - 1] == v
}

/// All vertex pairs are mutually reachable.
pub open spec fn is_connected(m: &Mesh) -> bool {
    forall|u: int, v: int| 0 <= u < vertex_count(m) && 0 <= v < vertex_count(m)
        ==> vertices_reachable(m, u, v)
}

// =============================================================================
// 2. Adjacency symmetry
// =============================================================================

/// Directed edge u→v implies directed edge v→u (via twin).
pub proof fn lemma_adjacent_symmetric(m: &Mesh, u: int, v: int)
    requires
        index_bounds(m),
        twin_endpoint_correspondence(m),
        adjacent_vertices(m, u, v),
    ensures
        adjacent_vertices(m, v, u),
{
    let h = choose|h: int| 0 <= h < half_edge_count(m)
        && m.half_edges@[h].vertex as int == u
        && m.half_edges@[m.half_edges@[h].next as int].vertex as int == v;

    let t = m.half_edges@[h].twin as int;
    assert(twin_endpoint_correspondence_at(m, h));
    assert(m.half_edges@[t].vertex as int == v);
    assert(m.half_edges@[m.half_edges@[t].next as int].vertex as int == u);
}

// =============================================================================
// 3. Path helpers (isolated for rlimit)
// =============================================================================

/// A single vertex is a valid path to itself.
pub proof fn lemma_trivial_path(m: &Mesh, u: int)
    requires 0 <= u < vertex_count(m),
    ensures vertices_reachable(m, u, u),
{
    let path = seq![u];
    assert(vertex_path(m, path));
}

/// Appending w to a valid path ending at v (where v→w) gives a valid path.
proof fn lemma_push_is_vertex_path(m: &Mesh, path: Seq<int>, w: int)
    requires
        vertex_path(m, path),
        adjacent_vertices(m, path[path.len() - 1], w),
        0 <= w < vertex_count(m),
    ensures
        vertex_path(m, path.push(w)),
        path.push(w)[0] == path[0],
        path.push(w).len() == path.len() + 1,
        path.push(w)[path.push(w).len() - 1] == w,
{
    let np = path.push(w);

    assert forall|i: int| 0 <= i < np.len()
    implies 0 <= #[trigger] np[i] < vertex_count(m)
    by {
        if i < path.len() { assert(np[i] == path[i]); }
    }

    assert forall|i: int| 0 <= i < np.len() - 1
    implies adjacent_vertices(m, #[trigger] np[i], np[i + 1])
    by {
        if i < path.len() - 1 {
            assert(np[i] == path[i]);
            assert(np[i + 1] == path[i + 1]);
        } else {
            assert(np[i] == path[path.len() - 1]);
            assert(np[i + 1] == w);
        }
    }
}

/// If reachable(u, v) and v→w adjacent, then reachable(u, w).
pub proof fn lemma_extend_path(m: &Mesh, u: int, v: int, w: int)
    requires
        vertices_reachable(m, u, v),
        adjacent_vertices(m, v, w),
        0 <= w < vertex_count(m),
    ensures
        vertices_reachable(m, u, w),
{
    let path = choose|p: Seq<int>| vertex_path(m, p) && p[0] == u && p[p.len() - 1] == v;
    lemma_push_is_vertex_path(m, path, w);
}

// =============================================================================
// 4. Reverse and concat (for full connectivity proof)
// =============================================================================

/// Reverse a sequence.
pub open spec fn reverse_seq(s: Seq<int>) -> Seq<int> {
    Seq::new(s.len(), |i: int| s[s.len() - 1 - i])
}

/// Reversing a valid path gives a valid path (adjacency is symmetric).
pub proof fn lemma_reverse_path(m: &Mesh, path: Seq<int>)
    requires
        index_bounds(m),
        twin_endpoint_correspondence(m),
        vertex_path(m, path),
    ensures
        vertex_path(m, reverse_seq(path)),
        reverse_seq(path).len() == path.len(),
        reverse_seq(path)[0] == path[path.len() - 1],
        path.len() >= 1 ==> reverse_seq(path)[reverse_seq(path).len() - 1] == path[0],
{
    let rev = reverse_seq(path);
    let n = path.len();

    assert forall|i: int| 0 <= i < n
    implies 0 <= #[trigger] rev[i] < vertex_count(m)
    by { assert(rev[i] == path[n - 1 - i]); }

    assert forall|i: int| 0 <= i < n - 1
    implies adjacent_vertices(m, #[trigger] rev[i], rev[i + 1])
    by {
        let j = (n - 2 - i) as int;
        assert(rev[i] == path[n - 1 - i]);
        assert(rev[i + 1] == path[j]);
        assert(path[j + 1] == rev[i]);
        assert(adjacent_vertices(m, path[j], path[j + 1]));
        lemma_adjacent_symmetric(m, path[j], path[j + 1]);
    }
}

/// Concatenate two paths sharing an endpoint (drop duplicate middle vertex).
pub open spec fn concat_paths(p1: Seq<int>, p2: Seq<int>) -> Seq<int>
    recommends p1.len() >= 1, p2.len() >= 1,
{
    Seq::new(
        (p1.len() + p2.len() - 1) as nat,
        |i: int| if i < p1.len() { p1[i] } else { p2[i - p1.len() + 1] },
    )
}

/// Helper: vertices in concat_paths are all in bounds.
pub proof fn lemma_concat_bounds(m: &Mesh, p1: Seq<int>, p2: Seq<int>)
    requires
        vertex_path(m, p1), vertex_path(m, p2),
        p1.len() >= 1, p2.len() >= 1,
        p1[p1.len() - 1] == p2[0],
    ensures
        forall|i: int| 0 <= i < (p1.len() + p2.len() - 1)
            ==> 0 <= #[trigger] concat_paths(p1, p2)[i] < vertex_count(m),
{
    let c = concat_paths(p1, p2);
    assert forall|i: int| 0 <= i < c.len()
    implies 0 <= #[trigger] c[i] < vertex_count(m)
    by {
        if i < p1.len() { assert(c[i] == p1[i]); }
        else { assert(c[i] == p2[i - p1.len() + 1]); }
    }
}

/// Helper: consecutive pairs in concat_paths are adjacent.
pub proof fn lemma_concat_adjacency(m: &Mesh, p1: Seq<int>, p2: Seq<int>)
    requires
        vertex_path(m, p1), vertex_path(m, p2),
        p1.len() >= 1, p2.len() >= 1,
        p1[p1.len() - 1] == p2[0],
    ensures
        forall|i: int| 0 <= i < (p1.len() + p2.len() - 2)
            ==> adjacent_vertices(m, #[trigger] concat_paths(p1, p2)[i], concat_paths(p1, p2)[i + 1]),
{
    let c = concat_paths(p1, p2);
    let n = c.len();
    assert forall|i: int| 0 <= i < n - 1
    implies adjacent_vertices(m, #[trigger] c[i], c[i + 1])
    by {
        if i < p1.len() - 1 {
            assert(c[i] == p1[i]);
            assert(c[i + 1] == p1[i + 1]);
        } else if i == p1.len() - 1 {
            // Boundary: c[i] = p1[last] = p2[0], c[i+1] = p2[1]
            assert(c[i] == p2[0]);
            if p2.len() > 1 {
                assert(c[i + 1] == p2[1]);
            }
        } else {
            let j = i - p1.len() + 1;
            assert(c[i] == p2[j]);
            assert(c[i + 1] == p2[j + 1]);
        }
    }
}

/// Concatenating two paths sharing an endpoint gives a valid path.
pub proof fn lemma_concat_paths(m: &Mesh, p1: Seq<int>, p2: Seq<int>)
    requires
        vertex_path(m, p1), vertex_path(m, p2),
        p1.len() >= 1, p2.len() >= 1,
        p1[p1.len() - 1] == p2[0],
    ensures
        vertex_path(m, concat_paths(p1, p2)),
        concat_paths(p1, p2).len() == p1.len() + p2.len() - 1,
        concat_paths(p1, p2)[0] == p1[0],
        concat_paths(p1, p2)[concat_paths(p1, p2).len() - 1] == p2[p2.len() - 1],
{
    lemma_concat_bounds(m, p1, p2);
    lemma_concat_adjacency(m, p1, p2);
}

/// Transitivity: reachable(u, v) and reachable(v, w) implies reachable(u, w).
pub proof fn lemma_reachable_transitive(m: &Mesh, u: int, v: int, w: int)
    requires
        vertices_reachable(m, u, v),
        vertices_reachable(m, v, w),
    ensures
        vertices_reachable(m, u, w),
{
    let p1 = choose|p: Seq<int>| vertex_path(m, p) && p[0] == u && p[p.len() - 1] == v;
    let p2 = choose|p: Seq<int>| vertex_path(m, p) && p[0] == v && p[p.len() - 1] == w;
    lemma_concat_paths(m, p1, p2);
}

// =============================================================================
// 5. Full connectivity from root reachability
// =============================================================================

/// If reachable(0, u) and reachable(0, v), then reachable(u, v).
proof fn lemma_pair_reachable(m: &Mesh, u: int, v: int)
    requires
        index_bounds(m),
        twin_endpoint_correspondence(m),
        vertices_reachable(m, 0, u),
        vertices_reachable(m, 0, v),
    ensures
        vertices_reachable(m, u, v),
{
    let pu = choose|p: Seq<int>| vertex_path(m, p) && p[0] == 0 && p[p.len() - 1] == u;
    let pv = choose|p: Seq<int>| vertex_path(m, p) && p[0] == 0 && p[p.len() - 1] == v;

    let rev = reverse_seq(pu);
    lemma_reverse_path(m, pu);

    let combined = concat_paths(rev, pv);
    lemma_concat_paths(m, rev, pv);
}

/// All vertices reachable from 0 implies full connectivity.
proof fn lemma_connected_from_root(m: &Mesh)
    requires
        index_bounds(m),
        twin_endpoint_correspondence(m),
        vertex_count(m) > 0,
        forall|v: int| 0 <= v < vertex_count(m) ==> vertices_reachable(m, 0, v),
    ensures
        is_connected(m),
{
    assert forall|u: int, v: int|
        0 <= u < vertex_count(m) && 0 <= v < vertex_count(m)
    implies vertices_reachable(m, u, v)
    by {
        lemma_pair_reachable(m, u, v);
    }
}

// =============================================================================
// 6. Connectivity checker (fixed-point iteration over half-edges)
// =============================================================================

/// Check connectivity via iterative edge relaxation.
/// Repeatedly scans all half-edges, propagating reachability.
pub fn check_connected(m: &Mesh) -> (out: bool)
    requires
        structurally_valid(m),
    ensures
        out ==> is_connected(m),
{
    let vcnt = m.vertex_half_edges.len();
    let hcnt = m.half_edges.len();

    if vcnt == 0 {
        proof { assert(is_connected(m)); }
        return true;
    }

    // Initialize visited array
    let mut visited: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < vcnt
        invariant
            0 <= i <= vcnt,
            visited@.len() == i as int,
            forall|j: int| 0 <= j < i ==> visited@[j] == false,
        decreases vcnt - i,
    {
        visited.push(false);
        i = i + 1;
    }

    visited.set(0, true);
    proof { lemma_trivial_path(m, 0); }

    // Fixed-point: repeat up to vcnt rounds
    let mut round: usize = 0;
    let mut changed: bool = true;

    while round < vcnt && changed
        invariant
            structurally_valid(m),
            vcnt as int == vertex_count(m),
            hcnt as int == half_edge_count(m),
            vcnt > 0,
            visited@.len() == vcnt as int,
            0 <= round <= vcnt,
            forall|v: int| 0 <= v < vertex_count(m) && visited@[v] == true
                ==> vertices_reachable(m, 0, v),
        decreases vcnt - round,
    {
        changed = false;
        let mut h: usize = 0;

        while h < hcnt
            invariant
                index_bounds(m),
                vcnt as int == vertex_count(m),
                hcnt as int == half_edge_count(m),
                vcnt > 0,
                visited@.len() == vcnt as int,
                0 <= h <= hcnt,
                forall|v: int| 0 <= v < vertex_count(m) && visited@[v] == true
                    ==> vertices_reachable(m, 0, v),
            decreases hcnt - h,
        {
            let u_idx = m.half_edges[h].vertex;
            let next_h = m.half_edges[h].next;
            let v_idx = m.half_edges[next_h].vertex;

            if visited[u_idx] && !visited[v_idx] {
                proof {
                    assert(m.half_edges@[h as int].vertex as int == u_idx as int);
                    assert(m.half_edges@[m.half_edges@[h as int].next as int].vertex as int == v_idx as int);
                    lemma_extend_path(m, 0, u_idx as int, v_idx as int);
                }
                visited.set(v_idx, true);
                changed = true;
            }

            h = h + 1;
        }

        round = round + 1;
    }

    // Check all visited
    let mut all_visited = true;
    let mut v: usize = 0;
    while v < vcnt
        invariant
            0 <= v <= vcnt,
            vcnt as int == vertex_count(m),
            visited@.len() == vcnt as int,
            all_visited ==> forall|j: int| 0 <= j < v as int ==> visited@[j] == true,
            forall|j: int| 0 <= j < vertex_count(m) && visited@[j] == true
                ==> vertices_reachable(m, 0, j),
        decreases vcnt - v,
    {
        if !visited[v] {
            all_visited = false;
        }
        v = v + 1;
    }

    if !all_visited {
        return false;
    }

    proof {
        assert(index_bounds(m));
        assert(twin_endpoint_correspondence(m));
        lemma_connected_from_root(m);
    }

    true
}

} // verus!
