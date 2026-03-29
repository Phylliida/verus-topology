use vstd::prelude::*;
use crate::mesh::*;

verus! {

pub open spec fn next_or_self(m: &Mesh, h: int) -> int {
    let hcnt = half_edge_count(m);
    if 0 <= h < hcnt {
        let n = m.half_edges@[h].next as int;
        if 0 <= n < hcnt {
            n
        } else {
            h
        }
    } else {
        h
    }
}

pub open spec fn vertex_ring_succ_or_self(m: &Mesh, h: int) -> int {
    let hcnt = half_edge_count(m);
    if 0 <= h < hcnt {
        let t = m.half_edges@[h].twin as int;
        if 0 <= t < hcnt {
            let n = m.half_edges@[t].next as int;
            if 0 <= n < hcnt {
                n
            } else {
                h
            }
        } else {
            h
        }
    } else {
        h
    }
}

pub open spec fn next_iter(m: &Mesh, h: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        h
    } else {
        next_or_self(m, next_iter(m, h, (n - 1) as nat))
    }
}

pub open spec fn vertex_ring_iter(m: &Mesh, h: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        h
    } else {
        vertex_ring_succ_or_self(m, vertex_ring_iter(m, h, (n - 1) as nat))
    }
}

pub proof fn lemma_next_iter_step(m: &Mesh, h: int, n: nat)
    ensures
        next_iter(m, h, (n + 1) as nat)
            == next_or_self(m, next_iter(m, h, n)),
{
    assert(next_iter(m, h, (n + 1) as nat)
        == next_or_self(m, next_iter(m, h, n)));
}

pub proof fn lemma_vertex_ring_iter_step(m: &Mesh, h: int, n: nat)
    ensures
        vertex_ring_iter(m, h, (n + 1) as nat)
            == vertex_ring_succ_or_self(m, vertex_ring_iter(m, h, n)),
{
    assert(vertex_ring_iter(m, h, (n + 1) as nat)
        == vertex_ring_succ_or_self(m, vertex_ring_iter(m, h, n)));
}

pub proof fn lemma_next_or_self_in_bounds(m: &Mesh, h: int)
    requires
        index_bounds(m),
        0 <= h < half_edge_count(m),
    ensures
        0 <= next_or_self(m, h) < half_edge_count(m),
{
    let hcnt = half_edge_count(m);
    let n = m.half_edges@[h].next as int;
    assert(0 <= n < hcnt);
    assert(next_or_self(m, h) == n);
}

pub proof fn lemma_vertex_ring_succ_or_self_in_bounds(m: &Mesh, h: int)
    requires
        index_bounds(m),
        0 <= h < half_edge_count(m),
    ensures
        0 <= vertex_ring_succ_or_self(m, h) < half_edge_count(m),
{
    let hcnt = half_edge_count(m);
    let t = m.half_edges@[h].twin as int;
    assert(0 <= t < hcnt);
    let n = m.half_edges@[t].next as int;
    assert(0 <= n < hcnt);
    assert(vertex_ring_succ_or_self(m, h) == n);
}

pub proof fn lemma_next_iter_in_bounds(m: &Mesh, h: int, n: nat)
    requires
        index_bounds(m),
        0 <= h < half_edge_count(m),
    ensures
        0 <= next_iter(m, h, n) < half_edge_count(m),
    decreases n
{
    if n == 0 {
    } else {
        lemma_next_iter_in_bounds(m, h, (n - 1) as nat);
        lemma_next_or_self_in_bounds(m, next_iter(m, h, (n - 1) as nat));
        lemma_next_iter_step(m, h, (n - 1) as nat);
    }
}

pub proof fn lemma_vertex_ring_iter_in_bounds(m: &Mesh, h: int, n: nat)
    requires
        index_bounds(m),
        0 <= h < half_edge_count(m),
    ensures
        0 <= vertex_ring_iter(m, h, n) < half_edge_count(m),
    decreases n
{
    if n == 0 {
    } else {
        lemma_vertex_ring_iter_in_bounds(m, h, (n - 1) as nat);
        lemma_vertex_ring_succ_or_self_in_bounds(
            m,
            vertex_ring_iter(m, h, (n - 1) as nat),
        );
        lemma_vertex_ring_iter_step(m, h, (n - 1) as nat);
    }
}

} //  verus!
