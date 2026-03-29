# Construction Proof Refactor Plan

## Goal
Prove all 10 construction invariants in `construction_proofs.rs` by instrumenting
`from_face_cycles` in `construction.rs` with ghost state and loop invariants.
End state: 0 assume(false), remove `check_structurally_valid` call.

## Architecture

`from_face_cycles` has 5 phases. Each phase establishes invariants that later phases depend on.

```
Phase A (validation) ─► Phase B (HE creation) ─► Phase C (twin matching)
                                                       │
                                                       ▼
                                                 Phase D (edges)
                                                       │
                                                       ▼
                                                 Phase E (vertices)
                                                       │
                                                       ▼
                                               structurally_valid
```

## Invariant Dependency Graph

```
index_bounds ◄── prev_next_bidirectional
     │                    │
     ▼                    ▼
twin_involution ──► no_degenerate_edges
     │                    │
     ▼                    ▼
edge_exactly_two ──► shared_edge_orientation
     │                    │
     ▼                    ▼
half_edge_edge_count   face_representative_cycles
     │                    │
     ▼                    ▼
half_edge_face_count   vertex_manifold
```

## Tasks (ordered by difficulty)

### Tier 1: Easy — straightforward loop invariants

- [ ] **1. index_bounds** (Phase B-E)
  - Phase B: vertex fields < vertex_count, next/prev within face block, face field == current face
  - Phase C: twin < half_edge_count
  - Phase D: edge < edge_count
  - Phase E: vertex_half_edges[v] < half_edge_count
  - Ghost: track that all fields stay in bounds through each phase's loop

- [ ] **2. prev_next_bidirectional** (Phase B)
  - Phase B sets `he[start+i].next = start + (i+1)%n` and `he[start+i].prev = start + (i-1+n)%n`
  - These are explicit inverses within each contiguous face block
  - Ghost: loop invariant that for all h processed so far, next(prev(h))==h and prev(next(h))==h
  - Later phases (C, D, E) don't modify next/prev fields

- [ ] **3. half_edge_edge_count_relation** (2E == HE, Phase D)
  - Phase D creates one edge per twin pair: for each h where edge==MAX, set edge for h and twin(h)
  - Since twin is an involution (Phase C), each pair is visited once
  - Ghost: count edges created so far, show final count == HE/2

### Tier 2: Medium — need cross-phase reasoning

- [ ] **4. twin_involution** (Phase C)
  - Phase C: for each h, find t with (from(h),to(h))==(to(t),from(t)), set h.twin=t
  - When we later process t, we find h as its match (unique match by Phase A validation)
  - Ghost: after processing h and setting h.twin=t, track that t.twin will be set to h
  - Key: matching is unique (no two HEs share the same oriented edge)

- [ ] **5. no_degenerate_edges** (Phase A + C)
  - Phase A rejects consecutive duplicate vertices in face cycles
  - So every oriented edge (from,to) has from != to
  - Twin has endpoints swapped, still distinct
  - Ghost: propagate "no self-loops" from Phase A validation through Phase C matching

- [ ] **6. edge_exactly_two_half_edges** (Phase D)
  - Phase D: for each unprocessed h, create edge e, assign to h and twin(h)
  - Only h and twin(h) get edge==e (loop skips already-processed HEs)
  - Ghost: for each edge created, track the exact two HEs assigned to it
  - Needs twin_involution to know twin(twin(h))==h

- [ ] **7. half_edge_face_count_lower_bound** (HE >= 3F, Phase B)
  - Phase B creates HEs from face cycles, each face cycle has >= 3 vertices (Phase A)
  - Total HE = sum of face cycle lengths >= 3 * face_count
  - Ghost: accumulate sum through Phase B loop, show sum >= 3*F

### Tier 3: Hard — complex structural arguments

- [ ] **8. shared_edge_orientation_consistency** (Phase B + C)
  - Twin faces distinct: Phase C matches HEs from different faces (matching (u,v) with (v,u)
    from a different face since each face is a simple polygon)
  - Twin endpoint correspondence: Phase C explicitly matches from(h)->to(h) with to(t)->from(t)
  - Ghost: track face assignments through Phase B, show matching in Phase C crosses faces

- [ ] **9. face_representative_cycles** (Phase B)
  - Phase B creates contiguous HE blocks per face with circular next/prev
  - face_half_edges[f] = start of block, all HEs in block have face==f
  - Walking next from start visits exactly n HEs before returning
  - Ghost: construct the cycle witness (start, length) per face during Phase B
  - Also need coverage: every HE belongs to exactly one face cycle (follows from contiguous blocks)

### Tier 4: Very hard — topological argument

- [ ] **10. vertex_manifold** (Phase B + C + E)
  - For each vertex v, the sequence of HEs with vertex==v connected via twin.next forms a cycle
  - Requires: twin bounces between faces, next stays on same vertex's outgoing edge
  - The input face cycles around v must form a connected fan (not multiple components)
  - This is the manifold condition: the link of v is a topological circle
  - Ghost: for each vertex, track the fan of incident face cycles through Phases B and C
  - May need auxiliary lemma: if twin.next forms a path visiting all incident HEs, it's a cycle

## Implementation Strategy

1. Add ghost scaffolding to `from_face_cycles`: capture original face_cycles as ghost, track
   per-phase invariants
2. Work through tiers 1-4 in order
3. After each invariant is proved, remove its assume(false) from construction_proofs.rs
4. After all 10 are proved, remove `check_structurally_valid` call and prove `structurally_valid`
   directly from construction

## Key Ghost State Needed

```rust
//  Phase B ghost state
ghost let face_starts: Seq<usize>;  //  start HE index per face
ghost let face_lens: Seq<usize>;    //  cycle length per face

//  Phase C ghost state
ghost let twin_map: Seq<usize>;     //  twin assignment

//  Phase D ghost state
ghost let edge_pairs: Seq<(usize, usize)>;  //  (h, twin(h)) per edge

//  Phase E ghost state
ghost let vertex_he: Seq<usize>;    //  representative HE per vertex
```
