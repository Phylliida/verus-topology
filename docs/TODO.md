# verus-topology — Implementation TODO

Formally verified half-edge mesh topology in Rust + Verus.

This crate handles **combinatorial topology only**: vertices, edges, faces,
half-edges, incidence relationships, structural invariants, Euler operators,
and genus tracking. Geometric embedding (coordinates, curves, surfaces) belongs
in downstream crates (`verus-geometry`, `verus-brep-kernel`).

## Crate layering

```
verus-bigint
  └→ verus-rational
       └→ verus-interval-arithmetic
            └→ verus-geometry + verus-linalg
                 └→ verus-topology              ← this crate
                      └→ verus-brep-kernel      (BREP evaluation, surfaces, intersections)
                           └→ verus-cad-ops     (extrude, boolean, fillet, ...)
```

Note: verus-topology itself needs only `vstd` and `verus-algebra` (for index
arithmetic). The geometry crates are peers, not dependencies — topology is
pure combinatorics. Geometric checks live in a downstream integration layer.

## What exists in old/VerusCAD

The `vcad-topology` crate (~38K lines) has substantial prior art we can mine:

| Component | Old location | Lines | Reuse plan |
|---|---|---|---|
| Half-edge data structures | `halfedge_mesh/mod.rs` | ~100 | Port directly, modernize index types |
| Constructor (`from_face_cycles`) | `halfedge_mesh/construction.rs` | ~200 | Port, add full semantic proof |
| Structural validators (7 checks) | `halfedge_mesh/validation.rs` | ~1,850 | Port, strengthen bridge kernels to full proofs |
| Connectivity / Euler characteristic | `halfedge_mesh/components.rs` | ~90 | Port, verify BFS termination |
| Verified checker kernels (10) | `verified_checker_kernels.rs` | ~2,600 | Port 5 fully-proven kernels; finish 5 bridge kernels |
| Runtime refinement bridge | `runtime_halfedge_mesh_refinement/` | ~1 MB | Heavily refactor — too large, extract core proofs |
| Geometric-topological checks (8) | `validation.rs` (feature-gated) | ~1,000 | Do NOT port here — belongs in downstream geometry layer |
| Tests | `halfedge_mesh/tests.rs` | ~7,800 | Port reference meshes, drop geometry-specific tests |

**Key decision: the old refinement layer is ~1 MB across 8 files. Much of that
is boilerplate from the include! pattern. The new crate should use clean module
structure with focused proof files, not monolithic includes.**

---

## Phase 0 — Project scaffolding

- [ ] Create `Cargo.toml` depending on `vstd`, `verus-algebra`
- [ ] Create `src/lib.rs` with module structure
- [ ] Set up `scripts/check.sh` with `--min-verified`, `--forbid-trusted-escapes`
- [ ] Verify empty crate compiles with `cargo-verus`
- [ ] Add CI workflow matching sibling crates

---

## Phase 1 — Core data structures

### 1.1 Index types

```
pub type VertexId = usize;
pub type EdgeId = usize;
pub type FaceId = usize;
pub type HalfEdgeId = usize;
```

Consider newtype wrappers for type safety (prevents mixing vertex/edge indices).
The old code uses raw `usize` — evaluate whether newtypes cause Verus friction.

- [ ] Define index types
- [ ] Define `INVALID: usize = usize::MAX` sentinel (used during construction)

### 1.2 Half-edge structure

```
pub struct HalfEdge {
    pub twin: HalfEdgeId,
    pub next: HalfEdgeId,
    pub prev: HalfEdgeId,
    pub vertex: VertexId,    // origin vertex
    pub edge: EdgeId,        // parent undirected edge
    pub face: FaceId,        // incident face
}
```

- [ ] Define `HalfEdge` struct
- [ ] Define ghost model `HalfEdgeModel` for spec-level reasoning

### 1.3 Vertex, Edge, Face

```
pub struct Vertex {
    pub half_edge: HalfEdgeId,   // one outgoing half-edge
}

pub struct Edge {
    pub half_edge: HalfEdgeId,   // one of the two half-edges
}

pub struct Face {
    pub half_edge: HalfEdgeId,   // one half-edge in the face cycle
}
```

- [ ] Define Vertex, Edge, Face structs
- [ ] Define ghost models for each

### 1.4 Mesh container

```
pub struct Mesh {
    pub vertices: Vec<Vertex>,
    pub edges: Vec<Edge>,
    pub faces: Vec<Face>,
    pub half_edges: Vec<HalfEdge>,
}
```

- [ ] Define `Mesh` struct
- [ ] Define `MeshModel` ghost type with `View` impl (`mesh@ -> MeshModel`)
- [ ] Spec accessors: `vertex_count_spec`, `edge_count_spec`, `face_count_spec`,
      `half_edge_count_spec`

**Design note:** Arena-indexed (Vec of structs) rather than pointer-based.
This is critical for Verus — usize arithmetic is tractable, pointer reasoning
is not. Also gives cache locality and trivial serialization.

---

## Phase 2 — Structural invariants (specs)

These are the 7 core invariants that define a valid half-edge mesh.
Each gets a spec predicate, a runtime checker, and a Verus proof that
the checker is sound.

### 2.1 Index bounds

```
spec fn index_bounds_spec(m: &MeshModel) -> bool {
    forall|h: int| 0 <= h < m.half_edge_count ==> {
        m.half_edges[h].twin < m.half_edge_count &&
        m.half_edges[h].next < m.half_edge_count &&
        m.half_edges[h].prev < m.half_edge_count &&
        m.half_edges[h].vertex < m.vertex_count &&
        m.half_edges[h].edge < m.edge_count &&
        m.half_edges[h].face < m.face_count
    }
    // ... plus vertex/edge/face representative refs in bounds
}
```

- [ ] Write spec predicate
- [ ] Write runtime checker (loop over all elements)
- [ ] Prove checker is sound: returns true <==> spec holds
- **Old status:** FULLY PROVEN in old crate. Port the proof.

### 2.2 Twin involution

```
spec fn twin_involution_spec(m: &MeshModel) -> bool {
    forall|h: int| 0 <= h < m.half_edge_count ==>
        m.half_edges[m.half_edges[h].twin].twin == h
}
```

- [ ] Write spec predicate
- [ ] Write runtime checker
- [ ] Prove soundness
- **Old status:** FULLY PROVEN. Port directly.

### 2.3 Prev/next inverse

```
spec fn prev_next_inverse_spec(m: &MeshModel) -> bool {
    forall|h: int| 0 <= h < m.half_edge_count ==>
        m.half_edges[m.half_edges[h].next].prev == h &&
        m.half_edges[m.half_edges[h].prev].next == h
}
```

- [ ] Write spec predicate
- [ ] Write runtime checker
- [ ] Prove soundness
- **Old status:** FULLY PROVEN. Port directly.

### 2.4 Face cycles

Every face's half-edges form a closed cycle under `next`, each half-edge
belongs to exactly one face, and every cycle has >= 3 half-edges.

- [ ] Write spec: cycle closure, global partition, min-length
- [ ] Write runtime checker (walk each face cycle, mark visited)
- [ ] Prove soundness
- **Old status:** BRIDGE KERNEL — soundness proven but semantic spec needs
  strengthening. Finish the full proof in the new crate.

### 2.5 No degenerate edges

```
spec fn no_degenerate_edges_spec(m: &MeshModel) -> bool {
    forall|h: int| 0 <= h < m.half_edge_count ==>
        m.half_edges[h].vertex != m.half_edges[m.half_edges[h].twin].vertex
}
```

- [ ] Write spec predicate
- [ ] Write runtime checker
- [ ] Prove soundness
- **Old status:** FULLY PROVEN. Port directly.

### 2.6 Vertex manifold (single fan)

For each vertex, the outgoing half-edges form exactly one cycle under
the operation `h → next(twin(h))`. This is the manifold condition —
it guarantees a disk-like neighborhood around each vertex.

- [ ] Write spec: single-cycle witness for each vertex
- [ ] Write runtime checker (walk vertex fan, check return to start)
- [ ] Prove soundness
- **Old status:** BRIDGE KERNEL. Finish full proof.

### 2.7 Edge-twin duality

Each edge record points to one of exactly two half-edges that share
that edge ID, and those two are twins of each other.

- [ ] Write spec predicate
- [ ] Write runtime checker
- [ ] Prove soundness
- **Old status:** BRIDGE KERNEL. Finish full proof.

### 2.8 Composite structural validity

```
spec fn structurally_valid_spec(m: &MeshModel) -> bool {
    index_bounds_spec(m)
    && twin_involution_spec(m)
    && prev_next_inverse_spec(m)
    && face_cycles_spec(m)
    && no_degenerate_edges_spec(m)
    && vertex_manifold_spec(m)
    && edge_twin_duality_spec(m)
}
```

- [ ] Composite spec
- [ ] Composite runtime checker calling all sub-checkers
- [ ] Prove: composite returns true <==> all sub-specs hold

---

## Phase 3 — Constructor

### 3.1 `from_face_cycles` builder

Input: vertex count + face definitions as cycles of vertex indices.
Output: `Result<Mesh, MeshBuildError>`.

Algorithm:
1. Validate inputs (non-empty, cycles >= 3, indices in range)
2. Create half-edges from face cycles (`twin = INVALID` initially)
3. Build oriented-edge map: `(from, to) → half_edge_id`
4. Match twins: for each `(from, to)`, find `(to, from)`
5. Build edge table (one per twin pair)
6. Assign vertex representative half-edges

Error cases:
- `EmptyVertexSet`, `EmptyFaceSet`
- `FaceTooSmall { face, len }`
- `VertexOutOfBounds { face, vertex, index }`
- `DegenerateOrientedEdge { face, index, vertex }` (self-loop)
- `DuplicateOrientedEdge { from, to }`
- `MissingTwin { half_edge, from, to }` (open boundary)
- `IsolatedVertex { vertex }`

- [ ] Define `MeshBuildError` enum
- [ ] Implement `from_face_cycles`
- [ ] **Prove:** on `Ok(mesh)`, `structurally_valid_spec(mesh@)` holds
- [ ] **Prove:** on `Err(e)`, no valid mesh could have been constructed
      (i.e., the error conditions are necessary, not just sufficient)

**Old status:** Implemented with witness tracking but full semantic proof
incomplete. This is a priority proof target.

### 3.2 Reference constructors

Concrete meshes for testing and as proof witnesses:

- [ ] `Mesh::tetrahedron()` — 4V, 6E, 4F, 12HE (simplest closed manifold)
- [ ] `Mesh::cube()` — 8V, 12E, 6F, 24HE
- [ ] `Mesh::triangular_prism()` — 6V, 9E, 5F, 18HE
- [ ] For each: prove `structurally_valid_spec` and `euler_char == 2`

---

## Phase 4 — Connectivity & Euler characteristic

### 4.1 Connected components (BFS)

- [ ] Implement BFS over half-edge adjacency (`twin`, `next`, `prev`)
- [ ] Return component count and per-component element sets
- [ ] **Prove:** BFS terminates (bounded by half-edge count)
- [ ] **Prove:** every half-edge is assigned to exactly one component
- [ ] **Prove:** components partition the mesh

### 4.2 Euler characteristic

For each component, compute `chi = |V| - |E| + |F|`.

- [ ] Implement per-component V, E, F counting
- [ ] Compute `chi` per component
- [ ] `check_euler_formula_closed()` — asserts all components have `chi == 2`
      (genus-0, closed, orientable manifold)

### 4.3 Euler-Poincare relation

The general formula: `V - E + F = 2(S - G) + R`
where S = shells, G = genus (handles), R = rings (inner loops / holes).

For our Phase 4 scope (genus-0, no holes): `V - E + F = 2` per component.

- [ ] **Prove:** `structurally_valid_spec(m) && all_chi_eq_2(m)` implies
      the mesh represents a closed orientable 2-manifold of genus 0
- [ ] Leave genus > 0 for later — document as explicit non-goal for now

### 4.4 Composite validity

```
spec fn valid_spec(m: &MeshModel) -> bool {
    structurally_valid_spec(m)
    && euler_closed_spec(m)
}
```

- [ ] Composite spec and checker

---

## Phase 5 — Euler operators

The six classical Euler operators are the *only* permitted way to mutate
topology. Each one preserves the Euler-Poincare invariant by construction.

### 5.1 MVFS — Make Vertex, Face, Shell

Creates a new connected component with one vertex, one face, no edges.
The degenerate "point shell."

```
fn mvfs(mesh: &mut Mesh, /* vertex data */) -> (VertexId, FaceId)
    ensures mesh@.valid_spec()  // if it held before
```

- [ ] Implement
- [ ] Prove: preserves `structurally_valid_spec`
- [ ] Prove: increments V by 1, F by 1, S by 1 → chi preserved

### 5.2 KVFS — Kill Vertex, Face, Shell

Inverse of MVFS. Removes a point shell.

- [ ] Implement
- [ ] Prove: inverse of MVFS (round-trip identity)
- [ ] Prove: preserves invariants

### 5.3 MEV — Make Edge, Vertex

Splits a vertex into two vertices connected by a new edge.
Adds 1 edge + 1 vertex → `delta(V - E) = 0` → chi preserved.

- [ ] Implement
- [ ] Prove: preserves `structurally_valid_spec`
- [ ] Prove: chi preserved
- [ ] Prove: twin/next/prev consistency of new half-edges

### 5.4 KEV — Kill Edge, Vertex

Inverse of MEV. Merges two vertices connected by an edge.

- [ ] Implement
- [ ] Prove: inverse of MEV
- [ ] Prove: preserves invariants

### 5.5 MEF — Make Edge, Face

Splits a face by adding an edge between two vertices on its boundary.
Adds 1 edge + 1 face → `delta(F - E) = 0` → chi preserved.

- [ ] Implement
- [ ] Prove: preserves `structurally_valid_spec`
- [ ] Prove: chi preserved
- [ ] Prove: both resulting faces have valid cycles

### 5.6 KEF — Kill Edge, Face

Inverse of MEF. Merges two faces by removing a shared edge.

- [ ] Implement
- [ ] Prove: inverse of MEF
- [ ] Prove: preserves invariants

### 5.7 Operator composition lemmas

- [ ] **Prove:** any sequence of Euler operators preserves `valid_spec`
      (by induction on operator count — each step preserves, so composition does)
- [ ] **Prove:** any closed orientable 2-manifold can be constructed from Euler
      operators starting from MVFS (existence / completeness — this is a deep theorem,
      may defer or take as axiom with citation)

---

## Phase 6 — Advanced Euler operators

These are compound operators built from the basic six, useful for modeling:

### 6.1 MEKR — Make Edge, Kill Ring

Connects an inner loop to the outer boundary of a face. Needed for holes.

- [ ] Implement as composition of basic operators
- [ ] Prove: preserves invariants
- [ ] Prove: correctly merges rings

### 6.2 KEMR — Kill Edge, Make Ring

Inverse of MEKR. Creates an inner loop (hole) in a face.

- [ ] Implement
- [ ] Prove: inverse of MEKR

### 6.3 MSEV — Make Shell, Edge, Vertex (glue two shells)

Joins two separate shells by adding an edge between them.

- [ ] Implement
- [ ] Prove: preserves invariants, decrements shell count by 1

### 6.4 KSEV — Kill Shell, Edge, Vertex (split a shell)

Inverse of MSEV.

- [ ] Implement
- [ ] Prove: inverse of MSEV

---

## Phase 7 — Higher-level topology utilities

Built on Euler operators, these are convenience functions for downstream use.

### 7.1 Face splitting

Split a face by a path of vertices.

- [ ] Implement as sequence of MEF calls
- [ ] Prove: all resulting faces are valid

### 7.2 Edge splitting

Insert a vertex along an existing edge.

- [ ] Implement as KEV + 2x MEV (or equivalent)
- [ ] Prove: preserves manifold, updates incidence correctly

### 7.3 Edge collapse

Collapse an edge to a single vertex (inverse of edge split).

- [ ] Implement
- [ ] Prove: preserves manifold when topologically safe
- [ ] Characterize when it's NOT safe (link condition) and reject

### 7.4 Vertex-to-face and face-to-vertex queries

Traversal utilities:

- [ ] `faces_around_vertex(v)` — walk the vertex fan via `twin`/`next`
- [ ] `vertices_of_face(f)` — walk the face cycle via `next`
- [ ] `edges_of_face(f)` — walk the face cycle, collect edge IDs
- [ ] `adjacent_faces(f)` — faces sharing an edge with f
- [ ] For each: prove termination and completeness (all neighbors visited)

### 7.5 Boundary detection

For meshes that aren't fully closed (intermediate construction states):

- [ ] `is_boundary_half_edge(h)` — twin's face is the "outer" face
- [ ] `boundary_loop(h)` — walk boundary half-edges
- [ ] `is_closed(m)` — no boundary half-edges exist

---

## Phase 8 — Genus tracking and higher topology

Extend beyond genus-0:

- [ ] Track genus per component: `chi = 2 - 2g` for closed orientable manifolds
- [ ] Handle meshes with boundary: `chi = 2 - 2g - b` (b = boundary components)
- [ ] Classify: closed, open, orientable, non-orientable
- [ ] Prove: Euler operators update genus/boundary counts correctly

This phase is lower priority — most CAD solids are genus-0. But tori,
through-holes, and handle-bodies need genus > 0.

---

## Proof strategy notes

### What to port from old crate

The old `verified_checker_kernels.rs` has 5 fully proven kernels:
- `kernel_check_index_bounds` — port as-is
- `kernel_check_twin_involution` — port as-is
- `kernel_check_prev_inverse_of_next` — port as-is
- `kernel_check_no_degenerate_edges` — port as-is
- `kernel_check_shared_edge_local_orientation_consistency` — port as-is

And 3 bridge kernels that need strengthening:
- `kernel_check_face_cycles` — finish semantic proof
- `kernel_check_vertex_manifold_single_cycle` — finish semantic proof
- `kernel_check_edge_has_exactly_two_half_edges` — finish semantic proof

### What NOT to port

- Geometric-topological checks (coplanarity, convexity, normals, intersection).
  These belong in a downstream crate that combines verus-topology + verus-geometry.
- The 1 MB refinement layer. Rewrite from scratch with cleaner module boundaries.
- The `include!` macro pattern. Use normal Rust modules.

### Proof difficulty estimates

| Item | Difficulty | Notes |
|---|---|---|
| Index bounds checker | Easy | Direct loop + indexing |
| Twin involution | Easy | Simple universal quantifier |
| Prev/next inverse | Easy | Same pattern as twin |
| No degenerate edges | Easy | Same pattern |
| Face cycles | Medium | Need cycle-witness construction, partition proof |
| Vertex manifold | Medium | Fan-cycle witness, needs twin+next composition reasoning |
| Edge-twin duality | Medium | Two-element set witness |
| `from_face_cycles` correctness | Hard | Must prove all 7 invariants hold on output mesh |
| Euler operator preservation | Hard | Each operator needs its own invariant-preservation proof |
| BFS termination + completeness | Medium | Standard visited-set argument |
| Euler characteristic correctness | Medium | Counting + algebraic identity |
| Operator composition induction | Medium | If individual proofs are solid, induction is routine |

---

## Trust surface

### Trusted (unverified) components

| Component | Why trusted | Mitigation |
|---|---|---|
| `vstd` | Verus standard library | Maintained by Verus team |
| `Vec` indexing | Rust std | Extensively tested, UB-free in safe Rust |

### Untrusted (verified) components

Everything in this crate. No `unsafe`, no `#[verifier::external_body]`,
no `assume`. The `--forbid-trusted-escapes` CI flag enforces this.

### Explicit non-goals

- **No geometry in this crate.** No coordinates, no distances, no angles.
  Pure combinatorial topology only.
- **No concurrency.** Single-threaded mutation via Euler operators.
- **No persistence / serialization.** Downstream concern.
- **No spatial indexing.** BVH, octree, etc. are downstream.

---

## Milestones

| Milestone | Phases | What it proves |
|---|---|---|
| **M1: Valid mesh** | 0-2 | Can construct meshes and verify all 7 structural invariants |
| **M2: Euler operators** | 3-5 | Can mutate topology while preserving invariants by construction |
| **M3: Full manifold** | 6-8 | Higher-genus support, boundary tracking, traversal utilities |

**M1 is the critical path for downstream work.** The BREP kernel needs
to construct and query meshes. Euler operators (M2) are needed for modeling
operations but can be developed in parallel with BREP geometry work.
