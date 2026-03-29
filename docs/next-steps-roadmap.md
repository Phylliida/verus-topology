# verus-topology — Next Steps Roadmap

Post Tiers 1–4a. Everything below targets gaps needed for a formally verified 3D CAD kernel.

---

## 1. Connectivity Preservation Under Euler Ops

**Priority:** Highest — biggest current spec gap
**Difficulty:** Hard
**File:** `connectivity.rs` (new section)

### Problem

We can *check* connectivity (`check_connected`) but can't *prove* that local operations preserve it. After any `split_edge` / `split_face` / `flip_edge` / `collapse_edge`, the connectivity guarantee is lost and must be re-checked from scratch.

### What's needed

#### 1.1 `lemma_split_edge_preserves_connected`
```rust
proof fn lemma_split_edge_preserves_connected(m: &Mesh, e: int)
    requires structurally_valid(m), is_connected(m), 0 <= e < edge_count(m), ...
    ensures is_connected(&split_edge_build(m, e)),
```
**Proof sketch:** Every old vertex path is still valid (old vertices preserved, old adjacencies preserved). The new vertex is adjacent to both endpoints of the split edge, so it's reachable from any old vertex in at most one extra step.

#### 1.2 `lemma_split_face_preserves_connected`
```rust
proof fn lemma_split_face_preserves_connected(m: &Mesh, h_start: int, h_end: int)
    requires structurally_valid(m), is_connected(m), ...
    ensures is_connected(&split_face_build(m, h_start, h_end)->Ok_0),
```
**Proof sketch:** Only adds a new diagonal edge. All old adjacencies preserved. The two new faces share the diagonal, maintaining connectivity.

#### 1.3 `lemma_flip_edge_preserves_connected`
```rust
proof fn lemma_flip_edge_preserves_connected(m: &Mesh, e: int)
    requires structurally_valid(m), is_connected(m), ...
    ensures is_connected(&flip_edge_build(m, e)),
```
**Proof sketch:** Hardest of the three. Removes one diagonal of a quad and adds the other. Need to show: the quad's 4 vertices remain mutually reachable through the new diagonal + surrounding edges. Then any path through the old diagonal can be rerouted through the quad boundary.

#### 1.4 `lemma_collapse_edge_preserves_connected`
**Proof sketch:** Merges two adjacent vertices into one. All paths through the collapsed edge's endpoints are still valid (just shorter). Need the "link condition" precondition to ensure we don't create non-manifold topology.

### Key challenge

The `is_connected` spec uses `vertices_reachable` which quantifies over paths. Proving connectivity preservation requires constructing new witness paths from old ones — either showing old paths still work (split_edge, split_face) or showing how to reroute them (flip_edge, collapse_edge).

---

## 2. Point-in-Solid (3D Ray Casting)

**Priority:** Very high — fundamental solid modeling query
**Difficulty:** Hard
**Files:** New `point_in_solid.rs` in verus-topology, leveraging verus-geometry predicates

### Problem

The fundamental CAD query: "is this point inside this solid?" We have all the ingredients — `ray_hits_triangle` in verus-geometry, mesh traversal in verus-topology — but no mesh-level integration.

### What's needed

#### 2.1 Ray-mesh crossing spec
```rust
///  Count signed crossings of a ray through all faces of a closed oriented mesh
pub open spec fn ray_mesh_crossing_count<T: OrderedField>(
    m: &Mesh, pos: Seq<Point3<T>>,
    ray_origin: Point3<T>, ray_dir: Vec3<T>,
) -> int
```
Sum over all faces: +1 if ray enters the solid through this face (crosses front-to-back), -1 if it exits (back-to-front), 0 if it misses. Uses `ray_hits_triangle` + `orient3d` for sign.

#### 2.2 Point-in-solid predicate
```rust
pub open spec fn point_inside_solid<T: OrderedField>(
    m: &Mesh, pos: Seq<Point3<T>>, p: Point3<T>,
) -> bool {
    //  For any non-degenerate ray direction, crossing count is odd
    exists|dir: Vec3<T>| ray_mesh_crossing_count(m, pos, p, dir) % 2 == 1
}
```

#### 2.3 Runtime checker
```rust
pub fn check_point_inside_solid<T: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint3<T>>,
    p: &RuntimePoint3<T>, dir: &RuntimeVec3<T>,
) -> (out: bool)
    requires
        structurally_valid(m),
        is_topological_sphere(m),
        consistently_oriented_3d(m, pos_view(pos)),
        //  ray doesn't pass through any edge or vertex (non-degenerate)
    ensures
        out ==> point_inside_solid(m, pos_view(pos), p@),
```

**Algorithm:** For each face, check if ray hits the triangle (using `ray_hits_triangle_nodiv_exec` already in verus-geometry). Count signed crossings. Return `count % 2 == 1`.

#### 2.4 Correctness lemma
```rust
proof fn lemma_crossing_parity_consistent<T: OrderedField>(
    m: &Mesh, pos: Seq<Point3<T>>, p: Point3<T>,
    dir1: Vec3<T>, dir2: Vec3<T>,
)
    requires
        is_topological_sphere(m),
        consistently_oriented_3d(m, pos),
        //  both rays non-degenerate
    ensures
        ray_mesh_crossing_count(m, pos, p, dir1) % 2
            == ray_mesh_crossing_count(m, pos, p, dir2) % 2,
```
This is the deep theorem: parity is independent of ray direction for a closed oriented manifold. This is a topological invariant (Jordan-Brouwer separation theorem for polyhedral surfaces). May need to be taken as an axiom with citation, or proved via a combinatorial argument about how crossings change as the ray rotates.

### Dependencies
- verus-geometry: `ray_hits_triangle`, `orient3d`, `ray_hits_aabb3` (for acceleration)
- verus-topology: `is_topological_sphere`, `consistently_oriented_3d`, face traversal
- For triangle meshes: `all_faces_triangles` (already exists). For general meshes: need face triangulation first.

---

## 3. Classical Euler Operators (MVFS / MEV / MEF)

**Priority:** High — BREP construction vocabulary
**Difficulty:** Medium-Hard
**File:** `euler_ops.rs` (extend existing)

### Problem

The current ops (split_edge, split_face, flip_edge, collapse_edge) are mesh refinement operations. The classical Euler operators are the construction vocabulary for BREP — how you build topology incrementally. An extrude operation is: MEV (extend edges) + MEF (cap faces). A revolve is: repeated MEV + MEF around an axis.

### What's needed

#### 3.1 MVFS — Make Vertex, Face, Shell
Creates a degenerate "point shell": 1 vertex, 1 face, 0 edges, 0 half-edges.
```rust
fn mvfs(mesh: &mut Mesh) -> (v: usize, f: usize)
    ensures structurally_valid(mesh),
```
**Note:** This is the only operator that creates topology from nothing. All others modify existing topology.

**Design question:** Our current `structurally_valid` requires `half_edge_count >= 3 * face_count`, which fails for a point shell (0 half-edges, 1 face). We may need a weaker `structurally_valid_partial` for construction intermediates, or redefine the face count lower bound.

#### 3.2 MEV — Make Edge, Vertex
Splits a vertex by inserting a new edge. Given vertex v in face f, creates a new vertex v' and edge (v, v').
```rust
fn mev(mesh: &mut Mesh, v: usize, f: usize) -> Result<(usize, usize), EulerError>
    requires structurally_valid(mesh),
    ensures match result { Ok((v_new, e_new)) => structurally_valid(mesh), ... }
```
Preserves chi: +1V, +1E → delta(V-E) = 0.

#### 3.3 KEV — Kill Edge, Vertex (inverse of MEV)
Merges two vertices connected by an edge.
```rust
fn kev(mesh: &mut Mesh, e: usize) -> Result<usize, EulerError>
    requires structurally_valid(mesh),
    ensures structurally_valid(mesh),
```

#### 3.4 MEF — Make Edge, Face
Splits a face by connecting two vertices on its boundary with a new edge.
```rust
fn mef(mesh: &mut Mesh, v1: usize, v2: usize, f: usize) -> Result<(usize, usize), EulerError>
    requires structurally_valid(mesh),
    ensures structurally_valid(mesh),
```
Preserves chi: +1E, +1F → delta(F-E) = 0.

**Note:** `split_face` is essentially MEF but with half-edge IDs instead of vertex+face IDs. MEF is the user-facing API; split_face is the implementation.

#### 3.5 KEF — Kill Edge, Face (inverse of MEF)
Merges two faces by removing a shared edge.

#### 3.6 Inverse round-trip proofs
```rust
proof fn lemma_kev_mev_roundtrip(m: &Mesh, v: usize, f: usize)
    ensures kev(mev(m, v, f).0, ...) ≡ m   //  modulo index renumbering

proof fn lemma_kef_mef_roundtrip(m: &Mesh, v1: usize, v2: usize, f: usize)
    ensures kef(mef(m, v1, v2, f).0, ...) ≡ m
```

### Key challenge

Index management. When we add/remove vertices/edges/faces, all indices shift. The current split_edge appends to the end (simple). KEV/KEF need to remove elements, which either requires tombstones (wasteful), swap-remove (invalidates indices), or a compaction pass. The choice affects proof complexity significantly.

---

## 4. Open Mesh / Boundary Support

**Priority:** High — prerequisite for incremental BREP construction
**Difficulty:** Medium
**Files:** `invariants.rs` (extend), new `boundary.rs`

### Problem

Currently all meshes are closed (every half-edge has a twin, every edge borders exactly two faces). Real CAD construction goes through intermediate open states: you start with a face (open), extrude it (open box), then cap it (closed solid). The classical Euler operators need this.

### What's needed

#### 4.1 Boundary predicates
```rust
///  A half-edge is on the boundary if its twin has the sentinel "boundary face"
pub open spec fn is_boundary_half_edge(m: &Mesh, h: int) -> bool

///  A vertex is on the boundary if any of its outgoing half-edges is boundary
pub open spec fn is_boundary_vertex(m: &Mesh, v: int) -> bool

///  An edge is on the boundary if either of its half-edges is boundary
pub open spec fn is_boundary_edge(m: &Mesh, e: int) -> bool
```

**Design choice:** Use a sentinel face ID (e.g., `usize::MAX`) for boundary, or use `Option<FaceId>` in the half-edge struct. Sentinel is more Verus-friendly (no option unwrapping in specs).

#### 4.2 Boundary loop traversal
```rust
///  Walk along boundary half-edges: from h, follow next until back to h
pub open spec fn boundary_loop(m: &Mesh, h: int) -> Seq<int>

///  All boundary loops of the mesh
pub open spec fn boundary_components(m: &Mesh) -> Seq<Seq<int>>
```

#### 4.3 Relaxed structural validity
```rust
pub open spec fn structurally_valid_with_boundary(m: &Mesh) -> bool {
    //  Same as structurally_valid but:
    //  - twin can be INVALID for boundary half-edges
    //  - edges can have 1 or 2 half-edges (boundary edges have 1)
    //  - vertex manifold: boundary vertices have a fan (not a full cycle)
}
```

#### 4.4 Euler-Poincaré with boundary
For manifolds with boundary: `V - E + F = 2 - 2g - b` where b = number of boundary components.

```rust
pub open spec fn euler_poincare_spec(m: &Mesh) -> bool {
    let chi = vertex_count(m) as int - edge_count(m) as int + face_count(m) as int;
    let b = boundary_component_count(m) as int;
    let g = genus_spec(m);
    chi == 2 - 2 * g - b
}
```

### Key challenge

Almost everything in the current codebase assumes closed meshes. Twin involution, face cycles covering all half-edges, vertex manifold (full cycle) — all need boundary-aware variants. This is a significant refactor of invariants.rs and all downstream proofs.

**Alternative approach:** Keep the closed-mesh invariants as-is and treat open meshes as "under construction" with weaker guarantees. Only require full `structurally_valid` when the mesh is finalized (closed). This avoids rewriting existing proofs.

---

## 5. Geometry-Topology Bridge (verus-brep-kernel)

**Priority:** High for CAD, but large scope
**Difficulty:** Very Hard
**Location:** New crate `verus-brep-kernel`

### Problem

In our current setup, faces are flat (positions at vertices, orientation from orient2d/3d). A real BREP has faces backed by parametric surfaces (planes, cylinders, cones, spheres, tori, NURBS) and edges backed by curves (lines, arcs, conics, splines). This is the fundamental difference between a mesh library and a CAD kernel.

### What's needed

#### 5.1 Surface trait
```rust
pub trait Surface {
    spec fn contains_point(&self, p: Point3<T>) -> bool;
    spec fn normal_at(&self, p: Point3<T>) -> Vec3<T>;
    spec fn parameter_at(&self, p: Point3<T>) -> (T, T);  //  (u, v) params
    exec fn eval(&self, u: T, v: T) -> Point3<T>;
}
```

Implementors: Plane, Cylinder, Cone, Sphere, Torus, BSplineSurface.

#### 5.2 Curve trait
```rust
pub trait Curve {
    spec fn contains_point(&self, p: Point3<T>) -> bool;
    spec fn parameter_at(&self, p: Point3<T>) -> T;
    exec fn eval(&self, t: T) -> Point3<T>;
    exec fn tangent_at(&self, t: T) -> Vec3<T>;
}
```

Implementors: Line, Arc, Conic, BSplineCurve.

#### 5.3 BREP structure
```rust
pub struct BrepFace {
    pub topology: FaceId,           //  link to half-edge mesh
    pub surface: Box<dyn Surface>,  //  geometric backing
    pub outer_loop: LoopId,
    pub inner_loops: Vec<LoopId>,   //  holes
}

pub struct BrepEdge {
    pub topology: EdgeId,
    pub curve: Box<dyn Curve>,
    pub t_start: T,
    pub t_end: T,
}
```

#### 5.4 Geometric consistency specs
```rust
///  Every vertex position lies on all its adjacent surfaces
spec fn vertex_surface_consistency(brep: &Brep) -> bool

///  Every edge curve lies on both adjacent surfaces
spec fn edge_surface_consistency(brep: &Brep) -> bool

///  Face surface normal agrees with topological orientation
spec fn orientation_consistency(brep: &Brep) -> bool
```

### Key challenges

- **Trait objects in Verus:** `Box<dyn Surface>` requires `external_body` or enum dispatch. Verus doesn't support trait objects in specs. Likely need an enum of concrete surface types.
- **Parametric surface intersection:** The hardest problem in computational geometry. Surface-surface intersection curves are generally not analytically representable.
- **Tolerance:** Real BREP kernels use tolerance (points within epsilon are "the same"). Formally verifying tolerant geometry is an open research problem.

### Phased approach
1. **Phase A:** Planar faces + line edges only (verified polygon BREP). This is already close to what we have.
2. **Phase B:** Add cylinder, cone, sphere surfaces + arc edges. Covers most mechanical parts.
3. **Phase C:** NURBS / B-spline. The general case. Much harder to verify.

---

## 6. Boolean Operations

**Priority:** High — the killer CAD feature
**Difficulty:** Very Hard
**Location:** `verus-brep-kernel` or new `verus-cad-ops`

### Problem

Union, intersection, and difference of solids. This is what makes a CAD kernel a CAD kernel. Without booleans, you can't combine shapes.

### What's needed (for the planar/triangulated case)

#### 6.1 Intersection detection
```rust
///  Find all pairs of faces from mesh A and mesh B that intersect
fn find_intersecting_face_pairs(
    a: &Mesh, pos_a: &[Point3<T>],
    b: &Mesh, pos_b: &[Point3<T>],
) -> Vec<(FaceId, FaceId)>
```
Accelerated by AABB trees (verus-geometry has `aabb3_separated`).

#### 6.2 Intersection computation
```rust
///  Compute the intersection curve of two triangles
fn triangle_triangle_intersection(
    a: &Triangle3<T>, b: &Triangle3<T>,
) -> Option<Segment3<T>>
```
verus-geometry has `segment_triangle_intersects_strict` — needs extension to compute the actual intersection segment, not just detect it.

#### 6.3 Point classification
```rust
///  Classify each face of mesh A as inside, outside, or on the boundary of mesh B
fn classify_faces(
    a: &Mesh, pos_a: &[Point3<T>],
    b: &Mesh, pos_b: &[Point3<T>],
) -> Vec<Classification>  //  Inside, Outside, OnBoundary
```
Uses point-in-solid (§2) as the core query.

#### 6.4 Topology reconstruction
```rust
///  Build the result mesh from classified faces
fn boolean_union(a: &Mesh, b: &Mesh, ...) -> Mesh
    ensures structurally_valid(&result) && is_topological_sphere(&result)

fn boolean_intersection(a: &Mesh, b: &Mesh, ...) -> Mesh
fn boolean_difference(a: &Mesh, b: &Mesh, ...) -> Mesh
```

### Key challenges

- **Exact arithmetic:** Boolean operations are notoriously sensitive to floating-point errors. Our `Rational` exact arithmetic is a huge advantage here — no robustness issues.
- **Degeneracies:** Coplanar faces, edges touching vertices, overlapping edges. Each needs careful handling.
- **Topology reconstruction:** After splitting faces along intersection curves and classifying, rebuilding a valid mesh is the hardest part. Need to prove the result satisfies `structurally_valid`.

### Realistic scope

A **verified boolean for convex polyhedra** (all faces planar, all vertices exact rational) is achievable and already useful. General boolean for curved BREP is a multi-year effort even in unverified code.

---

## 7. Delaunay Triangulation

**Priority:** Medium — meshing for CAD faces, strong showcase
**Difficulty:** Medium-Hard
**Files:** New `delaunay.rs` in verus-geometry or verus-topology

### Problem

Converting a planar face (polygon with holes) into a triangle mesh. Essential for rendering, FEA, and as a preprocessing step for many algorithms. The Delaunay property (no point inside any triangle's circumcircle) gives optimal triangle quality.

### What's needed

#### 7.1 Delaunay predicate (already exists!)
verus-geometry has `incircle2d` with full permutation/sign/trichotomy lemmas. This is the core predicate.

#### 7.2 Lawson flip algorithm
```rust
///  Flip edges until the Delaunay criterion holds everywhere
fn lawson_flip(m: &mut Mesh, pos: &[Point2<T>])
    requires structurally_valid(m), all_faces_triangles(m),
    ensures
        structurally_valid(m),
        all_faces_triangles(m),
        is_delaunay(m, pos),  //  no illegal edges
```

**Algorithm:** Maintain a stack of edges to check. For each edge, if the incircle test fails (the opposite vertex of one triangle is inside the circumcircle of the other), flip the edge. Repeat until stack is empty.

Uses: `flip_edge` (already in euler_ops.rs), `incircle2d_sign_exec` (already in verus-geometry runtime).

#### 7.3 Incremental insertion
```rust
///  Insert a point into a Delaunay triangulation
fn insert_point(m: &mut Mesh, pos: &mut Vec<Point2<T>>, p: Point2<T>)
    requires structurally_valid(m), is_delaunay(m, pos),
    ensures structurally_valid(m), is_delaunay(m, pos),
```

**Algorithm:** Locate containing triangle (walk), split it into 3 triangles (split_face × 2), then Lawson flip to restore Delaunay.

#### 7.4 Delaunay spec
```rust
pub open spec fn is_delaunay<T: OrderedField>(m: &Mesh, pos: Seq<Point2<T>>) -> bool {
    forall|e: int| 0 <= e < edge_count(m) ==> {
        //  For each interior edge, the opposite vertex of each adjacent triangle
        //  is NOT inside the circumcircle of the other triangle
        !incircle2d_positive(/* triangle vertices */, /* opposite vertex */)
    }
}
```

### Key challenge

**Termination of Lawson flips.** Classic proof: each flip increases the minimum angle of the triangulation (or equivalently, the number of Delaunay edges monotonically increases). This is a non-trivial termination argument.

**Point location:** Walking to find the containing triangle requires `orient2d` tests and termination proof (at most O(n) steps for a convex domain).

---

## Dependency Graph

```
1. Connectivity preservation  ← standalone, uses existing euler_ops + connectivity
2. Point-in-solid 3D         ← needs face traversal + ray_hits_triangle (both exist)
3. Classical Euler ops        ← needs boundary support (4) for full generality
4. Boundary support           ← refactors invariants.rs
5. BREP kernel                ← needs 3 + 4 + new surface/curve types
6. Boolean operations         ← needs 2 + 5
7. Delaunay triangulation     ← needs incircle (exists) + flip_edge (exists)
```

**Independent tracks that can be parallelized:**
- Track A: 1 → 2 → 6 (connectivity → point-in-solid → booleans)
- Track B: 4 → 3 → 5 (boundary → Euler ops → BREP)
- Track C: 7 (Delaunay, mostly standalone)

---

## Suggested Starting Points

| If you want... | Start with |
|---|---|
| Biggest spec gap closed | §1 Connectivity preservation |
| Most useful new capability | §2 Point-in-solid 3D |
| Best existing-infrastructure leverage | §7 Delaunay (incircle + flip_edge already exist) |
| Foundation for everything else | §4 Boundary support |
| The most ambitious | §6 Boolean operations |
