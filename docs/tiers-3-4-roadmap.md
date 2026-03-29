# verus-topology Tiers 3–4 Roadmap

## Current State (post Tiers 1a–2b)

**154 verified, 0 errors, 0 assume(false)**

| Module | What's there |
|--------|-------------|
| `invariants.rs` | `structurally_valid` (10 invariants), `is_closed` |
| `construction.rs` | `from_face_cycles`, `tetrahedron` (V=4,E=6,F=4), `cube` (V=8,E=12,F=6) |
| `euler_ops.rs` | `split_edge`, `split_face`, `flip_edge`, `collapse_edge` — all ensure `structurally_valid` |
| `refinement.rs` | `midpoint_subdivide`, `subdivide_n_times`, `lemma_subdivision_preserves_euler` |
| `queries.rs` | `face_degree`, `vertex_degree`, `euler_characteristic`, `all_faces_triangles`, chi preservation lemmas, chi=2 for tet/cube |
| `geometric_mesh.rs` | 2D/3D embedding specs, `face_oriented_ccw_2d`, `consistently_oriented_2d/3d`, `lemma_twin_orientation_flip_2d` |
| `connectivity.rs` | `adjacent_vertices`, `vertex_path`, `is_connected`, `check_connected`, `lemma_adjacent_symmetric` |

---

## Tier 3a: Orientability Checker (2D)

**Goal:** Runtime-check that a 2D-embedded mesh has all faces CCW.

**File:** `geometric_mesh.rs`

### 3a.1 `check_consistently_oriented_2d`
```rust
pub fn check_consistently_oriented_2d<T: OrderedRing>(
    m: &Mesh, pos: &Vec<RuntimePoint2<T>>,
) -> (out: bool)
    requires structurally_valid(m), pos@.len() == vertex_count(m),
    ensures out ==> consistently_oriented_2d(m, pos_to_spec(pos)),
```

**Algorithm:** Iterate faces 0..fcnt. For each face f, read the first 3 vertices of the face cycle (via `face_half_edges[f]` → `.next` → `.next`), compute `orient2d_sign(a, b, c)`, check it's Positive. Return false if any face fails.

**Proof:** Each iteration calls the runtime `orient2d_sign` (from verus-geometry's runtime layer) which ensures `result == orient2d_sign_spec(a@, b@, c@)`. The loop invariant carries `forall|ff| 0 <= ff < f ==> face_oriented_ccw_2d(m, pos_spec, ff)`.

**Dependencies:** verus-geometry runtime orient2d (already exists in `runtime/orient2d.rs`).

### 3a.2 `check_consistently_oriented_3d`
Same pattern but with `orient3d_sign` and an interior point parameter.

---

## Tier 3b: Genus

**Goal:** Define genus for closed surfaces and prove concrete meshes have genus 0.

**File:** `queries.rs`

### 3b.1 Genus spec
```rust
pub open spec fn genus_spec(m: &Mesh) -> int {
    (2 - euler_characteristic_spec(m)) / 2
}
```

Note: this is only meaningful for closed, connected, orientable 2-manifolds where chi = 2 - 2g. For integer division correctness, we need chi to be even; for closed orientable surfaces it always is.

### 3b.2 Concrete genus lemmas
```rust
pub proof fn lemma_tetrahedron_genus_zero(m: &Mesh)
    requires vertex_count(m) == 4, edge_count(m) == 6, face_count(m) == 4,
    ensures genus_spec(m) == 0,

pub proof fn lemma_cube_genus_zero(m: &Mesh)
    requires vertex_count(m) == 8, edge_count(m) == 12, face_count(m) == 6,
    ensures genus_spec(m) == 0,
```

Both are pure arithmetic from chi=2.

### 3b.3 Subdivision preserves genus
```rust
pub proof fn lemma_subdivision_preserves_genus(m: &Mesh)
    requires structurally_valid(m), all_faces_triangles(m),
    ensures genus_spec_from_counts(
        subdivision_vertex_count(m), subdivision_edge_count(m), subdivision_face_count(m)
    ) == genus_spec(m),
```

Follows from `lemma_subdivision_preserves_euler` already in refinement.rs.

---

## Tier 3c: Euler Ops ↔ Euler Preservation (concrete)

**Goal:** Connect the abstract chi preservation lemmas (pure arithmetic) to the actual Euler operations.

**File:** `queries.rs`

### 3c.1 Split edge preserves chi (concrete)
```rust
pub proof fn lemma_split_edge_preserves_euler_concrete(m: &Mesh, e: int)
    requires
        index_bounds(m), 0 <= e < edge_count(m),
        //  overflow guards (same as split_edge_build)
    ensures
        euler_characteristic_spec(&split_edge_build(m, e))
            == euler_characteristic_spec(m),
```

**Proof:** `split_edge_build` ensures V'=V+1, E'=E+1, F'=F. Apply `lemma_split_edge_preserves_euler`.

### 3c.2 Split face preserves chi (concrete)
```rust
pub proof fn lemma_split_face_preserves_euler_concrete(m: &Mesh, h_start: int, h_end: int)
    requires ...
    ensures euler_characteristic_spec(&split_face_build(m, h_start, h_end)->Ok_0)
                == euler_characteristic_spec(m),
```

### 3c.3 Flip edge preserves chi (concrete)
```rust
pub proof fn lemma_flip_edge_preserves_euler_concrete(m: &Mesh, e: int)
    requires ...
    ensures euler_characteristic_spec(&flip_edge_build(m, e))
                == euler_characteristic_spec(m),
```

---

## Tier 3d: Connectivity Preservation Under Euler Ops

**Goal:** Prove that local operations don't disconnect the mesh.

**File:** `connectivity.rs` (new section)

### 3d.1 Split edge preserves connectivity
```rust
pub proof fn lemma_split_edge_preserves_connected(m: &Mesh, e: int)
    requires structurally_valid(m), is_connected(m), 0 <= e < edge_count(m), ...
    ensures is_connected(&split_edge_build(m, e)),
```

**Proof sketch:** Every old vertex path is still valid (vertices preserved, edges only added). The new vertex is adjacent to the two endpoints of the split edge.

### 3d.2 Split face preserves connectivity
Similar — new diagonal only adds edges, never removes.

### 3d.3 Flip edge preserves connectivity
Trickier — edge removal + addition. Needs to show the quad remains connected through the new diagonal.

---

## Tier 4a: Topological Sphere Classification

**Goal:** Define and check "topologically a sphere" for 2-manifold meshes.

**File:** New section in `queries.rs` or new `classification.rs`

### 4a.1 Sphere predicate
```rust
pub open spec fn is_topological_sphere(m: &Mesh) -> bool {
    &&& structurally_valid(m)
    &&& is_closed(m)
    &&& is_connected(m)
    &&& euler_characteristic_spec(m) == 2
}
```

For closed connected orientable 2-manifolds, chi=2 uniquely characterizes the sphere. Our meshes are orientable by construction (consistent face cycles from `from_face_cycles`).

### 4a.2 Exec checker
```rust
pub fn check_topological_sphere(m: &Mesh) -> (out: bool)
    requires structurally_valid(m),
    ensures out ==> is_topological_sphere(m),
```

Calls `check_connected(m)` + `euler_characteristic(m) == 2`. Closedness is free from `structurally_valid`.

### 4a.3 Concrete sphere proofs
```rust
pub proof fn lemma_tetrahedron_is_sphere(m: &Mesh)
    requires
        structurally_valid(m), is_connected(m),
        vertex_count(m) == 4, edge_count(m) == 6, face_count(m) == 4,
    ensures is_topological_sphere(m),

pub proof fn lemma_cube_is_sphere(m: &Mesh)
    requires
        structurally_valid(m), is_connected(m),
        vertex_count(m) == 8, edge_count(m) == 12, face_count(m) == 6,
    ensures is_topological_sphere(m),
```

### 4a.4 Subdivision preserves sphere
```rust
pub proof fn lemma_subdivision_preserves_sphere(m: &Mesh, r: &Mesh)
    requires
        is_topological_sphere(m), all_faces_triangles(m),
        structurally_valid(r),  //  from midpoint_subdivide
        vertex_count(r) == subdivision_vertex_count(m),
        edge_count(r) == subdivision_edge_count(m),
        face_count(r) == subdivision_face_count(m),
        is_connected(r),  //  from connectivity preservation
    ensures is_topological_sphere(r),
```

Combines: chi preservation (already proved) + connectivity + closedness (from structurally_valid).

---

## Tier 4b: Winding Number / Point-in-Mesh (2D)

**Goal:** Determine if a point is inside a 2D mesh boundary using orientation predicates.

**File:** New `winding.rs` or section in `geometric_mesh.rs`

### 4b.1 Edge crossing spec
```rust
///  Does the ray from p rightward cross the edge from→to?
pub open spec fn ray_crosses_edge_2d<T: OrderedField>(
    from: Point2<T>, to: Point2<T>, p: Point2<T>,
) -> bool
```

Standard ray-casting: check if p.y is between from.y and to.y, and the crossing x is > p.x.

### 4b.2 Winding number spec
```rust
///  Sum of signed crossings of all boundary edges.
pub open spec fn winding_number_spec<T: OrderedField>(
    m: &Mesh, pos: Seq<Point2<T>>, p: Point2<T>,
) -> int
```

For a consistently oriented mesh, iterate all half-edges where `face != BOUNDARY`, sum +1/-1 based on upward/downward crossings.

### 4b.3 Point-inside checker
```rust
pub fn check_point_inside_2d<T: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint2<T>>, p: &RuntimePoint2<T>,
) -> (out: bool)
    requires
        structurally_valid(m),
        geometric_embedding_2d(m, pos_to_spec(pos)),
        consistently_oriented_2d(m, pos_to_spec(pos)),
    ensures
        out == (winding_number_spec(m, pos_to_spec(pos), p@) != 0),
```

### 4b.4 Interior/exterior correctness
```rust
pub proof fn lemma_winding_number_parity<T: OrderedField>(
    m: &Mesh, pos: Seq<Point2<T>>, p: Point2<T>,
)
    requires
        is_topological_sphere(m),
        consistently_oriented_2d(m, pos),
        //  p not on any edge
    ensures
        winding_number_spec(m, pos, p) == 0 || winding_number_spec(m, pos, p) == 1,
```

For a simple closed polygon mesh (sphere topology in 2D = simple closed curve), winding number is 0 (outside) or 1 (inside).

---

## Dependency Graph

```
Tier 3a (orientability checker)  ← needs verus-geometry runtime orient2d
Tier 3b (genus)                  ← needs chi=2 lemmas (done)
Tier 3c (euler ops ↔ chi)       ← needs euler_ops specs + chi lemmas (done)
Tier 3d (connectivity preservation) ← needs connectivity + euler_ops

Tier 4a (sphere classification) ← needs 3b (genus) + 2a (closed) + 2b (connected)
Tier 4b (winding number)        ← needs 3a (orientability) + 4a (sphere)
```

**Suggested order:**
1. 3b (genus) — pure arithmetic, trivial
2. 3c (euler ops ↔ chi) — connecting existing pieces
3. 3a (orientability checker) — needs runtime types, moderate
4. 4a (sphere classification) — combines 2a+2b+3b, mostly definitional
5. 3d (connectivity preservation) — hardest of Tier 3, inductive proofs
6. 4b (winding number) — most complex, new algorithms

---

## Estimated Difficulty

| Tier | Items | Difficulty | Notes |
|------|-------|-----------|-------|
| 3b | genus spec + 3 lemmas | Easy | Pure arithmetic |
| 3c | 3 concrete chi lemmas | Easy-Medium | Need to unfold euler_ops specs |
| 3a | 2 exec checkers | Medium | Runtime types, loop invariants |
| 4a | sphere pred + checker + 4 lemmas | Medium | Combines existing pieces |
| 3d | 3 connectivity preservation proofs | Hard | Inductive, need to trace path witnesses through modified mesh |
| 4b | winding number + point-in-mesh | Hard | New algorithm, crossing logic, parity proof |
