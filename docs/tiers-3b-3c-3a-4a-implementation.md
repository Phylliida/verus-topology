# Plan: verus-topology Tiers 3b → 3c → 3a → 4a

## Context
Tiers 1a–2b are complete (154 verified, 0 errors, 0 assume(false)). This plan implements the next four tiers from `verus-topology/docs/tiers-3-4-roadmap.md`, following the suggested order: 3b (genus) → 3c (Euler ops ↔ chi) → 3a (orientability checker) → 4a (sphere classification). Tiers 3d (connectivity preservation) and 4b (winding number) are deferred as they're substantially harder.

---

## Step 1: Tier 3b — Genus (queries.rs)

**File:** `verus-topology/src/queries.rs` — append after `lemma_cube_euler` (line 457)

Add `use crate::refinement::*;` at top of file (for `subdivision_*_count`, `lemma_subdivision_preserves_euler`).

### 1a. Specs
```rust
pub open spec fn genus_spec(m: &Mesh) -> int {
    (2 - euler_characteristic_spec(m)) / 2
}

/// Genus from raw V, E, F counts (needed for subdivision where counts are formulas, not a Mesh).
pub open spec fn genus_from_counts_spec(v: int, e: int, f: int) -> int {
    (2 - (v - e + f)) / 2
}
```

### 1b. Concrete genus lemmas (empty body — Z3 auto-closes)
```rust
pub proof fn lemma_tetrahedron_genus_zero(m: &Mesh)
    requires vertex_count(m) == 4, edge_count(m) == 6, face_count(m) == 4,
    ensures genus_spec(m) == 0,
{ }  // (2 - (4-6+4)) / 2 = 0

pub proof fn lemma_cube_genus_zero(m: &Mesh)
    requires vertex_count(m) == 8, edge_count(m) == 12, face_count(m) == 6,
    ensures genus_spec(m) == 0,
{ }  // (2 - (8-12+6)) / 2 = 0
```

### 1c. Subdivision preserves genus
```rust
pub proof fn lemma_subdivision_preserves_genus(m: &Mesh)
    requires structurally_valid(m), all_faces_triangles(m),
    ensures genus_from_counts_spec(
        subdivision_vertex_count(m), subdivision_edge_count(m), subdivision_face_count(m),
    ) == genus_spec(m),
{
    lemma_subdivision_preserves_euler(m);
    // Z3 sees: sub_V - sub_E + sub_F == chi(m), so both genus expressions use same chi.
}
```

**rlimit risk:** None. Pure integer arithmetic.

---

## Step 2: Tier 3c — Concrete Euler Preservation (queries.rs)

**File:** `verus-topology/src/queries.rs` — append after genus section

These are thin bridge lemmas. The `_build` functions in `euler_ops.rs` are exec, not spec, so we can't reference them in ensures. Instead, these take two meshes `m` (before) and `r` (after) with count postconditions matching the exec ensures — callers invoke them after a successful Euler op.

```rust
pub proof fn lemma_split_edge_preserves_euler_concrete(m: &Mesh, r: &Mesh)
    requires
        vertex_count(r) == vertex_count(m) + 1,
        edge_count(r) == edge_count(m) + 1,
        face_count(r) == face_count(m),
    ensures euler_characteristic_spec(r) == euler_characteristic_spec(m),
{
    lemma_split_edge_preserves_euler(m, r);
}

pub proof fn lemma_split_face_preserves_euler_concrete(m: &Mesh, r: &Mesh)
    requires
        vertex_count(r) == vertex_count(m),
        edge_count(r) == edge_count(m) + 1,
        face_count(r) == face_count(m) + 1,
    ensures euler_characteristic_spec(r) == euler_characteristic_spec(m),
{
    lemma_split_face_preserves_euler(m, r);
}

pub proof fn lemma_flip_edge_preserves_euler_concrete(m: &Mesh, r: &Mesh)
    requires
        vertex_count(r) == vertex_count(m),
        edge_count(r) == edge_count(m),
        face_count(r) == face_count(m),
    ensures euler_characteristic_spec(r) == euler_characteristic_spec(m),
{
    lemma_flip_edge_preserves_euler(m, r);
}
```

**Note:** These have identical requires to the existing abstract lemmas. Their value is API clarity — they document the "apply after exec Euler op" pattern and will be the natural search result.

**rlimit risk:** None. Direct delegation.

---

## Step 3: Tier 3a — Orientability Checker (new file)

**New file:** `verus-topology/src/geometric_checkers.rs`
**Modify:** `verus-topology/src/lib.rs` — add `#[cfg(verus_keep_ghost)] pub mod geometric_checkers;`

### 3a. Helper specs
```rust
pub open spec fn pos_view_2d(pos: &Vec<RuntimePoint2>) -> Seq<Point2<RationalModel>> {
    pos@.map(|_i: int, p: RuntimePoint2| p@)
}

pub open spec fn pos_view_3d(pos: &Vec<RuntimePoint3>) -> Seq<Point3<RationalModel>> {
    pos@.map(|_i: int, p: RuntimePoint3| p@)
}

pub open spec fn positions_wf_2d(pos: &Vec<RuntimePoint2>) -> bool {
    forall|i: int| 0 <= i < pos@.len() ==> pos@[i].wf_spec()
}

pub open spec fn positions_wf_3d(pos: &Vec<RuntimePoint3>) -> bool {
    forall|i: int| 0 <= i < pos@.len() ==> pos@[i].wf_spec()
}
```

### 3b. 2D checker
```rust
pub fn check_consistently_oriented_2d(m: &Mesh, pos: &Vec<RuntimePoint2>) -> (out: bool)
    requires
        structurally_valid(m),
        pos@.len() == vertex_count(m),
        positions_wf_2d(pos),
    ensures
        out ==> consistently_oriented_2d::<RationalModel>(m, pos_view_2d(pos)),
```

**Algorithm:** `while f < fcnt` loop. Each iteration:
1. Read `h0 = face_half_edges[f]`, `h1 = half_edges[h0].next`, `h2 = half_edges[h1].next`
2. Read vertex indices `v0, v1, v2` from the half-edges
3. Call `orient2d_sign_exec(&pos[v0], &pos[v1], &pos[v2])`
4. If not Positive, return false

**Loop invariant:** `forall|ff: int| 0 <= ff < f ==> face_oriented_ccw_2d::<RationalModel>(m, pos_view_2d(pos), ff)`

### 3c. 3D checker
Same pattern but calls `orient3d_sign_exec(a, b, c, interior)` and checks for `Negative`.

**Dependencies:**
- `orient2d_sign_exec` — `verus-geometry/src/runtime/classification.rs:69`
- `orient3d_sign_exec` — `verus-geometry/src/runtime/classification.rs:97`
- `RuntimePoint2` — `verus-geometry/src/runtime/point2.rs`
- `RuntimePoint3` — `verus-geometry/src/runtime/point3.rs`

**rlimit risk:** Low. Simple loop, one function call per iteration.

---

## Step 4: Tier 4a — Sphere Classification (queries.rs)

**File:** `verus-topology/src/queries.rs` — append after Tier 3c section

Add `use crate::connectivity::*;` at top of file (for `is_connected`, `check_connected`).

### 4a. Spec
```rust
pub open spec fn is_topological_sphere(m: &Mesh) -> bool {
    &&& structurally_valid(m)
    &&& is_closed(m)
    &&& is_connected(m)
    &&& euler_characteristic_spec(m) == 2
}
```

### 4b. Exec checker
```rust
pub fn check_topological_sphere(m: &Mesh) -> (out: bool)
    requires structurally_valid(m),
    ensures out ==> is_topological_sphere(m),
{
    proof { lemma_structurally_valid_is_closed(m); }
    let connected = check_connected(m);
    if !connected { return false; }

    let vcnt = m.vertex_half_edges.len();
    let ecnt = m.edge_half_edges.len();
    let fcnt = m.face_half_edges.len();
    // Overflow guards
    if vcnt >= isize::MAX as usize { return false; }
    if ecnt >= isize::MAX as usize { return false; }
    if fcnt >= isize::MAX as usize { return false; }
    let v = vcnt as isize;
    let e = ecnt as isize;
    let f = fcnt as isize;
    let ve = v - e;
    if ve > 0 && f > isize::MAX - ve { return false; }
    let chi = euler_characteristic(m);
    chi == 2
}
```

### 4c. Concrete sphere proofs
```rust
pub proof fn lemma_tetrahedron_is_sphere(m: &Mesh)
    requires structurally_valid(m), is_connected(m),
        vertex_count(m) == 4, edge_count(m) == 6, face_count(m) == 4,
    ensures is_topological_sphere(m),
{
    lemma_structurally_valid_is_closed(m);
    lemma_tetrahedron_euler(m);
}

pub proof fn lemma_cube_is_sphere(m: &Mesh)
    requires structurally_valid(m), is_connected(m),
        vertex_count(m) == 8, edge_count(m) == 12, face_count(m) == 6,
    ensures is_topological_sphere(m),
{
    lemma_structurally_valid_is_closed(m);
    lemma_cube_euler(m);
}
```

### 4d. Subdivision preserves sphere
```rust
pub proof fn lemma_subdivision_preserves_sphere(m: &Mesh, r: &Mesh)
    requires
        is_topological_sphere(m), all_faces_triangles(m),
        structurally_valid(r), is_connected(r),
        vertex_count(r) == subdivision_vertex_count(m),
        edge_count(r) == subdivision_edge_count(m),
        face_count(r) == subdivision_face_count(m),
    ensures is_topological_sphere(r),
{
    lemma_structurally_valid_is_closed(r);
    lemma_subdivision_preserves_euler(m);
}
```

**rlimit risk:** Low. Straightforward integer overflow reasoning.

---

## Implementation Order

```
Step 1 (3b: genus)     → queries.rs, ~25 lines, no deps
Step 2 (3c: concrete)  → queries.rs, ~30 lines, no deps
Step 3 (3a: orient)    → new geometric_checkers.rs + lib.rs, ~120 lines
Step 4 (4a: sphere)    → queries.rs, ~60 lines, needs connectivity import
```

Steps 1-2 can be done together (same file, append sequentially). Step 3 is independent. Step 4 needs Steps 1 complete (for genus context) but mainly needs existing infrastructure.

## Verification

After each step: `cd verus-topology && bash scripts/check.sh`

Expected final count: ~170+ verified (up from 154), 0 errors, 0 assume(false).

## Files Modified

| File | Change |
|------|--------|
| `verus-topology/src/queries.rs` | Add imports + genus specs/lemmas + concrete Euler lemmas + sphere predicate/checker/proofs |
| `verus-topology/src/geometric_checkers.rs` | **NEW**: pos_view helpers + check_consistently_oriented_2d/3d |
| `verus-topology/src/lib.rs` | Add `pub mod geometric_checkers;` |
