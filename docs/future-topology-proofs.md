# Future Topology Proof Directions

## Completed
- **Connectivity preservation**: split_edge, split_face, flip_edge all preserve `is_connected`
- **Euler characteristic**: split_edge/split_face/flip_edge preserve χ (in queries.rs)

## In Progress
- **Structural validity preservation** (task #11): Prove split_edge_build, split_face_build, flip_edge_build directly produce `structurally_valid` meshes, removing need for runtime `check_structurally_valid` fallback

## Future Directions

### 3a. Euler ops preserve `is_closed`
- `is_closed` (invariants.rs): every half-edge has a distinct twin
- split_edge adds 2 HEs as twin pair → closed preserved
- split_face adds 2 HEs as twin pair → closed preserved
- flip_edge doesn't add/remove HEs, only rewires twins → closed preserved
- Should be straightforward from the `*_post` specs

### 3b. Connectivity + genus relationship
- Connected mesh with χ=2 on a closed manifold → topological sphere
- Could strengthen `is_topological_sphere` (queries.rs) with connectivity requirement
- Prove: connected + χ=2 + orientable + closed → sphere (classification theorem for surfaces)

### 3c. Orientability preservation
- `check_consistently_oriented_2d/3d` (geometric_checkers.rs) checks orientation
- Prove Euler ops preserve consistent orientation
- Requires geometric mesh layer (geometric_mesh.rs)

### 3d. Face cycle preservation
- `face_representative_cycles` (invariants.rs): each face's HEs form a cycle
- Prove split_edge preserves face cycles (face count unchanged, cycles rerouted through v_new)
- Prove split_face creates two valid cycles from one
- Prove flip_edge produces valid triangle cycles

### 3e. Manifold property preservation
- `vertex_manifold` (invariants.rs): star of each vertex is a topological disk
- Prove Euler ops preserve vertex manifold property
- Most complex of the structural invariants
