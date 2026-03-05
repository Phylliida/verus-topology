use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec3::Vec3;
use verus_geometry::point2::Point2;
use verus_geometry::point3::Point3;
use verus_geometry::orient2d::*;
use verus_geometry::orientation_sign::*;
use verus_geometry::orient3d::*;
use crate::mesh::*;
use crate::invariants::*;
use crate::iteration::*;

verus! {

// =============================================================================
// 7.1 Geometric embedding specs
// =============================================================================

/// A 2D geometric embedding: positions for each vertex + valid mesh.
pub open spec fn geometric_embedding_2d<T: OrderedRing>(
    m: &Mesh,
    positions: Seq<Point2<T>>,
) -> bool {
    positions.len() == vertex_count(m) && structurally_valid(m)
}

/// A 3D geometric embedding: positions for each vertex + valid mesh.
pub open spec fn geometric_embedding_3d<T: OrderedRing>(
    m: &Mesh,
    positions: Seq<Point3<T>>,
) -> bool {
    positions.len() == vertex_count(m) && structurally_valid(m)
}

// =============================================================================
// 7.2 Half-edge position accessors
// =============================================================================

/// Position of the origin vertex of half-edge h (2D).
pub open spec fn he_from_pos_2d<T: Ring>(
    m: &Mesh,
    pos: Seq<Point2<T>>,
    h: int,
) -> Point2<T>
    recommends
        index_bounds(m),
        0 <= h < half_edge_count(m),
        pos.len() == vertex_count(m),
{
    pos[m.half_edges@[h].vertex as int]
}

/// Position of the destination vertex of half-edge h (2D).
/// Destination = origin of next(h).
pub open spec fn he_to_pos_2d<T: Ring>(
    m: &Mesh,
    pos: Seq<Point2<T>>,
    h: int,
) -> Point2<T>
    recommends
        index_bounds(m),
        0 <= h < half_edge_count(m),
        pos.len() == vertex_count(m),
{
    pos[m.half_edges@[m.half_edges@[h].next as int].vertex as int]
}

/// Position of the origin vertex of half-edge h (3D).
pub open spec fn he_from_pos_3d<T: Ring>(
    m: &Mesh,
    pos: Seq<Point3<T>>,
    h: int,
) -> Point3<T>
    recommends
        index_bounds(m),
        0 <= h < half_edge_count(m),
        pos.len() == vertex_count(m),
{
    pos[m.half_edges@[h].vertex as int]
}

/// Position of the destination vertex of half-edge h (3D).
pub open spec fn he_to_pos_3d<T: Ring>(
    m: &Mesh,
    pos: Seq<Point3<T>>,
    h: int,
) -> Point3<T>
    recommends
        index_bounds(m),
        0 <= h < half_edge_count(m),
        pos.len() == vertex_count(m),
{
    pos[m.half_edges@[m.half_edges@[h].next as int].vertex as int]
}

// =============================================================================
// 7.3 Consistent orientation predicate (2D)
// =============================================================================

/// Face f has counter-clockwise orientation in 2D.
/// Uses orient2d on the first three vertices of the face cycle.
pub open spec fn face_oriented_ccw_2d<T: OrderedRing>(
    m: &Mesh,
    pos: Seq<Point2<T>>,
    f: int,
) -> bool
    recommends
        index_bounds(m),
        0 <= f < face_count(m),
        pos.len() == vertex_count(m),
{
    let start = m.face_half_edges@[f] as int;
    let h0 = start;
    let h1 = m.half_edges@[h0].next as int;
    let h2 = m.half_edges@[h1].next as int;
    let a = pos[m.half_edges@[h0].vertex as int];
    let b = pos[m.half_edges@[h1].vertex as int];
    let c = pos[m.half_edges@[h2].vertex as int];
    orient2d_sign(a, b, c) == OrientationSign::Positive
}

/// All faces are oriented counter-clockwise in 2D.
pub open spec fn consistently_oriented_2d<T: OrderedRing>(
    m: &Mesh,
    pos: Seq<Point2<T>>,
) -> bool
    recommends
        geometric_embedding_2d(m, pos),
{
    forall|f: int|
        0 <= f < face_count(m)
            ==> face_oriented_ccw_2d(m, pos, f)
}

// =============================================================================
// 7.4 Twin reverses orientation lemma
// =============================================================================

/// Twin traversal swaps edge direction, so orient2d sign flips.
///
/// For half-edge h with twin t = twin(h):
///   from(h) = to(t) and to(h) = from(t)
///   So for any third point c, orient2d(from(h), to(h), c) and
///   orient2d(from(t), to(t), c) have opposite signs.
///
/// This connects to lemma_orient2d_swap_bc from verus-geometry:
///   orient2d(a, c, b) ≡ -orient2d(a, b, c)
pub proof fn lemma_twin_reverses_edge_direction<T: OrderedRing>(
    m: &Mesh,
    pos: Seq<Point2<T>>,
    h: int,
)
    requires
        geometric_embedding_2d(m, pos),
        0 <= h < half_edge_count(m),
    ensures
        // Twin swaps from/to vertices
        he_from_pos_2d(m, pos, m.half_edges@[h].twin as int)
            == he_to_pos_2d(m, pos, h),
        he_to_pos_2d(m, pos, m.half_edges@[h].twin as int)
            == he_from_pos_2d(m, pos, h),
{
    let t = m.half_edges@[h].twin as int;

    // geometric_embedding_2d implies structurally_valid, which implies
    // shared_edge_orientation_consistency, which implies twin_endpoint_correspondence.
    assert(structurally_valid(m));
    assert(shared_edge_orientation_consistency(m));
    assert(twin_endpoint_correspondence(m));
    assert(twin_endpoint_correspondence_at(m, h));

    // twin_endpoint_correspondence_at(m, h) gives us:
    //   half_edge_from_vertex(m, t) == half_edge_to_vertex(m, h)
    //   half_edge_to_vertex(m, t) == half_edge_from_vertex(m, h)
    //
    // Expanding:
    //   m.half_edges@[t].vertex == m.half_edges@[m.half_edges@[h].next as int].vertex
    //   m.half_edges@[m.half_edges@[t].next as int].vertex == m.half_edges@[h].vertex

    // First ensures: he_from_pos_2d(m, pos, t) == he_to_pos_2d(m, pos, h)
    // LHS = pos[m.half_edges@[t].vertex as int]
    // RHS = pos[m.half_edges@[m.half_edges@[h].next as int].vertex as int]
    // These are equal because half_edge_from_vertex(m, t) == half_edge_to_vertex(m, h)
    assert(m.half_edges@[t].vertex as int
        == m.half_edges@[m.half_edges@[h].next as int].vertex as int);

    // Second ensures: he_to_pos_2d(m, pos, t) == he_from_pos_2d(m, pos, h)
    // LHS = pos[m.half_edges@[m.half_edges@[t].next as int].vertex as int]
    // RHS = pos[m.half_edges@[h].vertex as int]
    // These are equal because half_edge_to_vertex(m, t) == half_edge_from_vertex(m, h)
    assert(m.half_edges@[m.half_edges@[t].next as int].vertex as int
        == m.half_edges@[h].vertex as int);
}

// =============================================================================
// 7.4b Twin orientation flip (2D)
// =============================================================================

/// Twin traversal flips the orient2d sign for any third point p.
///
/// Since twin swaps from/to, orient2d(from(twin), to(twin), p)
/// has opposite sign to orient2d(from(h), to(h), p).
pub proof fn lemma_twin_orientation_flip_2d<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point2<T>>, h: int, p: Point2<T>,
)
    requires
        geometric_embedding_2d(m, pos),
        0 <= h < half_edge_count(m),
    ensures
        orient2d_sign(
            he_from_pos_2d(m, pos, m.half_edges@[h].twin as int),
            he_to_pos_2d(m, pos, m.half_edges@[h].twin as int),
            p,
        ) == match orient2d_sign(
            he_from_pos_2d(m, pos, h),
            he_to_pos_2d(m, pos, h),
            p,
        ) {
            OrientationSign::Positive => OrientationSign::Negative,
            OrientationSign::Negative => OrientationSign::Positive,
            OrientationSign::Zero => OrientationSign::Zero,
        },
{
    // Twin swaps from/to
    lemma_twin_reverses_edge_direction(m, pos, h);
    let from_h = he_from_pos_2d(m, pos, h);
    let to_h = he_to_pos_2d(m, pos, h);
    let t = m.half_edges@[h].twin as int;

    // from(twin) == to(h), to(twin) == from(h)
    assert(he_from_pos_2d(m, pos, t) == to_h);
    assert(he_to_pos_2d(m, pos, t) == from_h);

    // orient2d_sign(to_h, from_h, p) flips orient2d_sign(from_h, to_h, p)
    lemma_orient2d_sign_swap_ab::<T>(from_h, to_h, p);
}

// =============================================================================
// 7.5 Face outward normal (3D)
// =============================================================================

/// Face f has an outward-pointing normal with respect to an interior point.
/// The face normal (computed from the first 3 vertices) points away from
/// the interior, meaning orient3d(v0, v1, v2, interior) is negative
/// (interior is below the plane of the face).
pub open spec fn face_outward_normal_3d<T: OrderedRing>(
    m: &Mesh,
    pos: Seq<Point3<T>>,
    f: int,
    interior: Point3<T>,
) -> bool
    recommends
        index_bounds(m),
        0 <= f < face_count(m),
        pos.len() == vertex_count(m),
{
    let start = m.face_half_edges@[f] as int;
    let h0 = start;
    let h1 = m.half_edges@[h0].next as int;
    let h2 = m.half_edges@[h1].next as int;
    let a = pos[m.half_edges@[h0].vertex as int];
    let b = pos[m.half_edges@[h1].vertex as int];
    let c = pos[m.half_edges@[h2].vertex as int];
    orient3d_sign(a, b, c, interior) == OrientationSign::Negative
}

/// All faces have outward-pointing normals (closed, consistently oriented 3D mesh).
pub open spec fn consistently_oriented_3d<T: OrderedRing>(
    m: &Mesh,
    pos: Seq<Point3<T>>,
    interior: Point3<T>,
) -> bool
    recommends
        geometric_embedding_3d(m, pos),
{
    forall|f: int|
        0 <= f < face_count(m)
            ==> face_outward_normal_3d(m, pos, f, interior)
}

} // verus!
