use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec3::Vec3;
use verus_geometry::point2::Point2;
use verus_geometry::point3::Point3;
use verus_geometry::orient2d::*;
use verus_geometry::orient3d::*;
use verus_geometry::orientation_sign::*;
use verus_geometry::runtime::point2::RuntimePoint2;
use verus_geometry::runtime::point3::RuntimePoint3;
use verus_geometry::runtime::classification::{orient2d_sign_exec, orient3d_sign_exec};
use verus_geometry::runtime::RationalModel;
use crate::mesh::*;
use crate::invariants::*;
use crate::geometric_mesh::*;

verus! {

// =============================================================================
// Position view helpers
// =============================================================================

/// Convert runtime 2D positions to spec positions.
pub open spec fn pos_view_2d(pos: &Vec<RuntimePoint2>) -> Seq<Point2<RationalModel>> {
    Seq::new(pos@.len(), |i: int| pos@[i]@)
}

/// Convert runtime 3D positions to spec positions.
pub open spec fn pos_view_3d(pos: &Vec<RuntimePoint3>) -> Seq<Point3<RationalModel>> {
    Seq::new(pos@.len(), |i: int| pos@[i]@)
}

/// All 2D positions have valid internal state.
pub open spec fn positions_wf_2d(pos: &Vec<RuntimePoint2>) -> bool {
    forall|i: int| 0 <= i < pos@.len() ==> (#[trigger] pos@[i]).wf_spec()
}

/// All 3D positions have valid internal state.
pub open spec fn positions_wf_3d(pos: &Vec<RuntimePoint3>) -> bool {
    forall|i: int| 0 <= i < pos@.len() ==> (#[trigger] pos@[i]).wf_spec()
}

// =============================================================================
// Proof helpers (isolated to reduce Z3 context in loops)
// =============================================================================

/// Bridge: orient2d_sign_exec result == Positive implies face_oriented_ccw_2d.
proof fn lemma_orient2d_positive_implies_face_ccw(
    m: &Mesh, pos: &Vec<RuntimePoint2>,
    f: int, v0: int, v1: int, v2: int,
)
    requires
        index_bounds(m),
        0 <= f < face_count(m),
        pos@.len() == vertex_count(m),
        0 <= v0 < vertex_count(m),
        0 <= v1 < vertex_count(m),
        0 <= v2 < vertex_count(m),
        m.half_edges@[m.face_half_edges@[f] as int].vertex as int == v0,
        m.half_edges@[m.half_edges@[m.face_half_edges@[f] as int].next as int].vertex as int == v1,
        m.half_edges@[m.half_edges@[m.half_edges@[m.face_half_edges@[f] as int].next as int].next as int].vertex as int == v2,
        orient2d_sign::<RationalModel>(pos@[v0]@, pos@[v1]@, pos@[v2]@)
            == OrientationSign::Positive,
    ensures
        face_oriented_ccw_2d::<RationalModel>(m, pos_view_2d(pos), f),
{
    let pv = pos_view_2d(pos);
    assert(pv[v0] == pos@[v0]@);
    assert(pv[v1] == pos@[v1]@);
    assert(pv[v2] == pos@[v2]@);
}

/// Bridge: orient3d_sign_exec result == Negative implies face_outward_normal_3d.
proof fn lemma_orient3d_negative_implies_face_outward(
    m: &Mesh, pos: &Vec<RuntimePoint3>,
    f: int, v0: int, v1: int, v2: int,
    interior: Point3<RationalModel>,
)
    requires
        index_bounds(m),
        0 <= f < face_count(m),
        pos@.len() == vertex_count(m),
        0 <= v0 < vertex_count(m),
        0 <= v1 < vertex_count(m),
        0 <= v2 < vertex_count(m),
        m.half_edges@[m.face_half_edges@[f] as int].vertex as int == v0,
        m.half_edges@[m.half_edges@[m.face_half_edges@[f] as int].next as int].vertex as int == v1,
        m.half_edges@[m.half_edges@[m.half_edges@[m.face_half_edges@[f] as int].next as int].next as int].vertex as int == v2,
        orient3d_sign::<RationalModel>(pos@[v0]@, pos@[v1]@, pos@[v2]@, interior)
            == OrientationSign::Negative,
    ensures
        face_outward_normal_3d::<RationalModel>(m, pos_view_3d(pos), f, interior),
{
    let pv = pos_view_3d(pos);
    assert(pv[v0] == pos@[v0]@);
    assert(pv[v1] == pos@[v1]@);
    assert(pv[v2] == pos@[v2]@);
}

// =============================================================================
// 2D consistent orientation checker
// =============================================================================

/// Check that all faces are oriented counter-clockwise in 2D.
pub fn check_consistently_oriented_2d(m: &Mesh, pos: &Vec<RuntimePoint2>) -> (out: bool)
    requires
        structurally_valid(m),
        pos@.len() == vertex_count(m),
        positions_wf_2d(pos),
    ensures
        out ==> consistently_oriented_2d::<RationalModel>(m, pos_view_2d(pos)),
{
    proof { assert(index_bounds(m)); }
    let fcnt = m.face_half_edges.len();
    let mut f: usize = 0;

    while f < fcnt
        invariant
            index_bounds(m),
            pos@.len() == vertex_count(m),
            0 <= f <= fcnt,
            fcnt == face_count(m),
            positions_wf_2d(pos),
            forall|ff: int| 0 <= ff < f as int
                ==> face_oriented_ccw_2d::<RationalModel>(m, pos_view_2d(pos), ff),
        decreases fcnt - f,
    {
        let h0 = m.face_half_edges[f];
        let h1 = m.half_edges[h0].next;
        let h2 = m.half_edges[h1].next;
        let v0 = m.half_edges[h0].vertex;
        let v1 = m.half_edges[h1].vertex;
        let v2 = m.half_edges[h2].vertex;

        let sign = orient2d_sign_exec(&pos[v0], &pos[v1], &pos[v2]);

        match sign {
            OrientationSign::Positive => {
                proof {
                    lemma_orient2d_positive_implies_face_ccw(
                        m, pos, f as int, v0 as int, v1 as int, v2 as int);
                }
            }
            _ => { return false; }
        }

        f = f + 1;
    }

    true
}

// =============================================================================
// 3D consistent orientation checker
// =============================================================================

/// Check that all faces have outward-pointing normals (interior point below each face plane).
pub fn check_consistently_oriented_3d(
    m: &Mesh,
    pos: &Vec<RuntimePoint3>,
    interior: &RuntimePoint3,
) -> (out: bool)
    requires
        structurally_valid(m),
        pos@.len() == vertex_count(m),
        positions_wf_3d(pos),
        interior.wf_spec(),
    ensures
        out ==> consistently_oriented_3d::<RationalModel>(m, pos_view_3d(pos), interior@),
{
    proof { assert(index_bounds(m)); }
    let fcnt = m.face_half_edges.len();
    let mut f: usize = 0;

    while f < fcnt
        invariant
            index_bounds(m),
            pos@.len() == vertex_count(m),
            positions_wf_3d(pos),
            interior.wf_spec(),
            0 <= f <= fcnt,
            fcnt == face_count(m),
            forall|ff: int| 0 <= ff < f as int
                ==> face_outward_normal_3d::<RationalModel>(m, pos_view_3d(pos), ff, interior@),
        decreases fcnt - f,
    {
        let h0 = m.face_half_edges[f];
        let h1 = m.half_edges[h0].next;
        let h2 = m.half_edges[h1].next;
        let v0 = m.half_edges[h0].vertex;
        let v1 = m.half_edges[h1].vertex;
        let v2 = m.half_edges[h2].vertex;

        let sign = orient3d_sign_exec(&pos[v0], &pos[v1], &pos[v2], interior);

        match sign {
            OrientationSign::Negative => {
                proof {
                    lemma_orient3d_negative_implies_face_outward(
                        m, pos, f as int, v0 as int, v1 as int, v2 as int, interior@);
                }
            }
            _ => { return false; }
        }

        f = f + 1;
    }

    true
}

} // verus!
