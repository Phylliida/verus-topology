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
    let hcnt = m.half_edges.len();
    let vcnt = m.vertex_half_edges.len();
    let mut f: usize = 0;

    while f < fcnt
        invariant
            index_bounds(m),
            pos@.len() == vertex_count(m),
            positions_wf_2d(pos),
            0 <= f <= fcnt,
            fcnt == face_count(m),
            hcnt == half_edge_count(m),
            vcnt == vertex_count(m),
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

        if sign != OrientationSign::Positive {
            return false;
        }

        proof {
            let pv = pos_view_2d(pos);
            // Step 1: exec postcondition gives us the sign
            assert(sign == orient2d_sign::<RationalModel>(
                pos@[v0 as int]@, pos@[v1 as int]@, pos@[v2 as int]@));
            // Step 2: combined with sign == Positive
            assert(orient2d_sign::<RationalModel>(
                pos@[v0 as int]@, pos@[v1 as int]@, pos@[v2 as int]@)
                == OrientationSign::Positive);
            // Step 3: Seq::new unfolding
            assert(pv[v0 as int] == pos@[v0 as int]@);
            assert(pv[v1 as int] == pos@[v1 as int]@);
            assert(pv[v2 as int] == pos@[v2 as int]@);
            // Step 4: substitution into orient2d_sign
            assert(orient2d_sign::<RationalModel>(
                pv[v0 as int], pv[v1 as int], pv[v2 as int])
                == OrientationSign::Positive);
            // Step 5: face_oriented_ccw_2d unfolding
            assert(face_oriented_ccw_2d::<RationalModel>(m, pv, f as int));
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
    let hcnt = m.half_edges.len();
    let vcnt = m.vertex_half_edges.len();
    let mut f: usize = 0;

    while f < fcnt
        invariant
            index_bounds(m),
            pos@.len() == vertex_count(m),
            positions_wf_3d(pos),
            interior.wf_spec(),
            0 <= f <= fcnt,
            fcnt == face_count(m),
            hcnt == half_edge_count(m),
            vcnt == vertex_count(m),
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

        if sign != OrientationSign::Negative {
            return false;
        }

        proof {
            let pv = pos_view_3d(pos);
            assert(sign == orient3d_sign::<RationalModel>(
                pos@[v0 as int]@, pos@[v1 as int]@, pos@[v2 as int]@, interior@));
            assert(orient3d_sign::<RationalModel>(
                pos@[v0 as int]@, pos@[v1 as int]@, pos@[v2 as int]@, interior@)
                == OrientationSign::Negative);
            assert(pv[v0 as int] == pos@[v0 as int]@);
            assert(pv[v1 as int] == pos@[v1 as int]@);
            assert(pv[v2 as int] == pos@[v2 as int]@);
            assert(orient3d_sign::<RationalModel>(
                pv[v0 as int], pv[v1 as int], pv[v2 as int], interior@)
                == OrientationSign::Negative);
            assert(face_outward_normal_3d::<RationalModel>(m, pv, f as int, interior@));
        }

        f = f + 1;
    }

    true
}

} // verus!
