use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec3::Vec3;
use verus_geometry::point2::Point2;
use verus_geometry::point3::Point3;
use verus_geometry::orient2d::*;
use verus_geometry::orient3d::*;
use verus_geometry::orientation_sign::*;
use verus_geometry::incircle::*;
use verus_geometry::delaunay::*;
use verus_geometry::convex_hull_3d::*;
use verus_geometry::runtime::point2::RuntimePoint2;
use verus_geometry::runtime::point3::RuntimePoint3;
use verus_geometry::runtime::classification::{
    orient2d_sign_exec, orient3d_sign_exec, incircle2d_sign_exec,
};

use crate::mesh::*;
use crate::invariants::*;
use crate::geometric_mesh::*;

verus! {

//  =============================================================================
//  Position view helpers
//  =============================================================================

///  Convert runtime 2D positions to spec positions.
pub open spec fn pos_view_2d<R: RuntimeRingOps<V>, V: OrderedField>(pos: &Vec<RuntimePoint2<R, V>>) -> Seq<Point2<V>> {
    Seq::new(pos@.len(), |i: int| pos@[i].model@)
}

///  Convert runtime 3D positions to spec positions.
pub open spec fn pos_view_3d<R: RuntimeRingOps<V>, V: OrderedField>(pos: &Vec<RuntimePoint3<R, V>>) -> Seq<Point3<V>> {
    Seq::new(pos@.len(), |i: int| pos@[i].model@)
}

///  All 2D positions have valid internal state.
pub open spec fn positions_wf_2d<R: RuntimeRingOps<V>, V: OrderedField>(pos: &Vec<RuntimePoint2<R, V>>) -> bool {
    forall|i: int| 0 <= i < pos@.len() ==> (#[trigger] pos@[i]).wf_spec()
}

///  All 3D positions have valid internal state.
pub open spec fn positions_wf_3d<R: RuntimeRingOps<V>, V: OrderedField>(pos: &Vec<RuntimePoint3<R, V>>) -> bool {
    forall|i: int| 0 <= i < pos@.len() ==> (#[trigger] pos@[i]).wf_spec()
}

//  =============================================================================
//  Proof helpers (isolated to reduce Z3 context in loops)
//  =============================================================================

///  Bridge: orient2d_sign_exec result == Positive implies face_oriented_ccw_2d.
proof fn lemma_orient2d_positive_implies_face_ccw<R: RuntimeRingOps<V>, V: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint2<R, V>>,
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
        orient2d_sign::<V>(pos@[v0].model@, pos@[v1].model@, pos@[v2].model@)
            == OrientationSign::Positive,
    ensures
        face_oriented_ccw_2d::<V>(m, pos_view_2d(pos), f),
{
    let pv = pos_view_2d(pos);
    assert(pv[v0] == pos@[v0].model@);
    assert(pv[v1] == pos@[v1].model@);
    assert(pv[v2] == pos@[v2].model@);
}

///  Bridge: orient3d_sign_exec result == Negative implies face_outward_normal_3d.
proof fn lemma_orient3d_negative_implies_face_outward<R: RuntimeRingOps<V>, V: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint3<R, V>>,
    f: int, v0: int, v1: int, v2: int,
    interior: Point3<V>,
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
        orient3d_sign::<V>(pos@[v0].model@, pos@[v1].model@, pos@[v2].model@, interior)
            == OrientationSign::Negative,
    ensures
        face_outward_normal_3d::<V>(m, pos_view_3d(pos), f, interior),
{
    let pv = pos_view_3d(pos);
    assert(pv[v0] == pos@[v0].model@);
    assert(pv[v1] == pos@[v1].model@);
    assert(pv[v2] == pos@[v2].model@);
}

//  =============================================================================
//  2D consistent orientation checker
//  =============================================================================

///  Check that all faces are oriented counter-clockwise in 2D.
pub fn check_consistently_oriented_2d<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(m: &Mesh, pos: &Vec<RuntimePoint2<R, V>>) -> (out: bool)
    requires
        structurally_valid(m),
        pos@.len() == vertex_count(m),
        positions_wf_2d(pos),
    ensures
        out ==> consistently_oriented_2d::<V>(m, pos_view_2d(pos)),
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
                ==> face_oriented_ccw_2d::<V>(m, pos_view_2d(pos), ff),
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

//  =============================================================================
//  3D consistent orientation checker
//  =============================================================================

///  Check that all faces have outward-pointing normals (interior point below each face plane).
pub fn check_consistently_oriented_3d<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    m: &Mesh,
    pos: &Vec<RuntimePoint3<R, V>>,
    interior: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires
        structurally_valid(m),
        pos@.len() == vertex_count(m),
        positions_wf_3d(pos),
        interior.wf_spec(),
    ensures
        out ==> consistently_oriented_3d::<V>(m, pos_view_3d(pos), interior.model@),
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
                ==> face_outward_normal_3d::<V>(m, pos_view_3d(pos), ff, interior.model@),
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
                        m, pos, f as int, v0 as int, v1 as int, v2 as int, interior.model@);
                }
            }
            _ => { return false; }
        }

        f = f + 1;
    }

    true
}

//  =============================================================================
//  Proof helper: incircle sign bridge for Delaunay checker
//  =============================================================================

///  Bridge: incircle2d_sign_exec result != Positive implies edge_delaunay_2d.
pub proof fn lemma_incircle_not_positive_implies_edge_delaunay<R: RuntimeRingOps<V>, V: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint2<R, V>>,
    e: int,
    va: int, vb: int, vc: int, vd: int,
)
    requires
        index_bounds(m),
        0 <= e < edge_count(m),
        pos@.len() == vertex_count(m),
        0 <= va < vertex_count(m),
        0 <= vb < vertex_count(m),
        0 <= vc < vertex_count(m),
        0 <= vd < vertex_count(m),
        //  The 4 vertices match the edge diamond
        m.half_edges@[m.edge_half_edges@[e] as int].vertex as int == va,
        m.half_edges@[m.half_edges@[m.edge_half_edges@[e] as int].next as int].vertex as int == vb,
        m.half_edges@[m.half_edges@[m.half_edges@[m.edge_half_edges@[e] as int].next as int].next as int].vertex as int == vc,
        ({
            let t = m.half_edges@[m.edge_half_edges@[e] as int].twin as int;
            m.half_edges@[m.half_edges@[m.half_edges@[t].next as int].next as int].vertex as int == vd
        }),
        //  Sign is not Positive
        incircle2d_sign::<V>(pos@[va].model@, pos@[vb].model@, pos@[vc].model@, pos@[vd].model@)
            != OrientationSign::Positive,
    ensures
        edge_delaunay_2d::<V>(m, pos_view_2d(pos), e),
{
    let pv = pos_view_2d(pos);
    assert(pv[va] == pos@[va].model@);
    assert(pv[vb] == pos@[vb].model@);
    assert(pv[vc] == pos@[vc].model@);
    assert(pv[vd] == pos@[vd].model@);
}

///  Bridge: incircle2d_sign_exec result == Positive implies NOT edge_delaunay_2d.
///  Converse of lemma_incircle_not_positive_implies_edge_delaunay.
pub proof fn lemma_incircle_positive_implies_not_edge_delaunay<R: RuntimeRingOps<V>, V: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint2<R, V>>,
    e: int,
    va: int, vb: int, vc: int, vd: int,
)
    requires
        index_bounds(m),
        0 <= e < edge_count(m),
        pos@.len() == vertex_count(m),
        0 <= va < vertex_count(m),
        0 <= vb < vertex_count(m),
        0 <= vc < vertex_count(m),
        0 <= vd < vertex_count(m),
        //  The 4 vertices match the edge diamond
        m.half_edges@[m.edge_half_edges@[e] as int].vertex as int == va,
        m.half_edges@[m.half_edges@[m.edge_half_edges@[e] as int].next as int].vertex as int == vb,
        m.half_edges@[m.half_edges@[m.half_edges@[m.edge_half_edges@[e] as int].next as int].next as int].vertex as int == vc,
        ({
            let t = m.half_edges@[m.edge_half_edges@[e] as int].twin as int;
            m.half_edges@[m.half_edges@[m.half_edges@[t].next as int].next as int].vertex as int == vd
        }),
        //  Sign IS Positive
        incircle2d_sign::<V>(pos@[va].model@, pos@[vb].model@, pos@[vc].model@, pos@[vd].model@)
            == OrientationSign::Positive,
    ensures
        !edge_delaunay_2d::<V>(m, pos_view_2d(pos), e),
{
    let pv = pos_view_2d(pos);
    assert(pv[va] == pos@[va].model@);
    assert(pv[vb] == pos@[vb].model@);
    assert(pv[vc] == pos@[vc].model@);
    assert(pv[vd] == pos@[vd].model@);
    //  incircle2d_sign == Positive <==> incircle2d_positive (by lemma_incircle2d_sign_matches)
    lemma_incircle2d_sign_matches::<V>(pos@[va].model@, pos@[vb].model@, pos@[vc].model@, pos@[vd].model@);
    //  So incircle2d_positive(a,b,c,d) == true
    //  edge_delaunay_2d unfolds to is_locally_delaunay_edge_2d(a,b,c,d) == !incircle2d_positive(a,b,c,d)
    //  Which is false. QED.
}

//  =============================================================================
//  Delaunay mesh checker (2D)
//  =============================================================================

///  Check that all edges in the mesh are locally Delaunay in 2D.
///  Loops over edges, extracts diamond via half-edge traversal,
///  calls incircle2d_sign_exec, rejects on Positive.
pub fn check_locally_delaunay_mesh_2d<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(m: &Mesh, pos: &Vec<RuntimePoint2<R, V>>) -> (out: bool)
    requires
        structurally_valid(m),
        pos@.len() == vertex_count(m),
        positions_wf_2d(pos),
    ensures
        out ==> is_locally_delaunay_mesh_2d::<V>(m, pos_view_2d(pos)),
{
    proof { assert(index_bounds(m)); }
    let ecnt = m.edge_half_edges.len();
    let mut e: usize = 0;

    while e < ecnt
        invariant
            index_bounds(m),
            pos@.len() == vertex_count(m),
            positions_wf_2d(pos),
            0 <= e <= ecnt,
            ecnt == edge_count(m),
            forall|ee: int| 0 <= ee < e as int
                ==> edge_delaunay_2d::<V>(m, pos_view_2d(pos), ee),
        decreases ecnt - e,
    {
        let h = m.edge_half_edges[e];
        let t = m.half_edges[h].twin;
        let va = m.half_edges[h].vertex;
        let h_next = m.half_edges[h].next;
        let vb = m.half_edges[h_next].vertex;
        let h_next_next = m.half_edges[h_next].next;
        let vc = m.half_edges[h_next_next].vertex;
        let t_next = m.half_edges[t].next;
        let t_next_next = m.half_edges[t_next].next;
        let vd = m.half_edges[t_next_next].vertex;

        let sign = incircle2d_sign_exec(&pos[va], &pos[vb], &pos[vc], &pos[vd]);

        match sign {
            OrientationSign::Positive => {
                return false;
            }
            _ => {
                proof {
                    lemma_incircle_not_positive_implies_edge_delaunay(
                        m, pos, e as int,
                        va as int, vb as int, vc as int, vd as int,
                    );
                }
            }
        }

        e = e + 1;
    }

    true
}

//  =============================================================================
//  Proof helper: orient3d sign bridge for convex hull face checker
//  =============================================================================

///  Bridge: orient3d_sign_exec result != Positive for one point.
proof fn lemma_orient3d_not_positive_for_point<R: RuntimeRingOps<V>, V: OrderedField>(
    points: &Vec<RuntimePoint3<R, V>>,
    a: Point3<V>,
    b: Point3<V>,
    c: Point3<V>,
    pi: int,
)
    requires
        0 <= pi < points@.len(),
        points@[pi].wf_spec(),
        orient3d_sign::<V>(a, b, c, points@[pi].model@)
            != OrientationSign::Positive,
    ensures
        !orient3d_positive::<V>(a, b, c, points@[pi].model@),
{
}

//  =============================================================================
//  Convex hull face checker (3D)
//  =============================================================================

///  Check that a single face (a, b, c) is a hull face: all points are on the
///  non-positive side.
pub fn check_convex_hull_face_3d<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    a: &RuntimePoint3<R, V>,
    b: &RuntimePoint3<R, V>,
    c: &RuntimePoint3<R, V>,
    points: &Vec<RuntimePoint3<R, V>>,
) -> (out: bool)
    requires
        a.wf_spec(),
        b.wf_spec(),
        c.wf_spec(),
        forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
    ensures
        out ==> all_points_on_or_below_plane::<V>(
            Seq::new(points@.len(), |i: int| points@[i].model@), a.model@, b.model@, c.model@,
        ),
{
    let pcnt = points.len();
    let mut i: usize = 0;

    while i < pcnt
        invariant
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            0 <= i <= pcnt,
            pcnt == points@.len(),
            forall|j: int| 0 <= j < points@.len() ==> (#[trigger] points@[j]).wf_spec(),
            forall|j: int| 0 <= j < i as int ==>
                !orient3d_positive::<V>(a.model@, b.model@, c.model@, points@[j].model@),
        decreases pcnt - i,
    {
        let sign = orient3d_sign_exec(a, b, c, &points[i]);

        match sign {
            OrientationSign::Positive => {
                return false;
            }
            _ => {
                proof {
                    lemma_orient3d_not_positive_for_point(
                        points, a.model@, b.model@, c.model@, i as int,
                    );
                }
            }
        }

        i = i + 1;
    }

    //  Bridge from per-point fact to Seq-based spec
    proof {
        let pt_views = Seq::new(points@.len(), |i: int| points@[i].model@);
        assert forall|j: int| 0 <= j < pt_views.len() implies
            !orient3d_positive::<V>(a.model@, b.model@, c.model@, #[trigger] pt_views[j])
        by {
            assert(pt_views[j] == points@[j].model@);
        }
    }

    true
}

///  Check that the mesh forms a convex hull of the given 3D points.
///  Loops over faces, extracts triangle vertices, calls check_convex_hull_face_3d.
pub fn check_convex_hull_mesh_3d<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    m: &Mesh,
    pos: &Vec<RuntimePoint3<R, V>>,
    points: &Vec<RuntimePoint3<R, V>>,
) -> (out: bool)
    requires
        structurally_valid(m),
        pos@.len() == vertex_count(m),
        positions_wf_3d(pos),
        forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
    ensures
        out ==> is_convex_hull_mesh_3d::<V>(m, pos_view_3d(pos),
            Seq::new(points@.len(), |i: int| points@[i].model@)),
{
    proof { assert(index_bounds(m)); }
    let fcnt = m.face_half_edges.len();
    let mut f: usize = 0;

    while f < fcnt
        invariant
            index_bounds(m),
            pos@.len() == vertex_count(m),
            positions_wf_3d(pos),
            0 <= f <= fcnt,
            fcnt == face_count(m),
            forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
            forall|ff: int| #![trigger m.face_half_edges@[ff]]
                0 <= ff < f as int ==> {
                let start = m.face_half_edges@[ff] as int;
                let h0 = start;
                let h1 = m.half_edges@[h0].next as int;
                let h2 = m.half_edges@[h1].next as int;
                let pv = pos_view_3d(pos);
                let a = pv[m.half_edges@[h0].vertex as int];
                let b = pv[m.half_edges@[h1].vertex as int];
                let c = pv[m.half_edges@[h2].vertex as int];
                all_points_on_or_below_plane::<V>(
                    Seq::new(points@.len(), |i: int| points@[i].model@), a, b, c,
                )
            },
        decreases fcnt - f,
    {
        let h0 = m.face_half_edges[f];
        let h1 = m.half_edges[h0].next;
        let h2 = m.half_edges[h1].next;
        let v0 = m.half_edges[h0].vertex;
        let v1 = m.half_edges[h1].vertex;
        let v2 = m.half_edges[h2].vertex;

        let ok = check_convex_hull_face_3d(&pos[v0], &pos[v1], &pos[v2], points);

        if !ok {
            return false;
        }

        //  Bridge: check result with spec view
        proof {
            let pv = pos_view_3d(pos);
            assert(pv[v0 as int] == pos@[v0 as int].model@);
            assert(pv[v1 as int] == pos@[v1 as int].model@);
            assert(pv[v2 as int] == pos@[v2 as int].model@);
        }

        f = f + 1;
    }

    true
}

} //  verus!
