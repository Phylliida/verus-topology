use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;
use verus_linalg::vec3::Vec3;
use verus_linalg::vec3::ops::*;
use verus_geometry::point3::Point3;
use verus_geometry::point3::sub3;
use verus_geometry::ray_triangle::*;
use verus_geometry::runtime::point3::RuntimePoint3;
use verus_geometry::runtime::ray_triangle::ray_hits_triangle_nodiv_exec;



use crate::mesh::*;
use crate::invariants::*;
use crate::queries::*;
use crate::geometric_mesh::*;
use crate::geometric_checkers::*;

verus! {

//  =============================================================================
//  Spec layer: ray-face intersection and crossing count
//  =============================================================================

///  Extract the three vertex positions of face f (assumes triangular face).
pub open spec fn face_tri_v0<T: Ring>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int,
) -> Point3<T>
    recommends
        index_bounds(m),
        0 <= f < face_count(m),
        pos.len() == vertex_count(m),
{
    let h0 = m.face_half_edges@[f] as int;
    pos[m.half_edges@[h0].vertex as int]
}

pub open spec fn face_tri_v1<T: Ring>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int,
) -> Point3<T>
    recommends
        index_bounds(m),
        0 <= f < face_count(m),
        pos.len() == vertex_count(m),
{
    let h0 = m.face_half_edges@[f] as int;
    let h1 = m.half_edges@[h0].next as int;
    pos[m.half_edges@[h1].vertex as int]
}

pub open spec fn face_tri_v2<T: Ring>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int,
) -> Point3<T>
    recommends
        index_bounds(m),
        0 <= f < face_count(m),
        pos.len() == vertex_count(m),
{
    let h0 = m.face_half_edges@[f] as int;
    let h1 = m.half_edges@[h0].next as int;
    let h2 = m.half_edges@[h1].next as int;
    pos[m.half_edges@[h2].vertex as int]
}

///  Does the ray from `origin` in direction `dir` hit face `f`?
///  Uses the division-free Moller-Trumbore test.
pub open spec fn ray_hits_face<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int,
    origin: Point3<T>, dir: Vec3<T>,
) -> bool
    recommends
        index_bounds(m),
        0 <= f < face_count(m),
        pos.len() == vertex_count(m),
{
    ray_hits_triangle_nodiv(
        origin, dir,
        face_tri_v0(m, pos, f),
        face_tri_v1(m, pos, f),
        face_tri_v2(m, pos, f),
    )
}

///  Number of faces hit by the ray, counting faces 0..n.
pub open spec fn ray_crossing_count_prefix<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
    n: int,
) -> int
    recommends
        index_bounds(m),
        pos.len() == vertex_count(m),
        0 <= n <= face_count(m),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        ray_crossing_count_prefix(m, pos, origin, dir, n - 1)
            + if ray_hits_face(m, pos, n - 1, origin, dir) { 1int } else { 0int }
    }
}

///  Total number of faces hit by the ray.
pub open spec fn ray_crossing_count<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
) -> int
    recommends
        index_bounds(m),
        pos.len() == vertex_count(m),
{
    ray_crossing_count_prefix(m, pos, origin, dir, face_count(m) as int)
}

///  A point is inside the solid if the ray crossing count is odd.
pub open spec fn point_in_solid<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
) -> bool {
    ray_crossing_count(m, pos, origin, dir) % 2 == 1
}

//  =============================================================================
//  Proof helpers
//  =============================================================================

///  Prefix count unfold: adding one more face.
proof fn lemma_prefix_unfold<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
    n: int,
)
    requires
        0 < n,
    ensures
        ray_crossing_count_prefix(m, pos, origin, dir, n)
            == ray_crossing_count_prefix(m, pos, origin, dir, n - 1)
                + if ray_hits_face(m, pos, n - 1, origin, dir) { 1int } else { 0int },
{
    //  Follows directly from the recursive definition
}

///  Prefix count is non-negative.
proof fn lemma_prefix_nonneg<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
    n: int,
)
    requires
        0 <= n,
    ensures
        ray_crossing_count_prefix(m, pos, origin, dir, n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_prefix_nonneg::<T>(m, pos, origin, dir, n - 1);
    }
}

///  Bridge: ray_hits_triangle_nodiv_exec result matches ray_hits_face spec.
proof fn lemma_ray_hits_face_bridge<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint3<R, V>>,
    f: int,
    origin: &RuntimePoint3<R, V>, dir: &RuntimePoint3<R, V>,
    v0: int, v1: int, v2: int,
    exec_result: bool,
)
    requires
        index_bounds(m),
        0 <= f < face_count(m),
        pos@.len() == vertex_count(m),
        positions_wf_3d(pos),
        origin.wf_spec(),
        dir.wf_spec(),
        0 <= v0 < vertex_count(m),
        0 <= v1 < vertex_count(m),
        0 <= v2 < vertex_count(m),
        m.half_edges@[m.face_half_edges@[f] as int].vertex as int == v0,
        m.half_edges@[m.half_edges@[m.face_half_edges@[f] as int].next as int].vertex as int == v1,
        m.half_edges@[m.half_edges@[m.half_edges@[m.face_half_edges@[f] as int].next as int].next as int].vertex as int == v2,
        exec_result == ray_hits_triangle_nodiv::<V>(
            origin.model@, dir.model@, pos@[v0].model@, pos@[v1].model@, pos@[v2].model@,
        ),
    ensures
        exec_result == ray_hits_face::<V>(
            m, pos_view_3d(pos), f, origin.model@, dir.model@,
        ),
{
    let pv = pos_view_3d(pos);
    assert(pv[v0] == pos@[v0].model@);
    assert(pv[v1] == pos@[v1].model@);
    assert(pv[v2] == pos@[v2].model@);
}

//  =============================================================================
//  Exec layer: runtime point-in-solid checker
//  =============================================================================

///  Count the number of mesh faces hit by a ray (runtime).
pub fn ray_crossing_count_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint3<R, V>>,
    origin: &RuntimePoint3<R, V>, dir: &RuntimePoint3<R, V>,
) -> (count: usize)
    requires
        structurally_valid(m),
        all_faces_triangles(m),
        pos@.len() == vertex_count(m),
        positions_wf_3d(pos),
        origin.wf_spec(),
        dir.wf_spec(),
        //  Overflow guard: face count fits in usize
        face_count(m) < usize::MAX,
    ensures
        count as int == ray_crossing_count::<V>(
            m, pos_view_3d(pos), origin.model@, dir.model@,
        ),
{
    proof { assert(index_bounds(m)); }
    let fcnt = m.face_half_edges.len();
    let mut f: usize = 0;
    let mut count: usize = 0;

    while f < fcnt
        invariant
            index_bounds(m),
            all_faces_triangles(m),
            pos@.len() == vertex_count(m),
            positions_wf_3d(pos),
            origin.wf_spec(),
            dir.wf_spec(),
            0 <= f <= fcnt,
            fcnt == face_count(m),
            fcnt < usize::MAX,
            count as int == ray_crossing_count_prefix::<V>(
                m, pos_view_3d(pos), origin.model@, dir.model@, f as int,
            ),
            count <= f,
        decreases fcnt - f,
    {
        let h0 = m.face_half_edges[f];
        let h1 = m.half_edges[h0].next;
        let h2 = m.half_edges[h1].next;
        let v0 = m.half_edges[h0].vertex;
        let v1 = m.half_edges[h1].vertex;
        let v2 = m.half_edges[h2].vertex;

        let hit = ray_hits_triangle_nodiv_exec(origin, dir, &pos[v0], &pos[v1], &pos[v2]);

        proof {
            lemma_ray_hits_face_bridge(
                m, pos, f as int, origin, dir,
                v0 as int, v1 as int, v2 as int, hit);
            lemma_prefix_unfold::<V>(
                m, pos_view_3d(pos), origin.model@, dir.model@, (f + 1) as int);
        }

        if hit {
            count = count + 1;
        }

        f = f + 1;
    }

    count
}

///  Check whether a point is inside a closed, consistently-oriented triangle mesh.
///
///  Casts a ray from `origin` in direction `dir` and counts the number of
///  face crossings. An odd count means the point is inside.
///
///  The caller must ensure the ray is in "general position" — it should not
///  pass through any edge or vertex of the mesh. With exact rational arithmetic,
///  this can be checked or guaranteed by perturbation.
pub fn check_point_in_solid<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint3<R, V>>,
    origin: &RuntimePoint3<R, V>, dir: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires
        structurally_valid(m),
        all_faces_triangles(m),
        pos@.len() == vertex_count(m),
        positions_wf_3d(pos),
        origin.wf_spec(),
        dir.wf_spec(),
        face_count(m) < usize::MAX,
    ensures
        out == point_in_solid::<V>(
            m, pos_view_3d(pos), origin.model@, dir.model@,
        ),
{
    let count = ray_crossing_count_exec(m, pos, origin, dir);
    count % 2 == 1
}

//  =============================================================================
//  Crossing count bounds
//  =============================================================================

///  Crossing count prefix is bounded by n.
pub proof fn lemma_crossing_count_bounded<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
    n: int,
)
    requires
        0 <= n,
    ensures
        0 <= ray_crossing_count_prefix(m, pos, origin, dir, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_crossing_count_bounded::<T>(m, pos, origin, dir, n - 1);
    }
}

///  Total crossing count is bounded by face count.
pub proof fn lemma_crossing_count_total_bounded<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
)
    ensures
        0 <= ray_crossing_count(m, pos, origin, dir) <= face_count(m) as int,
{
    lemma_crossing_count_bounded::<T>(m, pos, origin, dir, face_count(m) as int);
}

//  =============================================================================
//  General position: ray doesn't hit any face boundary
//  =============================================================================

///  The four Moller-Trumbore parameters for face f, lifted to the mesh.
pub open spec fn ray_face_det<T: Ring>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int, dir: Vec3<T>,
) -> T
    recommends index_bounds(m), 0 <= f < face_count(m), pos.len() == vertex_count(m),
{
    ray_tri_det(dir, face_tri_v0(m, pos, f), face_tri_v1(m, pos, f), face_tri_v2(m, pos, f))
}

pub open spec fn ray_face_u<T: Ring>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int,
    origin: Point3<T>, dir: Vec3<T>,
) -> T
    recommends index_bounds(m), 0 <= f < face_count(m), pos.len() == vertex_count(m),
{
    ray_tri_u_unnorm(origin, dir, face_tri_v0(m, pos, f), face_tri_v1(m, pos, f), face_tri_v2(m, pos, f))
}

pub open spec fn ray_face_v<T: Ring>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int,
    origin: Point3<T>, dir: Vec3<T>,
) -> T
    recommends index_bounds(m), 0 <= f < face_count(m), pos.len() == vertex_count(m),
{
    ray_tri_v_unnorm(origin, dir, face_tri_v0(m, pos, f), face_tri_v1(m, pos, f), face_tri_v2(m, pos, f))
}

pub open spec fn ray_face_t<T: Ring>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int,
    origin: Point3<T>, dir: Vec3<T>,
) -> T
    recommends index_bounds(m), 0 <= f < face_count(m), pos.len() == vertex_count(m),
{
    ray_tri_t_unnorm(origin, dir, face_tri_v0(m, pos, f), face_tri_v1(m, pos, f), face_tri_v2(m, pos, f))
}

///  Face f is in general position w.r.t. the ray: either the ray is parallel
///  to the face (det ≡ 0, automatic miss), or none of {u, v, det-u-v, t}
///  are zero (strictly interior or strictly exterior hit).
pub open spec fn ray_face_general_position<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int,
    origin: Point3<T>, dir: Vec3<T>,
) -> bool
    recommends index_bounds(m), 0 <= f < face_count(m), pos.len() == vertex_count(m),
{
    let det = ray_face_det(m, pos, f, dir);
    let u = ray_face_u(m, pos, f, origin, dir);
    let v = ray_face_v(m, pos, f, origin, dir);
    let t = ray_face_t(m, pos, f, origin, dir);
    det.eqv(T::zero()) || (
        !u.eqv(T::zero())
        && !v.eqv(T::zero())
        && !det.sub(u.add(v)).eqv(T::zero())
        && !t.eqv(T::zero())
    )
}

///  The ray is in general position w.r.t. the entire mesh: every face
///  satisfies `ray_face_general_position`.
pub open spec fn ray_general_position<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
) -> bool
    recommends index_bounds(m), pos.len() == vertex_count(m),
{
    forall|f: int| 0 <= f < face_count(m) ==>
        ray_face_general_position(m, pos, f, origin, dir)
}

///  Bridge: exec computation of Moller-Trumbore parameters matches face-level specs.
proof fn lemma_ray_face_params_bridge<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint3<R, V>>,
    f: int, origin: &RuntimePoint3<R, V>, dir: &RuntimePoint3<R, V>,
    v0: int, v1: int, v2: int,
    det_exec: &R, u_exec: &R,
    v_exec: &R, t_exec: &R,
)
    requires
        index_bounds(m),
        0 <= f < face_count(m),
        pos@.len() == vertex_count(m),
        positions_wf_3d(pos),
        origin.wf_spec(), dir.wf_spec(),
        det_exec.wf_spec(), u_exec.wf_spec(), v_exec.wf_spec(), t_exec.wf_spec(),
        0 <= v0 < vertex_count(m),
        0 <= v1 < vertex_count(m),
        0 <= v2 < vertex_count(m),
        m.half_edges@[m.face_half_edges@[f] as int].vertex as int == v0,
        m.half_edges@[m.half_edges@[m.face_half_edges@[f] as int].next as int].vertex as int == v1,
        m.half_edges@[m.half_edges@[m.half_edges@[m.face_half_edges@[f] as int].next as int].next as int].vertex as int == v2,
        det_exec.model() == ray_tri_det::<V>(dir.model@, pos@[v0].model@, pos@[v1].model@, pos@[v2].model@),
        u_exec.model() == ray_tri_u_unnorm::<V>(origin.model@, dir.model@, pos@[v0].model@, pos@[v1].model@, pos@[v2].model@),
        v_exec.model() == ray_tri_v_unnorm::<V>(origin.model@, dir.model@, pos@[v0].model@, pos@[v1].model@, pos@[v2].model@),
        t_exec.model() == ray_tri_t_unnorm::<V>(origin.model@, dir.model@, pos@[v0].model@, pos@[v1].model@, pos@[v2].model@),
    ensures
        det_exec.model() == ray_face_det::<V>(m, pos_view_3d(pos), f, dir.model@),
        u_exec.model() == ray_face_u::<V>(m, pos_view_3d(pos), f, origin.model@, dir.model@),
        v_exec.model() == ray_face_v::<V>(m, pos_view_3d(pos), f, origin.model@, dir.model@),
        t_exec.model() == ray_face_t::<V>(m, pos_view_3d(pos), f, origin.model@, dir.model@),
{
    let pv = pos_view_3d(pos);
    assert(pv[v0] == pos@[v0].model@);
    assert(pv[v1] == pos@[v1].model@);
    assert(pv[v2] == pos@[v2].model@);
}

///  Check that the ray is in general position w.r.t. all mesh faces.
///
///  For each face, computes the Moller-Trumbore determinant, barycentric
///  coordinates (u, v), and ray parameter (t). Returns false if any face
///  has a boundary hit (any of det, u, v, det-u-v, or t is zero).
pub fn check_ray_general_position<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    m: &Mesh, pos: &Vec<RuntimePoint3<R, V>>,
    origin: &RuntimePoint3<R, V>, dir: &RuntimePoint3<R, V>,
) -> (out: bool)
    requires
        structurally_valid(m),
        all_faces_triangles(m),
        pos@.len() == vertex_count(m),
        positions_wf_3d(pos),
        origin.wf_spec(),
        dir.wf_spec(),
    ensures
        out ==> ray_general_position::<V>(
            m, pos_view_3d(pos), origin.model@, dir.model@,
        ),
{
    proof { assert(index_bounds(m)); }
    let fcnt = m.face_half_edges.len();
    let mut f: usize = 0;
    let zero = origin.x.zero_like();

    while f < fcnt
        invariant
            index_bounds(m),
            all_faces_triangles(m),
            pos@.len() == vertex_count(m),
            positions_wf_3d(pos),
            origin.wf_spec(),
            dir.wf_spec(),
            zero.wf_spec(),
            zero.model() == V::from_int_spec(0),
            0 <= f <= fcnt,
            fcnt == face_count(m),
            forall|ff: int| 0 <= ff < f as int ==>
                ray_face_general_position::<V>(
                    m, pos_view_3d(pos), ff, origin.model@, dir.model@),
        decreases fcnt - f,
    {
        let h0 = m.face_half_edges[f];
        let h1 = m.half_edges[h0].next;
        let h2 = m.half_edges[h1].next;
        let vi0 = m.half_edges[h0].vertex;
        let vi1 = m.half_edges[h1].vertex;
        let vi2 = m.half_edges[h2].vertex;

        //  Compute Moller-Trumbore parameters
        let e1 = pos[vi1].sub(&pos[vi0]);
        let e2 = pos[vi2].sub(&pos[vi0]);
        let p = dir.cross(&e2);
        let det = e1.dot(&p);

        if det.eq(&zero) {
            //  Ray parallel to face — automatic miss, general position OK
            proof {
                assert(det.model().eqv_spec(zero.model()));
                assert(det.model() == ray_tri_det::<V>(
                    dir.model@, pos@[vi0 as int].model@, pos@[vi1 as int].model@, pos@[vi2 as int].model@));
                let pv = pos_view_3d(pos);
                assert(pv[vi0 as int] == pos@[vi0 as int].model@);
                assert(pv[vi1 as int] == pos@[vi1 as int].model@);
                assert(pv[vi2 as int] == pos@[vi2 as int].model@);
            }
            f = f + 1;
            continue;
        }

        let tvec = origin.sub(&pos[vi0]);
        let u = tvec.dot(&p);
        let q = tvec.cross(&e1);
        let v = dir.dot(&q);
        let t = e2.dot(&q);
        let uv = u.add(&v);
        let det_minus_uv = det.sub(&uv);

        if u.eq(&zero) || v.eq(&zero) || det_minus_uv.eq(&zero) || t.eq(&zero) {
            return false;
        }

        proof {
            lemma_ray_face_params_bridge(
                m, pos, f as int, origin, dir,
                vi0 as int, vi1 as int, vi2 as int,
                &det, &u, &v, &t);
        }

        f = f + 1;
    }

    true
}

//  =============================================================================
//  Signed crossings: connecting det sign to face orientation
//  =============================================================================

///  The sign of the ray-face determinant determines whether the ray
///  enters or exits the solid through face f.
///
///  - det > 0: ray goes against the outward face normal (entering)
///  - det < 0: ray goes with the outward face normal (exiting)
///
///  This follows from: ray_tri_det(dir, v0, v1, v2) = triple(e1, dir, e2)
///  = -triple(e1, e2, dir) = -dot(normal, dir), where normal = cross(e1, e2).
pub open spec fn ray_entering_face<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int, dir: Vec3<T>,
) -> bool
    recommends index_bounds(m), 0 <= f < face_count(m), pos.len() == vertex_count(m),
{
    T::zero().lt(ray_face_det(m, pos, f, dir))
}

pub open spec fn ray_exiting_face<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int, dir: Vec3<T>,
) -> bool
    recommends index_bounds(m), 0 <= f < face_count(m), pos.len() == vertex_count(m),
{
    ray_face_det(m, pos, f, dir).lt(T::zero())
}

///  Signed crossing contribution for face f: +1 (entering), -1 (exiting), 0 (miss).
pub open spec fn ray_crossing_sign<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>, f: int,
    origin: Point3<T>, dir: Vec3<T>,
) -> int
    recommends index_bounds(m), 0 <= f < face_count(m), pos.len() == vertex_count(m),
{
    if !ray_hits_face(m, pos, f, origin, dir) {
        0int
    } else if ray_entering_face(m, pos, f, dir) {
        1int
    } else {
        -1int
    }
}

///  Signed crossing count (prefix sum).
pub open spec fn ray_signed_crossing_prefix<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
    n: int,
) -> int
    recommends index_bounds(m), pos.len() == vertex_count(m), 0 <= n <= face_count(m),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        ray_signed_crossing_prefix(m, pos, origin, dir, n - 1)
            + ray_crossing_sign(m, pos, n - 1, origin, dir)
    }
}

///  Total signed crossing count.
pub open spec fn ray_signed_crossing_count<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
) -> int
    recommends index_bounds(m), pos.len() == vertex_count(m),
{
    ray_signed_crossing_prefix(m, pos, origin, dir, face_count(m) as int)
}

///  The determinant equals -triple(e1, e2, dir), connecting the Moller-Trumbore
///  determinant to the face normal direction.
///
///  ray_tri_det(dir, v0, v1, v2)
///    = triple(e1, dir, e2)         [definition]
///    ≡ -triple(e1, e2, dir)        [swap last two: triple(a, c, b) ≡ -triple(a, b, c)]
///    = -dot(cross(e1, e2), dir)    [definition of triple]
///    = -dot(face_normal, dir)
pub proof fn lemma_det_is_neg_triple_normal_dir<T: Ring>(
    dir: Vec3<T>, v0: Point3<T>, v1: Point3<T>, v2: Point3<T>,
)
    ensures
        ray_tri_det(dir, v0, v1, v2).eqv(
            triple(edge1(v0, v1), edge2(v0, v2), dir).neg()
        ),
{
    let e1 = edge1(v0, v1);
    let e2 = edge2(v0, v2);
    //  triple(e1, dir, e2) ≡ -triple(e1, e2, dir)  [swap_23]
    lemma_triple_swap_23(e1, e2, dir);
    //  lemma_triple_swap_23 gives: triple(e1, dir, e2) ≡ triple(e1, e2, dir).neg()
    //  And ray_tri_det(dir, v0, v1, v2) = triple(e1, dir, e2) by definition
}

///  Signed and unsigned crossing counts have the same parity.
///
///  Each hit contributes +1 to unsigned and ±1 to signed. The difference
///  per exit is 2 (unsigned +1, signed -1), so they agree mod 2.
pub proof fn lemma_signed_unsigned_parity<T: OrderedRing>(
    m: &Mesh, pos: Seq<Point3<T>>,
    origin: Point3<T>, dir: Vec3<T>,
    n: int,
)
    requires
        0 <= n,
        //  Under general position, every hit has det != 0
        forall|f: int| 0 <= f < n ==>
            ray_face_general_position(m, pos, f, origin, dir),
    ensures
        ray_crossing_count_prefix(m, pos, origin, dir, n) % 2
            == ((ray_signed_crossing_prefix(m, pos, origin, dir, n) % 2) + 2) % 2,
    decreases n,
{
    if n > 0 {
        lemma_signed_unsigned_parity::<T>(m, pos, origin, dir, n - 1);

        let prev_unsigned = ray_crossing_count_prefix(m, pos, origin, dir, n - 1);
        let prev_signed = ray_signed_crossing_prefix(m, pos, origin, dir, n - 1);
        let f = n - 1;

        if ray_hits_face(m, pos, f, origin, dir) {
            //  Face f is hit. Under general position, det != 0.
            //  So crossing_sign is +1 or -1. Either way, parity flips for both.
            assert(ray_face_general_position(m, pos, f, origin, dir));
            let det = ray_face_det(m, pos, f, dir);

            //  The hit means det != 0 (ray_hits_triangle_nodiv returns false when det ≡ 0)
            //  Under general position, det is nonzero.
            //  So crossing_sign is +1 (entering) or -1 (exiting).
            //  unsigned goes prev + 1, signed goes prev ± 1.
            //  In both cases parity flips: (prev + 1) % 2 != prev % 2,
            //  and (prev ± 1) % 2 != prev % 2.
            //  So they still agree mod 2.
        } else {
            //  Face f is not hit: +0 to both. Parity unchanged.
        }
    }
}

} //  verus!
