use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use verus_geometry::orient2d::*;
use verus_geometry::orientation_sign::*;
use verus_geometry::incircle::*;
use verus_geometry::delaunay::*;
use verus_geometry::runtime::point2::RuntimePoint2;
use verus_geometry::runtime::classification::incircle2d_sign_exec;

use crate::mesh::*;
use crate::invariants::*;
use crate::euler_ops::*;
use crate::geometric_mesh::*;
use crate::geometric_checkers::*;

verus! {

//  =============================================================================
//  Find first non-Delaunay edge
//  =============================================================================

///  Find the first edge that violates the Delaunay condition, or None if all pass.
pub fn find_non_delaunay_edge_2d(m: &Mesh, pos: &Vec<RuntimePoint2>) -> (out: Option<usize>)
    requires
        structurally_valid(m),
        pos@.len() == vertex_count(m),
        positions_wf_2d(pos),
    ensures
        out is None ==> is_locally_delaunay_mesh_2d::<V>(m, pos_view_2d(pos)),
        out is Some ==> 0 <= out->Some_0 < edge_count(m) as int,
        out is Some ==> !edge_delaunay_2d::<V>(m, pos_view_2d(pos), out->Some_0 as int),
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
                proof {
                    lemma_incircle_positive_implies_not_edge_delaunay(
                        m, pos, e as int,
                        va as int, vb as int, vc as int, vd as int,
                    );
                }
                return Some(e);
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

    None
}

//  =============================================================================
//  Single Lawson flip step
//  =============================================================================

///  Perform one step of Lawson's flip algorithm:
///  find a non-Delaunay edge and flip it, or report the mesh is already Delaunay.
///  Returns Ok((mesh, flipped)) where flipped indicates whether a flip was performed.
pub fn lawson_flip_step_2d(
    mesh: Mesh,
    pos: &Vec<RuntimePoint2>,
) -> (result: Result<(Mesh, bool), EulerError>)
    requires
        structurally_valid(&mesh),
        pos@.len() == vertex_count(&mesh),
        positions_wf_2d(pos),
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0.0),
        result is Ok ==> vertex_count(&result->Ok_0.0) == vertex_count(&mesh),
        result is Ok ==> edge_count(&result->Ok_0.0) == edge_count(&mesh),
        result is Ok ==> pos@.len() == vertex_count(&result->Ok_0.0),
        result is Ok ==> !result->Ok_0.1
            ==> is_locally_delaunay_mesh_2d::<V>(&result->Ok_0.0, pos_view_2d(pos)),
{
    let found = find_non_delaunay_edge_2d(&mesh, pos);
    match found {
        None => {
            Ok((mesh, false))
        }
        Some(e) => {
            proof { assert(index_bounds(&mesh)); }
            let new_mesh = flip_edge(mesh, e)?;
            proof {
                //  flip_edge_post gives us count preservation
                assert(vertex_count(&new_mesh) == vertex_count(&mesh))
                    by { /* from flip_edge_post */ };
                assert(edge_count(&new_mesh) == edge_count(&mesh))
                    by { /* from flip_edge_post */ };
            }
            Ok((new_mesh, true))
        }
    }
}

//  =============================================================================
//  Lawson flip loop
//  =============================================================================

///  Iteratively flip non-Delaunay edges until the mesh is locally Delaunay
///  or max_iter iterations are exhausted.
///  Returns Ok((mesh, converged)) where converged indicates whether
///  the mesh is locally Delaunay.
pub fn lawson_flip_2d(
    mesh: Mesh,
    pos: &Vec<RuntimePoint2>,
    max_iter: usize,
) -> (result: Result<(Mesh, bool), EulerError>)
    requires
        structurally_valid(&mesh),
        pos@.len() == vertex_count(&mesh),
        positions_wf_2d(pos),
    ensures
        result is Ok ==> structurally_valid(&result->Ok_0.0),
        result is Ok ==> pos@.len() == vertex_count(&result->Ok_0.0),
        result is Ok && result->Ok_0.1
            ==> is_locally_delaunay_mesh_2d::<V>(&result->Ok_0.0, pos_view_2d(pos)),
{
    let mut current = mesh;
    let mut i: usize = 0;

    while i < max_iter
        invariant
            structurally_valid(&current),
            pos@.len() == vertex_count(&current),
            positions_wf_2d(pos),
            0 <= i <= max_iter,
        decreases max_iter - i,
    {
        let step_result = lawson_flip_step_2d(current, pos);
        match step_result {
            Err(err) => {
                return Err(err);
            }
            Ok((new_mesh, flipped)) => {
                if !flipped {
                    //  Converged: mesh is locally Delaunay
                    return Ok((new_mesh, true));
                }
                current = new_mesh;
            }
        }

        i = i + 1;
    }

    //  Exhausted max_iter without converging
    Ok((current, false))
}

} //  verus!
