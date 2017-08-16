open OUnit
open Staged
open Basetypes
open Float
open Tuple
open Vectoren
open Pointen
open Affine

module T = Pair2D
module V = VectorStaged (Float_Real_Exact) (Pair2D)
module P = En_Point (Float_Real_Exact) (V) (Pair2D) 
module AT = AffineTransformations (Float_Real_Exact) (V) (P) (Pair2D)

let test_translate _ =
 (* translate the triangle (0,0),(1,0),(1,1) -> triangle
     (1,0),(1,1),(0,1) *)
  let p0 = P.of_immediate (0., 0.)
  and p1 = P.of_immediate (1., 0.)
  and p2 = P.of_immediate (1., 1.)
  and t0 = AT.translation (V.of_immediate (1., 0.))
  and t1 = AT.translation (V.of_immediate (0., 1.))
  and t2 = AT.translation (V.of_immediate (-. 1., 0.)) in
  let p0' = AT.apply_p t0 p0
  and p1' = AT.apply_p t1 p1
  and p2' = AT.apply_p t2 p2 in
  assert_equal ~msg:"err #1" p0' p1;
  assert_equal ~msg:"err #2" p1' p2;
  assert_equal ~msg:"err #3" p2' (P.of_immediate (0., 1.))

let test_scale _ =
  let p0 = P.of_list [Now 0.; Now 0.]
  and p1 = P.of_list [Now 1.; Now 0.]
  and p2 = P.of_list [Now 1.; Now 1.]
  and t0 = AT.scaling (T.of_list_n [1.; 1.])
  and t1 = AT.scaling (T.of_list_n [1.; 1.])
  and t2 = AT.scaling (T.of_list_n [~-. 1.; 2.]) in
  let p0' = AT.apply_p t0 p0
  and p1' = AT.apply_p t1 p1
  and p2' = AT.apply_p t2 p2 in
  assert_equal ~msg:"err #1" p0' p0;
  assert_equal ~msg:"err #2" p1' p1;
  assert_equal ~msg:"err #3" p2' (P.of_list [Now ~-. 1.; Now 2.])

let test_id _ =
  let p = P.of_list [Now 0.; Now 0.; Now 1.] in
  let p' = AT.apply_p (AT.id 3) p in
  assert_equal ~msg:"err #1" p' p

let test_compose _ =
  let p = P.of_list [Now 0.; Now 0.; Now 1.]
  and t0 = AT.translation (V.of_coords [Now 1.; Now 1.; Now 1.])
  and t1 = AT.translation (V.of_coords [Now 2.; Now ~-. 1.; Now 0.])
  (* vector of t2 = vector of t0 + vector of t1 *)
  and t2 = AT.translation (V.of_coords [Now 3.; Now 0.; Now 1.]) in
  let p1 = AT.apply_p t1 (AT.apply_p t0 p)
  and p2 = AT.apply_p (AT.compose t0 t1) p
  and p3 = AT.apply_p t2 p in
  assert_equal ~msg:"err #1" p1 p2;
  assert_equal ~msg:"err #2" p1 p3

let suite = "Affine Test Suite" >::: [
  "test_translate" >:: test_translate;
  "test_scale" >:: test_scale;
  "test_id" >:: test_id;
  "test_compose" >:: test_compose
  ]

(* Translate Axioms (with redundacy because the implementation
 * might violate some):
 * if T(v, p) = p' then vector(pp') = v
 * if T(v, p) = p' then T(-v, p') = p
 * T(v, T(-v, p)) = p,    T(-v, T(v, p)) = p
 * zero vector is the unit element: T(zero, p) = p
 * T(u, T(v, p)) = T(v, T(u, p))
 * T(u, T(v, p)) = T(u+v, p)
 * isometery: dist(a, b) = dist(T(v, a), T(v, b))
 *)

