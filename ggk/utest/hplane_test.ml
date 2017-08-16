open OUnit
open Staged
open Basetypes
open Float
open Tuple
open Vectoren
open Pointen
open Hplane

module V = VectorStaged (Float_Real_Exact) (Pair2D)
module P = En_Point (Float_Real_Exact) (V) (Pair2D)
module L = N_plane (Float_Real_Exact)(V)(P)
(* module L = Line (Float)(V)(P) *)
module LO = Hplane_Operations (L)

(* -8.8944 x + 0.4772 y + 0 = 0 *)
(* basis : u = 8,16 normalized = 0.4472, 0.8944 *)
(* normal : -0.8944, 0.4772 *)
let p0 () = P.of_list [Now 1.; Now 2.]
let p1 () = P.of_list [Now 9.; Now 18.]
let l () = L.of_points [p0 (); p1 ()]

let test_create _ =
  assert_equal ~msg:"err #1" (L.point (l()) 0) (p0 ());
  assert_equal ~msg:"err #2" (L.point (l()) 1) (p1 ())

let test_poly _ =
  let p = L.poly (l()) 
  and n = L.normal (l()) in
  assert_equal ~msg:"err #1" p.(0) (V.coord n 0);
  assert_equal ~msg:"err #2" p.(1) (V.coord n 1);
  assert_equal ~msg:"err #3" p.(2) (Now 0.);
  assert_equal ~msg:"err #4" p.(2) (L.d (l()))

(* unsafe *)
let unbox = function
  | Now x -> x
  | Later _ -> failwith "unbox fail hplane_test.ml:38"

let test_normal _ =
  let n = L.normal (l()) in
  let x, y = (V.coord n 0), (V.coord n 1) in
  let x, y = (unbox x), (unbox y) in
  let b0 = x > (~-. 0.895) && x < (-. 0.893)
  and b1 = y < 0.4473 && y > 0.4471 in
  assert_bool "err #1" b0;
  assert_bool "err #2" b1

let test_basis _ =
  let b = L.basis (l()) 0 in
  let x, y = (V.coord b 0), (V.coord b 1) in
  let x, y = (unbox x), (unbox y) in
  let b0 = x < 0.4473 && x > 0.4471
  and b1 = y > 0.892 && y < 0.895 in
  assert_bool "err #1" b0;
  assert_bool "err #2" b1

let between x lb ub = x >= lb && x < ub

let test_dist _ =
  let c1 = P.of_list [Now 10.; Now 10.]
  and c2 = P.of_list [Now 7.5; Now 15.]
  and c3 = P.of_list [Now 5.; Now 20.] in
  (* -4.472, 0.0, 4.472 *)
  let d1 = LO.dist (l()) c1 
  and d2 = LO.dist (l()) c2
  and d3 = LO.dist (l()) c3 in
  assert_bool "err #1" (between (unbox d1) (-. 4.473) (-. 4.471));
  assert_bool "err #2" (between (unbox d2) (-. 0.001) 0.001);
  assert_bool "err #3" (between (unbox d3) 4.471 4.473)

let test_project _ =
  let c1 = P.of_list [Now 10.; Now 10.]
  and c2 = P.of_list [Now 6.; Now 12.]
  and c3 = P.of_list [Now 0.; Now 15.] in
  let p1 = LO.project (l()) c1
  and p2 = LO.project (l()) c2
  and p3 = LO.project (l()) c3 in
  assert_equal ~msg:"err #1" (P.eq_tol p1 c2) (Now true);
  assert_equal ~msg:"err #2" (P.eq_tol p2 c2) (Now true);
  assert_equal ~msg:"err #3" (P.eq_tol p3 c2) (Now true)

let suite = "Hplane Line test" >::: [
  "test_create" >:: test_create;
  "test_poly" >:: test_poly;
  "test_normal" >:: test_normal;
  "test_basis" >:: test_basis;
  "test_dist" >:: test_dist;
  "test_project" >:: test_project
]
