open OUnit
open Staged
open Basetypes
open Float
open Tuple
open Vectoren
open Pointen
open Hplane
open Sphere


module V = VectorStaged (Float_Real_Exact) (Pair2D)
module P = En_Point (Float_Real_Exact) (V) (Pair2D)
module C = Sphere(Float_Real_Exact)(P)
module CO = Sphere_Operations (Float_Real_Exact)(C)

(* circle passing throug (3,2) (-1, 4) (-2, -1) 
   centre: (0.0909090909091, 1.18181818182)
   radius: 3.02195820702 
   circumference: 18.9875234052
   area: 28.6897510927 *)

let test_create _ =
  let p0 = P.of_list [Now 3.; Now 2.]
  and p1 = P.of_list [Now ~-. 1.; Now 4.]
  and p2 = P.of_list [Now ~-. 2.; Now ~-. 1.] in
  let c = C.of_points [p0; p1; p2] in
  assert_equal ~msg:"err #1" (C.dim c) 2;
  let ps = Array.of_list (C.points c)
  and ps' = Array.init 3 (C.point c) in
  assert_equal ~msg:"err #2" ps ps'

let test_centre _ =
  let p0 = P.of_list [Now 3.; Now 2.]
  and p1 = P.of_list [Now ~-. 1.; Now 4.]
  and p2 = P.of_list [Now ~-. 2.; Now ~-. 1.] in
  let c = C.of_points [p0; p1; p2] in
  let cn = CO.centre c
  and r = CO.radius c in
  let b1 = P.eq_tol cn (P.of_list [Now 0.0909090909091;
				   Now 1.18181818182])
  and b2 = Float_Real_Exact.eq_tol r (Now 3.02195820702) in
  assert_equal ~msg:"err #1" b1 (Now true);
  assert_equal ~msg:"err #2" b2 (Now true)

let test_area _ =
  let p0 = P.of_list [Now 3.; Now 2.]
  and p1 = P.of_list [Now ~-. 1.; Now 4.]
  and p2 = P.of_list [Now ~-. 2.; Now ~-. 1.] in
  let c = C.of_points [p0; p1; p2] in
  let area = CO.content c
  and cfer = CO.surface c
  and area' = Now 28.6897510927
  and cfer' = Now 18.9875234052 in
  let b1 = Float_Real_Exact.eq_tol cfer cfer'
  and b2 = Float_Real_Exact.eq_tol area area' in
  assert_equal ~msg:"err #1" b1 (Now true);
  assert_equal ~msg:"err #2" b2 (Now true)

let suite = "Circle test" >::: [
  "test_create" >:: test_create;
  "test_centre" >:: test_centre;
  "test_area" >:: test_area
			    ]

(* Sphere : 3D *)

(* Sphere passing through
   (3, 2, 1) (-1, 4, 1) (-2, -1, 1)
   (.090909, 1.1818, 4.02195)
   centre: (0.0909090909091, 1.18181818182, 1)
   radius: 3.02195820702 
   surface area (4*pi*r^2): 114.759004371
   volume (4/3*pi*r^3): 115.598971696 *)

let fixture _ =
  let p0 = P.of_list [Now 3.; Now 2.; Now 1.]
  and p1 = P.of_list [Now ~-. 1.; Now 4.; Now 1.]
  and p2 = P.of_list [Now ~-. 2.; Now ~-. 1.; Now 1.]
  and p3 = P.of_list [Now 0.0909090909091; Now 1.18181818182;
		      Now 4.02195820702] in
  let s = C.of_points [p0; p1; p2; p3] in
  p0, p1, p2, p3, s

let test_create1 _ =
  let p0, p1, p2, p3, s = fixture () in
  assert_equal ~msg:"err #1" (C.dim s) 3;
  let ps = Array.of_list (C.points s)
  and ps' = Array.init 4 (C.point s) in
  assert_equal ~msg:"err #2" ps ps'

let test_centre1 _ =
  let p0, p1, p2, p3, s = fixture () in
  let cn = CO.centre s
  and r = CO.radius s in
  let b1 = P.eq_tol cn (P.of_list
    [Now 0.0909090909091; Now 1.18181818182; Now 1.])
  and b2 = Float_Real_Exact.eq_tol r (Now 3.02195820702) in
  assert_equal ~msg:"err #1" b1 (Now true);
  assert_equal ~msg:"err #2" b2 (Now true)

let test_area1 _ =
  let _, _, _, _, s = fixture () in
  let vol = CO.content s
  and are = CO.surface s in
  let vol' = Now 115.598971696
  and are' = Now 114.759004371 in
  let b1 = Float_Real_Exact.eq_tol vol vol'
  and b2 = Float_Real_Exact.eq_tol are are' in
  assert_equal ~msg:"err #1" b1 (Now true);
  assert_equal ~msg:"err #2" b2 (Now true)

let suite1 = "Sphere test" >::: [
  "test_create1" >:: test_create1;
  "test_centre1" >:: test_centre1;
  "test_area1" >:: test_area1
			    ]
