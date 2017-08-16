open OUnit
open Staged
open Basetypes
open Algebra
open Float
open Tuple
open Vectoren
open Pointen
open Sphere
open Hplane
open Insphere



module F = Float_Real_Exact
module V = VectorStaged (F) (Pair2D)
module P = En_Point (F) (V) (Pair2D)
module S = Sphere (F) (P)
module IS = Insphere (S)

let test_incircle _ =
  let a = P.of_list [Now 3.; Now 4.]
  and b = P.of_list [Now ~-. 2.; Now 4.]
  and c = P.of_list [Now ~-. 2.; Now ~-. 1.] in
  let s = S.of_points [a; b; c] in
  (* p0: in, p1: out, p2: on *)
  let p0 = P.of_list [Now 1.; Now 2.]
  and p1 = P.of_list [Now 5.; Now 5.]
  and p2 = P.of_list [Now 3.; Now ~-. 1.] in
  (* in *)
  assert_equal ~msg:"err #1" (IS.in_ s p0) (Now true);
  let s' = S.of_points [b; c; a] in
  assert_equal ~msg:"err #2" (IS.in_ s' p0) (Now true);
  (* out *)
  assert_equal ~msg:"err #3" (IS.out s p1) (Now true);
  let s' = S.of_points [b; a; c] in
  assert_equal ~msg:"err #4" (IS.in_ s' p1) (Now true);
  (* on *)
  assert_equal ~msg:"err #5" (IS.on s p2) (Now true)

let suite = "Insphere test" >::: [
  "test_incircle" >:: test_incircle;
]
