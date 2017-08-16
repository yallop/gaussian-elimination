open OUnit
open Staged
open Basetypes
open Algebra
open Float
open Tuple
open Vectoren
open Pointen
open Hplane
open Orient

module F = Float_Real_Exact
module V = VectorStaged (F) (Pair2D)
module P = En_Point (F) (V) (Pair2D)
module H = Line (F)(V)(P)
module HO = Orient (H)

(* Line between (1, 2), (9, 18) *)
(* -8.8944 x + 0.4772 y + 0 = 0 *)
(* basis : u = 8,16 normalized = 0.4472, 0.8944 *)
(* normal : -0.8944, 0.4772 *)

let test_orient _ =
  let a = P.of_list [Now 1.; Now 2.]
  and b = P.of_list [Now 9.; Now 18.] in
  let l = H.of_points [a; b] in
  let p1 = P.of_list [Now 10.; Now 10.]
  and p2 = P.of_list [Now 7.5; Now 15.]
  and p3 = P.of_list [Now 5.; Now 20.] in
  (* p2: on the line *)
  assert_equal ~msg:"err #1" (HO.col l p2) (Now true);
  (* p1: -ve distance & cw; same side of normal *)
  assert_equal ~msg:"err #2" (HO.cw l p1) (Now true);
  (* a b p1 == p1 a b; same order *)
  let con = HO.cw (H.of_points [p1; a]) b in
  assert_equal ~msg:"err #3" con (Now true);
  (* a b p1 =/= b a p1 *)
  let con = HO.ccw (H.of_points [b; a]) p1 in
  assert_equal ~msg:"err #4" con (Now true);
  (* p3: +ve distance & ccw; opposite side of normal *)
  assert_equal ~msg:"err #5" (HO.ccw l p3) (Now true)

let suite = "Orient point line test" >::: [
  "test_orient" >:: test_orient
]
