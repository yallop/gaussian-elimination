open OUnit
open Staged
open Basetypes
open Float
open Tuple
open Vectoren

open Pointen

module V2R = VectorStaged (Float_Real_Exact) (Record2D)
module P = Iso_Axis_Ordered_En_Point (Float_Real_Exact) (V2R) (Record2D) 

let p0 () = P.of_immediate { c0 = 0.; c1 = 0. }
let p1 () = P.of_immediate { c0 = 10.; c1 = 10. }
let p2 () = P.of_immediate { c0 = 1.; c1 = 2. }

let test_eq _ =
  assert_equal ~msg:"err #1" (P.eq (P.of_immediate (P.orig 2)) (p0())) (Now true);
  assert_equal ~msg:"err #2" (P.neq (P.of_immediate (P.orig 2)) (p1())) (Now true)

let test_coordinate _ =
  assert_equal ~msg:"err #1" (P.coord (p2()) 0) (Now 1.);
  assert_equal ~msg:"err #2" (P.coord (p2()) 1) (Now 2.)

let suite = "Point E^n" >::: [
  "test_equality" >:: test_eq;
  "test_coordinate" >:: test_coordinate;
]
