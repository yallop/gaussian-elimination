open Staged
open Instances

open OUnit

let one = lift_const 1.0;;
let s1 = S1.of_centre_radius (P1.P.orig ()) (one) ;;

let p1a = P1.P.of_list [lift_const 0.5];;
let p1b = P1.P.of_list [lift_const 1.5];;
let s2 = S2.of_centre_radius (EP2R.P.orig ()) (one) ;;
let p2a = EP2R.P.of_list [lift_const 0.5; lift_const 0.];;
let p2b = EP2R.P.of_list [lift_const 1.5; lift_const 0.];;
let s3 = S3.of_centre_radius (EP3R.P.orig ()) (one) ;;
let p3a = EP3R.P.of_list [lift_const 0.5; lift_const 0.; lift_const 0.3];;
let p3b = EP3R.P.of_list [lift_const 1.5; lift_const 0.; lift_const 0.3];;

(* helper function *)
let nowVal vs = vs.now

let stripSome v = match v with
   | Some v -> v
   | None -> failwith "None is not a valid option value"

let to_value vs = stripSome (nowVal vs)

(* SPHERE TEST *)

(* Sphere 1 content () *)
let test_vol1D _ =
   assert_equal (to_value (S1.content s1)) (2.0);;

(* Sphere 2 content ()*)
let test_vol2D _ =
   assert_equal (to_value (S2.content s2)) 3.14159265358979312;;

(* Sphere 3 content () *)
let test_vol3D _ =
   assert_equal (to_value (S3.content s3)) 4.18879020478639053;;

(* Sphere 1 surface () *)
let test_surf1D _ =
   assert_equal (to_value (S1.surface s1)) (2.0);;

(* Sphere 2 surface () *)
let test_surf2D _ =
   assert_equal (to_value (S2.surface s2)) (6.28318530717958623);;

(* Sphere 3 surface () *)
let test_surf3D _ =
   assert_equal (to_value (S3.surface s3)) (12.5663706143591725);;

(* Sphere 1 inside () True *)
let test_inside1DTrue _ =
   assert_equal (to_value (S1.inside s1 p1a)) (true);;

(* Sphere 2 inside () True *)
let test_inside2DTrue _ =
   assert_equal (to_value (S2.inside s2 p2a)) (true);;

(* Sphere 3 inside () True *)
let test_inside3DTrue _ =
   assert_equal (to_value (S3.inside s3 p3a)) (true);;

(* Sphere 1 inside () False *)
let test_inside1DFalse _ =
   assert_equal (to_value (S1.inside s1 p1b)) (false);;

(* Sphere 2 inside () False *)
let test_inside2DFalse _ =
   assert_equal (to_value (S2.inside s2 p2b)) (false);;

(* Sphere 3 inside () False *)
let test_inside3DFalse _ =
   assert_equal (to_value (S3.inside s3 p3b)) (false);;

(* Test Suite *)

let suite = "OUnit Test" >:::
   ["test_vol1D" >:: test_vol1D; 
    "test_vol2D" >:: test_vol2D;
    "test_vol3D" >:: test_vol3D;
    "test_surf1D" >:: test_surf1D;
    "test_surf2D" >:: test_surf2D;
    "test_surf3D" >:: test_surf3D;
    "test_inside1DTrue" >:: test_inside1DTrue;
    "test_inside2DTrue" >:: test_inside2DTrue;
    "test_inside3DTrue" >:: test_inside3DTrue;
    "test_inside1DFalse" >:: test_inside1DFalse;
    "test_inside2DFalse" >:: test_inside2DFalse;
    "test_inside3DFalse" >:: test_inside3DFalse] 

let _ =
   run_test_tt_main suite
