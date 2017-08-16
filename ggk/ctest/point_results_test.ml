open Staged
open Point
open Instances
open Tuple
open Vector

open OUnit

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
          (E : ISO_AXIS_ORDERED_EUCLIDEAN with type ('a,'b) N.rep = ('a,'b) ST.rep 
                                           and type ('a,'b) P.trep = ('a,'b) ST.trep) = struct
  let inst1 f = .< fun a -> .~( to_code (f (ST.mkc (Constant, .<a>.)))) >.
  let inst2 f = .< fun a b -> .~( ST.extract (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.
  let inst3 f = .< fun a b -> .~( to_code (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.

  let test1 () = inst2 E.sub
  let test2 () = inst3 (E.lt 0)
  let test3 () = inst3 (fun a b -> E.V.length (E.sub a b)) (* dist *)

end

module GP2R = Gen(Tuple.Record2D) (P2R) ;;
module GP3R = Gen(Tuple.Record3D) (P3R) ;;

(* POINT TEST *)

(* Point_En Record2d sub () *)
let resGP2R = GP2R.test1 () ;;
let rGP2R = .! resGP2R;;

let p1 = {c0 = 1.0; c1 = 1.0};;
let p2 = {c0 = 3.0; c1 = 6.0};;
let test_GP2R_sub _ =
   let v = {c0 = p1.c0 -. p2.c0; c1 = p1.c1 -. p2.c1} in
   assert_equal (v) (rGP2R p1 p2);;

(* Point_En Record3d sub () *)
let resGP3R = GP3R.test1 () ;;
let rGP3R = .! resGP3R;;

let p1 = {x = 1.0; y = 1.0; z = 3.0};;
let p2 = {x = 3.0; y = 6.0; z = 15.0};;
let test_GP3R_sub _ =
   let v = {x = p1.x -. p2.x; y = p1.y -. p2.y; z = p1.z -. p2.z} in
   assert_equal (v) (rGP3R p1 p2);;

(* Point_En Record2d cmp_x () *)
let resGP2R = GP2R.test2 () ;;
let rGP2R = .! resGP2R;;

let p1 = {c0 = 3.0; c1 = 1.0};;
let p2 = {c0 = 3.0; c1 = 6.0};;
let test_GP2R_cmp_x1 _ =
   assert_equal (p1.c0 < p2.c0) (rGP2R p1 p2);;

let p1 = {c0 = 1.0; c1 = 6.0};;
let p2 = {c0 = 3.0; c1 = 1.0};;
let test_GP2R_cmp_x2 _ =
   assert_equal (p1.c0 < p2.c0) (rGP2R p1 p2);;

let p1 = {c0 = 5.0; c1 = 6.0};;
let p2 = {c0 = 3.0; c1 = 6.0};;
let test_GP2R_cmp_x3 _ =
   assert_equal (p1.c0 < p2.c0) (rGP2R p1 p2);;

(* Point_En Record3d cmp_x () *)
let resGP3R = GP3R.test2 () ;;
let rGP3R = .! resGP3R;;

let p1 = {x = 1.0; y = 6.0; z = 33.0};;
let p2 = {x = 3.0; y = 1.0; z = 15.0};;
let test_GP3R_cmp_x1 _ =
   assert_equal (p1.x < p2.x) (rGP3R p1 p2);;

let p1 = {x = 3.0; y = 1.0; z = 33.0};;
let p2 = {x = 3.0; y = 6.0; z = 15.0};;
let test_GP3R_cmp_x2 _ =
   assert_equal (p1.x < p2.x) (rGP3R p1 p2);;

let p1 = {x = 5.0; y = 1.0; z = 3.0};;
let p2 = {x = 3.0; y = 6.0; z = 15.0};;
let test_GP3R_cmp_x3 _ =
   assert_equal (p1.x < p2.x) (rGP3R p1 p2);;

(* Point_En Record2d dist () *)
let resGP2R = GP2R.test3 () ;;
let rGP2R = .! resGP2R;;

let p1 = {c0 = 1.0; c1 = 1.0};;
let p2 = {c0 = 3.0; c1 = 6.0};;
let test_GP2R_dist _ =
   let v = {c0 = p1.c0 -. p2.c0; c1 = p1.c1 -. p2.c1} in
   assert_equal (sqrt(v.c0*.v.c0 +. v.c1*.v.c1)) (rGP2R p1 p2);;

(* Point_En Record3d dist () *)
let resGP3R = GP3R.test3 () ;;
let rGP3R = .! resGP3R;;

let p1 = {x = 1.0; y = 1.0; z = 3.0};;
let p2 = {x = 3.0; y = 6.0; z = 15.0};;
let test_GP3R_dist _ =
   let v = {x = p1.x -. p2.x; y = p1.y -. p2.y; z = p1.z -. p2.z} in
   assert_equal (sqrt(v.x*.v.x +. v.y*.v.y +. v.z*.v.z)) (rGP3R p1 p2);;


(* Test Suite *)

let suite = "OUnit Test" >:::
   ["test_GP2R_sub" >:: test_GP2R_sub;
    "test_GP3R_sub" >:: test_GP3R_sub;
    "test_GP2R_cmp_x1" >:: test_GP2R_cmp_x1;
    "test_GP2R_cmp_x2" >:: test_GP2R_cmp_x2;
    "test_GP2R_cmp_x3" >:: test_GP2R_cmp_x3;
    "test_GP3R_cmp_x1" >:: test_GP3R_cmp_x1;
    "test_GP3R_cmp_x2" >:: test_GP3R_cmp_x2;
    "test_GP3R_cmp_x3" >:: test_GP3R_cmp_x3;
    "test_GP2R_dist" >:: test_GP2R_dist;
    "test_GP3R_dist" >:: test_GP3R_dist]

let _ =
   run_test_tt_main suite