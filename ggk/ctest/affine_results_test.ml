open Staged
open Affine
open Instances
open Tuple

open OUnit

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
          (AT : AFFINE with type ('a,'b) trep = ('a,'b) ST.trep) = struct
  let inst2 f = .< fun p v -> .~( ST.extract (f (ST.mkc (Constant, .<p>.)) (ST.mkc (Constant, .<v>.))) ) >.

  let test1 () = inst2 (fun p v -> let t = AT.translation v in AT.apply_p t p)
end

module G2R = Gen(Tuple.Record2D)(AT2R) ;;
module G3R = Gen(Tuple.Record3D)(AT3R) ;;

(* AFFINE TEST *)

(* Translation Record2d *)
let resG2R = G2R.test1 () ;;
let rG2R = .! resG2R;;

let p1 = {c0 = 1.0; c1 = -3.0};;
let v = {c0 = 3.0; c1 = 6.0};;
let test_G2R_trans _ =
   let p2 = {c0 = p1.c0 +. v.c0; c1 = p1.c1 +. v.c1} in
   assert_equal (p2) (rG2R p1 v);;

(* Translation Record3d *)
let resG3R = G3R.test1 () ;;
let rG3R = .! resG3R;;

let p1 = {x = 1.0; y = 1.0; z = 2.0};;
let v = {x = 3.0; y = 6.0; z = -4.0};;
let test_G3R_trans _ =
   let p2 = {x = p1.x +. v.x; y = p1.y +. v.y; z = p1.z +. v.z} in
   assert_equal (p2) (rG3R p1 v);;

(* Test Suite *)

let suite = "OUnit Test" >:::
   ["test_G2R_trans" >:: test_G2R_trans;
    "test_G3R_trans" >:: test_G3R_trans]

let _ =
   run_test_tt_main suite