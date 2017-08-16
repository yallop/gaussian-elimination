(* tests with integers, instead of inexact floats, as the field type *)

open Staged
open Vector
open Instances
open Tuple

open OUnit

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
          (V:RMODULE with type ('a,'b) rep = ('a,'b) ST.rep and type ('a,'b) trep = ('a,'b) ST.trep) = struct
  let inst1 f = .< fun a -> .~( to_code (f (ST.mkc (Constant, .<a>.)))) >.
  let inst2 f = .< fun a b -> .~( ST.extract (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.
  let inst3 f = .< fun a b -> .~( to_code (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.

  let test2 () = inst2 V.sub
  let test5 () = inst3 V.dot
end

module GV1P = Gen(Tuple.Tuple1D)(V1Int);;
module GV3R = Gen(Tuple.Record3D)(V3Int);;

(* VECTOR RESULTS TEST *)

(* VectorStaged Tuple1D sub *)

let resGV1P = GV1P.test2 ();;
let rGV1P = .! resGV1P;;

let a = 13;;
let b = 5;;
let test_GV1P_posResult_sub _ =
   assert_equal (a - b) (rGV1P a b);;

let test_GV1P_negResult_sub _ =
   assert_equal (b - a) (rGV1P b a);;

(* VectorStaged Record3D sub *)

let resGV3R = GV3R.test2 ();;
let rGV3R = .! resGV3R;;

let a = {x = 1; y = 1; z = 1};;
let b = {x = 3; y = 15; z = -3};;
let test_GV3R_sub _ =
   let ax = a.x in
   let ay = a.y in
   let az = a.z in
   let bx = b.x in
   let by = b.y in
   let bz = b.z in
   assert_equal ({x = ax - bx; y = ay - by; z = az - bz}) (rGV3R a b);;

(* VectorStaged Tuple1D dot *)

let resGV1P = GV1P.test5 ();;
let rGV1P = .! resGV1P;;

let a = -5;;
let b = 10;;
let test_GV1P_dot _ =
   assert_equal (a*b) (rGV1P a b);;

(* VectorStaged Record3D dot *)

let resGV3R = GV3R.test5 ();;
let rGV3R = .! resGV3R;;

let a = {x = 1; y = 1; z = 1};;
let b = {x = 3; y = 15; z = -3};;

let test_GV3R_dot _ =
   assert_equal (a.x*b.x + a.y*b.y + a.z*b.z) (rGV3R a b);;

(* Test Suite *)

let suite = "OUnit Test" >:::
   [
    "test_GV1P_posResult_sub" >:: test_GV1P_posResult_sub;
    "test_GV1P_negResult_sub" >:: test_GV1P_negResult_sub;
    "test_GV3R_sub" >:: test_GV3R_sub;
    "test_GV1P_dot" >:: test_GV1P_dot;
    "test_GV3R_dot" >:: test_GV3R_dot]

let _ =
   run_test_tt_main suite
