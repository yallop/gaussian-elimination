open Staged
open Vector
open Instances
open Tuple

open OUnit

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
          (V:NORMEDVECTOR with type ('a,'b) rep = ('a,'b) ST.rep and type ('a,'b) trep = ('a,'b) ST.trep) = struct
  let inst1 f = .< fun a -> .~( to_code (f (ST.mkc (Constant, .<a>.)))) >.
  let inst2 f = .< fun a b -> .~( ST.extract (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.
  let inst3 f = .< fun a b -> .~( to_code (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.

  let test1 () = inst1 V.length 
  let test2 () = inst2 V.sub
  let test3 () = inst3 (fun a b -> V.length (V.sub a b)) (* distance *)
  let test4 () = inst2 (fun a b -> V.direction (V.sub a b)) (* unit_vec *)
  let test5 () = inst3 V.dot
end

module GV1P = Gen(Tuple.Tuple1D)(V1);;
module GV2R = Gen(Tuple.Record2D)(V2R);;
module GV2P = Gen(Tuple.Pair2D)(V2P);;
module GV3R = Gen(Tuple.Record3D)(V3R);;

(* VECTOR RESULTS TEST *)

(* VectorStaged Tuple1D length *)

let resGV1P = GV1P.test1 ();;
let rGV1P = .! resGV1P;;

let input = 3.0;;
let test_GV1P_posNum_length _ =
   assert_equal (input) (rGV1P input);;

let input = -15.0;;
let test_GV1P_negNum_length _ =
   assert_equal (abs_float input) (rGV1P input);;

(* VectorStaged Record2D length *)

let resGV2R = GV2R.test1 ();;
let rGV2R = .! resGV2R;;

let input = {c0 = 1.0; c1 = 1.0};;
let test_GV2R_length _ =
   assert_equal (sqrt (input.c0 *. input.c0 +. input.c1 *. input.c1)) (rGV2R input);;

let input = {c0 = -1.0; c1 = -3.0};;
let test_GV2R_negQuad_length _ =
   assert_equal (sqrt (input.c0 *. input.c0 +. input.c1 *. input.c1)) (rGV2R input);;

(* VectorStaged Tuple2D (Pair) length *)

let resGV2P = GV2P.test1 ();;
let rGV2P = .! resGV2P;;

let input = (1.0, 3.0);;
let test_GV2P_posQuad_length _ =
   let x = fst input in
   let y = snd input in
   assert_equal (sqrt (x *. x +. y *. y)) (rGV2P input);;

let input = (-1.0, -3.0);;
let test_GV2P_negQuad_length _ =
   let x = fst input in
   let y = snd input in
   assert_equal (sqrt (x *. x +. y *. y)) (rGV2P input);;

(* VectorStaged Record3D length *)

let resGV3R = GV3R.test1 ();;
let rGV3R = .! resGV3R;;

let input = {x = 1.0; y = 1.0; z = 1.0};;
let test_GV3R_length _ =
   let v1 = input.x in
   let v2 = input.y in
   let v3 = input.z in
   assert_equal (sqrt (v1 *. v1 +. v2 *. v2 +. v3 *. v3)) (rGV3R input);;

let input = {x = -1.0; y = -7.0; z = -11.0};;
let test_GV3R_negQuad_length _ =
   let v1 = input.x in
   let v2 = input.y in
   let v3 = input.z in
   assert_equal (sqrt (v1 *. v1 +. v2 *. v2 +. v3 *. v3)) (rGV3R input);;

(* VectorStaged Tuple1D sub *)

let resGV1P = GV1P.test2 ();;
let rGV1P = .! resGV1P;;

let a = 13.0;;
let b = 5.0;;
let test_GV1P_posResult_sub _ =
   assert_equal (a -. b) (rGV1P a b);;

let test_GV1P_negResult_sub _ =
   assert_equal (b -. a) (rGV1P b a);;

(* VectorStaged Record2D sub *)

let resGV2R = GV2R.test2 ();;
let rGV2R = .! resGV2R;;

let a = {c0 = 1.0; c1 = 1.0};;
let b = {c0 = 3.0; c1 = 6.0};;
let test_GV2R_sub _ =
   let c = {c0 = a.c0 -. b.c0; c1 = a.c1 -. b.c1} in
   assert_equal (c) (rGV2R a b);;

(* VectorStaged Pair2D sub *)

let resGV2P = GV2P.test2 ();;
let rGV2P = .! resGV2P;;

let a = (1.0, 3.0);;
let b = (12.0, 15.0);;
let test_GV2P_sub _ =
   let xa = fst a in
   let ya = snd a in
   let xb = fst b in
   let yb = snd b in
   assert_equal ((xa -. xb, ya -. yb)) (rGV2P a b);;

(* VectorStaged Record3D sub *)

let resGV3R = GV3R.test2 ();;
let rGV3R = .! resGV3R;;

let a = {x = 1.0; y = 1.0; z = 1.0};;
let b = {x = 3.0; y = 15.0; z = -3.0};;
let test_GV3R_sub _ =
   let ax = a.x in
   let ay = a.y in
   let az = a.z in
   let bx = b.x in
   let by = b.y in
   let bz = b.z in
   assert_equal ({x = ax -. bx; y = ay -. by; z = az -. bz}) (rGV3R a b);;

(* VectorStaged Tuple1D dist *)

let resGV1P = GV1P.test3 ();;
let rGV1P = .! resGV1P;;

let a = 5.0;;
let b = 15.0;;
let test_GV1P_dist _ =
   assert_equal (abs_float (a -. b)) (rGV1P a b);;

(* VectorStaged Record2D dist *)

let resGV2R = GV2R.test3 ();;
let rGV2R = .! resGV2R;;

let a = {c0 = 1.0; c1 = 1.0};;
let b = {c0 = 3.0; c1 = 6.0};;
let mag v = sqrt (v.c0*.v.c0 +. v.c1*.v.c1)
let test_GV2R_dist _ =
   let c = {c0 = a.c0 -. b.c0; c1 = a.c1 -. b.c1} in
   assert_equal (mag c) (rGV2R a b);;

(* VectorStaged Pair2D dist *)

let resGV2P = GV2P.test3 ();;
let rGV2P = .! resGV2P;;

let a = (1.0, 3.0);;
let b = (12.0, 15.0);;
let mag v = 
   let x = fst v in
   let y = snd v in
   sqrt (x*.x +. y*.y)

let test_GV2P_dist _ =
   let xa = fst a in
   let ya = snd a in
   let xb = fst b in
   let yb = snd b in
   assert_equal (mag ((xa -. xb, ya -. yb))) (rGV2P a b);;

(* VectorStaged Record3D dist *)

let resGV3R = GV3R.test3 ();;
let rGV3R = .! resGV3R;;

let a = {x = 1.0; y = 1.0; z = 1.0};;
let b = {x = 3.0; y = 15.0; z = -3.0};;
let mag v = sqrt (v.x*.v.x +. v.y*.v.y +. v.z*.v.z);;
let test_GV3R_dist _ =
   let ax = a.x in
   let ay = a.y in
   let az = a.z in
   let bx = b.x in
   let by = b.y in
   let bz = b.z in
   assert_equal (mag ({x = ax -. bx; y = ay -. by; z = az -. bz})) (rGV3R a b);;

(* VectorStaged Tuple1D unit vector *)

let resGV1P = GV1P.test4 ();;
let rGV1P = .! resGV1P;;

let a = 5.0;;
let b = 10.0;;
let test_GV1P_unitV _ =
   assert_equal ((a -. b) /. abs_float (a -. b)) (rGV1P a b);;

(* VectorStaged Record2D unit vector *)

let resGV2R = GV2R.test4 ();;
let rGV2R = .! resGV2R;;

let a = {c0 = 1.0; c1 = 1.0};;
let b = {c0 = 3.0; c1 = 6.0};;
let mag v = sqrt (v.c0*.v.c0 +. v.c1*.v.c1)
let test_GV2R_unitV _ =
   let c = {c0 = (a.c0 -. b.c0); c1 = (a.c1 -. b.c1)} in
   let len = mag c in
   assert_equal ({c0 = c.c0/.len; c1 = c.c1/.len}) (rGV2R a b);;

(* VectorStaged Pair2D unit vector *)

let resGV2P = GV2P.test4 ();;
let rGV2P = .! resGV2P;;

let subCode = GV2P.test2 ();;
let sub = .! subCode;;

let lengthCode = GV2P.test1 ();;
let length = .! lengthCode;;

let a = (1.0, 3.0);;
let b = (12.0, 15.0);;

let test_GV2P_unitV _ =
   let d = sub a b in
   let len = length d in
   assert_equal (((fst d)/.len, (snd d)/.len)) (rGV2P a b);;

(* VectorStaged Record3D unit vector *)

let resGV3R = GV3R.test4 ();;
let rGV3R = .! resGV3R;;

let subCode = GV3R.test2 ();;
let sub = .! subCode;;

let lengthCode = GV3R.test1 ();;
let length = .! lengthCode;;

let a = {x = 1.0; y = 1.0; z = 1.0};;
let b = {x = 3.0; y = 15.0; z = -3.0};;

let test_GV3R_unitV _ =
   let d = sub a b in
   let len = length d in
   assert_equal ({x=d.x/.len; y=d.y/.len; z=d.z/.len}) (rGV3R a b);;

(* VectorStaged Tuple1D dot *)

let resGV1P = GV1P.test5 ();;
let rGV1P = .! resGV1P;;

let a = -5.0;;
let b = 10.0;;
let test_GV1P_dot _ =
   assert_equal (a*.b) (rGV1P a b);;

(* VectorStaged Record2D dot *)

let resGV2R = GV2R.test5 ();;
let rGV2R = .! resGV2R;;

let a = {c0 = 1.0; c1 = 1.0};;
let b = {c0 = 3.0; c1 = 6.0};;
let test_GV2R_dot _ =
   assert_equal (a.c0*.b.c0 +. a.c1*.b.c1) (rGV2R a b);;

(* VectorStaged Pair2D dot *)

let resGV2P = GV2P.test5 ();;
let rGV2P = .! resGV2P;;

let a = (1.0, 3.0);;
let b = (12.0, 15.0);;

let test_GV2P_dot _ =
   let ax = fst a in
   let ay = snd a in 
   let bx = fst b in
   let by = snd b in
   assert_equal (ax*.bx +. ay*.by) (rGV2P a b);;

(* VectorStaged Record3D dot *)

let resGV3R = GV3R.test5 ();;
let rGV3R = .! resGV3R;;

let a = {x = 1.0; y = 1.0; z = 1.0};;
let b = {x = 3.0; y = 15.0; z = -3.0};;

let test_GV3R_dot _ =
   assert_equal (a.x*.b.x +. a.y*.b.y +. a.z*.b.z) (rGV3R a b);;


(* Test Suite *)

let suite = "OUnit Test" >:::
   ["test_GV1P_posNum_length" >:: test_GV1P_posNum_length;
    "test_GV1P_negNum_length" >:: test_GV1P_negNum_length;
    "test_GV2R_negQuadlength" >:: test_GV2R_length;
    "test_GV2R_length" >:: test_GV2R_length;
    "test_GV2P_posQuad_length" >:: test_GV2P_posQuad_length;
    "test_GV2P_posQuad_length" >:: test_GV2P_posQuad_length;
    "test_GV3R_length" >:: test_GV3R_length;
    "test_GV3R_negQuad_length" >:: test_GV3R_negQuad_length;
    "test_GV1P_posResult_sub" >:: test_GV1P_posResult_sub;
    "test_GV1P_negResult_sub" >:: test_GV1P_negResult_sub;
    "test_GV2R_sub" >:: test_GV2R_sub;
    "test_GV2P_sub" >:: test_GV2P_sub;
    "test_GV3R_sub" >:: test_GV3R_sub;
    "test_GV1P_dist" >:: test_GV1P_dist;
    "test_GV2R_dist" >:: test_GV2R_dist;
    "test_GV2P_dist" >:: test_GV2P_dist;
    "test_GV3R_dist" >:: test_GV3R_dist;
    "test_GV1P_unitV" >:: test_GV1P_unitV;
    "test_GV2R_unitV" >:: test_GV2R_unitV;
    "test_GV2P_unitV" >:: test_GV2P_unitV;
    "test_GV3R_unitV" >:: test_GV3R_unitV;
    "test_GV1P_dot" >:: test_GV1P_dot;
    "test_GV2R_dot" >:: test_GV2R_dot;
    "test_GV2P_dot" >:: test_GV2P_dot;
    "test_GV3R_dot" >:: test_GV3R_dot]
let _ =
   run_test_tt_main suite
