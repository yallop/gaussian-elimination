open Staged
open Point
open Simplex
open Instances
open Tuple

open OUnit

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
           (E : EUCLIDEAN with type ('a,'b) N.rep = ('a,'b) ST.rep 
                           and type ('a,'b) P.trep = ('a,'b) ST.trep) = struct
  let inst4 f = .< fun ps p -> .~( to_code (f (Staged.of_marked (Constant, .<ps>.)) (ST.mkc (Constant, .<p>.)))) >.
  let st_array n ps = Array.to_list (Array.init n (fun i -> ST.mkc (Constant, .<(.~(to_code ps)).(i)>.))) 

  module S = N_Simplex(E)

  let in_ n = inst4 (fun ps p -> 
      let ps' = st_array n ps in
      (* create a hyperplane *)
      S.in_ (S.of_vertices ps') p )

  let out n = inst4 (fun ps p -> 
      let ps' = st_array n ps in
      (* create a hyperplane *)
      S.out (S.of_vertices ps') p )

  let on n = inst4 (fun ps p -> 
      let ps' = st_array n ps in
      (* create a hyperplane *)
      fst (S.on (S.of_vertices ps') p) )

  let onIndex n = inst4 (fun ps p -> (* returns the face number, edge number, that point lies on *)
      let ps' = st_array n ps in
      (* create a hyperplane *)
      snd (S.on (S.of_vertices ps') p) )

  let in_or_on n = inst4 (fun ps p -> 
      let ps' = st_array n ps in
      (* create a hyperplane *)
      S.in_or_on (S.of_vertices ps') p )

end;;

module GSeg = Gen (Tuple.Tuple1D)(P1) ;;
module GTri = Gen (Tuple.Record2D)(P2R) ;;
module GTet = Gen (Tuple.Record3D)(P3R) ;;

(* INSIDE TEST *)

(* GSeg.in_ 2;; *) (* testing segments might not work? *)

(* Simplex 2D Triangle *)

(* Verticies, points and simplex taken from Mustafa's utest folder *)

(* verticies *)
let v0 = {c0 = 4.0; c1 = 3.0}
let v1 = {c0 = 1.0; c1 = 5.0}
let v2 = {c0 = -1.0; c1 = -1.0}

(* s1 is taken from Mustafa's utest *)
let s1 = [| v0; v1 ; v2 |]

(* The points from Mustafa's utest are as follows: *)

(* outside *)
let p3 = {c0 = 3.0; c1 = 1.0}
let p4 = {c0 = -1.0; c1 = 4.0}

(* inside *)
let p5 = {c0 = 2.0; c1 = 3.0}

(* on *)
let p6 = {c0 = 0.0; c1 = 2.0}

(* collinear with v2v0 *)
let p7 = {c0 = 6.5; c1 = 5.0}

(* 2D Point inside triangle *)
let in_2DTriCode = GTri.in_ 3 ;;
let in_2DTri = .!(in_2DTriCode);;

(* 2D Point outside triangle *)
let out2DTriCode = GTri.out 3 ;;
let out2DTri = .!(out2DTriCode);;

(* 2D Point on triangle *)
let on2DTriCode = GTri.on 3 ;;
let on2DTri = .!(on2DTriCode);; (* true if point lies on any edge of triangle *)
let onIndex2DTriCode = GTri.onIndex 3 ;;
let onIndex2DTri = .!(onIndex2DTriCode);; (* returns the face (edge) number *)

let test_out _ =
(* the points tested are all outside the triangle *)
  assert_equal ~msg:"err #1" (out2DTri s1 p3) true;
  assert_equal ~msg:"err #2" (out2DTri s1 p4) true;
  assert_equal ~msg:"err #3" (on2DTri s1 p3) false;
  assert_equal ~msg:"err #4" (on2DTri s1 p4) false;
  assert_equal ~msg:"err #5" (in_2DTri s1 p3) false;
  assert_equal ~msg:"err #6" (in_2DTri s1 p4) false;;

let test_in _ =
(* the point is inside the simplex *)
  assert_equal ~msg:"err #1" (in_2DTri s1 p5) true;
  assert_equal ~msg:"err #2" (out2DTri s1 p5) false;
  assert_equal ~msg:"err #3" (on2DTri s1 p5) false;;

let test_on _ =
(* the point tested lies on an edge of the triangel *)
  assert_equal ~msg:"err #1" (on2DTri s1 p6) true;
  assert_equal ~msg:"err #2" (onIndex2DTri s1 p6) 0.0; (* should the face number be an integer? *)
  assert_equal ~msg:"err #3" (in_2DTri s1 p6) false;
  assert_equal ~msg:"err #4" (out2DTri s1 p6) false;
  (* rotate the triangle definition maintaining same
     orientation. now p6 is on edge 2 *)
  let s' = [| v1; v2; v0 |] in
  assert_equal ~msg:"err #5" (on2DTri s' p6) true;
  assert_equal ~msg:"err #6" (onIndex2DTri s' p6) 2.0;;  (* should the face number be an integer? *)

let test_col _ =
(* the point tested does not lie on an edge, but it is collinear with an edge *)
  assert_equal ~msg:"err #1" (out2DTri s1 p7) true;
  assert_equal ~msg:"err #2" (in_2DTri s1 p7) false;
  assert_equal ~msg:"err #3" (on2DTri s1 p7) false;;

(* Some additional tests not take from Mustafa's utest folder *)
let s2 = [|{c0 = 0.0; c1 = 0.0}; {c0 = 2.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|]

(* points for s2 *)

(* inside *)
let q1 = {c0 = 1.0; c1 = 0.5}

(* outside *)
let p8 = {c0 = -10.0; c1 = 40.0}

let test_in_2DTri_true _ =
(* the point is inside the simplex 2D triangle - using a different triangle *)
   assert_equal (in_2DTri s2 q1) true;; 

let test_in_2DTri_false _ =
(* the point is outside the simplex 2D triangle - using a different point *)
   assert_equal (in_2DTri s1 p8) false;;

let test_out2DTri_true _ =
(* the point is outside the simplex 2D triangle - using a different point *)
   assert_equal (out2DTri s1 p8) true;;

let test_out2DTri_false _ =
(* the point is inside the simplex 2D triangle - using a different triangle. *)
   assert_equal (out2DTri s2 q1) false;;

(* Simplex 3D Tetrahedron *)

(* Verticies, points and simplex *)

(* verticies *)
let v0 = {x = 1.0; y = 0.0; z = 0.0}
let v1 = {x = 0.0; y = 1.0; z = 0.0}
let v2 = {x = 0.0; y = 0.0; z = 1.0}
let v3 = {x = -1.0; y = 0.0; z = 0.0}

let s = [| v0; v1; v2; v3 |]

(* outside *)
let p4 = {x = 0.0; y = 0.0; z = 10.0}
let p5 = {x = 2.0; y = 1.0; z = 3.0}

(* inside *)
let p6 = {x = 0.0; y = 0.1; z = 0.1}

(* on *)
let p7 = {x = 0.0; y = 0.5; z = 0.0}

(* collinear with v2v0 *)
let p8 = {x = 3.0; y = 0.0; z = 0.0}

(* Inside simplex 3D Tetrahedron in_ () *)
let in_3DTetCode = GTet.in_ 4;;
let in_3DTet = .!(in_3DTetCode);;

(* 3D Point outside Tetrahedron *)
let out3DTetCode = GTet.out 4;;
let out3DTet = .!(out3DTetCode);;

(* 3D Point on Tetrahedron *)
let on3DTetCode = GTet.on 4;;
let on3DTet = .!(on3DTetCode);; (* true if point lies on any edge of or face of tet *)
let onIndex3DTetCode = GTet.onIndex 4;;
(* let onIndex3DTet = .!(onIndex3DTetCode);; (* returns the face number *) *)

let test_3DTest_out _ =
(* the points tested are all outside the tetrahedron *)
  assert_equal ~msg:"err #1" (out3DTet s p4) true;
  assert_equal ~msg:"err #2" (out3DTet s p5) true;
  assert_equal ~msg:"err #3" (on3DTet s p4) false;
  assert_equal ~msg:"err #4" (on3DTet s p5) false; 
  assert_equal ~msg:"err #5" (in_3DTet s p4) false;
  assert_equal ~msg:"err #6" (in_3DTet s p5) false;;

let test_3DTest_in _ =
(* the point is inside the simplex *)
  assert_equal ~msg:"err #1" (in_3DTet s p6) true;
  assert_equal ~msg:"err #2" (out3DTet s p6) false;
  assert_equal ~msg:"err #3" (on3DTet s p6) false;;

let test_3DTest_on _ =
(* the point tested lies on a face of the tet *)
  assert_equal ~msg:"err #1" (on3DTet s p7) true;
(*  assert_equal ~msg:"err #2" (onIndex2DTri s p7) 0.0; (* should the face number be an integer? *)
*)
  assert_equal ~msg:"err #3" (in_3DTet s p7) false;
  assert_equal ~msg:"err #4" (out3DTet s p7) false;
  (* rotate the tetrahedron definition maintaining same
     orientation. now p7 is on face ? *)
  let s' = [| v2; v3; v0; v1 |] in
  assert_equal ~msg:"err #5" (on3DTet s' p7) true;;
(*  assert_equal ~msg:"err #6" (onIndex2DTri s' p6) 2.0;;  (* should the face number be an integer? *)
*)

(* Test Suite *)

let suite = "OUnit Test" >:::
   ["test_out" >:: test_out;
    "test_in" >:: test_in; 
    "test_on" >:: test_on;
    "test_col" >:: test_col; 
    "test_in_2DTri_true" >:: test_in_2DTri_true;
    "test_in_2DTri_false" >:: test_in_2DTri_false;
    "test_out2DTri_true" >:: test_out2DTri_true;
    "test_out2DTri_false" >:: test_out2DTri_false;
    "test_3DTest_out" >:: test_3DTest_out;
    "test_3DTest_in" >:: test_3DTest_in;
    "test_3DTest_on" >:: test_3DTest_on]

let _ =
   run_test_tt_main suite
