open OUnit
open Staged
open Basetypes
open Algebra
open Float
open Tuple
open Vectoren
open Pointen
open Hplane
open Vertex
open Simplex
open Inside

module F = Float_Real_Exact
module V = VectorStaged (F) (Record2D)
module P = En_Point (F) (V) (Record2D)
module H = Line (F)(V)(P)

module Ver = Vertex (P)
module S = N_Simplex (Ver)
module IS = Inside (H) (S)

(* 2D Point inside triangle *)

let fixture _ =
  let v0 = Ver.create (P.of_list [Now 4.; Now 3.])
  and v1 = Ver.create (P.of_list [Now 1.; Now 5.])
  and v2 = Ver.create (P.of_list [Now ~-. 1.; Now ~-. 1.])

  (* outside *)
  and p3 = P.of_list [Now 3.; Now 1.]
  and p4 = P.of_list [Now ~-. 1.; Now 4.]

  (* inside *)
  and p5 = P.of_list [Now 2.; Now 3.]

  (* on *)
  and p6 = P.of_list [Now 0.; Now 2.]

  (* collinear with v2v0 *)
  and p7 = P.of_list [Now 6.5; Now 5.] in

  let t = S.of_vertices [v0; v1; v2] in
  v0, v1, v2, p3, p4, p5, p6, p7, t

let test_out _ =
  let v0, v1, v2, p3, p4, p5, p6, p7, t = fixture () in
  assert_equal ~msg:"err #1" (IS.out t p3) (Now true);
  assert_equal ~msg:"err #2" (IS.out t p4) (Now true);
  assert_equal ~msg:"err #3" (fst (IS.on t p3)) (Now false);
  assert_equal ~msg:"err #4" (fst (IS.on t p4)) (Now false);
  assert_equal ~msg:"err #5" (IS.in_ t p3) (Now false);
  assert_equal ~msg:"err #6" (IS.in_ t p4) (Now false)

let test_in _ =
  let v0, v1, v2, p3, p4, p5, p6, p7, t = fixture () in
  assert_equal ~msg:"err #1" (IS.in_ t p5) (Now true);
  assert_equal ~msg:"err #2" (IS.out t p5) (Now false);
  assert_equal ~msg:"err #3" (fst (IS.on t p5)) (Now false)

let test_on _ =
  let v0, v1, v2, p3, p4, p5, p6, p7, t = fixture () in
  let on, i = IS.on t p6 in
  assert_equal ~msg:"err #1" on (Now true);
  assert_equal ~msg:"err #2" i (Now 0);
  assert_equal ~msg:"err #3" (IS.in_ t p6) (Now false);
  assert_equal ~msg:"err #4" (IS.out t p6) (Now false);
  (* rotate the triangle definition maintaining same
     orientation. now p6 is on edge 2 *)
  let t' = S.of_vertices [v1; v2; v0] in
  let on, i = IS.on t' p6 in
  assert_equal ~msg:"err #5" on (Now true);
  assert_equal ~msg:"err #6" i (Now 2)

let test_col _ =
  let v0, v1, v2, p3, p4, p5, p6, p7, t = fixture () in
  assert_equal ~msg:"err #1" (IS.out t p7) (Now true);
  assert_equal ~msg:"err #2" (IS.in_ t p7) (Now false);
  assert_equal ~msg:"err #3" (fst (IS.on t p7)) (Now false)

let suite = "2D Point inside Triangle test" >::: [
  "test_out" >:: test_out;
  "test_in" >:: test_in;
  "test_on" >:: test_on;
  "test_col" >:: test_col;
]

