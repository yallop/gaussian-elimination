open Staged
open Hplane
open Instances
open Tuple

open OUnit

(* TO DO - add test cases using the inexact float with epsilon *)

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
          (H:HYPER_PLANE with type ('a,'b) rep = ('a,'b) ST.rep 
                          and type ('a,'b) trep = ('a,'b) ST.trep) = struct
  let inst4 f = .< fun ps p -> .~( to_code (f (Staged.of_marked (Constant, .<ps>.)) (ST.mkc (Constant, .<p>.)))) >.
  let inst5 f = .< fun ps p -> .~( ST.extract (f (Staged.of_marked (Constant, .<ps>.)) (ST.mkc (Constant, .<p>.)))) >.

  let st_array n ps = Array.to_list (Array.init n (fun i -> ST.mkc (Constant, .<(.~(to_code ps)).(i)>.))) 

  let dist = fun n -> inst4 (fun ps p -> 
      let ps' = st_array (n+1) ps in
      (* create a hyperplane *)
      let h = H.of_points ps' in H.dist h p)
  let proj = fun n -> inst5 (fun ps p ->
      let points = st_array n ps in 
      let l = H.of_points points in 
      H.project l p)
  let col = fun n -> inst4 (fun ps p -> (* collinear *)
      let points = st_array n ps in 
      let l = H.of_points points in 
      H.orient l p Sign.Zero)
  let pos = fun n -> inst4 (fun ps p -> (* on positive side *)
      let points = st_array n ps in 
      let l = H.of_points points in 
      H.orient l p Sign.Pos) (* positive is assumed to be on the left (ElSheikh, 2010, page 64)*)
end ;;
                      
module GenDist1D = Gen(Tuple.Tuple1D) (H0) ;;
module GenDist2D = Gen(Tuple.Record2D) (H1) ;;
module GenDist3D = Gen(Tuple.Record3D) (H2) ;;

(* HPLANE TEST *)

(*0-hyperplane dist ()*)
let dist1DCode = GenDist1D.dist 0;;
let dist1D = .! dist1DCode;;

let test_dist1D _ =
   let h = [|1.0|] in
   let p = 2.0 in
   assert_equal (dist1D h p) 1.0;;
 
(*1-hyperplane dist () on Line*)
let dist2DCode = GenDist2D.dist 1;;
let dist2D = .! dist2DCode;;

let test_dist2D_onLine _ =
(* the hyperplane h is a line in 2D space.  The line goes through the origin and 
 has a slope of 1.  The point p lies on the line (hyperplane). *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let p = {c0 = 0.5; c1 = 0.5} in
   assert_equal (dist2D h p) 0.0;;

(*1-hyperplane dist () off Line*)

let test_dist2D_offLineBelow _ =
(* the hyperplane h is a line in 2D space.  The line goes through the origin and 
 has a slope of 1.  The point p lies below the line (on the x axis). *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let p = {c0 = 1.0; c1 = 0.0} in 
   let cmp_f = (cmp_float ~epsilon: 1e-15) in
   assert_equal ~cmp: cmp_f (dist2D h p) (-1.0*.(sqrt 2.) /. 2.);;

let test_dist2D_offLineAbove _ =
(* the hyperplane h is a line in 2D space.  The line goes through the origin and 
 has a slope of 1.  The point p lies above the line (on the y axis). *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let p = {c0 = 0.0; c1 = 1.0} in 
   let cmp_f = (cmp_float ~epsilon: 1e-15) in
   assert_equal ~cmp: cmp_f (dist2D h p) ((sqrt 2.) /. 2.);;

(*2-hyperplane dist ()*)
let dist3DCode = GenDist3D.dist 2;;
let dist3D = .! dist3DCode;;

let test_dist3D_onPlane1 _ =
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p lies on the plane (hyperplane). *)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}|] in
   let p = {x = 1.0; y = 0.0; z = 0.0} in
   assert_equal (dist3D h p) 0.0;;

let test_dist3D_onPlane2 _ =
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p lies on the plane (hyperplane) at (1/3, 1/3, 1/3). *)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}|] in
   let p = {x = 1.0/.3.0; y = 1.0/.3.0; z = 1.0/.3.0} in
(*   Printf.printf "\n%g\n" (dist3D h p);; *)
   let cmp_f = fun a b -> abs_float (a -. b) <= 1e-15 in
   assert_equal ~cmp: cmp_f (dist3D h p) 0.0;;

let test_dist3D_belowPlane _ =
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p lies on below the plane (hyperplane) at the origin. *)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}|] in
   let p = {x = 0.0; y = 0.0; z = 0.0} in
   let cmp_f = (cmp_float ~epsilon: 1e-15) in
   assert_equal ~cmp: cmp_f (dist3D h p) (-1.0 /. (sqrt 3.0));;

let test_dist3D_fourPointPlane _ = (* this shouldn't be allowed by Hplane *)
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p lies on below the plane (hyperplane) at the origin. This
test uses 4 points instead of 3 to specify the plane, but the 4th point is also on
the plane. It would make more sense if having four points for a 2D plane is not allowed.*)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}; {x = 1.0/.3.0; y = 1.0/.3.0; z = 1.0/.3.0} |] in
   let p = {x = 0.0; y = 0.0; z = 0.0} in
   let cmp_f = (cmp_float ~epsilon: 1e-15) in
   assert_equal ~cmp: cmp_f (dist3D h p) (-1.0 /. (sqrt 3.0));;

(* 
Tests are not included for the following, since Hplane is not set-up for them:
- coincident points in the set of points specifying h
- too many points specifying h
- not enough points specifying h
*)

(* Line proj () *)
let proj2DCode = GenDist2D.proj 2;;
let proj2D = .! proj2DCode;;

let test_proj2D_coincident1 _ =
(* the hyperplane h is a line in 2D space.  The line (h) goes through the origin and 
 has a slope of 1.  The point p to be projected on h lies coincident with h. *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let p = {c0 = 1.0; c1 = 1.0} in
   assert_equal (proj2D h p) p;;

let test_proj2D_coincident2 _ =
(* the hyperplane h is a line in 2D space.  The line (h) goes through the origin and 
 has a slope of 1.  The point p projected on h lies coincident with h. *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let p = {c0 = -3.0; c1 = -3.0} in
   assert_equal (proj2D h p) p;;

let test_proj2D_origin _ =
(* the hyperplane h is a line in 2D space.  The line (h) goes through the origin and 
 has a slope of 1.  The point p projects onto the origin. *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let p = {c0 = -1.0; c1 = 1.0} in
   let pr = proj2D h p in
   let prExp = {c0 = 0.0; c1 = 0.0} in (* the expected projection *)
(*   Printf.printf "\n%g  %g\n" pr.c0 pr.c1;; *)
   let sqr = fun x -> x*.x in
   let cmp_f = fun a b -> sqrt (sqr (a.c0-.b.c0) +. sqr (a.c1-.b.c1)) <= 1e-15 in
   assert_equal ~cmp: cmp_f pr prExp;; (* the expected projection is close to the calculated *)

let test_proj2D_general1 _ =
(* the hyperplane h is a line in 2D space.  The line (h) goes through the origin and 
 has a slope of 1.  The line segment l projected on h is neither perpendicular nor
 parallel to h.  The line segment has a general orientation with respect to h. 
 projh l = (l dot h)/|h|^2 * h *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let l = {c0 = 0.5; c1 = 2.0} in
   let s = (l.c0 +. l.c1) /. 2.0 in
   let pr = proj2D h l in
   let prExp = {c0 = s; c1 = s} in (* the expected projection *)
   let sqr = fun x -> x*.x in
   let cmp_f = fun a b -> sqrt (sqr (a.c0-.b.c0) +. sqr (a.c1-.b.c1)) <= 1e-15 in
   assert_equal ~cmp: cmp_f pr prExp;; (* the expected projection is close to the calculated *)

let test_proj2D_general2 _ =
(* the hyperplane h is a line in 2D space.  The line (h) goes through the origin and 
 has a slope of 1.  The line segment l projected on h is neither perpendicular nor
 parallel to h.  The line segment has a general orientation with respect to h. 
 projh l = (l dot h)/|h|^2 * h *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let l = {c0 = -15.5; c1 = -21.7} in
   let s = (l.c0 +. l.c1) /. 2.0 in
   let pr = proj2D h l in
   let prExp = {c0 = s; c1 = s} in (* the expected projection *)
   let sqr = fun x -> x*.x in
   let cmp_f = fun a b -> sqrt (sqr (a.c0-.b.c0) +. sqr (a.c1-.b.c1)) <= 1e-14 in
   assert_equal ~cmp: cmp_f pr prExp;; (* the expected projection is close to the calculated *)

let test_proj2D_hNotThroughOrigin _ =
(* the hyperplane h is a line in 2D space.  The line (h) goes through the (0, -1) and 
 (1, 0).  It does not pass through the origin.  The point p is projected on h. 
 The expected solution is found by taking point q as (1,0) (q lies on h).  The point p
 (to be projected) is (c0, c1).  The answer then is:
 q + projh (pq), where projh (pq) is the projection of vector pq (that is p - q) onto plane h *)
   let h = [|{c0 = 0.0; c1 = -1.0}; {c0 = 1.0; c1 = 0.0}|] in
   let p = {c0 = 1.0; c1 = 1.0} in
   let q = {c0 = 1.0; c1 = 0.0} in (* q has to lie on the hyperplane *)
   let pr = proj2D h p in
   let s = (p.c0 -. q.c0 +. p.c1 -. q.c1) /. 2.0 in
   let prExp = {c0 = q.c0 +. s; c1 = q.c1 +. s} in
   let sqr = fun x -> x*.x in
   let cmp_f = fun a b -> sqrt (sqr (a.c0-.b.c0) +. sqr (a.c1-.b.c1)) <= 1e-15 in
   assert_equal ~cmp: cmp_f pr prExp;; (* the expected projection is close to the calculated *)

(* Plane proj () *)
let proj3DCode = GenDist3D.proj 3;;
let proj3D = .! proj3DCode;;

let test_proj3D_onPlane _ =
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p to be projected on h lies on the plane h. *)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}|] in
   let p = {x = 1.0; y = 0.0; z = 0.0} in
   let pr = proj3D h p in
   let prExp = p in (* the expected projection *)
   let sqr = fun x -> x*.x in
   let cmp_f = fun a b -> sqrt (sqr (a.x-.b.x) +. sqr (a.y-.b.y) +. sqr (a.z-.b.z)) <= 1e-15 in
   assert_equal ~cmp: cmp_f pr prExp;; (* the expected projection is close to the calculated *)

let test_proj3D_alongNormal _ =
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p to be projected on h lies on the unit normal of h. *)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}|] in
   let p = {x = 1.0; y = 1.0; z = 1.0} in
   let pr = proj3D h p in
   let prExp = {x = 1.0/.3.0; y = 1.0/.3.0; z = 1.0/.3.0} in (* the expected projection *)
   let sqr = fun x -> x*.x in
   let cmp_f = fun a b -> sqrt (sqr (a.x-.b.x) +. sqr (a.y-.b.y) +. sqr (a.z-.b.z)) <= 1e-15 in
   assert_equal ~cmp: cmp_f pr prExp;; (* the expected projection is close to the calculated *)

let test_proj3D_notAlongNormal _ =
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p to be projected on h does not lie on the unit normal of h. 
Instead the test problem is constructed from selecting the solution (projection) to be
(1, 0, 0).  The point to be projected is found by selecting a point along the normal (using
the scalar value s) and then adding to this point the same vector that moves the point
(1/3, 1/3, 1/3) to the point (1, 0, 0). *)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}|] in
   let s = 3.5 in (* some scalar value *)
   let p = {x = (sqrt(3.0)*.s +. 2.0)/.3.0; y = (sqrt(3.0)*.s -. 1.0)/.3.0; z = (sqrt(3.0)*.s -. 1.0)/.3.0} in
   let pr = proj3D h p in
   let prExp = {x = 1.0; y = 0.0; z = 0.0} in (* the expected projection *)
   let sqr = fun x -> x*.x in
   let cmp_f = fun a b -> sqrt (sqr (a.x-.b.x) +. sqr (a.y-.b.y) +. sqr (a.z-.b.z)) <= 1e-15 in
   assert_equal ~cmp: cmp_f pr prExp;; (* the expected projection is close to the calculated *)

(*H0 collinear ()*)
let col1DCode = GenDist1D.col 1;;
let col1D = .! col1DCode;;

let test_col1D_false _ =
(* the hyperplane h is a point in 1D space; that is, it is a point along the "real" number line.
The point p is a point that is not located at the same location as h.  The test for collinearity
then should return false *)
   let h = [|1.0|] in
   let p = 2.0 in
   assert_equal (col1D h p) false;;

let test_col1D_true _ =
(* the hyperplane h is a point in 1D space; that is, it is a point along the "real" number line.
The point p is a point that is located at the same location as h.  The test for collinearity
then should return true *)
   let h = [|1.0|] in
   let p = 1.0 in
   assert_equal (col1D h p) true;;

(*H1 col ()*)
let col2DCode = GenDist2D.col 2 ;;
let col2D = .! col2DCode;;

let test_col2D_collinear _ =
(* the hyperplane h is a line in 2D space.  The line (h) goes through the origin and 
 has a slope of 1.  The point p to be tested for collinearity lies on h. *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let s = 2.0 in
   let p = {c0 = s; c1 = s} in
   assert_equal (col2D h p) true;;

let test_col2D_above _ =
(* the hyperplane h is a line in 2D space.  The line (h) goes through the origin and 
 has a slope of 1.  The point p to be tested for collinearity lies above h. *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let s = 2.0 in
   let p = {c0 = s; c1 = 2.0*.s} in
   assert_equal (col2D h p) false;;

let test_col2D_below _ =
(* the hyperplane h is a line in 2D space.  The line (h) goes through the origin and 
 has a slope of 1.  The point p to be tested for collinearity lies below h. *)
   let h = [|{c0 = 0.0; c1 = 0.0}; {c0 = 1.0; c1 = 1.0}|] in
   let s = 2.0 in
   let p = {c0 = 2.0*.s; c1 = s} in
   assert_equal (col2D h p) false;;

(*H2 plane col ()*)
let col3DCode = GenDist3D.col 3 ;;
let col3D = .! col3DCode;;

let test_col3D_onPlane _ =
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p to be tested for collinearity on h lies on the plane h. *)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}|] in
   let p = {x = 1.0; y = 0.0; z = 0.0} in
   assert_equal (col3D h p) true;;

let test_col3D_abovePlane _ =
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p to be tested for collinearity on h lies above the plane h. *)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}|] in
   let p = {x = 1.0; y = 1.0; z = 1.0} in
   assert_equal (col3D h p) false;;

let test_col3D_belowPlane _ =
(* the hyperplane h is a 2D plane in 3D space.  The plane has the unit normal vector
1/sqrt(3), 1/sqrt(3), 1/sqrt(3) and goes through the points (1, 0, 0), (0, 0, 1)
and (0, 1, 0).  The point p to be tested for collinearity on h lies below the plane h. *)
   let h = [|{x = 1.0; y = 0.0; z = 0.0}; {x = 0.0; y = 1.0; z = 0.0}; {x = 0.0; y = 0.0; z = 1.0}|] in
   let p = {x = -1.0; y = -1.0; z = -1.0} in
   assert_equal (col3D h p) false;;

(*H0 positive ()*)
let pos1DCode = GenDist1D.pos 1;;
let pos1D = .! pos1DCode;;

let test_pos1D_false _ =
(* the hyperplane h is a point in 1D space; that is, it is a point along the "real" number line.
The point p is a point that is not located above the location as h.  That is, p
is to the left of h.  The test for positive should return true *)
   let h = [|1.0|] in
   let p = -2.0 in
   assert_equal (pos1D h p) true;;

(* Test Suite *)

let suite = "OUnit Test" >:::
   ["test_dist1D" >:: test_dist1D;
    "test_dist2D_onLine" >:: test_dist2D_onLine;
    "test_dist2D_offLineBelow" >:: test_dist2D_offLineBelow;
    "test_dist2D_offLineAbove" >:: test_dist2D_offLineAbove;
    "test_dist3D_onPlane1" >:: test_dist3D_onPlane1;
    "test_dist3D_onPlane2" >:: test_dist3D_onPlane2;
    "test_dist3D_belowPlane" >:: test_dist3D_belowPlane;
    "test_dist3D_fourPointPlane" >:: test_dist3D_fourPointPlane;
    "test_proj2D_coincident1" >:: test_proj2D_coincident1;
    "test_proj2D_coincident2" >:: test_proj2D_coincident2;
    "test_proj2D_origin" >:: test_proj2D_origin;
    "test_proj2D_general1" >:: test_proj2D_general1; 
    "test_proj2D_general2" >:: test_proj2D_general2;
    "test_proj2D_hNotThroughOrigin" >:: test_proj2D_hNotThroughOrigin;
    "test_proj3D_onPlane" >:: test_proj3D_onPlane;
    "test_proj3D_alongNormal" >:: test_proj3D_alongNormal; 
    "test_proj3D_notAlongNormal" >:: test_proj3D_notAlongNormal; 
    "test_col1D_false" >:: test_col1D_false;
    "test_col1D_true" >:: test_col1D_true;
    "test_col2D_collinear" >:: test_col2D_collinear;
    "test_col2D_above" >:: test_col2D_above; 
    "test_col2D_below" >:: test_col2D_below;
    "test_col3D_onPlane" >:: test_col3D_onPlane;
    "test_col3D_abovePlane" >:: test_col3D_abovePlane;
    "test_col3D_belowPlane" >:: test_col3D_belowPlane;
    "test_pos1D_false" >:: test_pos1D_false] 

let _ =
   run_test_tt_main suite