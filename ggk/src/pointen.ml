open Algebra
open Vector
open Point
open Tuple

(* General point *)
module GPoint (N:MONOID) 
              (T : TUPLE with type ('a,'b) rep = ('a,'b) N.rep) = struct
  type n = N.n
  type 'a point = ('a,n) T.trep
  type ('a,'b) rep = ('a,'b) N.rep
  type ('a,'b) trep = ('a,'b) T.trep
  (* @TODO fix the order of parameters in Tuple signature *)
  let orig () = T.init (fun _ -> N.zero)
  let dim = T.dim
  let coord p i = T.proj p i
  (* coercions *)
  let of_list l = T.of_list l
  let to_array p = Array.init dim (coord p)
  let to_list p = Array.to_list (to_array p)
  let of_array p = of_list (Array.to_list p)

  (* equality *)
  let eq a b = T.map2fold N.eq N.and_ N.true_ a b
  let neq a b = N.not_ (eq a b)
end

(* Point in E^n *)
module En_Point (C : Repr.REPR)
                (N : REALFIELD with type ('a,'b) rep = ('a,'b) C.rep)
                (T : TUPLE with type ('a,'b) rep = ('a,'b) C.rep)
             (* : EUCLIDEAN *) = struct
  module N = N
  module P = GPoint(N)(T)
  module V = Vectoren.NormedVector(C)(N)(T)
  (* operations *)
  let pos_vec p = p
  let sub p0 p1 = V.sub (pos_vec p0) (pos_vec p1)
  let add p v =
    T.lettt v (fun v -> V.add v (pos_vec p))
    (* Code.let_ v (fun v ->
      mapi (fun i x -> V.N.add_s (V.coord v i) x) p) *)
  let lett v f = f v
end

(* There are several kinds of point orders *)

(* Ordered Point along certain axis *)
module Iso_Axis_Ordered_En_Point 
    (C : Repr.REPR)
    (N : REALFIELD with type ('a,'b) rep = ('a,'b) C.rep)
    (T : TUPLE with type ('a,'b) rep = ('a,'b) C.rep)
  (* : ISO_AXIS_ORDERED_EUCLIDEAN *) = struct
  include En_Point(C)(N)(T)

  (* apply is a utility that can generate better code
   * apply i p0 p1 f == f (proj i p0 p1) *)
  let apply2 f i p0 p1 = f (P.coord p0 i) (P.coord p1 i)
  let lt i p0 p1 = apply2 N.lt i p0 p1
  let le i p0 p1 = apply2 N.le i p0 p1
  let gt i p0 p1 = apply2 N.gt i p0 p1
  let ge i p0 p1 = apply2 N.ge i p0 p1
  (*
  let min i p0 p1 =
    T.lettt p0 (fun p0 -> T.lettt p1 (fun p1 ->
      T.ift (le i p0 p1) p0 p1))
  let max i p0 p1 =
    T.lettt p0 (fun p0 -> T.lettt p1 (fun p1 ->
      T.ift (ge i p0 p1) p0 p1))
  *)
end
