module type POINT = sig
  include Repr.REPR
  type n
  type ('a,'b) trep
  type 'a point = ('a,n) trep
  val dim : int (* each module has a fixed dimension *)
  (* of_list, to_list are utilties for generation time.
   * Coercion from/to lists is extremely useful at
   * generation time for tuple-like structures. It's not an optimal
   * choice for manipulating components of a point (because coercion
   * forgets about domain & design -specific information such as number
   * of dimensions). In addition, coercion breaks the encapsulation, thus
   * risking the model integrity. However, it is still a handy tool if
   * carefully used inside other modules such as simplex etc. *)
  val of_list : ('a,n) rep list -> 'a point
  val to_list : 'a point -> ('a,n) rep list
  val of_array : ('a,'b) rep array -> ('a,'b) trep
  val to_array : 'a point -> ('a,n) rep array
  val orig : unit -> 'a point
  val coord : 'a point -> int -> ('a,n) rep
  val eq : 'a point -> 'a point -> ('a,bool) rep
end

(* Point with ordering *)
module type ORDERED_POINT = sig
  include POINT
  val lt : 'a point -> 'a point -> ('a,bool) rep
  val le : 'a point -> 'a point -> ('a,bool) rep
  val gt : 'a point -> 'a point -> ('a,bool) rep
  val ge : 'a point -> 'a point -> ('a,bool) rep
end

(* Euclidean Space *)
module type EUCLIDEAN = sig
  module N : Algebra.REALFIELD
  module P : POINT with type n = N.n and type ('a,'b) rep = ('a,'b) N.rep
  module V : Vector.NORMEDVECTOR with type n = N.n 
                                  and type ('a,'b) rep = ('a,'b) N.rep
                                  and type ('a,'b) trep = ('a,'b) P.trep
  (* position vector of point *)
  val pos_vec : 'a P.point -> ('a,N.n) V.vector
  val add : 'a P.point -> ('a,N.n) V.vector -> 'a P.point
  val sub : 'a P.point -> 'a P.point -> ('a,N.n) V.vector

  val lett : ('a,'b) V.vector -> (('a,'b) V.vector -> 'a P.point) -> 'a P.point
  (* L_f(p) =  (p, f(p)) :: R^d -> R^d+1 *)
end

(* Special version of point ordering: axis-oriented ordering.
* The extra 'int' parameter referes to the coordinate in E^n *)
module type ISO_AXIS_ORDERED_EUCLIDEAN = sig
  include EUCLIDEAN
  val lt : int -> 'a P.point -> 'a P.point -> ('a,bool) N.rep
  val le : int -> 'a P.point -> 'a P.point -> ('a,bool) N.rep
  val gt : int -> 'a P.point -> 'a P.point -> ('a,bool) N.rep
  val ge : int -> 'a P.point -> 'a P.point -> ('a,bool) N.rep
end
