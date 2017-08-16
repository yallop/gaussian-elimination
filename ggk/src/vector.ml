(* Operations of vector space:
     - vector -> vector
     vector * scalar -> scalar
     vector [+-] vector -> vector
     vector [./] scalar -> vector
     point - point -> vector
     point [+-] vector -> point
     point + point -> undef
*)

(* module over a RIG *)
module type RIGMODULE = sig
  include Repr.REP
  type n
  type ('a,'b) trep
  type ('a,'b) vector = ('a,'b) trep
  type coordinate_enum = int
  val dim : int
  val zero : unit -> ('a,n) vector
  val of_coords : ('a,'b) rep list -> ('a,'b) vector
  val coord : ('a,'b) vector -> coordinate_enum -> ('a,'b) rep
  val add : ('a,n) vector -> ('a,n) vector -> ('a,n) vector
  val dot : ('a,n) vector -> ('a,n) vector -> ('a,n) rep
  val scale : ('a,n) vector -> ('a,n) rep -> ('a,n) vector
  (* length squared *)
  val length2 : ('a,n) vector -> ('a,n) rep

  val letvv : ('a,'b) vector -> (('a,'b) vector -> ('a,'c) vector) -> ('a,'c) vector
  val letvn : ('a,'b) vector -> (('a,'b) vector -> ('a,'c) rep) -> ('a,'c) rep
end

(* module over a RING *)
module type RMODULE = sig
  include RIGMODULE
  val mirror : ('a,n) vector -> ('a,n) vector
  val sub : ('a,n) vector -> ('a,n) vector -> ('a,n) vector
  (* generalized cross product of n-vectors *)
  val gcross : ('a,n) vector list -> ('a,n) vector
end

(* Free Vectors *)
module type VECTOR = sig
  include RMODULE
  val shrink : ('a,n) vector -> ('a,n) rep -> ('a,n) vector
end

module type NORMEDVECTOR = sig
  include VECTOR
  (* unit vector *)
  val direction : ('a,n) vector -> ('a,n) vector
  val length : ('a,n) vector -> ('a,n) rep
end
