open Staged

module type SET = sig
  include Repr.REP
end

module type NSET = sig
  include Logic.LOGIC
  include Repr.LANG with type ('a,'b) l = ('a,'b) rep

  type n
  val eq : ('a,n) rep -> ('a,n) rep -> ('a,bool) rep
  val neq : ('a,n) rep -> ('a,n) rep -> ('a,bool) rep
end

module GenSet(S:NSET) = struct
  include Repr.GenRep(S)

  let rec for_all p = function
    | [] -> S.true_
    | x :: xs -> S.and_ (p x) (for_all p xs)

  let rec exists p = function
    | [] -> S.false_
    | x :: xs -> S.or_ (p x) (exists p xs)

end

module type ORDER = sig
  include SET

  (* 0: equal ; +ve: > ; -ve: < *)
  val compare : ('a,'b) rep -> ('a,'b) rep -> ('a, int) rep
  val lt : ('a,'b) rel
  val le : ('a,'b) rel
  val gt : ('a,'b) rel
  val ge : ('a,'b) rel
  val min : ('a,'b) bin
  val max : ('a,'b) bin
end

module type MONOID = sig
  include NSET
  val zero : ('a,n) rep
  val add : ('a,n) bin
end

module type NORMED_SET = sig
  include SET
  module R : MONOID
  val norm : ('a,'b) rep -> ('a,'c) R.rep
end

module type RING = sig
  include MONOID (* include here is safe *)
  val one : ('a,n) rep
  val negone : ('a,n) rep
  val sub : ('a,n) bin
  val neg : ('a,n) una
  val mul : ('a,n) bin
  val of_int : int -> ('a,n) rep
  (* int_pow : x ^ n, where n : integer *)
  val int_pow : int -> ('a,n) rep -> ('a,n) rep
end

module GenListRing(C:Repr.LREP)
                  (R:RING with type ('a,'b) rep = ('a,'b) C.rep) = struct
  include C
  let findi p =
    let rec findi i = function
      | [] -> R.of_int i
      | x :: xs -> C.ife (p x) (R.of_int i) (findi (i+1) xs)
    in findi 0
end

module type FIELD = sig
  (* also safe *)
  include RING
  val inv : ('a,n) una
  val div : ('a,n) bin
end

module type REALFIELD = sig
  (* we can use only 1 include, the rest must be duplicated *)
  include FIELD
  (* 0: equal ; +ve: > ; -ve: < *)
  val compare : ('a,n) rep -> ('a,n) rep -> ('a, int) rep
  val lt : ('a,n) rel
  val le : ('a,n) rel
  val gt : ('a,n) rel
  val ge : ('a,n) rel
  val min : ('a,n) bin
  val max : ('a,n) bin
  val sgn : ('a,n) rep -> Sign.t -> ('a,bool) rep

  val pi : ('a,n) rep
  val sqrt : ('a,n) una

(*
  val cos : 'a ns -> 'a ns
  val sin : 'a ns -> 'a ns
  val tan : 'a ns -> 'a ns
  val acos : 'a ns -> 'a ns
  val asin : 'a ns -> 'a ns
  val atan : 'a ns -> 'a ns *)
end
