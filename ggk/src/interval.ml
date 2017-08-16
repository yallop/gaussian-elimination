open Staged
open Simplify

module FloatN = struct
  include Repr.GenRep(Repr.Imm)
  include Logic.LogicN
  let eq = (=)
  let neq = (<>)
  let of_int = float_of_int
  let compare = Pervasives.compare
  let lt = (<)
  let le = (<=)
  let gt = (>)
  let ge = (>=)
  let max = max
  let min = min
  let add = (+.)
  let neg = (~-.)
  let sub = (-.)
  let mul = ( *.)
  let inv = fun x -> 1. /. x
  let div = ( /. )
  let abs = abs_float
  let sqrt = sqrt
  let zero = 0.
  let one = 1.
  let negone = -1.
  let pi = 4.0 *. atan 1.0
end

module FloatC = struct
  include Repr.GenRep(Repr.Code)
  include Logic.LogicC
  let eq = fun x y -> .< .~x = .~y >.
  let neq = fun x y -> .< .~x <> .~y >.
  let of_int = fun x -> .< float_of_int .~x >.
  let compare = fun x y -> .< Pervasives.compare .~x .~y >.
  let lt = fun x y -> .< .~x < .~y >.
  let le = fun x y -> .< .~x <= .~y >.
  let gt = fun x y -> .< .~x > .~y >.
  let ge = fun x y -> .< .~x >= .~y >.
  let max = fun x y -> .< max .~x .~y >.
  let min = fun x y -> .< min .~x .~y >.
  let add = fun x y -> .< .~x +. .~y >.
  let sub = fun x y -> .< .~x -. .~y >.
  let mul = fun x y -> .< .~x *. .~y >.
  let neg = fun x -> .< ~-. .~x >.
  let abs = fun x -> .< abs_float .~x >.
  let inv = fun x -> .< 1. /. .~x >.
  let div = fun x y -> .< .~x /. .~y >.
  let sqrt = fun x -> .< sqrt .~x >.
  let zero = .<0.>.
  let one = .<1.>.
  let negone = .<-1.>.
  let pi = .< FloatN.pi >.
end

module Float_Set (* : Algebra.NSET *) = struct
  include Repr.GenRep(Repr.CGen)
  include Logic.LogicStaged
  type n = float

  let of_int n = Staged.of_atom (FloatN.of_int n)

  (* order structure *)
  let compare a b = Staged.binary FloatN.compare FloatC.compare a b
  let lt a b = Staged.binary FloatN.lt FloatC.lt a b
  let le a b = Staged.binary FloatN.le FloatC.le a b
  let gt a b = Staged.binary FloatN.gt FloatC.gt a b
  let ge a b = Staged.binary FloatN.ge FloatC.ge a b
  let max a b = Staged.binary FloatN.max FloatC.max a b
  let min a b = Staged.binary FloatN.min FloatC.min a b

  (* monoid structure *)
  let zero = Staged.of_atom FloatN.zero
  let add a b = monoid FloatN.zero FloatN.add FloatC.add (a,b)

  (* norm structure *)
  let norm x = Staged.unary FloatN.abs FloatC.abs x
end

module Float_Normed_Set (* : NORMED_SET *) = struct
  module R = Float_Set
  let norm x = Staged.unary FloatN.abs FloatC.abs x
end

module Float_Ring_Base = struct
  include Float_Set
  let one = Staged.of_atom FloatN.one
  let negone = Staged.of_atom FloatN.negone

  let neg a   = Staged.unary FloatN.neg FloatC.neg a
  let sub a b = inverse FloatN.zero neg FloatN.sub FloatC.sub a b
  let mul a b = ring FloatN.zero FloatN.one FloatN.negone neg FloatN.mul FloatC.mul a b
  let abs x = Staged.unary FloatN.abs FloatC.abs x

  (* binary powering *)
  let int_pow n x =
    match x with
    | {now = Some z} -> of_atom (z ** (FloatN.of_int n))
    | {later = (b,xx)} ->
        let k f = (match b with
          | Constant -> f xx
          | Comp     -> Repr.Code.let_ xx f) in
        let rec doit m z = match m with
        | 0 -> FloatC.one
        | 1 -> z
        | n -> if n mod 2 = 0 then 
                   Repr.Code.let_ (doit (n/2) z) (fun w -> FloatC.mul w w)
               else FloatC.mul xx (doit (n-1) z) in
        of_comp (k (doit n))
end

module Float_Sign_Inexact (E : sig val eps : float * ('a, float) code end) =
struct
  let eps = fst E.eps
  let eps_c = snd E.eps
  let sgn y s =
    let sgn_now s x = Sign.bind (x > eps) (x >= -.eps && x <= eps)
      (x < -.eps) (x >= -.eps) (x <= eps) s
    and sgn_later s x = Sign.bind
      .< .~x > .~eps_c >.
      .< let x = .~x and eps = .~eps_c in x >= -.eps &&  x <= eps >.
      .< .~x < -. .~eps_c >.
      .< .~x >= -. .~eps_c >.
      .< .~x <= .~eps_c >. s in
    unary (sgn_now s) (sgn_later s) y
end

module Float_Sign_Exact = struct
  let sgn y s =
    let n f z = f z FloatN.zero in
    let l f z = f z FloatC.zero in
    let sgn_now w x = Sign.bind
      (n FloatN.gt x) (n FloatN.eq x) (n FloatN.lt x)
      (n FloatN.ge x) (n FloatN.le x) w
    and sgn_later w x = Sign.bind
      (l FloatC.gt x) (l FloatC.eq x) (l FloatC.lt x)
      (l FloatC.ge x) (l FloatC.le x) w in
    unary (sgn_now s) (sgn_later s) y
end

module Float_Ring_Inexact
    (E : sig val eps : float * ('a, float) code end) (* : RING *) =
struct
  include Float_Ring_Base
  include Float_Sign_Inexact (E)
end

module Float_Field_Base = struct
  include Float_Ring_Base
  let inv x = Staged.unary FloatN.inv FloatC.inv x
  let div x y = inverse FloatN.one inv FloatN.div FloatC.div x y
end

module Float_Real_Base = struct
  include Float_Field_Base

  let pi = Staged.of_atom FloatN.pi
  let compare a b = Staged.binary FloatN.compare FloatC.compare a b
  let lt a b = Staged.binary FloatN.lt FloatC.lt a b
  let le a b = Staged.binary FloatN.le FloatC.le a b
  let gt a b = Staged.binary FloatN.gt FloatC.gt a b
  let ge a b = Staged.binary FloatN.ge FloatC.ge a b
  let max a b = Staged.binary FloatN.max FloatC.max a b
  let min a b = Staged.binary FloatN.min FloatC.min a b
  let sqrt x = Staged.unary FloatN.sqrt FloatC.sqrt x
end

module Float_Real_Exact (* : REALFIELD *) = struct
  include Float_Real_Base
  include Float_Sign_Exact
end

module Float_Real_Inexact
    (E : sig val eps : float * ('a, float) code end) (* : REALFIELD *) =
struct
  include Float_Real_Base
  include Float_Sign_Inexact (E)
end
