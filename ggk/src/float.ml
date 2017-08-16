open Staged
open Simplify

module FloatN = struct
  type n = float
  include Repr.GenRep(Repr.Imm)
  include Repr.ImmLang
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
  let norm = abs_float
  let sqrt = sqrt
  let zero = 0.
  let one = 1.
  let negone = -1.
  let pi = 4.0 *. atan 1.0
  let int_pow n x = x ** (float_of_int n)
(*  let sgn y s = 
    let n f z = f z zero in
    let sgn_now w x = Sign.bind
      (n gt x) (n eq x) (n lt x) (n ge x) (n le x) w in
    sgn_now s y *)
end

module FloatC = struct
  type n = float
  include Repr.GenRep(Repr.Code)
  include Repr.CodeLang
  include Logic.LogicC
  let eq = fun x y -> .< .~x = .~y >.
  let neq = fun x y -> .< .~x <> .~y >.
  let of_int = fun x -> .< float_of_int x >.
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
  let norm = fun x -> .< abs_float .~x >.
  let inv = fun x -> .< 1. /. .~x >.
  let div = fun x y -> .< .~x /. .~y >.
  let sqrt = fun x -> .< sqrt .~x >.
  let zero = .<0.>.
  let one = .<1.>.
  let negone = .<-1.>.
  let pi = .< FloatN.pi >.
  let int_pow = fun n x -> let m = float_of_int n in.< .~x ** m >.
(*  let sgn y s =
    let l f z = f z zero in
    let sgn_later w x = Sign.bind
      (l gt x) (l eq x) (l lt x) (l ge x) (l le x) w in
    sgn_later s y *)
end

module Float_Set (* : Algebra.NSET *) = struct
  include Repr.GenRep(Repr.CGen)
  include Repr.CGenLang
  include Logic.LogicStaged
  type n = float

  let of_int n = Staged.of_atom (FloatN.of_int n)

  (* equality *)
  let eq a b = Staged.binary FloatN.eq FloatC.eq a b 
  let neq a b = Staged.binary FloatN.neq FloatC.neq a b 

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
  let norm x = Staged.unary FloatN.norm FloatC.norm x
end

module Float_Normed_Set (* : NORMED_SET *) = struct
  module R = Float_Set
  let norm x = Staged.unary FloatN.norm FloatC.norm x
end

module Float_Ring_Base = struct
  include Float_Set
  let one = Staged.of_atom FloatN.one
  let negone = Staged.of_atom FloatN.negone

  let neg a   = Staged.unary FloatN.neg FloatC.neg a
  let sub a b = inverse FloatN.zero neg FloatN.sub FloatC.sub a b
  let mul a b = ring FloatN.zero FloatN.one FloatN.negone neg FloatN.mul FloatC.mul a b
  let norm x = Staged.unary FloatN.norm FloatC.norm x

  (* binary powering *)
  let int_pow n x =
    match x with
    | {now = Some z} -> of_atom (z ** (FloatN.of_int n))
    | {later = (b,xx)} ->
        let k f = (match b with
          | Constant -> f xx
          | Comp     -> Repr.CodeLang.let_ xx f) in
        let rec doit m z = match m with
        | 0 -> FloatC.one
        | 1 -> z
        | n -> if n mod 2 = 0 then 
                   Repr.CodeLang.let_ (doit (n/2) z) (fun w -> FloatC.mul w w)
               else FloatC.mul xx (doit (n-1) z) in
        of_comp (k (doit n))
end

module type PRECISION = sig val eps : float end

module FloatNI(E : PRECISION) = struct
  include FloatN
  let sgn y s =
    let eps = E.eps in
    let sgn_now s x = Sign.bind (x > eps) (x >= -.eps && x <= eps)
      (x < -.eps) (x >= -.eps) (x <= eps) s in
    sgn_now s y 
end

module FloatCI(E : PRECISION) = struct
  include FloatC
  let sgn y s = 
     let eps_c = .< E.eps >. in
     let sgn_later s x = Sign.bind
      .< .~x > .~eps_c >.
      .< let x = .~x and eps = .~eps_c in x >= -.eps &&  x <= eps >.
      .< .~x < -. .~eps_c >.
      .< .~x >= -. .~eps_c >.
      .< .~x <= .~eps_c >. s in
  sgn_later s y
end

module Float_Sign_Inexact (E : PRECISION) = struct
  let sgn y s = 
    let module NI = FloatNI(E) in
    let module CI = FloatCI(E) in
    unary (fun x -> NI.sgn x s) (fun x -> CI.sgn x s) y
end

module Float_Ring_Inexact (E : PRECISION) (* : RING *) = struct
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
end

module Float_Real_Inexact(E : PRECISION) (* : REALFIELD *) = struct
  include Float_Real_Base
  include Float_Sign_Inexact (E)
end
