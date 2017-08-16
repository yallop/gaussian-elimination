open Staged
open Simplify

module IntegerN = struct
  type n = int
  include Repr.GenRep(Repr.Imm)
  include Repr.ImmLang
  include Logic.LogicN
  let eq = (=)
  let neq = (<>)
  let of_int x = x
  let norm = abs
  let add = (+)
  let sub = (-)
  let neg = (~-)
  let mul = ( * )
  let zero = 0
  let negone = -1
  let one = 1
  let rec int_pow n x = if n = 0 then 1 else if n = 1 then x else
                    x * int_pow (n-1) x
  let sgn x s = Sign.bind (x > 0) (x = 0) (x < 0) (x >= 0) (x <= 0) s
end

module IntegerC = struct
  type n = int
  include Repr.GenRep(Repr.Code)
  include Repr.CodeLang
  include Logic.LogicC
  let eq = fun x y -> .< .~x = .~y >.
  let neq = fun x y -> .< .~x <> .~y >.
  let norm = fun x -> .< abs .~x >.
  let add = fun x y -> .< .~x + .~y >.
  let sub = fun x y -> .< .~x - .~y >.
  let neg = fun x -> .< ~- .~x >.
  let mul = fun x y -> .< .~x * .~y >.
  let of_int = fun x -> .< x >.
  let zero = .< 0 >.
  let one = .< 1 >.
  let negone = .< -1 >.
  let rec int_pow n x = if n = 0 then one else if n = 1 then x else
                    mul x (int_pow (n-1) x)
  let sgn x s = Sign.bind .< .~x > 0 >.  .< .~x = 0 >.
      .< .~x < 0 >.  .< .~x >= 0 >.  .< .~x <= 0 >. s
end

module Set (* : NSET *) = struct
  include Repr.GenRep(Repr.CGen)
  include Repr.CGenLang
  include Logic.LogicStaged
  type n = int

  let eq x y = binary IntegerN.eq IntegerC.eq x y
  let neq x y = binary IntegerN.neq IntegerC.neq x y

  let of_int n = of_atom (IntegerN.of_int n)
end

module Normed_Set (* : NORMED_SET *) = struct
  include Set
  let norm x = unary IntegerN.norm IntegerC.norm x
end

(* (Z,+,0) monoid *)
module Add_Monoid (* : MONOID *) = struct
  include Set
  let zero = of_atom IntegerN.zero
  let add x y = monoid IntegerN.zero IntegerN.add IntegerC.add (x,y)
end

module Add_Normed_Monoid (* : NORMED_MONOID *) = struct
  include Normed_Set
  let zero = 0
  let add x y = monoid zero IntegerN.add IntegerC.add (x,y)
end

module Ring (* : NORMED_MONOID *) (* : RING *) = struct
  include Add_Monoid
  let one = of_atom IntegerN.one
  let negone = of_atom IntegerN.negone

  let neg x = unary IntegerN.neg IntegerC.neg x
  let sub a b = inverse IntegerN.zero neg IntegerN.sub IntegerC.sub a b
  let mul a b = ring IntegerN.zero IntegerN.one IntegerN.negone neg IntegerN.mul IntegerC.mul a b

  let sgn y s = unary (fun x -> IntegerN.sgn x s) (fun x -> IntegerC.sgn x s) y
  let int_pow n x = failwith "not implemented"

  (* NORMED_MONOID stuff *)
  let norm = Normed_Set.norm
end
