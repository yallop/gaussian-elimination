open Staged
open Simplify
open Algebra
open Num

module RationalN = struct
  type n = num
  include Repr.GenRep(Repr.Imm)
  include Repr.ImmLang
  include Logic.LogicN
  let eq = (=/)
  let neq = (<>/)
  let of_int = num_of_int
  let norm = abs_num
  let zero = num_of_int 0
  let one = num_of_int 1
  let add = (+/)
  let sub = (-/)
  let neg = minus_num
  let mul = ( */ )
  let negone = num_of_int (-1)
  let div = ( // )
  let inv = fun x -> num_of_int 1 // x
  let int_pow n x = power_num (num_of_int n) x

  let ispos x = x >/ zero
  let iszero x = x =/ zero
  let isnonneg x = (x >=/ zero)
  let isneg x = lt_num x zero 
  let isnonpos x = x <=/ zero
end

module RationalC = struct
  type n = num
  include Logic.LogicC
  include Repr.CodeLang
  include Repr.GenRep(Repr.Code)
  let eq = fun x y -> .< .~x =/ .~y >.
  let neq = fun x y -> .< .~x <>/ .~y >.
  let norm = fun x -> .< abs_num .~x >.
  let add = fun x y -> .< .~x +/ .~y >.
  let sub = fun x y -> .< .~x -/ .~y >.
  let neg = fun x -> .< minus_num .~x >.
  let mul = fun x y -> .< .~x */ .~y >.
  let zero = let z = num_of_int 0 in .< z >.
  let one = let z = num_of_int 1 in .< z >.
  let negone = let z = num_of_int (-1) in .< z >.
  let div = fun x y -> .< .~x // .~y >.
  let inv = fun x -> .< .~one // .~x >.
  let int_pow = fun n x -> let m = num_of_int n in .< power_num m .~x >.
  let of_int = fun n -> let m = num_of_int n in .< m >.

  let ispos x = .< .~x >/ .~zero >.
  let iszero x = .< .~x =/ .~zero >.
  let isneg x = .< .~x </ .~zero  >.
  let isnonneg x = .< .~x >=/ .~zero >.
  let isnonpos x = .< .~x <=/ .~zero >.
end

module Rational_Set (* : NSET *) = struct
  include Repr.GenRep(Repr.CGen)
  include Repr.CGenLang
  include Logic.LogicStaged
  type n = num

  let eq x y = Staged.binary RationalN.eq RationalC.eq x y
  let neq x y = Staged.binary RationalN.neq RationalC.neq x y

  let of_int n = Staged.of_atom (RationalN.of_int n)
end

module Rational_Ring (* : RING *) = struct
  include Rational_Set
  let zero = Staged.of_atom RationalN.zero
  let one = Staged.of_atom RationalN.one
  let negone = Staged.of_atom RationalN.negone

  let add x y = monoid RationalN.zero RationalN.add RationalC.add (x,y)
  let neg x = Staged.unary RationalN.neg RationalC.neg x
  let sub a b = inverse RationalN.zero neg RationalN.sub RationalC.sub a b
  let mul a b = ring RationalN.zero RationalN.one RationalN.negone neg RationalN.mul RationalC.mul a b
  let int_pow n x = failwith "not implemented"
end

module Field = struct
  include Rational_Ring

  let inv x = Staged.unary RationalN.inv RationalC.inv x
  let div x y = inverse RationalN.one inv RationalN.div RationalC.div x y
end

module Signed_Ring = struct
  include Rational_Ring
  let abs x = Staged.unary RationalN.norm RationalC.norm x

  let sgn y s =
    let module N = RationalN in
    let module C = RationalC in
    let sgn_now s x = Sign.bind (N.ispos x) (N.iszero x)
      (N.isneg x) (N.isnonneg x) (N.isnonpos x) s
    and sgn_later s x = Sign.bind (C.ispos x) (C.iszero x) (C.isneg x)
	                        (C.isnonneg x) (C.isnonpos x) s
    in
    {now = apply_op (sgn_now s) y.now; later = lift_code (sgn_later s (to_code y))}
end
