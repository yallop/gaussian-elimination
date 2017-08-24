open Domains

module Rational = struct
  type v = Num.num
  type kind = field
  type 'a exp = 'a
  let zero = let zero = Num.num_of_int 0 in zero
  let one = let one = Num.num_of_int 1 in one
  let plus x y = Num.add_num x y
  let times x y = Num.mult_num x y
  let minus x y = Num.sub_num x y
  let uminus x = Num.minus_num x
  let div x y = Num.div_num x y
  let better_than = None (* no such thing here *)
  let normalizerf = None
  let normalizerg = fun x -> x
end

module RationalCode = struct
  type v = Num.num
  type kind = field
  type 'a exp = 'a code
  let zero = let zero = Num.num_of_int 0 in .< zero >.
  let one = let one = Num.num_of_int 1 in .< one >.
  let plus x y = .<Num.add_num .~x .~y >.
  let times x y = .<Num.mult_num .~x .~y>.
  let minus x y = .<Num.sub_num .~x .~y>.
  let uminus x = .<Num.minus_num .~x>.
  let div x y = .<Num.div_num .~x .~y>.
  let better_than = None (* no such thing here *)
  let normalizerf = None
  let normalizerg = fun x -> x
end
