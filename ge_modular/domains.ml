type field (* abstract *)
type ring  (* abstract *)

module type S =
sig
  type v
  type kind (* Field or Ring ? *)
  type _ exp
  val zero : v exp
  val one : v exp
  val plus : v exp -> v exp -> v exp
  val times : v exp -> v exp -> v exp
  val minus : v exp -> v exp -> v exp
  val uminus : v exp -> v exp
  val div : v exp -> v exp -> v exp
  val better_than : (v exp -> v exp -> bool exp) option
  val normalizerf : (v -> v) exp option
  val normalizerg : v exp -> v exp
end

module Float =
struct
  type v = float
  type kind = field
  type 'a exp = 'a
  let zero = 0.
  let one = 1.
  let plus x y = x +. y
  let times x y = x *. y
  let minus x y = x -. y
  let uminus x = -. x
  let div x y = x /. y
  let better_than = Some (fun x y -> abs_float x < abs_float y)
  let normalizerf = None
  let normalizerg = fun x -> x
end

module FloatCode =
struct
  type v = float
  type kind = field
  type 'a exp = 'a code
  let zero = .< 0. >.
  let one = .< 1. >.
  let plus x y = .<.~x +. .~y>.
  let times x y = .<.~x *. .~y>.
  let minus x y = .<.~x -. .~y>.
  let uminus x = .<-. .~x>.
  let div x y = .<.~x /. .~y>.
  let better_than = Some (fun x y -> .<abs_float .~x < abs_float .~y >. )
  let normalizerf = None
  let normalizerg = fun x -> x
end

module Integer =
struct
  type v = int
  type kind = ring
  type 'a exp = 'a
  let zero =  0
  let one =  1
  let plus x y = x + y
  let times x y = x * y
  let minus x y = x - y
  let uminus x =  - x
  let div x y = x / y
  let better_than = Some (fun x y -> abs x > abs y  )
  let normalizerf = None
  let normalizerg = fun x -> x
end

module IntegerCode =
struct
  type v = int
  type kind = ring
  type 'a exp = 'a code
  let zero = .< 0 >.
  let one = .< 1 >.
  let plus x y = .<.~x + .~y>.
  let times x y = .<.~x * .~y>.
  let minus x y = .<.~x - .~y>.
  let uminus x = .< - .~x>.
  let div x y = .<.~x / .~y>.
  let better_than = Some (fun x y -> .<abs .~x > abs .~y >. )
  let normalizerf = None
  let normalizerg = fun x -> x
end

module Rational =
struct
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

module RationalCode =
struct
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
