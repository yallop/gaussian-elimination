open Prelude
open CodePrelude
open Domains

module RationalCode = struct
  type v      = Num.num
  type kind   = field
  type 'a exp = 'a code

  let zero      = let zero = Num.num_of_int 0 in .< zero >.
  let one       = let one = Num.num_of_int 1 in .< one >.
  let negone    = let negone = Num.num_of_int (-1) in .< negone >.
  let plus x y  = .<Num.add_num .~x .~y >.
  let times x y = .<Num.mult_num .~x .~y>.
  let minus x y = .<Num.sub_num .~x .~y>.
  let uminus x  = .<Num.minus_num .~x>.
  let div x y   = .<Num.div_num .~x .~y>.
  let better_than = None (* no such thing here *)
  let normalizerf = None
  let normalizerg = fun x -> x
end

module Rational = struct
  type v          = RationalCode.v
  type kind       = RationalCode.kind
  type 'a exp     = 'a               (* difference here *)

  let zero        = run0 RationalCode.zero
  let one         = run0 RationalCode.one
  let negone      = run0 RationalCode.negone
  let plus        = run2 RationalCode.plus
  let times       = run2 RationalCode.times
  let minus       = run2 RationalCode.minus
  let uminus      = run1 RationalCode.uminus
  let div         = run2 RationalCode.div
  let better_than = maybe (fun z -> Some (run2 z)) None RationalCode.better_than
  let normalizerf = maybe (fun z -> Some z)        None RationalCode.normalizerf
  let normalizerg =      RationalCode.normalizerg (* this is a cheat? *)

end

