(* The kind of the domain: a ring or a field *)
type field
type ring

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

module Float : S
     with type kind = field
      and type v = float
      and type 'a exp = 'a

module FloatCode : S
     with type kind = field
      and type v = float
      and type 'a exp = 'a code

module Integer : S
     with type kind = ring
      and type v = int
      and type 'a exp = 'a

module IntegerCode : S
     with type kind = ring
      and type v = int
      and type 'a exp = 'a code

module Rational : S
     with type kind = field
      and type v = Num.num
      and type 'a exp = 'a

module RationalCode : S
     with type kind = field
      and type v = Num.num
      and type 'a exp = 'a code
