open Domains

module Rational : S
     with type kind = field
      and type v = Num.num
      and type 'a exp = 'a

module RationalCode : S
     with type kind = field
      and type v = Num.num
      and type 'a exp = 'a code
