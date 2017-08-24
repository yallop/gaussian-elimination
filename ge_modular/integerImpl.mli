open Domains

module Integer : S
     with type kind = ring
      and type v = int
      and type 'a exp = 'a

module IntegerCode : S
     with type kind = ring
      and type v = int
      and type 'a exp = 'a code
