open Domains

module ZpMake(P:sig val p:int end) : S
  with type kind = field
   and type v = int
   and type 'a exp = 'a

module ZpMakeCode(P:sig val p:int end) : S
  with type kind = field
   and type v = int
   and type 'a exp = 'a code
  
