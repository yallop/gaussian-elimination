open Domains

module Float : S
     with type kind = field
      and type v = float
      and type 'a exp = 'a

module FloatCode : S
     with type kind = field
      and type v = float
      and type 'a exp = 'a code
