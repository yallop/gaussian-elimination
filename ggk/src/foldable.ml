open Staged

module type FOLDABLE = functor(C:Repr.REP) -> sig
  type 'a t
  val map : ('a, 'b, 'c) C.unary_fun ->
               ('a, 'b t) C.rep -> ('a, 'c t) C.rep

  val map2 : ('a, 'b, 'b, 'd) C.binary_fun ->  ('a, 'b t) C.rep ->
               ('a, 'b t) C.rep -> ('a, 'd t) C.rep

  val fold : ('a, 'b, 'c, 'c) C.binary_fun -> 'c ->
               ('a, 'b t) C.rep -> ('a, 'c) C.rep

  val mapfold : ('a, 'b, 'd) C.unary_fun -> ('a, 'd, 'c, 'c) C.binary_fun ->
                'c -> ('a, 'b t) C.rep -> ('a, 'c) C.rep

  val map2fold : ('a, 'b, 'c, 'd) C.binary_fun -> ('a, 'd, 'e, 'e) C.binary_fun ->
                 'e -> ('a, 'b t) C.rep ->
                     ('a, 'c t) C.rep -> ('a, 'e) C.rep
end

