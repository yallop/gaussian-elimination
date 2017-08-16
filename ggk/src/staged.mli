type choice = Comp | Constant
type ('a,'b) comp = choice * ('a,'b) code
type ('a, 'b) staged = { now : 'b option; later : ('a, 'b) comp }

val lift_const : 'a -> ('b, 'a) staged
val lift_code : ('a,'b) code -> ('a,'b) comp

val of_atom : 'b -> ('a, 'b) staged
val of_comp : ('a,'b) code -> ('a, 'b) staged
val of_const : ('a,'b) code -> ('a, 'b) staged
val of_marked : ('a,'b) comp -> ('a, 'b) staged

val to_code : ('a,'b) staged -> ('a,'b) code

val stage : ('a,'b) comp -> choice

(* These probably should not be exported? *)
val apply_op : ('a -> 'b) -> 'a option -> 'b option
val apply2_op : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option

module LiftCode : sig
  val unary : (('a,'b) code -> 'c) -> ('a,'b) staged -> choice * 'c
  val binary : (('a,'b) code -> ('a,'c) code -> 'd) -> ('a,'b) staged -> ('a,'c) staged -> choice * 'd
end

val unary :
  ('a -> 'b) ->
  (('c, 'a) code -> ('d, 'b) code) -> ('c, 'a) staged -> ('d, 'b) staged
val binary :
  ('a -> 'b -> 'c) ->
  (('d, 'a) code -> ('e, 'b) code -> ('f, 'c) code) ->
  ('d, 'a) staged -> ('e, 'b) staged -> ('f, 'c) staged
