(*module type T = functor(R: Abstractrep.T) -> sig *)
module type T = sig
open Prelude
(* Abstract Representation of ``code'' of ``code'' *)
type 'b abstract (* = 'b R.abstract *)

val retN : 'b abstract -> 
    ('s -> ('s -> 'b abstract -> 'w abstract ) -> 'w abstract)

val seq : 'b abstract -> 'c abstract -> 'c abstract
val seqL : 'b abstract -> 'c abstract -> 'd -> ('d -> 'c abstract -> 'e) -> 'e
val seqM :
  ('a -> ('b -> 'c -> 'c) -> 'e abstract) ->
  ('a -> ('f -> 'g -> 'g) -> 'h abstract) ->
  'a -> ('a -> 'h abstract -> 'i) -> 'i

val optSeq : 'b abstract -> 'b abstract option -> 'b abstract

val optSeqM : 
  ('a -> ('a -> 'e abstract -> 'e abstract) -> 'e abstract) ->
  ('a -> ('a -> 'g -> 'g) -> 'e abstract) option ->
  'a -> ('a -> 'e abstract -> 'e abstract) -> 'e abstract

val ifM :
  bool abstract ->
  ('b -> ('c -> 'd -> 'd) -> 'e abstract) ->
  ('b -> ('f -> 'g -> 'g) -> 'e abstract) ->
  'b -> ('b -> 'e abstract -> 'h) -> 'h
val rshiftM : ('a -> 'b) -> 'a -> ('a -> 'b -> 'c) -> 'c
val whenM :
  bool abstract ->
  ('b -> ('c -> 'd -> 'd) -> unit abstract) ->
  'b -> ('b -> unit abstract -> 'e) -> 'e
val loopM :
  int abstract ->
  int abstract ->
  (int abstract -> 'b -> ('c -> 'd -> 'd) -> 'e abstract) ->
  dir ->
  'b -> ('b -> unit abstract -> 'f) -> 'f
val whileM :
  bool abstract ->
  ('b -> ('c -> 'd -> 'd) -> 'e abstract) ->
  'b -> ('b -> unit abstract -> 'f) -> 'f
val matchM :
  'b option abstract ->
  ('b abstract -> 'c -> ('d -> 'e -> 'e) -> 'f abstract) ->
  ('c -> ('g -> 'h -> 'h) -> 'f abstract) ->
  'c -> ('c -> 'f abstract -> 'i) -> 'i
val genrecloop :
  (('b -> 'c) abstract ->
   'b abstract -> 'd -> ('e -> 'f -> 'f) -> 'c abstract) ->
  'b abstract -> 'd -> ('d -> 'c abstract -> 'g) -> 'g
val lift : 'a -> 'a abstract
val liftRef : 'b abstract -> 'b ref abstract
val liftGet : 'b ref abstract -> 'b abstract
val unitL : 'a -> ('a -> unit abstract -> 'c) -> 'c
val liftPair : ('b * 'c) abstract -> 'b abstract * 'c abstract
val liftPPair :
  (('b * 'c) * 'd) abstract -> 'b abstract * 'c abstract * 'd abstract
module Logic :
  sig
    val notL : bool abstract -> bool abstract
    val equalL : 'b abstract -> 'b abstract -> bool abstract
    val notequalL : 'b abstract -> 'b abstract -> bool
    abstract
    val andL : bool abstract -> bool abstract -> bool abstract
  end
module Idx :
  sig
    val zero : int abstract
    val one : int abstract
    val minusone : int abstract
    val succ : int abstract -> int abstract
    val pred : int abstract -> int abstract
    val less : 'b abstract -> 'b abstract -> bool abstract
    val uminus : int abstract -> int abstract
    val add : int abstract -> int abstract -> int abstract
    val minusoneL : 'a -> ('a -> int abstract -> 'c) -> 'c
  end
module Maybe :
  sig
    val just : 'b abstract -> 'b option abstract
    val none : 'b option abstract
  end
val applyMaybe : ('a -> 'a) option -> 'a -> 'a
module Tuple :
  sig
    val tup2 : 'b abstract -> 'c abstract -> ('b * 'c) abstract
    val tup3 :
      'b abstract -> 'c abstract -> 'd abstract -> ('b * 'c * 'd) abstract
    val tup4 : 'b abstract -> 'c abstract -> 'd abstract -> 
               'e abstract -> ('b * 'c * 'd * 'e) abstract
  end
module CList :
  sig
    val nil : 'b list abstract
    val cons : 'b abstract -> 'b list abstract -> 'b list
    abstract
  end
val cunit : unit abstract
val update :
  'b ref abstract -> ('b abstract -> 'b abstract) -> unit abstract
val assign : 'b ref abstract -> 'b abstract -> unit abstract
val apply : ('b -> 'c) abstract -> 'b abstract -> 'c abstract
val updateM :
  'b ref abstract -> ('b abstract -> 'b abstract) ->
  'c -> ('c -> unit abstract -> 'd) -> 'd
val assignM :
  'b ref abstract ->
  'b abstract -> 'c -> ('c -> unit abstract -> 'd) -> 'd
val applyM :
  ('b -> 'c) abstract -> 'b abstract -> 'd -> ('d -> 'c abstract -> 'e) -> 'e
module Transformers :
  sig
    val full_unroll :
      int -> int -> (int -> unit abstract) -> unit abstract
  end

module Array1Dim : sig
  val init : int abstract -> int array abstract
  val setL : int array abstract -> (int*int) abstract -> int array abstract
end

val liftRowSwap : int abstract -> int abstract -> perm abstract
val liftColSwap : int abstract -> int abstract -> perm abstract

end
