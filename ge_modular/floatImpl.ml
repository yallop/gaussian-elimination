open Prelude
open CodePrelude
open Domains
open Staged
open Simplify

(* The Code version is _primary_, in the sense that we will
  obtain the Direct version from it. *)
module FloatCode = struct
  type v      = float
  type kind   = field
  type 'a exp = 'a code

  let zero      = .<  0. >.
  let one       = .<  1. >.
  let negone    = .< -1. >.
  let plus  x y = .<.~x +. .~y>.
  let uminus x  = .<-. .~x>.
  let minus x y = .<.~x -. .~y>.
  let times x y = .<.~x *. .~y>.
  let inv x     = .< 1. /. .~x>.
  let div x y   = .<.~x /. .~y>.
  let better_than = Some (fun x y -> .<abs_float .~x < abs_float .~y >. )
  let normalizerf = None
  let normalizerg = fun x -> x
end

(* This version is now obviously consistent with the above *)
module Float = struct
  type v          = FloatCode.v
  type kind       = FloatCode.kind
  type 'a exp     = 'a               (* difference here *)

  let zero        = run0 FloatCode.zero
  let one         = run0 FloatCode.one
  let negone      = run0 FloatCode.negone
  let plus        = run2 FloatCode.plus
  let minus       = run2 FloatCode.minus
  let uminus      = run1 FloatCode.uminus
  let times       = run2 FloatCode.times
  let inv         = run1 FloatCode.inv
  let div         = run2 FloatCode.div
  let better_than = maybe (fun z -> Some (run2 z)) None FloatCode.better_than
  let normalizerf = maybe (fun z -> Some z)        None FloatCode.normalizerf
  let normalizerg =      FloatCode.normalizerg (* this is a cheat? *)
end

(* And here is where things really get interesting.  Explicitly using the
  Direct and Code versions, we weave them together to create a simplifying
  partial evaluator. *)
module FloatStaged = struct
  type v          = FloatCode.v
  type kind       = FloatCode.kind
  type 'a exp     = 'a staged         (* difference here *)

  let zero        = Staged.of_atom Float.zero
  let one         = Staged.of_atom Float.one
  let plus  a b   = monoid Float.zero Float.plus FloatCode.plus (a,b)
  let uminus      = Staged.unary Float.uminus FloatCode.uminus
  let minus       = inverse Float.zero uminus Float.minus FloatCode.minus
  let times       = ring Float.zero Float.one Float.negone uminus Float.times FloatCode.times
  let inv         = Staged.unary Float.inv FloatCode.inv
  let div         = inverse Float.one inv Float.div FloatCode.div
  let better_than = maybe_apply2 Staged.binary Float.better_than FloatCode.better_than
end

