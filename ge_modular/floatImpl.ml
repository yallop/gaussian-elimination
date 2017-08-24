open Prelude
open CodePrelude
open Domains

(* The Code version is _primary_, in the sense that we will
  obtain the Direct version from it. *)
module FloatCode = struct
  type v = float
  type kind = field
  type 'a exp = 'a code
  let zero = .< 0. >.
  let one = .< 1. >.
  let plus x y = .<.~x +. .~y>.
  let times x y = .<.~x *. .~y>.
  let minus x y = .<.~x -. .~y>.
  let uminus x = .<-. .~x>.
  let div x y = .<.~x /. .~y>.
  let better_than = Some (fun x y -> .<abs_float .~x < abs_float .~y >. )
  let normalizerf = None
  let normalizerg = fun x -> x
end

(* This version is now obviously consistent with the above *)
module Float = struct
  type v = float
  type kind = field
  type 'a exp = 'a

  let zero        = run0 FloatCode.zero
  let one         = run0 FloatCode.one
  let plus        = run2 FloatCode.plus
  let times       = run2 FloatCode.times
  let minus       = run2 FloatCode.minus
  let uminus      = run1 FloatCode.uminus
  let div         = run2 FloatCode.div
  let better_than = maybe (fun z -> Some (run2 z)) None FloatCode.better_than
  let normalizerf = maybe (fun z -> Some z)        None FloatCode.normalizerf
  let normalizerg =      FloatCode.normalizerg (* this is a cheat? *)
end

