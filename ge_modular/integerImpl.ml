open Prelude
open CodePrelude
open Domains

module IntegerCode = struct
  type v      = int
  type kind   = ring
  type 'a exp = 'a code

  let zero      = .< 0 >.
  let one       = .< 1 >.
  let plus x y  = .<.~x + .~y>.
  let times x y = .<.~x * .~y>.
  let minus x y = .<.~x - .~y>.
  let uminus x  = .< - .~x>.
  let div x y   = .<.~x / .~y>.
  let better_than = Some (fun x y -> .<abs .~x > abs .~y >. )
  let normalizerf = None
  let normalizerg = fun x -> x
end

module Integer = struct
  type v      = IntegerCode.v
  type kind   = IntegerCode.kind
  type 'a exp = 'a

  let zero        = run0 IntegerCode.zero
  let one         = run0 IntegerCode.one
  let plus        = run2 IntegerCode.plus
  let times       = run2 IntegerCode.times
  let minus       = run2 IntegerCode.minus
  let uminus      = run1 IntegerCode.uminus
  let div         = run2 IntegerCode.div
  let better_than = maybe (fun z -> Some (run2 z)) None IntegerCode.better_than
  let normalizerf = maybe (fun z -> Some z)        None IntegerCode.normalizerf
  let normalizerg =      IntegerCode.normalizerg (* this is a cheat? *)

end

