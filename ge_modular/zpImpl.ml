open Prelude
open CodePrelude
open Domains

(* A naive primality tester. Should suffice for now, it is used
   only to make sure the generator ZpMake is instantiated correctly
*)
let is_prime n = 
  let rec loop j jsq =
    jsq > n || (n mod j <> 0 && loop (j+2) (jsq + 4*(j+1))) in
  n = 2 || ( n > 2 && (n mod 2 <> 0) && loop 3 9)
;;

(* Need to compute GCDs.  Make this shareable. *)
let rec extended_gcd a b =
  if a mod b == 0 then
    (0,1)
  else
    let (x,y) = extended_gcd b (a mod b) in
    (y, x-y*(a / b))

module ZpMakeCode = functor(P:sig val p:int end) -> struct
    (* Make sure this functor is instantiated correctly:
       a run-time test, but at generation time
    *)
  let () = assert (is_prime P.p)

  type v  = int
  type kind = field
  type vc = v code

  let zero      = .< 0 >.  
  let one       = .< 1 >. 
  let negone    = .< P.p - 1 >. 

  let plus x y  = .< (.~x + .~y) mod P.p >.
  let times x y = .< (.~x * .~y) mod P.p >.
  let minus x y = .< (.~x - .~y) mod P.p >.
  let uminus x  = .< (- .~x)     mod P.p >.
  let inv x     = .< fst (extended_gcd   1 .~x) >.
  let div x y   = .< fst (extended_gcd .~x .~y) >.

  let normalizerf  = None
  let normalizerg  = None
  let better_than  = None
end

module ZpMake = functor(P:sig val p:int end) -> struct
  module C = ZpMakeCode(P)

  type v          = C.v
  type kind       = C.kind
  type 'a exp     = 'a               (* difference here *)

  let zero        = run0 C.zero
  let one         = run0 C.one
  let negone      = run0 C.negone
  let plus        = run2 C.plus
  let minus       = run2 C.minus
  let uminus      = run1 C.uminus
  let times       = run2 C.times
  let inv         = run1 C.inv
  let div         = run2 C.div
  let better_than = None (* FIXME: Hack to appease the type checker *)
     (* maybe (fun z -> Some (run2 z)) None C.better_than *)
  let normalizerf = maybe (fun z -> Some z)        None C.normalizerf
  let normalizerg =      C.normalizerg (* this is a cheat? *)

end
