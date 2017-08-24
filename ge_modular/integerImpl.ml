open Domains

module Integer = struct
  type v = int
  type kind = ring
  type 'a exp = 'a
  let zero =  0
  let one =  1
  let plus x y = x + y
  let times x y = x * y
  let minus x y = x - y
  let uminus x =  - x
  let div x y = x / y
  let better_than = Some (fun x y -> abs x > abs y  )
  let normalizerf = None
  let normalizerg = fun x -> x
end

module IntegerCode = struct
  type v = int
  type kind = ring
  type 'a exp = 'a code
  let zero = .< 0 >.
  let one = .< 1 >.
  let plus x y = .<.~x + .~y>.
  let times x y = .<.~x * .~y>.
  let minus x y = .<.~x - .~y>.
  let uminus x = .< - .~x>.
  let div x y = .<.~x / .~y>.
  let better_than = Some (fun x y -> .<abs .~x > abs .~y >. )
  let normalizerf = None
  let normalizerg = fun x -> x
end
