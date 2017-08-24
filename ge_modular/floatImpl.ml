open Domains

module Float = struct
  type v = float
  type kind = field
  type 'a exp = 'a
  let zero = 0.
  let one = 1.
  let plus x y = x +. y
  let times x y = x *. y
  let minus x y = x -. y
  let uminus x = -. x
  let div x y = x /. y
  let better_than = Some (fun x y -> abs_float x < abs_float y)
  let normalizerf = None
  let normalizerg = fun x -> x
end

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
