module Imm = struct
  let concat = (^)
end

module Code = struct
  let concat x y = .< .~x ^ .~y >.
end

(* Staged String *)
module Staged = struct
  let concat s t = Simplify.monoid "" (^) (fun x y -> .<.~x ^ .~y>.) (s,t)
end
