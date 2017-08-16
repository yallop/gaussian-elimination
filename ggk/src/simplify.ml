open Staged

(* Simplification rules which are useful throughout *)
let abstr = to_code
let dyn = of_comp

let build1 fnow flater = function
  | {now = Some v} -> lift_const (fnow v)
  | e -> dyn (flater (abstr e))

let build2 f1 f2 = function
| {now = Some m}, {now = Some n} -> lift_const (f1 m n)
| e1, e2 -> dyn (f2 (abstr e1) (abstr e2))

(* one * a = a * one = a *)
let monoid one f1 f2 = function
| {now = Some e'}, e when e' = one -> e
| e, {now = Some e'} when e' = one -> e
| ee -> build2 f1 f2 ee

(* zero - a = - a,  a - zero = a *)
let inverse zero uinv bnow blater x y =
  match x, y with
  | {now = Some e'}, e when e' = zero -> uinv e
  | e, {now = Some e'} when e' = zero -> e
  | x, y                     -> monoid zero bnow blater (x,y)

(* multiplicative structure of semiring *)
let semiring zero one bnow blater x y =
  match x, y with
  | {now = Some x}, _ when x = zero -> lift_const zero
  | _, {now = Some x} when x = zero -> lift_const zero
  | x, y -> monoid one bnow blater (x,y)

(* multiplicative structure of ring *)
let ring zero one negone neg bnow blater x y =
  match x, y with
  | {now = Some x}, y when x = negone -> neg y
  | x, {now = Some y} when y = negone -> neg x
  | x, y -> semiring zero one bnow blater x y
