open Staged

(* simplification rules *)

(* Names inspired by abstract interpretation *)
let abstr = to_code
let dyn = of_comp

(* Applying unary and binary functions in the
   presence of various laws (including none).
  A numeric suffic is the arity. *)

(* No Laws - just use stage information *)
let apply1 fnow flater = function
  | {now = Some v} -> lift_const (fnow v)
  | e -> dyn (flater (abstr e))

let apply2 f1 f2 = function
| {now = Some m}, {now = Some n} -> lift_const (f1 m n)
| e1, e2 -> dyn (f2 (abstr e1) (abstr e2))

(* Simplification laws for a monoid 
     Note the dispatch to apply2 at the end.

  Unit laws, namely
  - one * a = a
  - a * one = a 
  are 'orientable', so use them. *)
let monoid one f1 f2 = function
| {now = Some e'}, e when e' = one -> e
| e, {now = Some e'} when e' = one -> e
| ee -> apply2 f1 f2 ee

(* Simplification laws for a group, additively.
  Orientable (new) laws are:
  - zero - a = - a
  - a - zero = a 
  and dispatch otherwise *)
let inverse zero uinv bnow blater x y =
  match x, y with
  | {now = Some e'}, e when e' = zero -> uinv e
  | e, {now = Some e'} when e' = zero -> e
  | x, y                     -> monoid zero bnow blater (x,y)

(* multiplicative structure of semiring.
   The new item is that zero is cancels, even
   if one argument is dynamic. 
  Note that this doesn't simplify the additive structure at all. 
  [Find a better name?] *)
let semiring zero one bnow blater x y =
  match x, y with
  | {now = Some x}, _ when x = zero -> lift_const zero
  | _, {now = Some x} when x = zero -> lift_const zero
  | x, y -> monoid one bnow blater (x,y)

(* multiplicative structure of ring 
  This is a more minor simplification, a small optimization of -1*x.
  And then dispatch.
  [Find a better name?] *)
let ring zero one negone neg bnow blater x y =
  match x, y with
  | {now = Some x}, y when x = negone -> neg y
  | x, {now = Some y} when y = negone -> neg x
  | x, y -> semiring zero one bnow blater x y
