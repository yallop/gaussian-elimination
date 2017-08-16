
open OUnit 
open Staged

(* representative fixture! *)
let x = 5
let xc = .<5>.
let xcs = lift_atom xc

(* Axioms:
 *  of_immediate x = Now x
 *  of_code x = Later x
 *  to_later (Now x) = Later <x>  to_later (Later x) = Later x
 *  to_expr (Now x) = <x>         to_code (Later x) = x
 *  is_now (Now x) = true         is_now (Later x) = false
 *  is_later (Now x) = false      is_later (Later x) = true
 *)
let test_staged_type _ =
  assert_equal (of_immediate x) (Now x);
  assert_equal (of_expr xcs) (Later xcs);

  (* Equality is not defined on type ('a, 'b) code.
   * But it's defined on 'b. *)
  assert_equal (.! to_code (Now x)) (.! xc);
  assert_equal (.! to_code (Later xcs)) (.! xc);

  (* once x is lifted, we can no longer compare it with xc *)
  assert_equal (.! to_code (to_later (Now x))) (.! to_code (Later xcs));
  assert_equal (to_later (Later xcs)) (Later xcs);

  assert_bool "is_now (Now x) <> true" (is_now (Now x));
  assert_bool "is_now (Later xcs) <> false" (not (is_now (Later xcs)));

  assert_bool "is_later (Now x) <> false" (not (is_later (Now x)));
  assert_bool "is_later (Later xcs) <> true" (is_later (Later xcs))

(* Axioms:
 *  of_code (lift x) = to_later (of_immediate x)
 *  to_code (of_code x) = x
 *  of_code (to_code x) = x
 *  lift x = to_code (to_later (of_immediate x))
 *)
let test_staged_commute _ =
  assert_equal (.! to_code (of_expr (lift_const x)))
               (.! to_code (to_later (of_immediate x)));
  assert_equal (.! to_code (of_expr xcs)) (.! xc);
  assert_equal (of_comp (to_code (Later xcs))) (Later xcs);
  assert_equal (.! .< x >. )
               (.! to_code (to_later (of_immediate x)))

(* Axioms:
 * is_now (mk_const x) = true
 * mk_const x = Now x
 *)
let test_mk_const _ =
  assert_bool "is_now <> true" (is_now (mk_const x));
  assert_equal (mk_const x) (Now x)

(* Axioms:
 *  f (Now x) = Now (f.unow x)
 *  f (Later <x>) = Later (f.ulater <x>)
 *  is_now (f (Now x)) = true
 *  is_later (f (Later x)) = true
 *)
let test_mk_unary _ =
  let succ = { unow = (fun x -> x + 1); ulater = (fun x -> lift_comp .<.~(x.c) + 1>.) } in
  let succ_s x = mk_unary succ x in
  assert_equal (succ_s (Now x)) (Now (succ.unow x));
  assert_equal (.! to_code (succ_s (of_comp .<x>.)))
               (.! to_code (Later (succ.ulater (lift_comp .< x >.))));
  assert_bool "is_now (succ_s (Now x)) <> true" (is_now (succ_s (Now x)));
  assert_bool "is_later (succ_s (Later x)) <> true" (is_later (succ_s (of_comp .<x>.)))

(* Axioms:
 *  is_now (f (Now x) (Now y)) = true
 *  is_later (f (Later x) (Later y)) = true
 *  is_later (f (Now x) (Later y)) = true
 *  is_later (f (Later x) (Now y)) = true
 *  f (Now x) (Now y) = Now (f.bnow x y)
 *  f (Later <x>) (Later <y>) = Later (f.blater <x> <y>)
 *  f (Now x) (Later <y>) = Later (f.blater <x> <y>)
 *  f (Later <x>) (Now y) = Later (f.blater <x> <y>)
 *)
let test_mk_binary _ =
  let x, xc, y, yc = 2, .<2>., 3, .<3>. in
  let xcs, ycs = lift_atom xc, lift_atom yc in
  let xn, xl, yn, yl = (Now x), (of_atom xc), (Now y), (of_atom yc) in
  let add = { bnow = (fun x y -> x+y); blater = fun x y -> lift_comp .<.~(x.c) + .~(y.c)>. } in
  let add_s x = mk_binary add x in
  let zn = add_s xn yn  and zl1 = add_s xl yl
  and zl2 = add_s xn yl and zl3 = add_s xl yn in
  assert_bool "is_now <> true" (is_now zn);
  assert_bool "is_later 1 <> true" (is_later zl1);
  assert_bool "is_later 2 <> true" (is_later zl2);
  assert_bool "is_later 3 <> true" (is_later zl3);
  assert_equal zn (Now (add.bnow x y));
  let zl_value = add.blater xcs ycs in
  assert_equal (.! to_code zl1) (.! zl_value.c);
  assert_equal (.! to_code zl2) (.! zl_value.c);
  assert_equal (.! to_code zl3) (.! zl_value.c)


(* Axioms:
 *  one * a = a * one = a
 *  f (Later x) (Now one) = Later x
 *  f (Now one) (Later x) = Later x
 *)
let test_mk_monoid _ =
  let add = { bnow = ( + ); blater = fun x y -> lift_comp .<.~(x.c) + .~(y.c)>. } in
  let add_mon = { bop = add; uelem = 0 } in
  let add_s = mk_monoid add_mon in
  assert_equal (add_s (Now 0) (of_comp xc)) (of_comp xc);
  assert_equal (add_s (of_comp xc) (Now 0)) (of_comp xc)

(* Axioms:
 *  one * a = a * one = a
 *  zero * a = a * zero = zero
 *  f (Now zero) x = Now zero
 *  f x (Now zero) = Now zero
 *  f (Now one) x = x
 *  f x (Now one) = x
 *)
let test_mk_ring _ =
  let mul = { bnow = ( * ); blater = fun x y -> lift_comp .<.~(x.c) * .~(y.c)>. } in
  let mul_mon = { bop = mul; uelem = 1 } in
  let mul_rng = { monp = mul_mon; mont = mul_mon } in
  let mul_s = mk_ring mul_rng in
  assert_equal (mul_s (Now 1) (of_comp xc)) (of_comp xc);
  assert_equal (mul_s (of_comp xc) (Now 1)) (of_comp xc);
  assert_equal (mul_s (Now 0) (of_comp xc)) (Now 0);
  assert_equal (mul_s (of_comp xc) (Now 0)) (Now 0)

let suite = "Staged Test" >::: [
  "test_staged_type" >:: test_staged_type ;
  "test_staged_commute" >:: test_staged_commute ;
  "test_mk_const" >:: test_mk_const ;
  "test_mk_unary" >:: test_mk_unary ;
  "test_mk_binary" >:: test_mk_binary ;
  "test_mk_monoid" >:: test_mk_monoid ;
  "test_mk_ring" >:: test_mk_ring ]


