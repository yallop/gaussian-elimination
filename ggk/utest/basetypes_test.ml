open OUnit
open Staged
open Basetypes
open Util

(* *** module Int *** *)

(* *** module String *** *)

let s = "hello"
let sc = .<"hello">.

(* Axioms:
 *  concat_s has identity (Now "")
 *)
let test_String_concat _ =
  let s1 = String.concat_s (Now "") (Now s)
  and s2 = String.concat_s (of_atom sc) (of_expr (lift_const "")) in
  assert_equal s1 (Now s);
  assert_equal (of_atom sc) s2

(* *** module Bool **** *)

let fl = Bool.false_
let flc = lift_comp .< 1<>1 >.

(* *)
let test_Bool_not _ =
  (* not_b.unow false = not_s (Now false) *)
  assert_equal (Bool.not_b.unow fl) true;
  assert_equal (Bool.not_s (Now fl)) (Now true);
  (* not_b.ulater <false> = not_s (Later <false>) *)
  assert_equal (.! (Bool.not_b.ulater flc).c)
               (.! to_code (Bool.not_s (Later flc)))

(* check for 'and' identities *)
let test_Bool_and _ =
  assert_equal (Bool.and_s (Later flc) (Now Bool.false_))
               (Now Bool.false_);
  let b = Bool.and_s (Now Bool.true_) (Later flc) in
  assert_bool "err #1 is_later b" (is_later b);
  let b' = ((function Later flc -> true | _ -> false) b) in
  assert_bool "err #2" b'

(* check for 'or' identities *)
let test_Bool_or _ =
  let b = Bool.or_s (Later flc) (Now Bool.false_) in
  assert_bool "err #1" (is_later b);
  let b' = (function Later flc -> true | _ -> false) b in
  assert_bool "err #2" b';
  let b1 = Bool.or_s (Now Bool.true_) (Later flc) in
  assert_bool "err #3" (is_now b1);
  assert_equal b1 (Now Bool.true_)

(* check for eq *)
let test_Bool_eq _ =
  (* other cases of Later values will coerce into code expressions
   * so there is no point of testing them. such cases will be covered
   * in REPL testing *)
  assert_equal (Bool.eq (Now 1) (Now 2)) (Now false)

(* *** module Code *** *)

let tn = Now true
let tl = of_atom .<true>.
let fn = Now false
let fl = of_atom .<false>.

(* Axioms:
 *  ife_ (Now true)  a b = a
 *  ife_ (Now false) a b = b
 *  ife_ (Later c) a b = Later <if c then a else b>
 *)
let test_Code_ife _ =
  let a = Now 0 and b = Now 1 in
  assert_equal (Code.ife tn a b to_code) a;
  assert_equal (Code.ife fn a b to_code) b;
  assert_equal (.! to_code (Code.ife tl a b to_code ))
               (.! to_code a);
  assert_equal (.! to_code (Code.ife fl a b to_code ))
               (.! to_code b)

(* For now, it's better to disable if_
(* Axioms:
 *  if_ (Now true) a = a
 *  if_ (Now false) a = Now ()
 *  if_ (Later c) a = Later <if c then a else ()>
 *)
let test_Code_if _ =
  (* if's action has a side effect *)
  let state = ref 0 in
  (* a encodes an action with a side effect is generated *)
  let a = Now ((fun _ -> ignore (state := !state + 1)) ()) in
  (* @TODO *assumption* given is_now() is strict, if_() will
   * get evaluated and the side effect is tested later
   * UPDATE: No, it has to be lazy. Second thought is needed.
   *)
  assert_bool "err #1" (is_now (Code.if_ (Now true) a));
  assert_equal !state 1;
  assert_bool "err #2" (is_now (Code.if_ (Now false) a));
  assert_equal ~msg:"err #3" !state 1; (* nothing changed *)
  .! to_code (Code.if_ (Later .<true>.) a);
  assert_equal ~msg:"err #4" !state 2;
  .! to_code (Code.if_ (Later .<false>.) a);
  assert_equal ~msg:"err #5" !state 2
*)

(* *** utils *** *)

(*
let test_list_all_equal _ =
  let l1 = [(Now 1); (Now 1); (Now 1)] (* now all equal *)
  and l2 = [(Now 0); (Now 1); (Now 1)] (* now not all equal *)
  and l3 = [(of_atom .<1>.); (Now 1); (Now 1)] (* mixed all equal *)
  and l4 = [(of_atom .<0>.); (Now 1); (Now 1)] (* mixed not all equal *)
  and l5 = [(of_atom .<1>.); (of_atom .<1>.); (of_atom .<1>.)] (* later all equal *)
  and l6 = [(of_atom .<0>.); (of_atom .<1>.); (of_atom .<1>.)] (* later not all equal *)
  in
  let c1 = _list_all_equal l1 and c2 = _list_all_equal l2
  and c3 = _list_all_equal l3 and c4 = _list_all_equal l4
  and c5 = _list_all_equal l5 and c6 = _list_all_equal l6 in
  assert_equal c1 (Now true);
  assert_equal c2 (Now false);
  assert_equal (.! to_code c3) true;
  assert_equal (.! to_code c4) false;
  assert_equal (.! to_code c5) true;
  assert_equal (.! to_code c6) false
*)

let test_for_all _ =
  let l1 = [(Now 1); (Now 1); (Now 1)]
  and l2 = [(Now 0); (Now 1); (Now 1)]
  and l3 = [(of_atom .<1>.); (Now 1); (Now 1)]
  and l4 = [(of_atom .<0>.); (Now 1); (Now 1)]
  and l5 = [(of_atom .<1>.); (of_atom .<1>.); (of_atom .<1>.)]
  and l6 = [(of_atom .<0>.); (of_atom .<1>.); (of_atom .<1>.)]
  (* greater than zero *)
  and gtzero x =
    mk_unary { unow = (fun x -> x > 0);
               ulater = (fun x -> lift_comp .< .~(x.c) > 0 >.) } x
  in
  let c1 = for_all gtzero l1 and c2 = for_all gtzero l2
  and c3 = for_all gtzero l3 and c4 = for_all gtzero l4
  and c5 = for_all gtzero l5 and c6 = for_all gtzero l6 in
  assert_equal c1 (Now true);
  assert_equal c2 (Now false);
  assert_equal (.! to_code c3) true;
  assert_equal (.! to_code c4) false;
  assert_equal (.! to_code c5) true;
  assert_equal (.! to_code c6) false

let test_exists _ =
  let l1 = [(Now 1); (Now 1); (Now 1)]
  and l2 = [(Now 0); (Now 1); (Now 1)]
  and l3 = [(of_atom .<1>.); (Now 1); (Now 1)]
  and l4 = [(of_atom .<0>.); (Now 1); (Now 1)]
  and l5 = [(of_atom .<1>.); (of_atom .<1>.); (of_atom .<1>.)]
  and l6 = [(of_atom .<0>.); (of_atom .<1>.); (of_atom .<1>.)]
  (* equal zero *)
  and eqzero x = Bool.eq x (Now 0) in
  let c1 = exists eqzero l1 and c2 = exists eqzero l2
  and c3 = exists eqzero l3 and c4 = exists eqzero l4
  and c5 = exists eqzero l5 and c6 = exists eqzero l6 in
  assert_equal c1 (Now false);
  assert_equal c2 (Now true);
  assert_equal (.! to_code c3) false;
  assert_equal (.! to_code c4) true;
  assert_equal (.! to_code c5) false;
  assert_equal (.! to_code c6) true

let test_findi _ =
  let l1 = [(Now 1); (Now 1); (Now 1)]
  and l2 = [(Now 0); (Now 1); (Now 1)]
  and l3 = [(of_atom .<1>.); (Now 1); (Now 1)]
  and l4 = [(of_atom .<0>.); (Now 1); (Now 1)]
  and l5 = [(of_atom .<1>.); (of_atom .<1>.); (of_atom .<1>.)]
  and l6 = [(of_atom .<0>.); (of_atom .<1>.); (of_atom .<1>.)]
  (* equal zero *)
  and eqzero x = Bool.eq x (Now 0) in
  let c1 = findi eqzero l1 and c2 = findi eqzero l2
  and c3 = findi eqzero l3 and c4 = findi eqzero l4
  and c5 = findi eqzero l5 and c6 = findi eqzero l6 in
  assert_equal ~msg:"err #1" c1 (Now 3);
  assert_equal ~msg:"err #2" c2 (Now 0);
  assert_bool "err #3" (is_later c3);
  assert_bool "err #4" (is_later c4);
  assert_bool "err #5" (is_later c5);
  assert_bool "err #6" (is_later c6);
  assert_equal ~msg:"err #7" (.! to_code c3) 3;
  assert_equal ~msg:"err #8" (.! to_code c4) 0;
  assert_equal ~msg:"err #9" (.! to_code c5) 3;
  assert_equal ~msg:"err #10" (.! to_code c6) 0

let suite = "Basetypes Test" >::: [
  "test_String_concat" >:: test_String_concat ;
  "test_Bool_not" >:: test_Bool_not ;
  "test_Bool_and" >:: test_Bool_and ;
  "test_Bool_or" >:: test_Bool_or ;
  "test_Bool_eq" >:: test_Bool_eq ;
  "test_Code_ife" >:: test_Code_ife ;
  (* "test_Code_if" >:: test_Code_if ; *)
  (* "test_list_all_equal" >:: test_list_all_equal ; *)
  "test_for_all" >:: test_for_all ;
  "test_exists" >:: test_exists ;
  "test_findi" >:: test_findi ]

