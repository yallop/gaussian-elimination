
open OUnit
open Staged
open Basetypes
open Algebra
open Float

(* This test is partial and non-interesting *)

module FS = Float_Set

let test_Float_Set_to_string _ =
  assert_equal ~msg:"err #1" (FS.to_string_s (Now 0.)) (Now "0.");
  assert_equal ~msg:"err #2" (.! to_code (FS.to_string_s (of_atom .<0.>.))) "0."

let test_Float_Set_eq _ =
  let c0 = FS.eq_s (Now 0.) (Now 0.)
  and c1 = FS.eq_s (Now 0.) (Now 1.)
  and c2 = .! to_code (FS.eq_s (Now 0.) (of_atom .<0.>.))
  and c3 = .! to_code (FS.eq_s (of_atom .<0.>.) (of_atom .<1.>.))
  in
  assert_equal ~msg:"err #1" c0 (Now true);
  assert_equal ~msg:"err #2" c1 (Now false);
  assert_equal ~msg:"err #3" c2 true;
  assert_equal ~msg:"err #4" c3 false

let test_Float_Set_neq _ =
  let c0 = FS.neq_s (Now 0.) (Now 0.)
  and c1 = FS.neq_s (Now 0.) (Now 1.)
  and c2 = .! to_code (FS.neq_s (Now 0.) (of_atom .<0.>.))
  and c3 = .! to_code (FS.neq_s (of_atom .<0.>.) (of_atom .<1.>.))
  in
  assert_equal ~msg:"err #1" c0 (Now false);
  assert_equal ~msg:"err #2" c1 (Now true);
  assert_equal ~msg:"err #3" c2 false;
  assert_equal ~msg:"err #4" c3 true

module FR = Float_Ring_Exact

(* testing only Now *)
let test_Float_Ring_sgn _ =
  let an = Now 0.
  and bn = Now 1.
  and cn = Now ~-. 1. in
  (* zero *)
  assert_equal ~msg:"err #1" (FR.sgn an Sign.Zero) (Now true);
  assert_equal ~msg:"err #2" (FR.sgn an Sign.PosOrZero) (Now true);
  assert_equal ~msg:"err #3" (FR.sgn an Sign.NegOrZero) (Now true);
  assert_equal ~msg:"err #4" (FR.sgn an Sign.Neg) (Now false);
  assert_equal ~msg:"err #5" (FR.sgn an Sign.Pos) (Now false);
  (* pos *)
  assert_equal ~msg:"err #6" (FR.sgn bn Sign.Zero) (Now false);
  assert_equal ~msg:"err #7" (FR.sgn bn Sign.PosOrZero) (Now true);
  assert_equal ~msg:"err #8" (FR.sgn bn Sign.NegOrZero) (Now false);
  assert_equal ~msg:"err #9" (FR.sgn bn Sign.Neg) (Now false);
  assert_equal ~msg:"err #10" (FR.sgn bn Sign.Pos) (Now true);
  (* neg *)
  assert_equal ~msg:"err #11" (FR.sgn cn Sign.Zero) (Now false);
  assert_equal ~msg:"err #12" (FR.sgn cn Sign.PosOrZero) (Now false);
  assert_equal ~msg:"err #13" (FR.sgn cn Sign.NegOrZero) (Now true);
  assert_equal ~msg:"err #14" (FR.sgn cn Sign.Neg) (Now true);
  assert_equal ~msg:"err #15" (FR.sgn cn Sign.Pos) (Now false)

let suite =  "Float Test" >::: [
  "test_Float_Set_to_string" >:: test_Float_Set_to_string ;
  "test_Float_Set_eq" >:: test_Float_Set_eq ;
  "test_Float_Set_neq" >:: test_Float_Set_neq ;
  "test_Float_Ring_sgn" >::  test_Float_Ring_sgn ]
