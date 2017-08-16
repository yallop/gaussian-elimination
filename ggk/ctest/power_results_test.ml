open Staged
open Algebra

open OUnit

module GenericPower (R : RING) = struct
  let rec power n x =
    match n with
    | 0 -> R.one
    | n -> R.mul x (power (n-1) x)
end ;;

module type POWER_VAR = sig
  module R : RING with type ('a,'b) rep = ('a,'b) staged
  val n : int
end ;;

module PowerGen (PV : POWER_VAR) = struct
  let power_gen () =
    let module GP = GenericPower(PV.R) in
    .< fun x -> .~(to_code
		     (GP.power PV.n (of_const .<x>.))) >.
end ;;

module Float1 = struct
  module R = Float.Float_Real_Exact
  let n = 1
end
;;

module Float2 = struct
  module R = Float.Float_Real_Exact
  let n = 2
end
;;

module Float8 = struct
  module R = Float.Float_Real_Exact
  let n = 8
end
;;

module Integer1 = struct
  module R = Integer.Ring
  let n = 1
end ;;

module Integer2 = struct
  module R = Integer.Ring
  let n = 2
end ;;

module Integer8 = struct
  module R = Integer.Ring
  let n = 8
end ;;

module PG_F1 = PowerGen(Float1);;
module PG_F2 = PowerGen(Float2);;
module PG_F8 = PowerGen(Float8);;

module PG_I1 = PowerGen(Integer1);;
module PG_I2 = PowerGen(Integer2);;
module PG_I8 = PowerGen(Integer8);;

(* module PowerRational = PowerGen(Rational_Ring);;
module PowerInteger = PowerGen(Ring);; *)

(* POWER TEST *)

(* PowerFloat power () *)
(* PowerFloat.power_gen () ;; *)

let pg_f1_powCode = PG_F1.power_gen () ;;
let pg_f1_pow = .! pg_f1_powCode;;

let pg_f2_powCode = PG_F2.power_gen () ;;
let pg_f2_pow = .! pg_f2_powCode;;

let pg_f8_powCode = PG_F8.power_gen () ;;
let pg_f8_pow = .! pg_f8_powCode;;

let pg_i1_powCode = PG_I1.power_gen () ;;
let pg_i1_pow = .! pg_i1_powCode;;

let pg_i2_powCode = PG_I2.power_gen () ;;
let pg_i2_pow = .! pg_i2_powCode;;

let pg_i8_powCode = PG_I8.power_gen () ;;
let pg_i8_pow = .! pg_i8_powCode;;

let test_pgf1pow _ =
   let x = 3.0 in
   assert_equal (pg_f1_pow x) x;;

let test_pgf2pow _ =
   let x = 2.0 in
   assert_equal (pg_f2_pow x) (x*.x);;

let test_pgf8pow _ =
   let x = 2.0 in
   assert_equal (pg_f8_pow x) (x**8.0);;

let test_pgi1pow _ =
   let x = 7 in
   assert_equal (pg_i1_pow x) (x);;

let test_pgi2pow _ =
   let x = 7 in
   assert_equal (pg_i2_pow x) (x*x);;

let test_pgi8pow _ =
   let x = 7 in
   assert_equal (pg_i8_pow x) (x*x*x*x*x*x*x*x);;

let suite = "OUnit Test" >:::
   ["test_pgf1pow" >:: test_pgf1pow;
    "test_pgf2pow" >:: test_pgf2pow;
    "test_pgf8pow" >:: test_pgf8pow;
    "test_pgi1pow" >:: test_pgi1pow;
    "test_pgi2pow" >:: test_pgi2pow;
    "test_pgi8pow" >:: test_pgi8pow]

let _ =
   run_test_tt_main suite


