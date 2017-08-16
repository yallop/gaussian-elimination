open Staged
open Algebra

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

Printf.printf "\n\n ==== CUT MARKER ==== \n\n" ;;
Printf.printf "\n\n ==== POWER TEST ==== \n\n" ;;

Printf.printf "\n\n ==== PowerFloat power () ==== \n\n" ;;
(* PowerFloat.power_gen () ;; *)

PG_F1.power_gen () ;;
PG_F2.power_gen () ;;
PG_F8.power_gen () ;;

PG_I1.power_gen () ;;
PG_I2.power_gen () ;;
PG_I8.power_gen () ;;


(* PowerFloat.gen_power 2  ;;
PowerFloat.gen_power 3  ;;
PowerFloat.gen_power 6  ;; *)

(*
Printf.printf "\n\n ==== PowerRational power () ==== \n\n" ;;
PowerRational.gen_power 1  ;;
PowerRational.gen_power 2  ;;
PowerRational.gen_power 3  ;;
PowerRational.gen_power 6  ;;

Printf.printf "\n\n ==== PowerInteger power () ==== \n\n" ;;
PowerInteger.gen_power 1  ;;
PowerInteger.gen_power 2  ;;
PowerInteger.gen_power 3  ;;
PowerInteger.gen_power 6  ;;
*)
