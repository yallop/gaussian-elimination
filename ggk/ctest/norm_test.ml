open Staged
open Vector
open Instances

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
          (V:VECTOR with type ('a,'b) rep = ('a,'b) ST.rep and type ('a,'b) trep = ('a,'b) ST.trep) = struct
  let inst1 f = .< fun a -> .~( to_code (f (ST.mkc (Constant, .<a>.)))) >.
  let inst2 f = .< fun a b -> .~( ST.extract (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.
  let inst3 f = .< fun a b -> .~( to_code (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.

  let test1 () = inst1 V.length 
  let test2 () = inst2 V.sub
  let test3 () = inst3 (fun a b -> V.length (V.sub a b)) (* distance *)
  let test4 () = inst2 (fun a b -> V.direction (V.sub a b)) (* unit_vec *)
  let test5 () = inst3 V.dot
end

module GV2R = Gen(Tuple.Record2D)(V2R);;
module GV2P = Gen(Tuple.Pair2D)(V2P);;
module GV3R = Gen(Tuple.Record3D)(V3R);;

Printf.printf "\n\n ==== CUT MARKER ==== \n\n" ;;
Printf.printf "\n\n ==== VECTOR TEST ==== \n\n" ;;

Printf.printf "\n\n ==== VectorStaged Record2D length () ==== \n\n" ;;
GV2R.test1 () ;;
Printf.printf "\n\n ==== VectorStaged Pair2D length () ==== \n\n" ;;
GV2P.test1 () ;;
Printf.printf "\n\n ==== VectorStaged Record3D length () ==== \n\n" ;;
GV3R.test1 () ;;

Printf.printf "\n\n ==== VectorStaged Record2D sub () ==== \n\n" ;;
GV2R.test2 () ;;
Printf.printf "\n\n ==== VectorStaged Pair2D sub () ==== \n\n" ;;
GV2P.test2 () ;;
Printf.printf "\n\n ==== VectorStaged Record3D sub () ==== \n\n" ;;
GV3R.test2 () ;;

Printf.printf "\n\n ==== VectorStaged Record2D dist () ==== \n\n" ;;
GV2R.test3 () ;;
Printf.printf "\n\n ==== VectorStaged Pair2D dist () ==== \n\n" ;;
GV2P.test3 () ;;
Printf.printf "\n\n ==== VectorStaged Record3D dist () ==== \n\n" ;;
GV3R.test3 () ;;

Printf.printf "\n\n ==== VectorStaged Record2D unit_vec () ==== \n\n" ;;
GV2R.test4 () ;;
Printf.printf "\n\n ==== VectorStaged Pair2D unit_vec () ==== \n\n" ;;
GV2P.test4 () ;;
Printf.printf "\n\n ==== VectorStaged Record3D univ_vec () ==== \n\n" ;;
GV3R.test4 () ;;

Printf.printf "\n\n ==== VectorStaged Record2D dot () ==== \n\n" ;;
GV2R.test5 () ;;
Printf.printf "\n\n ==== VectorStaged Pair2D dot () ==== \n\n" ;;
GV2P.test5 () ;;
Printf.printf "\n\n ==== VectorStaged Record3D dot () ==== \n\n" ;;
GV3R.test5 () ;;

