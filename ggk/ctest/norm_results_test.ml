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

(* VECTOR TEST *)


(* VectorStaged Record2D length () *)
GV2R.test1 () ;;
(* VectorStaged Pair2D length () *)
GV2P.test1 () ;;
(* VectorStaged Record3D length () *)
GV3R.test1 () ;;

(* VectorStaged Record2D sub () *)
GV2R.test2 () ;;
(* VectorStaged Pair2D sub () *)
GV2P.test2 () ;;
(* VectorStaged Record3D sub () *)
GV3R.test2 () ;;

(* VectorStaged Record2D dist () *)
GV2R.test3 () ;;
(* VectorStaged Pair2D dist () *)
GV2P.test3 () ;;
(* VectorStaged Record3D dist () *)
GV3R.test3 () ;;

(* VectorStaged Record2D unit_vec () *)
GV2R.test4 () ;;
(* VectorStaged Pair2D unit_vec () *)
GV2P.test4 () ;;
(* VectorStaged Record3D univ_vec () *)
GV3R.test4 () ;;

(* VectorStaged Record2D dot () *)
GV2R.test5 () ;;
(* VectorStaged Pair2D dot () *)
GV2P.test5 () ;;
(* VectorStaged Record3D dot () *)
GV3R.test5 () ;;

