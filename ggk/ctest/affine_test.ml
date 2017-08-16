open Staged
open Affine
open Instances

let print s = Printf.printf "\n\n ==== %s ==== \n\n" s ;;

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
          (AT : AFFINE with type ('a,'b) trep = ('a,'b) ST.trep) = struct
  let inst2 f = .< fun p v -> .~( ST.extract (f (ST.mkc (Constant, .<p>.)) (ST.mkc (Constant, .<v>.))) ) >.

  let test1 () = inst2 (fun p v -> let t = AT.translation v in AT.apply_p t p)
end

module G2R = Gen(Tuple.Record2D)(AT2R) ;;
module G3R = Gen(Tuple.Record3D)(AT3R) ;;

print "CUT MARKER" ;;

G2R.test1 () ;;
G3R.test1 () ;;
