open Staged
open Point
open Simplex
open Instances

let print s = Printf.printf "\n\n ==== %s ==== \n\n" s ;;

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
           (E : EUCLIDEAN with type ('a,'b) N.rep = ('a,'b) ST.rep 
                           and type ('a,'b) P.trep = ('a,'b) ST.trep) = struct
  let inst4 f = .< fun ps p -> .~( to_code (f (Staged.of_marked (Constant, .<ps>.)) (ST.mkc (Constant, .<p>.)))) >.
  let st_array n ps = Array.to_list (Array.init n (fun i -> ST.mkc (Constant, .<(.~(to_code ps)).(i)>.))) 

  module S = N_Simplex(E)

  let in_ n = inst4 (fun ps p -> 
      let ps' = st_array n ps in
      (* create a hyperplane *)
      S.in_ (S.of_vertices ps') p )

end;;

module GSeg = Gen (Tuple.Tuple1D)(P1) ;;
module GTri = Gen (Tuple.Record2D)(P2R) ;;
module GTet = Gen (Tuple.Record3D)(P3R) ;;

print "CUT MARKER" ;;

print "INSIDE TEST" ;;

(* GSeg.in_ 2;; *)
print "Inside simplex 2D Triangle in_ ()" ;;
GTri.in_ 3 ;;
print "Inside simplex 3D Tetra in_ ()" ;;
GTet.in_ 4 ;;
