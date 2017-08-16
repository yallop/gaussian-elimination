open Staged
open Hplane
open Instances

let print s = Printf.printf "\n\n ==== %s ==== \n\n" s ;;

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
          (H:HYPER_PLANE with type ('a,'b) rep = ('a,'b) ST.rep 
                          and type ('a,'b) trep = ('a,'b) ST.trep) = struct
  let inst4 f = .< fun ps p -> .~( to_code (f (Staged.of_marked (Constant, .<ps>.)) (ST.mkc (Constant, .<p>.)))) >.
  let inst5 f = .< fun ps p -> .~( ST.extract (f (Staged.of_marked (Constant, .<ps>.)) (ST.mkc (Constant, .<p>.)))) >.

  let st_array n ps = Array.to_list (Array.init n (fun i -> ST.mkc (Constant, .<(.~(to_code ps)).(i)>.))) 

  let dist = fun n -> inst4 (fun ps p -> 
      let ps' = st_array (n+1) ps in
      (* create a hyperplane *)
      let h = H.of_points ps' in H.dist h p)
  let proj = fun n -> inst5 (fun ps p ->
      let points = st_array n ps in 
      let l = H.of_points points in 
      H.project l p)
  let col = fun n -> inst4 (fun ps p ->
      let points = st_array n ps in 
      let l = H.of_points points in 
      H.orient l p Sign.Zero)
  let pos = fun n -> inst4 (fun ps p ->
      let points = st_array n ps in 
      let l = H.of_points points in 
      H.orient l p Sign.Pos)
end ;;
                      
module GenDist1D = Gen(Tuple.Tuple1D) (H0) ;;
module GenDist2D = Gen(Tuple.Record2D) (H1) ;;
module GenDist3D = Gen(Tuple.Record3D) (H2) ;;

print "CUT MARKER" ;;
print "HPLANE TEST" ;;

print "0-hyperplane dist ()" ;;
GenDist1D.dist 0;;
print "1-hyperplane dist ()" ;;
GenDist2D.dist 1 ;;
print "2-hyperplane dist ()" ;;
GenDist3D.dist 2 ;;

print "Line proj ()" ;;
GenDist2D.proj 2 ;;
print "Plane proj ()" ;;
GenDist3D.proj 3 ;;

print "H0 col ()" ;;
GenDist1D.col 1 ;;
print "H1 col ()" ;;
GenDist2D.col 2 ;;
print "H2 plane col ()" ;;
GenDist3D.col 3 ;;

print "H0 pos ()" ;;
GenDist1D.pos 1 ;;
