open Staged
open Float
open Tuple
open Vectoren
open Pointen
open Domain
open Pointdomain

let print s = Printf.printf "\n\n ==== %s ==== \n\n" s ;;

module Float = Float_Real_Exact

module V1 = VectorStaged (Float) (Tuple1D)
module P1 = En_Point (V1) (Tuple1D)
module V2R = VectorStaged (Float) (Record2D)
module P2R = En_Point (V2R) (Record2D)
module V3R = VectorStaged (Float) (Record3D)
module P3R = En_Point (V3R) (Record3D)

module D1 = PointDomain (P1)
module D2R = PointDomain (P2R)
module D3R = PointDomain (P3R)

module Gen (D : DOMAIN) =
struct
  let rand _ =
    .< fun d -> .~(to_code (D.rand_point .<d>.)) >.
  let itern n f =
    .< fun d -> .~(D.itern n .<d>. f) >.
  let fold f z =
    .< fun d -> .~(D.fold .<d>. f z) >.

  let add_x _ =
    let f ac p =
      let p = of_atom p and ac = of_atom ac in
      Staged.to_code (D.P.N.add_s (D.P.coord p 0) ac)
    in
    .< fun d -> .~(D.fold .<d>. f .<D.P.N.zero>.) >. ;;

end

module GD1 = Gen(D1)
module GD2R = Gen(D2R)
module GD3R = Gen(D3R) ;;

print "CUT MARKER" ;;
print "DOMAIN TEST" ;;

print "D1 rand point ()" ;;
GD1.rand () ;;
print "D2R rand point ()" ;;
GD2R.rand () ;;
print "D3R rand point ()" ;;
GD3R.rand () ;;

print "D1 intern ()" ;;
GD1.itern .<10>. (fun _ p ->
  .<let _ = .~(to_code (P1.coord (of_atom p) 0)) in ()>.) ;;
print "D2R itern ()" ;;
GD2R.itern .<10>. (fun _ p ->
  .<let _ = .~(to_code (P2R.coord (of_atom p) 1)) in ()>.) ;;
print "D3R intern ()" ;;
GD3R.itern .<10>. (fun _ p ->
  .<let _ = .~(to_code (P3R.coord (of_atom p) 2)) in ()>.) ;;

print "D1 addx ()" ;;
GD1.add_x () ;;
print "GD2R addx ()" ;;
GD2R.add_x () ;;
print "GD3R addx ()" ;;
GD3R.add_x () ;;

