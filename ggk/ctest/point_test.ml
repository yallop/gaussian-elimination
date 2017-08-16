open Staged
open Point
open Instances

let print s = Printf.printf "\n\n ==== %s ==== \n\n" s ;;

(* Some things are instance specific *)
module Gen(ST:Tuple.StagedTuple)
          (E : ISO_AXIS_ORDERED_EUCLIDEAN with type ('a,'b) N.rep = ('a,'b) ST.rep 
                                           and type ('a,'b) P.trep = ('a,'b) ST.trep) = struct
  let inst1 f = .< fun a -> .~( to_code (f (ST.mkc (Constant, .<a>.)))) >.
  let inst2 f = .< fun a b -> .~( ST.extract (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.
  let inst3 f = .< fun a b -> .~( to_code (f (ST.mkc (Constant, .<a>.)) (ST.mkc (Constant, .<b>.))) ) >.

  let test1 () = inst2 E.sub
  let test2 () = inst3 (E.lt 0) (* The 'int' parameter refers to the coordinate in E^n *)
  let test3 () = inst3 (fun a b -> E.V.length (E.sub a b)) (* distance *)

end

module GP2R = Gen(Tuple.Record2D)(P2R) ;;
module GP3R = Gen(Tuple.Record3D) (P3R) ;;

print "CUT MARKER" ;;
print "POINT TEST" ;;

print "Point_En Record2d sub () " ;;
GP2R.test1 () ;;
print "Point_En Record3d sub () " ;;
GP3R.test1 () ;;

print "Point_En Record2d cmp_x () " ;;
GP2R.test2 () ;;
print "Point_En Record3d cmp_x () " ;;
GP3R.test2 () ;;

print "Point_En Record2d dist () " ;;
GP2R.test3 () ;;
print "Point_En Record3d dist () " ;;
GP3R.test3 () ;;
