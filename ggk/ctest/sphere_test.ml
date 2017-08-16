(* This file was used for diff tests with sphere.  Since these tests are more
appropriately considered unit tests, all tests have been ported to the unit test file.
The set of tests in this file will be removed from the project and no longer
maintained.  (SS, Jan 11, 2013) *)

open Staged
open Instances

let print s = Printf.printf "\n\n ==== %s ==== \n\n" s ;;

let one = lift_const 1.0;;
let s1 = S1.of_centre_radius (P1.P.orig ()) (one) ;;

let p1a = P1.P.of_list [lift_const 0.5];;
let p1b = P1.P.of_list [lift_const 1.5];;
let s2 = S2.of_centre_radius (EP2R.P.orig ()) (one) ;;
let p2a = EP2R.P.of_list [lift_const 0.5; lift_const 0.];;
let p2b = EP2R.P.of_list [lift_const 1.5; lift_const 0.];;
let s3 = S3.of_centre_radius (EP3R.P.orig ()) (one) ;;
let p3a = EP3R.P.of_list [lift_const 0.5; lift_const 0.; lift_const 0.3];;
let p3b = EP3R.P.of_list [lift_const 1.5; lift_const 0.; lift_const 0.3];;

print "CUT MARKER" ;;
print "SPHERE TEST" ;;

print "Sphere 1 content ()" ;
S1.content s1 ;;
print "Sphere 2 content ()" ;
S2.content s2 ;;
print "Sphere 3 content ()" ;
S3.content s3 ;;

print "Sphere 1 surface ()" ;
S1.surface s1 ;;
print "Sphere 2 surface ()" ;
S2.surface s2 ;;
print "Sphere 3 surface ()" ;
S3.surface s3 ;;

print "Sphere 1 inside (yes)" ;
S1.inside s1 p1a;;
print "Sphere 2 inside (yes)" ;
S2.inside s2 p2a;;
print "Sphere 3 inside (yes)" ;
S3.inside s3 p3a;;
print "Sphere 1 inside (no)" ;
S1.inside s1 p1b;;
print "Sphere 2 inside (no)" ;
S2.inside s2 p2b;;
print "Sphere 3 inside (no)" ;
S3.inside s3 p3b;;
