
open OUnit
open Staged
open Float
open Matrix
open Determinant

module M = Matrix (Float_Field_Exact)
module D = Determinant (Float_Field_Exact) (M)

let a () =
  [| [| Now 1.; Now 1.; Now (~-. 1.) |] ;
     [| Now 4.; Now 2.; Now 0.       |] ;
     [| Now 9.; Now 3.; Now (~-. 2.) |] |]
let ma () = M.create 3 3 (fun i j -> (a()).(i).(j))

let test_eval_1 _ =
  assert_equal ~msg:"err #1" (D.eval (ma())) (Now 10.)

(* transpose *)
let a' () =
  [| [| Now 1.;       Now 4.; Now 9. |] ;
     [| Now 1.;       Now 2.; Now 3.       |] ;
     [| Now (~-. 1.); Now 0.; Now (~-. 2.) |] |]
let ma' () = M.create 3 3 (fun i j -> (a'()).(i).(j))

let test_eval_transpose _ =
  assert_equal ~msg:"err #2" (D.eval (ma'())) (Now 10.)

(* row exchange *)
let a1 () =
  [| [| Now 4.; Now 2.; Now 0.       |] ;
     [| Now 1.; Now 1.; Now (~-. 1.) |] ;
     [| Now 9.; Now 3.; Now (~-. 2.) |] |]
let ma1 () = M.create 3 3 (fun i j -> (a1()).(i).(j))

let test_eval_swap _ =
  assert_equal ~msg:"err #3" (D.eval (ma1())) (Now (~-. 10.))

(* matrix with code values *)
let a2 () =
  [| [| (of_atom .<4.>.); Now 5. |] ;
     [| Now 2.;           Now 0. |] |]
let ma2 () = M.create 2 2 (fun i j -> (a2()).(i).(j))

let test_eval_code _ =
  let v = D.eval (ma2()) in
  assert_bool "err #4" (is_now v);
  assert_equal ~msg:"err #5" v (Now (~-. 10.))

let suite = "Determinant Test" >::: [
  "test_eval_1" >:: test_eval_1 ;
  "test_eval_transpose" >:: test_eval_transpose ;
  "test_eval_swap" >:: test_eval_swap ;
  "test_eval_code" >:: test_eval_code ]
