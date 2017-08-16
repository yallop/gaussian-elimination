
open OUnit
open Staged
open Float
open Matrix

module M = Matrix (Float_Field_Exact)

(* Test fixutes are function because of monomorphism. *)

let a () =
  [| [| Now 1.; Now 1.; Now (~-. 1.) |] ;
     [| Now 4.; Now 2.; Now 0.       |] ;
     [| Now 9.; Now 3.; Now (~-. 2.) |] |]
let m () = { a = 3; b = 3; c = (a ()) }

(* transpose *)
let a' () =
  [| [| Now 1.;       Now 4.; Now 9. |] ;
     [| Now 1.;       Now 2.; Now 3.       |] ;
     [| Now (~-. 1.); Now 0.; Now (~-. 2.) |] |]
let m' () = { a = 3; b = 3; c = (a' ()) }

(* matrix with code values *)
let a2 () =
  [| [| (of_atom .<4.>.); Now 5. |] ;
     [| Now 4.;           Now 1. |] ;
     [| Now 3.;           Now 2. |] |]
let m2 () = { a = 3; b = 2; c = (a2 ()) }

let test_nrows_ncols _ =
  assert_equal ~msg:"err #1" (M.nrows (m2 ())) 3;
  assert_equal ~msg:"err #2" (M.ncols (m2 ())) 2

let test_get _ =
  assert_equal ~msg:"err #1" (a ())
               (Array.init 3 (fun i ->
                  Array.init 3 (fun j -> M.get (m ()) i j)))

let test_row _ =
  let test i =
    let r = M.row (m ()) i in
    let ra = Array.map (fun j -> M.get r 0 j) [| 0; 1; 2 |] in
    assert_equal ~msg:("err #" ^ (string_of_int i)) ra (a()).(i)
  in test 0; test 1; test 2

let test_col _ =
  let test j =
    let c = M.col (m ()) j in
    let ca = Array.map (fun i -> M.get c i 0) [| 0; 1; 2 |] in
    assert_equal ~msg:("err #" ^ (string_of_int j)) ca (a'()).(j)
  in test 0; test 1; test 2
  (* let c = M.col (m()) 
  assert_equal ~msg:"err #1" (a' ())
               (Array.init 3 (fun i -> M.col (m ()) i)) *)

let test_same_dim _ =
  assert_equal ~msg:"err #1" (M.same_dim (m ()) (m' ())) true;
  assert_equal ~msg:"err #1" (M.same_dim (m ()) (m2 ())) false

let test_create _ =
  assert_equal ~msg:"err #1" (m ()) (M.create 3 3 (fun i j -> (a ()).(i).(j)));
  assert_equal ~msg:"err #1" (m' ()) (M.create 3 3 (fun i j -> (a' ()).(i).(j)));
  assert_equal ~msg:"err #1" (m2 ()) (M.create 3 2 (fun i j -> (a2 ()).(i).(j)))

let z () =
  [| [| Now 0.; Now 0. |] ;
     [| Now 0.; Now 0. |] ;
     [| Now 0.; Now 0. |] |]
let zmat () = { a = 3; b = 2; c = (z ()) }

let d () =
  [| [| Now 1.; Now 0.; Now 0. |] ;
     [| Now 0.; Now 2.; Now 0. |] ;
     [| Now 0.; Now 0.; Now 3. |] |]
let diagmat () = { a = 3; b = 3; c = (d ()) }


let id () =
  [| [| Now 1.; Now 0.; Now 0. |] ;
     [| Now 0.; Now 1.; Now 0. |] ;
     [| Now 0.; Now 0.; Now 1. |] |]
let idmat () = { a = 3; b = 3; c = (id ()) }

let test_zero _ =
  assert_equal ~msg:"err #1" (zmat()) (M.zero 3 2)

let test_diagonal _ =
  let d = M.diag 3 (fun i -> (Now [|1.; 2.; 3.|].(i))) in
  assert_equal ~msg:"err #1" (diagmat()) d

let test_identity _ =
  assert_equal ~msg:"err #1" (idmat()) (M.id 3)

let test_transpose _ =
  let m () = M.create 1 2 (fun _ j -> [| Now 1.; Now 2. |].(j))
  and m' () = M.create 2 1 (fun i j -> [| [| Now 1. |]; [| Now 2. |] |].(i).(j))
  in
  assert_equal ~msg:"err #1" (m'()) (M.transpose (m()))

let test_haugment _ =
  let m () = { a=2; b=1; c=[|[|Now 1.|]; [|Now 2.|]|] }
  and m' () = { a=2; b=2; c=[|[|Now 1.; Now 1.|];
			     [|Now 2.; Now 2.|]|]} in
  let res () = M.haugment (m()) (m()) in
  assert_equal ~msg:"err #1" (res()) (m'())

let test_vaugment _ =
  let m () = { a=2; b=1; c=[|[|Now 0.|]; [|Now 2.|]|] }
  and m' () = {a=3; b=1; c=[|[|Now 0.|]; [|Now 2.|];[|Now 1.|]|]} in
  assert_equal ~msg:"err #1" (M.vaugment (m()) (M.id 1)) (m'())

(* m \times diagmat *)
let ans () =
 [| [| Now 1.; Now 2.; Now ~-. 3. |] ;
    [| Now 4.; Now 4.; Now ~-. 0. |] ;
    [| Now 9.; Now 6.; Now ~-. 6. |] |]
let m_ans () = { a = 3; b = 3; c = (ans ()) }

let test_mul _ =
  let m_times_d = M.mul (m()) (diagmat()) in
  assert_equal m_times_d (m_ans())

(* m + m' *)
let ans1 () =
  [| [| Now 2.  ;  Now 5. ;  Now 8.   |] ;
     [| Now 5.  ;  Now 4. ;  Now 3.   |] ;
     [| Now 8.  ;  Now 3. ;  Now ~-. 4. |] |]
let m_ans1 () = { a = 3; b = 3; c = (ans1 ()) }

let test_add _ =
  assert_equal ~msg:"err #1" (M.add (m()) (m'())) (m_ans1())

let test_smul _ =
  assert_equal (M.zero 3 3) (M.add (m()) (M.smul (m()) (Now ~-. 1.)))

(* @TODO more tests of all identities
 * of matrix/scalar add, sub, mul *)

let suite = "Matrix Test" >::: [
  "test_nrows_ncols" >:: test_nrows_ncols ;
  "test_get" >:: test_get ;
  "test_row " >:: test_row ;
  "test_col " >:: test_col ;
  "test_same_dim " >:: test_same_dim ;
  "test_create " >:: test_create ;
  "test_zero " >:: test_zero ;
  "test_diagonal " >:: test_diagonal ;
 "test_identity " >:: test_identity ;
 "test_transpose " >:: test_transpose ;
 "test_vaugment " >:: test_vaugment ;
 "test_haugment " >:: test_haugment ;
 "test_mul " >:: test_mul ;
 "test_add " >:: test_add ;
 "test_smul" >:: test_smul ]
