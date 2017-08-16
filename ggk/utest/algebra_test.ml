
(* *********************** *)
(* This file is incomplete *)
(* *********************** *)


(* SET *)

module Testable_SET (S : SET) =
struct
    
end

module Test_Set (S : SET) =
struct
  let test_Float_Set_to_string _ =
    assert_equal ~msg:"err #1" (S.to_string_s (Now 0.)) (Now "0.");
    assert_equal ~msg:"err #2" (.! to_code (S.to_string_s (Later .<0.>.))) 

end
