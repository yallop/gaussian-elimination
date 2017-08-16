
open OUnit

let suite = "mag4 OUnit Test" >:::
  [ Staged_test.suite ;
    Basetypes_test.suite;
    Float_test.suite;
    Matrix_test.suite;
    Determinant_test.suite;
    Pointen_test.suite;
    Affine_test.suite ;
    Hplane_test.suite ;
    Sphere_test.suite; Sphere_test.suite1;
    Orient_test.suite;
    Insphere_test.suite;
    Inside_test.suite ]

let _ =
  run_test_tt_main suite
