
- : unit = ()
#   

 ==== INSIDE TEST ==== 

- : unit = ()
#     

 ==== Inside simplex 2D Triangle in_ () ==== 

- : unit = ()
# - : ('a,
     Instances.P2R.P.n Tuple.Record2D.t array ->
     Instances.P2R.P.n Tuple.Record2D.t -> bool)
    code
=
.<fun ps_1 ->
   fun p_2 ->
    (((((ps_1.(1)).c0 *. ((ps_1.(2)).c1 +. (~-. p_2.c1))) +.
        ((~-. ((ps_1.(1)).c1 *. ((ps_1.(2)).c0 +. (~-. p_2.c0)))) +.
          (((ps_1.(2)).c0 *. p_2.c1) +. (~-. ((ps_1.(2)).c1 *. p_2.c0))))) >
       1e-05) &&
      (((((ps_1.(2)).c0 *. ((ps_1.(0)).c1 +. (~-. p_2.c1))) +.
          ((~-. ((ps_1.(2)).c1 *. ((ps_1.(0)).c0 +. (~-. p_2.c0)))) +.
            (((ps_1.(0)).c0 *. p_2.c1) +. (~-. ((ps_1.(0)).c1 *. p_2.c0)))))
         > 1e-05) &&
        ((((ps_1.(0)).c0 *. ((ps_1.(1)).c1 +. (~-. p_2.c1))) +.
           ((~-. ((ps_1.(0)).c1 *. ((ps_1.(1)).c0 +. (~-. p_2.c0)))) +.
             (((ps_1.(1)).c0 *. p_2.c1) +. (~-. ((ps_1.(1)).c1 *. p_2.c0)))))
          > 1e-05)))>.
# 

 ==== Inside simplex 3D Tetra in_ () ==== 

- : unit = ()
# - : ('a,
     Instances.P3R.P.n Tuple.Record3D.t array ->
     Instances.P3R.P.n Tuple.Record3D.t -> bool)
    code
=
.<fun ps_9 ->
   fun p_10 ->
    (((((ps_9.(2)).x *.
         (((ps_9.(1)).y *. ((ps_9.(3)).z +. (~-. p_10.z))) +.
           ((~-. ((ps_9.(1)).z *. ((ps_9.(3)).y +. (~-. p_10.y)))) +.
             (((ps_9.(3)).y *. p_10.z) +. (~-. ((ps_9.(3)).z *. p_10.y))))))
        +.
        ((~-.
           ((ps_9.(2)).y *.
             (((ps_9.(1)).x *. ((ps_9.(3)).z +. (~-. p_10.z))) +.
               ((~-. ((ps_9.(1)).z *. ((ps_9.(3)).x +. (~-. p_10.x)))) +.
                 (((ps_9.(3)).x *. p_10.z) +. (~-. ((ps_9.(3)).z *. p_10.x)))))))
          +.
          (((ps_9.(2)).z *.
             (((ps_9.(1)).x *. ((ps_9.(3)).y +. (~-. p_10.y))) +.
               ((~-. ((ps_9.(1)).y *. ((ps_9.(3)).x +. (~-. p_10.x)))) +.
                 (((ps_9.(3)).x *. p_10.y) +. (~-. ((ps_9.(3)).y *. p_10.x))))))
            +.
            (~-.
              (((ps_9.(1)).x *.
                 (((ps_9.(3)).y *. p_10.z) +. (~-. ((ps_9.(3)).z *. p_10.y))))
                +.
                ((~-.
                   ((ps_9.(1)).y *.
                     (((ps_9.(3)).x *. p_10.z) +.
                       (~-. ((ps_9.(3)).z *. p_10.x))))) +.
                  ((ps_9.(1)).z *.
                    (((ps_9.(3)).x *. p_10.y) +.
                      (~-. ((ps_9.(3)).y *. p_10.x)))))))))) > 1e-05) &&
      (((((ps_9.(0)).x *.
           (((ps_9.(2)).y *. ((ps_9.(3)).z +. (~-. p_10.z))) +.
             ((~-. ((ps_9.(2)).z *. ((ps_9.(3)).y +. (~-. p_10.y)))) +.
               (((ps_9.(3)).y *. p_10.z) +. (~-. ((ps_9.(3)).z *. p_10.y))))))
          +.
          ((~-.
             ((ps_9.(0)).y *.
               (((ps_9.(2)).x *. ((ps_9.(3)).z +. (~-. p_10.z))) +.
                 ((~-. ((ps_9.(2)).z *. ((ps_9.(3)).x +. (~-. p_10.x)))) +.
                   (((ps_9.(3)).x *. p_10.z) +.
                     (~-. ((ps_9.(3)).z *. p_10.x))))))) +.
            (((ps_9.(0)).z *.
               (((ps_9.(2)).x *. ((ps_9.(3)).y +. (~-. p_10.y))) +.
                 ((~-. ((ps_9.(2)).y *. ((ps_9.(3)).x +. (~-. p_10.x)))) +.
                   (((ps_9.(3)).x *. p_10.y) +.
                     (~-. ((ps_9.(3)).y *. p_10.x)))))) +.
              (~-.
                (((ps_9.(2)).x *.
                   (((ps_9.(3)).y *. p_10.z) +.
                     (~-. ((ps_9.(3)).z *. p_10.y)))) +.
                  ((~-.
                     ((ps_9.(2)).y *.
                       (((ps_9.(3)).x *. p_10.z) +.
                         (~-. ((ps_9.(3)).z *. p_10.x))))) +.
                    ((ps_9.(2)).z *.
                      (((ps_9.(3)).x *. p_10.y) +.
                        (~-. ((ps_9.(3)).y *. p_10.x)))))))))) > 1e-05) &&
        (((((ps_9.(1)).x *.
             (((ps_9.(0)).y *. ((ps_9.(3)).z +. (~-. p_10.z))) +.
               ((~-. ((ps_9.(0)).z *. ((ps_9.(3)).y +. (~-. p_10.y)))) +.
                 (((ps_9.(3)).y *. p_10.z) +. (~-. ((ps_9.(3)).z *. p_10.y))))))
            +.
            ((~-.
               ((ps_9.(1)).y *.
                 (((ps_9.(0)).x *. ((ps_9.(3)).z +. (~-. p_10.z))) +.
                   ((~-. ((ps_9.(0)).z *. ((ps_9.(3)).x +. (~-. p_10.x)))) +.
                     (((ps_9.(3)).x *. p_10.z) +.
                       (~-. ((ps_9.(3)).z *. p_10.x))))))) +.
              (((ps_9.(1)).z *.
                 (((ps_9.(0)).x *. ((ps_9.(3)).y +. (~-. p_10.y))) +.
                   ((~-. ((ps_9.(0)).y *. ((ps_9.(3)).x +. (~-. p_10.x)))) +.
                     (((ps_9.(3)).x *. p_10.y) +.
                       (~-. ((ps_9.(3)).y *. p_10.x)))))) +.
                (~-.
                  (((ps_9.(0)).x *.
                     (((ps_9.(3)).y *. p_10.z) +.
                       (~-. ((ps_9.(3)).z *. p_10.y)))) +.
                    ((~-.
                       ((ps_9.(0)).y *.
                         (((ps_9.(3)).x *. p_10.z) +.
                           (~-. ((ps_9.(3)).z *. p_10.x))))) +.
                      ((ps_9.(0)).z *.
                        (((ps_9.(3)).x *. p_10.y) +.
                          (~-. ((ps_9.(3)).y *. p_10.x)))))))))) > 1e-05) &&
          ((((ps_9.(0)).x *.
              (((ps_9.(1)).y *. ((ps_9.(2)).z +. (~-. p_10.z))) +.
                ((~-. ((ps_9.(1)).z *. ((ps_9.(2)).y +. (~-. p_10.y)))) +.
                  (((ps_9.(2)).y *. p_10.z) +.
                    (~-. ((ps_9.(2)).z *. p_10.y)))))) +.
             ((~-.
                ((ps_9.(0)).y *.
                  (((ps_9.(1)).x *. ((ps_9.(2)).z +. (~-. p_10.z))) +.
                    ((~-. ((ps_9.(1)).z *. ((ps_9.(2)).x +. (~-. p_10.x))))
                      +.
                      (((ps_9.(2)).x *. p_10.z) +.
                        (~-. ((ps_9.(2)).z *. p_10.x))))))) +.
               (((ps_9.(0)).z *.
                  (((ps_9.(1)).x *. ((ps_9.(2)).y +. (~-. p_10.y))) +.
                    ((~-. ((ps_9.(1)).y *. ((ps_9.(2)).x +. (~-. p_10.x))))
                      +.
                      (((ps_9.(2)).x *. p_10.y) +.
                        (~-. ((ps_9.(2)).y *. p_10.x)))))) +.
                 (~-.
                   (((ps_9.(1)).x *.
                      (((ps_9.(2)).y *. p_10.z) +.
                        (~-. ((ps_9.(2)).z *. p_10.y)))) +.
                     ((~-.
                        ((ps_9.(1)).y *.
                          (((ps_9.(2)).x *. p_10.z) +.
                            (~-. ((ps_9.(2)).z *. p_10.x))))) +.
                       ((ps_9.(1)).z *.
                         (((ps_9.(2)).x *. p_10.y) +.
                           (~-. ((ps_9.(2)).y *. p_10.x)))))))))) > 1e-05))))>.
# 
