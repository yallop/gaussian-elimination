
- : unit = ()
# 

 ==== POINT TEST ==== 

- : unit = ()
#   

 ==== Point_En Record2d sub ()  ==== 

- : unit = ()
# - : ('a,
     Instances.P2R.P.n Tuple.Record2D.t ->
     Instances.P2R.P.n Tuple.Record2D.t -> Instances.P2R.N.n Tuple.Record2D.t)
    code
=
.<fun a_1 -> fun b_2 -> {c0 = (a_1.c0 -. b_2.c0); c1 = (a_1.c1 -. b_2.c1)}>.
# 

 ==== Point_En Record3d sub ()  ==== 

- : unit = ()
# - : ('a,
     Instances.P3R.P.n Tuple.Record3D.t ->
     Instances.P3R.P.n Tuple.Record3D.t -> Instances.P3R.N.n Tuple.Record3D.t)
    code
=
.<fun a_3 ->
   fun b_4 ->
    {x = (a_3.x -. b_4.x); y = (a_3.y -. b_4.y); z = (a_3.z -. b_4.z)}>.
#   

 ==== Point_En Record2d cmp_x ()  ==== 

- : unit = ()
# - : ('a,
     Instances.P2R.P.n Tuple.Record2D.t ->
     Instances.P2R.P.n Tuple.Record2D.t -> bool)
    code
= .<fun a_5 -> fun b_6 -> (a_5.c0 < b_6.c0)>.
# 

 ==== Point_En Record3d cmp_x ()  ==== 

- : unit = ()
# - : ('a,
     Instances.P3R.P.n Tuple.Record3D.t ->
     Instances.P3R.P.n Tuple.Record3D.t -> bool)
    code
= .<fun a_7 -> fun b_8 -> (a_7.x < b_8.x)>.
#   

 ==== Point_En Record2d dist ()  ==== 

- : unit = ()
# - : ('a,
     Instances.P2R.P.n Tuple.Record2D.t ->
     Instances.P2R.P.n Tuple.Record2D.t -> Instances.P2R.V.n)
    code
=
.<fun a_9 ->
   fun b_10 ->
    (sqrt
      let v_11 = {c0 = (a_9.c0 -. b_10.c0); c1 = (a_9.c1 -. b_10.c1)} in
      ((v_11.c0 *. v_11.c0) +. (v_11.c1 *. v_11.c1)))>.
# 

 ==== Point_En Record3d dist ()  ==== 

- : unit = ()
# - : ('a,
     Instances.P3R.P.n Tuple.Record3D.t ->
     Instances.P3R.P.n Tuple.Record3D.t -> Instances.P3R.V.n)
    code
=
.<fun a_12 ->
   fun b_13 ->
    (sqrt
      let v_14 =
       {x = (a_12.x -. b_13.x); y = (a_12.y -. b_13.y);
        z = (a_12.z -. b_13.z)} in
      (((v_14.x *. v_14.x) +. (v_14.y *. v_14.y)) +. (v_14.z *. v_14.z)))>.
# 
