
- : unit = ()
#   - : ('a,
     Instances.AT2R.n Tuple.Record2D.t ->
     Instances.AT2R.n Tuple.Record2D.t -> Instances.AT2R.n Tuple.Record2D.t)
    code
=
.<fun p_1 -> fun v_2 -> {c0 = (p_1.c0 +. v_2.c0); c1 = (p_1.c1 +. v_2.c1)}>.
# - : ('a,
     Instances.AT3R.n Tuple.Record3D.t ->
     Instances.AT3R.n Tuple.Record3D.t -> Instances.AT3R.n Tuple.Record3D.t)
    code
=
.<fun p_3 ->
   fun v_4 ->
    {x = (p_3.x +. v_4.x); y = (p_3.y +. v_4.y); z = (p_3.z +. v_4.z)}>.
# 
