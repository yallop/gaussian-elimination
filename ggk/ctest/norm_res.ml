
- : unit = ()
# 

 ==== VECTOR TEST ==== 

- : unit = ()
#   

 ==== VectorStaged Record2D length () ==== 

- : unit = ()
# - : ('a, Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n) code =
.<fun a_1 -> (sqrt ((a_1.c0 *. a_1.c0) +. (a_1.c1 *. a_1.c1)))>.
# 

 ==== VectorStaged Pair2D length () ==== 

- : unit = ()
# - : ('a, Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n) code =
.<fun a_2 -> (sqrt let (x_3, y_4) = a_2 in ((x_3 *. x_3) +. (y_4 *. y_4)))>.
# 

 ==== VectorStaged Record3D length () ==== 

- : unit = ()
# - : ('a, Instances.V3R.n Tuple.Record3D.t -> Instances.V3R.n) code =
.<fun a_5 ->
   (sqrt (((a_5.x *. a_5.x) +. (a_5.y *. a_5.y)) +. (a_5.z *. a_5.z)))>.
#   

 ==== VectorStaged Record2D sub () ==== 

- : unit = ()
# - : ('a,
     Instances.V2R.n Tuple.Record2D.t ->
     Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n Tuple.Record2D.t)
    code
=
.<fun a_6 -> fun b_7 -> {c0 = (a_6.c0 -. b_7.c0); c1 = (a_6.c1 -. b_7.c1)}>.
# 

 ==== VectorStaged Pair2D sub () ==== 

- : unit = ()
# - : ('a,
     Instances.V2P.n Tuple.Pair2D.t ->
     Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n Tuple.Pair2D.t)
    code
=
.<fun a_8 ->
   fun b_9 ->
    let (x_10, y_11) = a_8 in
    let (x_12, y_13) = b_9 in ((x_10 -. x_12), (y_11 -. y_13))>.
# 

 ==== VectorStaged Record3D sub () ==== 

- : unit = ()
# - : ('a,
     Instances.V3R.n Tuple.Record3D.t ->
     Instances.V3R.n Tuple.Record3D.t -> Instances.V3R.n Tuple.Record3D.t)
    code
=
.<fun a_14 ->
   fun b_15 ->
    {x = (a_14.x -. b_15.x); y = (a_14.y -. b_15.y); z = (a_14.z -. b_15.z)}>.
#   

 ==== VectorStaged Record2D dist () ==== 

- : unit = ()
# - : ('a,
     Instances.V2R.n Tuple.Record2D.t ->
     Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n)
    code
=
.<fun a_16 ->
   fun b_17 ->
    (sqrt
      let v_18 = {c0 = (a_16.c0 -. b_17.c0); c1 = (a_16.c1 -. b_17.c1)} in
      ((v_18.c0 *. v_18.c0) +. (v_18.c1 *. v_18.c1)))>.
# 

 ==== VectorStaged Pair2D dist () ==== 

- : unit = ()
# - : ('a,
     Instances.V2P.n Tuple.Pair2D.t ->
     Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n)
    code
=
.<fun a_19 ->
   fun b_20 ->
    (sqrt
      let v_27 =
       let (x_21, y_22) = a_19 in
       let (x_23, y_24) = b_20 in ((x_21 -. x_23), (y_22 -. y_24)) in
      let (x_28, y_29) = v_27 in ((x_28 *. x_28) +. (y_29 *. y_29)))>.
# 

 ==== VectorStaged Record3D dist () ==== 

- : unit = ()
# - : ('a,
     Instances.V3R.n Tuple.Record3D.t ->
     Instances.V3R.n Tuple.Record3D.t -> Instances.V3R.n)
    code
=
.<fun a_30 ->
   fun b_31 ->
    (sqrt
      let v_32 =
       {x = (a_30.x -. b_31.x); y = (a_30.y -. b_31.y);
        z = (a_30.z -. b_31.z)} in
      (((v_32.x *. v_32.x) +. (v_32.y *. v_32.y)) +. (v_32.z *. v_32.z)))>.
#   

 ==== VectorStaged Record2D unit_vec () ==== 

- : unit = ()
# - : ('a,
     Instances.V2R.n Tuple.Record2D.t ->
     Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n Tuple.Record2D.t)
    code
=
.<fun a_33 ->
   fun b_34 ->
    let v_37 = {c0 = (a_33.c0 -. b_34.c0); c1 = (a_33.c1 -. b_34.c1)} in
    let v_38 = (sqrt ((v_37.c0 *. v_37.c0) +. (v_37.c1 *. v_37.c1))) in
    {c0 = (v_37.c0 /. v_38); c1 = (v_37.c1 /. v_38)}>.
# 

 ==== VectorStaged Pair2D unit_vec () ==== 

- : unit = ()
# - : ('a,
     Instances.V2P.n Tuple.Pair2D.t ->
     Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n Tuple.Pair2D.t)
    code
=
.<fun a_39 ->
   fun b_40 ->
    let v_55 =
     let (x_41, y_42) = a_39 in
     let (x_43, y_44) = b_40 in ((x_41 -. x_43), (y_42 -. y_44)) in
    let v_60 =
     (sqrt let (x_56, y_57) = v_55 in ((x_56 *. x_56) +. (y_57 *. y_57))) in
    let (x_61, y_62) = v_55 in ((x_61 /. v_60), (y_62 /. v_60))>.
# 

 ==== VectorStaged Record3D univ_vec () ==== 

- : unit = ()
# - : ('a,
     Instances.V3R.n Tuple.Record3D.t ->
     Instances.V3R.n Tuple.Record3D.t -> Instances.V3R.n Tuple.Record3D.t)
    code
=
.<fun a_63 ->
   fun b_64 ->
    let v_67 =
     {x = (a_63.x -. b_64.x); y = (a_63.y -. b_64.y); z = (a_63.z -. b_64.z)} in
    let v_68 =
     (sqrt
       (((v_67.x *. v_67.x) +. (v_67.y *. v_67.y)) +. (v_67.z *. v_67.z))) in
    {x = (v_67.x /. v_68); y = (v_67.y /. v_68); z = (v_67.z /. v_68)}>.
#   

 ==== VectorStaged Record2D dot () ==== 

- : unit = ()
# - : ('a,
     Instances.V2R.n Tuple.Record2D.t ->
     Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n)
    code
= .<fun a_69 -> fun b_70 -> ((a_69.c0 *. b_70.c0) +. (a_69.c1 *. b_70.c1))>.
# 

 ==== VectorStaged Pair2D dot () ==== 

- : unit = ()
# - : ('a,
     Instances.V2P.n Tuple.Pair2D.t ->
     Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n)
    code
=
.<fun a_71 ->
   fun b_72 ->
    let (x_73, y_74) = a_71 in
    let (x_75, y_76) = b_72 in ((x_73 *. x_75) +. (y_74 *. y_76))>.
# 

 ==== VectorStaged Record3D dot () ==== 

- : unit = ()
# - : ('a,
     Instances.V3R.n Tuple.Record3D.t ->
     Instances.V3R.n Tuple.Record3D.t -> Instances.V3R.n)
    code
=
.<fun a_77 ->
   fun b_78 ->
    (((a_77.x *. b_78.x) +. (a_77.y *. b_78.y)) +. (a_77.z *. b_78.z))>.
#   
