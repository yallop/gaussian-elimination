
- : unit = ()
# 

 ==== VECTOR TEST ==== 

- : unit = ()
#     

 ==== VectorStaged Tuple1D length () ==== 

- : unit = ()
# - : ('a, Instances.V1.n Tuple.Tuple1D.t -> Instances.V1.n) code =
.<fun a_1 -> (sqrt (a_1 *. a_1))>.
# 

 ==== VectorStaged Record2D length () ==== 

- : unit = ()
# - : ('a, Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n) code =
.<fun a_2 -> (sqrt ((a_2.c0 *. a_2.c0) +. (a_2.c1 *. a_2.c1)))>.
# 

 ==== VectorStaged Pair2D length () ==== 

- : unit = ()
# - : ('a, Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n) code =
.<fun a_3 -> (sqrt (((fst a_3) *. (fst a_3)) +. ((snd a_3) *. (snd a_3))))>.
# 

 ==== VectorStaged Record3D length () ==== 

- : unit = ()
# - : ('a, Instances.V3R.n Tuple.Record3D.t -> Instances.V3R.n) code =
.<fun a_4 ->
   (sqrt (((a_4.x *. a_4.x) +. (a_4.y *. a_4.y)) +. (a_4.z *. a_4.z)))>.
#   

 ==== VectorStaged Tuple1D sub () ==== 

- : unit = ()
# - : ('a,
     Instances.V1.n Tuple.Tuple1D.t ->
     Instances.V1.n Tuple.Tuple1D.t -> Instances.V1.n Tuple.Tuple1D.t)
    code
= .<fun a_5 -> fun b_6 -> (a_5 -. b_6)>.
# 

 ==== VectorStaged Record2D sub () ==== 

- : unit = ()
# - : ('a,
     Instances.V2R.n Tuple.Record2D.t ->
     Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n Tuple.Record2D.t)
    code
=
.<fun a_7 -> fun b_8 -> {c0 = (a_7.c0 -. b_8.c0); c1 = (a_7.c1 -. b_8.c1)}>.
# 

 ==== VectorStaged Pair2D sub () ==== 

- : unit = ()
# - : ('a,
     Instances.V2P.n Tuple.Pair2D.t ->
     Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n Tuple.Pair2D.t)
    code
=
.<fun a_9 ->
   fun b_10 ->
    let (x_11, y_12) = a_9 in
    let (x_13, y_14) = b_10 in ((x_11 -. x_13), (y_12 -. y_14))>.
# 

 ==== VectorStaged Record3D sub () ==== 

- : unit = ()
# - : ('a,
     Instances.V3R.n Tuple.Record3D.t ->
     Instances.V3R.n Tuple.Record3D.t -> Instances.V3R.n Tuple.Record3D.t)
    code
=
.<fun a_15 ->
   fun b_16 ->
    {x = (a_15.x -. b_16.x); y = (a_15.y -. b_16.y); z = (a_15.z -. b_16.z)}>.
#   

 ==== VectorStaged Tuple1D dist () ==== 

- : unit = ()
# - : ('a,
     Instances.V1.n Tuple.Tuple1D.t ->
     Instances.V1.n Tuple.Tuple1D.t -> Instances.V1.n)
    code
=
.<fun a_17 -> fun b_18 -> (sqrt let v_19 = (a_17 -. b_18) in (v_19 *. v_19))>.
# 

 ==== VectorStaged Record2D dist () ==== 

- : unit = ()
# - : ('a,
     Instances.V2R.n Tuple.Record2D.t ->
     Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n)
    code
=
.<fun a_20 ->
   fun b_21 ->
    (sqrt
      let v_22 = {c0 = (a_20.c0 -. b_21.c0); c1 = (a_20.c1 -. b_21.c1)} in
      ((v_22.c0 *. v_22.c0) +. (v_22.c1 *. v_22.c1)))>.
# 

 ==== VectorStaged Pair2D dist () ==== 

- : unit = ()
# - : ('a,
     Instances.V2P.n Tuple.Pair2D.t ->
     Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n)
    code
=
.<fun a_23 ->
   fun b_24 ->
    (sqrt
      let v_29 =
       let (x_25, y_26) = a_23 in
       let (x_27, y_28) = b_24 in ((x_25 -. x_27), (y_26 -. y_28)) in
      (((fst v_29) *. (fst v_29)) +. ((snd v_29) *. (snd v_29))))>.
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

 ==== VectorStaged Tuple1D unit_vec () ==== 

- : unit = ()
# - : ('a,
     Instances.V1.n Tuple.Tuple1D.t ->
     Instances.V1.n Tuple.Tuple1D.t -> Instances.V1.n Tuple.Tuple1D.t)
    code
=
.<fun a_33 ->
   fun b_34 ->
    let v_37 = (a_33 -. b_34) in
    let v_38 = (sqrt (v_37 *. v_37)) in (v_37 /. v_38)>.
# 

 ==== VectorStaged Record2D unit_vec () ==== 

- : unit = ()
# - : ('a,
     Instances.V2R.n Tuple.Record2D.t ->
     Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n Tuple.Record2D.t)
    code
=
.<fun a_39 ->
   fun b_40 ->
    let v_43 = {c0 = (a_39.c0 -. b_40.c0); c1 = (a_39.c1 -. b_40.c1)} in
    let v_44 = (sqrt ((v_43.c0 *. v_43.c0) +. (v_43.c1 *. v_43.c1))) in
    {c0 = (v_43.c0 /. v_44); c1 = (v_43.c1 /. v_44)}>.
# 

 ==== VectorStaged Pair2D unit_vec () ==== 

- : unit = ()
# - : ('a,
     Instances.V2P.n Tuple.Pair2D.t ->
     Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n Tuple.Pair2D.t)
    code
=
.<fun a_45 ->
   fun b_46 ->
    let v_57 =
     let (x_47, y_48) = a_45 in
     let (x_49, y_50) = b_46 in ((x_47 -. x_49), (y_48 -. y_50)) in
    let v_60 =
     (sqrt (((fst v_57) *. (fst v_57)) +. ((snd v_57) *. (snd v_57)))) in
    let (x_61, y_62) = v_57 in ((x_61 /. v_60), (y_62 /. v_60))>.
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

 ==== VectorStaged Tuple1D dot () ==== 

- : unit = ()
# - : ('a,
     Instances.V1.n Tuple.Tuple1D.t ->
     Instances.V1.n Tuple.Tuple1D.t -> Instances.V1.n)
    code
= .<fun a_69 -> fun b_70 -> (a_69 *. b_70)>.
# 

 ==== VectorStaged Record2D dot () ==== 

- : unit = ()
# - : ('a,
     Instances.V2R.n Tuple.Record2D.t ->
     Instances.V2R.n Tuple.Record2D.t -> Instances.V2R.n)
    code
= .<fun a_71 -> fun b_72 -> ((a_71.c0 *. b_72.c0) +. (a_71.c1 *. b_72.c1))>.
# 

 ==== VectorStaged Pair2D dot () ==== 

- : unit = ()
# - : ('a,
     Instances.V2P.n Tuple.Pair2D.t ->
     Instances.V2P.n Tuple.Pair2D.t -> Instances.V2P.n)
    code
=
.<fun a_73 ->
   fun b_74 -> (((fst a_73) *. (fst b_74)) +. ((snd a_73) *. (snd b_74)))>.
# 

 ==== VectorStaged Record3D dot () ==== 

- : unit = ()
# - : ('a,
     Instances.V3R.n Tuple.Record3D.t ->
     Instances.V3R.n Tuple.Record3D.t -> Instances.V3R.n)
    code
=
.<fun a_75 ->
   fun b_76 ->
    (((a_75.x *. b_76.x) +. (a_75.y *. b_76.y)) +. (a_75.z *. b_76.z))>.
#   
