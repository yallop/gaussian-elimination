(*
  Hyperplane implementation

  The orientation definition is taken from:
  Adaptive Precision Floating-Point Arithmetic and Fast Robust
  Geometric Predicates, J. R. Shewchuck, Discrete & Computational
  Geometry 18(3):305-363, October 1997.
  http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.71.8830
  
 @ARTICLE{Shewchuk97adaptiveprecision,
    author = {Jonathan Richard Shewchuk},
    title = {Adaptive precision floating-point arithmetic and fast robust geometric predicates},
    journal = {Discrete & Computational Geometry},
    year = {1997},
    volume = {18},
    pages = {305--363}}
*)

(* +ve -> left;  -ve -> right (1D)
   +ve -> ccw;  -ve -> cw (2D)
   +ve -> below; -ve -> above (3D) *)

open Point

(* type ('p, 'v) frame = { orig : 'p; basis : 'v list }
let create_frame o b = { orig = o; basis = b } *)

(* k-hyperplane in n-dimensions has (k+1) points
   k = 0, 1, 2, 3+ for point, line, plane, hyperplane *)

module type HYPER_PLANE = sig
  include Repr.REP
  type n
  type ('a,'b) trep
  type ('a,'b) ts
  val dim : ('a,n) ts -> int
  (* construction *)
  val of_points : ('a,n) trep list -> ('a,n) ts
  (* implicit equation : \sum (a_i x_i) + d *)
  val poly : ('a,n) ts -> ('a,n) rep array
  (* vector equation : p.n + d = 0 *)
  val normal : ('a,n) ts -> ('a,n) trep
  val d : ('a,n) ts -> ('a,n) rep
  (* frame *)
  val orig : ('a,n) ts -> ('a,n) trep
  val basis : ('a,n) ts -> int -> ('a,n) trep
  val bases : ('a,n) ts -> ('a,n) trep list
  (* val frame : ('a,n) ts -> (('a,n) trep, ('a,n) trep) frame *)
  (* local coordinates of a point 'on' the hyperplane *)
  val coord : ('a,n) ts -> ('a,n) trep -> ('a,n) trep
  val pos_vec : ('a,n) ts -> ('a,n) trep -> ('a,n) trep
  (* orientation *)
  val orient : ('a,n) ts -> ('a,n) trep -> Sign.t -> ('a,bool) rep
  (* dist *)
  val dist : ('a,n) ts -> ('a,n) trep-> ('a,n) rep
  val project : ('a,n) ts -> ('a,n) trep -> ('a,n) trep
end

(* Line is 2D hyperplane *)
module Line (C : Repr.REP) 
            (E : EUCLIDEAN with type ('a,'b) N.rep = ('a,'b) C.rep) 
    (* : HYPER_PLANE *) =
struct
  include Repr.GenRep(C)
  type n = E.P.n
  type ('a,'b) trep = ('a,'b) E.P.trep
  type ('a,'b) ts = ('a,'b) trep * ('a,'b) trep
  let dim _ = 1
  let of_points = function
   | [z1;z2] -> (z1,z2)
   | _       -> failwith "2D hyperplane must be given by exactly 2 points"
  let points = fun (a, b) -> [a; b]
  let point l i = List.nth (points l) i
  (* Frame *)
  let orig (p0, p1) = p0
  (* one basis vector *)
  (* r0, r1: position vector of p0, p1 *)
  (* d = normalized  (p1 - p0) *)
  let basis (p0,p1) i =
    E.V.direction (E.V.sub (E.pos_vec p1) (E.pos_vec p0))
  let bases h = [basis h 0]
  (* let frame h = create_frame (orig h) (bases h) *)
  (* normal vector (normalized) *)
  let normal h =
    E.V.letvv (basis h 0) (fun b ->
     let x,y = (E.V.coord b 0), (E.V.coord b 1) in
     E.V.letvv (E.V.of_coords [(E.N.neg y); x]) E.V.direction)
  (* d = -n.p0 *)
  let d h = 
    let p0 = orig h and n = normal h in
    E.V.letvn n (fun n -> E.N.neg (E.V.dot (E.pos_vec p0) n))
  (* polynomial ax + by + c = 0
     (a, b) = n, c = -p0.n *)
  let v_to_list v = Array.to_list (Array.init E.V.dim (E.V.coord v))
  let poly h = Array.of_list ((v_to_list (normal h)) @ [(d h)])
  (* Local coord of p in the line *)
  let coord h p =
    (* find t = d . (p - orig) *)
    let d = basis h 0
    and v = E.V.sub (E.pos_vec p) (E.pos_vec (orig h)) in
    let t = (E.V.dot d v) in
    (* 1D point relative the frame *)
    E.P.of_list [t]
  (* local position vector of p *)
  let pos_vec h p = E.pos_vec (coord h p)

  (* pull this in -- orientation *)
  let orient_val (p1,p2) p =
    let module M = Matrix.Matrix(E.N) in
    let m = M.create 3 3
      (fun i j ->
          if j == 2 then E.N.one
          else if i == 2 then List.nth (E.P.to_list p) j
          else if i == 1 then List.nth (E.P.to_list p2) j
          else                List.nth (E.P.to_list p1) j ) in
    M.det m

  let orient h p = E.N.sgn (orient_val h p)

  (* @TODO The expression p-p0 is computed inside 'normal' but this
	   caller has no clue. Hence the code repetition is inevitable
           in this case. *)
  let project h p =
    E.lett (normal h) (fun n ->
      let p0 = orig h in
      let v = E.sub p p0 in
      let t = E.N.neg (E.V.dot n v) in
      let dis = E.V.scale n t in
      E.add p dis)

  let dist h p = E.V.dot (normal h) (E.sub p (orig h))
end

(* n-D plane *)
module N_plane (C : Repr.REP) 
               (E : EUCLIDEAN with type ('a,'b) N.rep = ('a,'b) C.rep) 
    (* : HYPER_PLANE *) = struct
  include Repr.GenRep(C)
  type n = E.P.n
  type ('a,'b) trep = ('a,'b) E.P.trep
  type 'a point = 'a E.P.point
  type ('a,'b) ts = ('a,'b) trep list
  (* k-hyperplane has k+1 points *)
  let dim h = (List.length h)-1
  let of_points l = l
  let point h i = List.nth h i
  let points h = h

  (* frame *)
  let orig h = point h 0
  (* normalized bases
     p1-p0, p2-p0, p3-p0, ... *)
  let basis h i =
    if (dim h) = 0 then E.V.zero () else
    let p = point h (i+1) and o = orig h in
    E.V.direction (E.sub p o)
  let bases h =
    if (dim h) = 0 then [basis h 0] else
    Array.to_list (Array.init (dim h) (basis h))
  (* let frame h = create_frame (orig h) (bases h) *)

  (* normal vector (normalized) *)
  (* @TODO this is only valid for 1,2,3D;
     since gcross is not implemented yet *)
  let normal h =
    if (dim h) = 0 then E.V.of_coords [E.N.one]
    else if (dim h) = 1 then
      E.V.letvv (basis h 0) (fun b ->
	E.V.of_coords [E.N.neg (E.V.coord b 1); (E.V.coord b 0)])
    else E.V.direction (E.V.gcross [basis h 0; basis h 1])
  (* d = -n.p0 *)
  let d h = 
    let p0 = orig h and n = normal h in
    E.N.neg (E.V.dot (E.pos_vec p0) n)
  (* polynomial a0x0 + a1x1 + ... + d = 0
     (a0, a1, ...) = n, d = -p0.n *)
  let v_to_list v = Array.to_list (Array.init E.V.dim (E.V.coord v))
  let poly h = Array.of_list ((v_to_list (normal h)) @ [d h])
  (* baricentric coord of p *)
  (* @TODO this is a 3D only version *)
  let coord h p =
    let u = basis h 0
    and v = basis h 1
    and w = E.sub p (orig h) in
    (* denom = (u.v)^2 - (u.u)(v.v) = (u.v)^2 - 1
       because all basis normalized? *)
    let den = E.N.sub (E.N.int_pow 2 (E.V.dot u v))
	              (E.N.mul (E.V.dot u u) (E.V.dot v v))
    in
    let s = E.N.sub (E.N.mul (E.V.dot u v) (E.V.dot w v))
	            (E.N.mul (E.V.dot v v) (E.V.dot w u))
    and t = E.N.sub (E.N.mul (E.V.dot u v) (E.V.dot w u))
	            (E.N.mul (E.V.dot u u) (E.V.dot w v))
    in
    let s = E.N.div s den
    and t = E.N.div t den in
    let b0 = E.N.sub (E.N.sub E.N.one s) t
    and b1 = s and b2 = t in
    E.P.of_list [b0; b1; b2]
  (* local position vector of p *)
  let pos_vec h p = E.pos_vec (coord h p)

  (* dist (h,p) =  n.p + d = n.p - n.p0 = n (p-p0) *)
  let dist h p = E.V.dot (normal h) (E.sub p (orig h))
(*    C.let_ (normal h) (fun n ->
      E.N.sub (E.V.dot n (E.pos_vec p))
                (E.V.dot n (E.pos_vec (orig h)))) *)
  (* p' = p - d(p,h).n *)
  (* @TODO The expression p-p0 is computed inside 'normal' but this
	   caller has no clue. Hence the code repetition is inevitable
           in this case. *)
  let project h p =
    E.lett (normal h) (fun n ->
      let p0 = orig h in
      let v = E.sub p p0 in
      let t = E.N.neg (E.V.dot n v) in
      let dis = E.V.scale n t in
      E.add p dis)

  (* pull this in -- orientation *)
  let orient_val h p =
    let module M = Matrix.Matrix(E.N) in
    let d = dim h + 1 in
    let d1 = d+1 in
    let m = M.create d1 d1
      (fun i j ->
          if j == d then E.N.one
          else if i == d then List.nth (E.P.to_list p) j
          else List.nth (E.P.to_list (point h i)) j) in
    M.det m

  let orient h p = E.N.sgn (orient_val h p)
end
