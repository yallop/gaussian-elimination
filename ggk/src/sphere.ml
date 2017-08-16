module type HSPHERE = sig
  include Repr.REP
  type 'a point
  type 'a sphere
  val dim : 'a sphere -> int
  val radius : 'a sphere -> ('a,'b) rep
  (* nD content (volume):
     1, length, area, volume, hypervolume for
     point, line, circle, sphere, hypersphere respectively *)
  val content : 'a sphere -> ('a,'b) rep
  (* (n-1)D content (surface area):
     0, 2, circumference, surface area, hyper-
     surface area for point, line, circle, sphere, hypersphere
     respectively *)
  val surface : 'a sphere -> ('a,'b) rep

  val inside : 'a sphere -> 'a point -> ('a,bool) rep
end

(* Sphere is a generation time concept *)

(* CR = centre-radius *)
module CRSphere (E : Point.EUCLIDEAN) = struct
  type 'a rep = ('a,E.N.n) E.N.rep
  type 'a point = 'a E.P.point
  type 'a sphere = {center:'a point; radius:'a rep; dim:int}
  let of_centre_radius c r =  {center = c; radius = r; dim = E.P.dim }

  (* util *)
  let even n = (n mod 2) = 0
  let rec pow2 = function 0 -> 1 | n -> 2 * pow2 (n-1)
  let rec fact = function 0 -> 1 | n -> n * fact (n - 1)
  let rec dfact = function 1 -> 1 | n -> n * dfact (n - 2)
  let pi = E.N.pi
  (* returns (a, b, c) where C_n = (2^a * pi^b / c) *) 
  let c_n n =
    let (a, b, c) =
      if (even n) then let nh = n/2 in (0, nh, fact (nh))
      else ((n+1)/2, (n-1)/2, dfact (n)) in
    let a = E.N.of_int (pow2 a)
    and c = E.N.of_int c in
    E.N.div (E.N.mul a (E.N.int_pow b pi)) c
  (* V_n = C_n r^n *)
  let v_n n r = E.N.mul (c_n n) (E.N.int_pow n r)
  (* S_n = n C_n r^n-1 *)
  let s_n n r =
    E.N.mul (E.N.of_int n) (E.N.mul (c_n n) (E.N.int_pow (n-1) r))

  let dim s = s.dim
  let radius c = c.radius
  let content c = v_n (dim c) (radius c) (* hyper-volume of the sphere *)
  let surface c = s_n (dim c) (radius c) (* hyper-surface area of the sphere *)

  let inside c p = 
    E.N.lt (E.V.length2 (E.sub p (c.center))) 
           (E.N.let_ c.radius (fun x -> E.N.mul x x))
end


(*
  insphere p_0 p_1 .. p_n-1 p:
    1. let h = hplane L(p_0) L(p_1) .. L(p_n-1)
               where L = parabolic lifting
    2. make sure oriented p_0 p_1 ... p_n-1 is pos
       otherwise swap p_0 and p_1
    3. get s = orient h p
    4. interpret s as:
        +ve -> in, -ve -> out, 0 -> on
       [basically +ve = below the lifted hplane = inside
                  -ve = above ... = outside ]

  usage: arrange a b c d such that: abc are cw and d is above, or
         abc are ccw and d is below.
*)

(* This will go in to the implementation for the n-points 
   representation of a sphere
  module M = Matrix.Matrix (S.N)
  (* (c0, c1, c2, .. , cn) ->
     (c0, .. , cn, c0^2 + .. + cn^2) *)
  let parab p = 
    let v = (S.P.pos_vec p) in
    S.P.V.dot v v

  let matrix ps =
    let p_row p = Array.of_list (
      (S.P.to_list p) @ [parab p] @ [Now S.N.one]) in
    let a = Array.of_list ps in
    let arr = Array.map p_row a in
    M.of_array arr  

  let inside_val s p =
    let ps = (S.points s) @ [p] in
    let m = matrix ps in
    M.det m

  let inside s p =
    let d = (inside_val s p) in
    S.N.sgn d

  (* point is inside, if it's below to hyperplan *)
  let in_ s p = (inside s p) Sign.Pos
  let on s p = (inside s p) Sign.Zero
  let out s p = (inside s p) Sign.Neg
  let in_or_on s p = (inside s p) Sign.PosOrZero
  let out_or_on s p = (inside s p) Sign.NegOrZero
*)

(* http://mathforum.org/library/drmath/view/55239.html

circle with radius r, centre (a, b)
(x-a)^2 + (x-b)^2 = r^2

circle passing through (x1, y1) (x2, y2) (x3, y3)

    [ x1^2+y1^2 y1 1 ]
A = [ x2^2+y2^2 y2 1 ]
    [ x3^2+y3^2 y3 1 ]

    [ x1 x1^2+y1^2 1 ]
B = [ x2 x2^2+y2^2 1 ]
    [ x3 x3^2+y3^2 1 ]

    [ x1  y1  1 ]
D = [ x2  y2  1 ]
    [ x3  y3  1 ]

center   = (det(A)/2*det(D), det(B)/2*det(D))
radius^2 = (x1-xc)^2 + (y1-yc)^2
*)


(*
http://local.wasp.uwa.edu.au/~pbourke/geometry/spherefrom4/

Sphere passing through 4 points
(x1,y1,z1) (x2,y2,z2) (x3,y3,z3) (x4,y4,z4)
with centre (xc,yc,zc)
Equation: (x-xc)^2 + (y-yc)^2 + (z-zc)^2 = r^2

M = [ -              -  -  -  - ] <- don't care
    [ x1^2+y1^2+z1^2 x1 y1 z1 1 ]    because it's
    [ x2^2+y2^2+z2^2 x2 y2 z2 1 ]    symbolic. use 0's
    [ x3^2+y3^2+z3^2 x3 y3 z3 1 ]
    [ x4^2+y4^2+z4^2 x4 y4 z4 1 ]

xc = .5 M12 / M11
yc = - .5 M13 / M11
zc = .5 M14 / M11
r^2 = xc^2 + yc^2 + zc^2 - M15 / M11
*)
