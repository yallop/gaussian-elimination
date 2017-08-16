open Staged
open Point

(* d-simplex has (d+1)-vertices *)
module type SIMPLEX = sig
  module E : EUCLIDEAN
  type 'a simplex
  val dim : 'a simplex -> int
  val of_vertices : 'a E.P.point list -> 'a simplex
  (* isomorphism modulo order of vertices *)
  val seq : 'a simplex -> 'a simplex -> ('a,bool) E.N.rep
  (* vertices *)
  val vertices : 'a simplex -> 'a E.P.point list
  val is_vertex : 'a simplex -> 'a E.P.point -> ('a,bool) E.N.rep
  (* faces *)
  (* non-oriented face: nD *)
  val face : 'a simplex -> int -> 'a simplex
  (* Oriented face: 2D  & 3D only. Such that for a vertex v_i
     and opposite face f_i: orient f_i v_i = +ve *)
  val faces : 'a simplex -> 'a simplex list
  val ofaces : 'a simplex -> 'a simplex list

  (* inside check *)
  val in_ : 'a simplex -> 'a E.P.point -> ('a,bool) E.N.rep
  val out : 'a simplex -> 'a E.P.point -> ('a,bool) E.N.rep
  val on : 'a simplex -> 'a E.P.point -> ('a,bool) E.N.rep
  val in_or_on : 'a simplex -> 'a E.P.point -> ('a,bool) E.N.rep
end

(* util:  [| 0 .. n-1 |] *)
let array_0n n = Array.init n (fun i -> i)

(* util: [ f 0 ; .. ; f (n-1) ] *)
let list_0n n f = Array.to_list (Array.init n f)

module N_Simplex (E : EUCLIDEAN) (* : SIMPLEX *) = struct
  module S = E.N

  module H = Hplane.N_plane(S)(E)

  module N = Algebra.GenSet(S)
  module F = Algebra.GenListRing(S)(S)

  type 'a simplex = 'a E.P.point list
  let dim s = (List.length s)-1
  let of_vertices l = l

  let vertex s i = List.nth s i
  let vertices s = s
  let is_vertex s v = N.exists (E.P.eq v) s

  (* isomorphism *)
  let seq a b =
    if (dim a) <> (dim b) then S.false_
    else
      (* |ver(b)| = |ver(a)| && v(b) \subset v(a) *)
      let l = List.map (is_vertex a) b in
      List.fold_left (S.and_) S.true_ l

  let oface_desc s =
    let d = dim s in
    let normal i j = if i<j then i else i+1 in (* normal case already in clockwise order *)
    Array.init (d + 1) (fun j ->
        Array.init d (fun i ->
            if (d+j) mod 2 = 1 then (* need to switch first two entries to make clockwise order *)
                (if i = 0 then normal 1 j
                else if i = 1 then normal 0 j
                else normal i j)
            else
                normal i j) ) 
(*    if d = 2 then
      [| [| 1; 2 |]; [| 2; 0 |]; [| 0; 1 |] |] 
    else if d = 3 then
      [| [| 2; 1; 3 |]; [| 0; 2; 3 |];
         [| 1; 0; 3 |]; [| 0; 1; 2 |] |]
    else failwith "dimensions higher than 3 are not implemented"
*)

(* 
the vertex numbering for the faces of an oriented affine simplex
are explained in "The Geometrical Language of Continuum Mechanics," by
Marcelo Epstein, page 71, see: http://books.google.ca/books?id=u3Gyjc1ufDoC
*) 

  let face_desc s i =
   (* simplex discriptor matrix
       m : n by n-1 matrix;
       n faces & n-1 vertices per face *)
    let n = dim s in
    Array.init (n + 1) (fun j ->
        Array.init n (fun i -> if i<j then i else i+1 ))

  let _face s m i =
    (* extract i^th face and get the vertices for that face *)
    let f = Array.map (vertex s) m.(i) in
    (* the face is also a simplex *)
    of_vertices (Array.to_list f)

  (* oriented face: 2D  & 3D only *)
  let oface s i = _face s (oface_desc s) i
  (* non-oriented face: nD *)
  let face s i = _face s (face_desc s i) i

  let faces s = list_0n ((dim s)+1) (face s)
  let ofaces s = list_0n ((dim s)+1) (oface s)

  let hyperplanes s =
    (* get all the faces *)
    let fs = ofaces s in
    (* build a hyperplane out of points of every face *)
    let hplane_of_face f =
      H.of_points (vertices f) in
    List.map hplane_of_face fs

  let in_ s p =
    let hs = hyperplanes s in
    let o_ccw = List.map (fun h -> H.orient h p Sign.Pos) hs in
    N.for_all (fun b -> b) o_ccw

  let out s p =
    let hs = hyperplanes s in
    let o_cw = List.map (fun h -> H.orient h p Sign.Neg) hs in
    N.exists (fun b -> b) o_cw

  let on s p =
    let hs = hyperplanes s in
    let o_ccw_or_col = List.map (fun h -> H.orient h p Sign.PosOrZero) hs
    and o_col = List.map (fun h -> H.orient h p Sign.Zero) hs in
    let c0 = N.for_all (fun b -> b) o_ccw_or_col in
    let i = F.findi (fun b -> b) o_col in
    let c1 = S.not_ (S.eq i (S.of_int (List.length o_col))) in
    (S.and_ c0 c1), i

  let in_or_on s p = S.not_ (out s p)
end
