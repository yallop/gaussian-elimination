open Staged
open Algebra
open Vector
open Point
open Matrix

(* T(p) = Mp + t
   T(v) = Mt      *)
module type AFFINE = sig
  type n
  type ('a,'b) trep
  type 'a point = ('a, n) trep
  type ('a,'b) vector = ('a,'b) trep
  type ('a,'b) t
  val apply_p : ('a,'b) t -> 'a point -> 'a point
  val apply_v : ('a,n) t -> ('a,n) vector -> ('a,n) vector
  val compose : ('a,'b) t -> ('a,'b) t -> ('a,'b) t
  (* Some affine transforms *)
  val id : int -> ('a,'b) t
  val translation : ('a,n) vector -> ('a,n) t
  (* val rotation : 'a M.n_s -> t *)
  (* val mirror : point -> point -> t *)
end

module AffineTransformations (E : EUCLIDEAN) (* : AFFINE *) = struct
  module M = Matrix (E.N)
  type n = E.N.n
  type ('a,'b) trep = ('a,'b) E.P.trep
  type 'a point = 'a E.P.point 
  type ('a,'b) vector = ('a,'b) trep
  type ('a,'b) t = ('a, 'b) M.m
  (* Apply m: transform matrix; (n+1) square
           obj: object matrix; n by 1 *)
  let apply m obj = M.mul m (M.vaugment obj (M.id 1))
  (* Compose depends on the way you apply. So, if:
     apply m p = m * p, then: (a o b) p = b * a,
     such that: apply (a o b) p = b * a * p
   *)
  let compose m1 m2 = M.mul m2 m1
  (* utils from/to matrix <-> point, vector *)
  let p_to_matrix p =
    M.create_col E.P.dim (fun i -> (E.P.to_array p).(i))
  let v_to_array v =
    Array.init E.V.dim (E.V.coord v)
  let v_to_matrix v =
    M.create_col E.V.dim (fun i -> (v_to_array v).(i))
  let p_of_matrix m =
    let arr = Array.init ((M.nrows m)-1) (fun i -> M.get m i 0) in
    E.P.of_array arr
  let v_of_matrix m =
    let arr = Array.init ((M.nrows m)-1) (fun i -> M.get m i 0) in
    E.V.of_coords (Array.to_list arr)
  let apply_p t p = p_of_matrix (apply t (p_to_matrix p))
  let apply_v t v = v_of_matrix (apply t (v_to_matrix v))
  (* row_mat: util *)
  let row_mat arr =
    M.create (Array.length arr) 1 (fun i _ -> arr.(i))
  let col_mat arr = M.transpose (row_mat arr)
  (* Linear fraction transformation matrix =
     lftm a b c d = [ a | b ]
                    [ --|-- ]
                    [ c | d ] *)
  let lftm a b c d =
    M.vaugment (M.haugment a b) (M.haugment c d)
  (* Affine matrix *)
  let affine a b =
    let c = M.zero 1 (M.ncols a) and d = M.id 1 in
    lftm a b c d
  (* http://www.eng.mu.edu/corlissg/151.08Sp/ch05.html *)
  let id n = affine (M.id n) (M.zero n 1)
  let translation v = affine (M.id E.V.dim) (v_to_matrix v)
end

(* 
Affine tranformation matrix (ATM)
ATM = diagonal n+1 matrix of ones

A: (n+1) by (n+1)
a: n by n
b: n by 1
x: n by 1

     [    a    | b  ] [ x ]
A =  [ ------------ ] [---]
     [ 0 ... 0 | 1  ] [ 1 ]

Affine tranformation matrix (ATM)
ATM = diagonal n+1 matrix of ones

A: (n+1) by (n+1)
a: n by n
b: n by 1
x: n by 1

     [    a    | b  ] [ x ]
A =  [ ------------ ] [---]
     [ 0 ... 0 | 1  ] [ 1 ]



[| m |]


A = diagonal n+1 matrix of ones
A[i = 0..n-2][n] <- coord v_i
X = column n+1 matrix
A[i = 0..n-1] <- 

    Affine.
    let m = [| [|  |] |]
    T.of_list (List.map2 N.add (E.V.to_list v) (to_list p))

*)
