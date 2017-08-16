(* @TODO separate the matrix container from the matrix operations
 *       so the container can change for sparse, dense, etc. *)

module type MATRIX = sig
  type ('a,'b) rep
  type ('a,'b) m
  val nrows : ('a,'b) m -> int
  val ncols : ('a,'b) m -> int
  val dim : ('a,'b) m -> int * int
  val get : ('a,'b) m -> int -> int -> ('a,'b) rep
  val row : ('a,'b) m -> int -> ('a,'b) m 
  val col : ('a,'b) m -> int -> ('a,'b) m 
  val create : int -> int -> (int -> int -> ('a,'b) rep) -> ('a,'b) m 
  (* special matrices *)
  val zero : int -> int -> ('a,'b) m 
  val diag : int -> (int -> ('a,'b) rep) -> ('a,'b) m 
  val id : int -> ('a,'b) m 
  (* transformations *)
  val transpose : ('a,'b) m -> ('a,'b) m 
  val haugment : ('a,'b) m -> ('a,'b) m -> ('a,'b) m 
  val vaugment : ('a,'b) m -> ('a,'b) m -> ('a,'b) m 
  (* algebra *)
  val add : ('a,'b) m -> ('a,'b) m -> ('a,'b) m 
  val sub : ('a,'b) m -> ('a,'b) m -> ('a,'b) m 
  val mul : ('a,'b) m -> ('a,'b) m -> ('a,'b) m 
  (* higher level operations *)
  val det : ('a,'b) m -> ('a,'b) rep
end

(* Implementation *)

type 'c triple_type = { a: int; b: int; c: 'c }
let triple_create a b c = { a = a; b = b; c = c }
let triple_fst t = t.a
let triple_snd t = t.b
let triple_thr t = t.c

(* Dangerously dynamic *)
module Matrix (N : Algebra.RING) (* : MATRIX *) = struct
  type ('a,'b) rep = ('a,N.n) N.rep
  type ('a,'b) mrep = ('a,'b) rep array array
  (* 0: row, 1: col, 2: matrix *)
  type ('a,'b) m = ('a,'b) mrep triple_type
  (* _matrix, _row, _col: utils *)
  let _matrix m = triple_thr m
  let _row m i = (_matrix m).(i)
  let _col m i = Array.map (fun r -> r.(i)) (_matrix m)
  let nrows m = triple_fst m
  let ncols m = triple_snd m
  let dim m = (nrows m), (ncols m)
  let same_dim a b =
    ((nrows a) = (nrows b)) &&
    ((ncols a) = (ncols b))
  let create r c f =
    triple_create r c (Array.init r (fun i ->
      Array.init c (fun j -> f i j)))
  let create_row c f = create 1 c (fun _ j -> f j)
  let create_col r f = create r 1 (fun i _ -> f i)
  let get m i j = (_matrix m).(i).(j)
  let row m i = create_row (ncols m) (fun j -> (_row m i).(j))
  let col m j = create_col (nrows m) (fun i -> (_col m j).(i))
  let zero r c = create r c (fun _ _ -> N.zero)
  let diag n f = create n n (fun i j ->
      if i = j then f i else N.zero)
  let id n = diag n (fun _ -> N.one)
  let transpose m =
    create (ncols m) (nrows m) (fun i j -> get m j i)
  (* a | b *)
  let haugment a b =
    let ra, ca = nrows a, ncols a
    and rb, cb = nrows b, ncols b in
    assert (ra = rb);
    let aug = Array.mapi (fun i x ->
      Array.append x (_row b i)) (_matrix a) in
    triple_create ra (ca + cb) aug
  (*  a
   * --- = a' | b'
   *  b
   *)
  let vaugment a b = transpose (haugment (transpose a) (transpose b))
  let map2 f a b =
    if not (same_dim a b) then
      failwith "Matrix.map2: wrong dimesions"
    else
      create (nrows a) (ncols a) (fun i j -> f (get a i j) (get b i j))
  let add a b = map2 N.add a b
  let sub a b = map2 N.sub a b
  let _vector_mul a b =
    let n = Array.length a in
    let p = Array.init n (fun i -> N.mul a.(i) b.(i)) in
    Array.fold_left (fun acc x -> N.add acc x) N.zero p
  let mul a b =
    let f i j = _vector_mul (_row a i) (_col b j) in
    create (nrows a) (ncols b) f

  let det a =
    let rec minorsum (i,j,f) =
      if i=j then f i
      else (N.add (f i) (minorsum (i+1,j,f))) in
    let minor (i,j) a x y = 
      a (if x<i then x else x+1) (if y<j then y else y+1) in
    let signexp j = if j mod 2 = 0 then (fun x -> x) else N.neg in
    let rec det' n a = match n with
    | 1 -> a 0 0
    | n -> minorsum (0,n-1, fun j ->
      signexp j (N.mul (a 0 j) (det' (n-1) (minor (0,j) a))))
    in det' (nrows a) (get a)

  (* ------------ nothing below here is used ------------ *)

  (* minor m i j = copy of m without row i and column j *)
  let minor m i j =
    let skip x th = if x < th then x else x+1 in
    let f x y = get m (skip x i) (skip y j) in
    create ((nrows m)-1) ((ncols m)-1) f
end
