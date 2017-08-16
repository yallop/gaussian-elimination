open Staged
open Simplify

(* staged container *)
module type TUPLE = sig
  include Repr.REP
  type 'b t                            (* container *)
  type ('a,'b) trep
  val dim : int
  val init : (int -> ('a,'b) rep) -> ('a,'b) trep
  val proj : ('a, 'b) trep -> int -> ('a, 'b) rep

  val unfold : ('a,'b) trep -> ('a,'b) rep list
  val of_list : ('a,'b) rep list -> ('a, 'b) trep

  val map : ('a, 'b, 'c) unary_fun -> ('a, 'b) trep -> ('a, 'c) trep
  val map2 : ('a, 'b, 'c, 'd) binary_fun -> 
             ('a, 'b) trep -> ('a, 'c) trep -> ('a, 'd) trep

  (* fold_left *)
  val fold : ('a,'b,'c,'b) binary_fun -> ('a,'b) rep -> ('a, 'c) trep -> ('a,'b) rep

  val mapfold : ('a, 'b, 'd) unary_fun -> (('a,'c) rep -> ('a,'d) rep -> ('a,'c) rep) ->
                  ('a,'c) rep -> ('a, 'b) trep -> ('a,'c) rep

  val map2fold : ('a, 'b, 'c, 'd) binary_fun -> ('a, 'e, 'd, 'e) binary_fun ->
              ('a,'e) rep -> ('a, 'b) trep -> ('a, 'c) trep -> ('a, 'e) rep

  val letbt : ('a,'b) rep -> (('a,'b) rep -> ('a,'c) trep) -> ('a,'c) trep
  val lettt : ('a,'b) trep -> (('a,'b) trep -> ('a,'c) trep) -> ('a,'c) trep
  val lettb : ('a,'b) trep -> (('a,'b) trep -> ('a,'c) rep) -> ('a,'c) rep
end

module type TupleRep = sig type 'a t end

module type StagedTuple = sig
  include TupleRep
  type ('a,'b) rep = ('a,'b) staged
  type ('a,'b) trep = { stn : ('a,'b) rep t option; stl: ('a, 'b t) comp }
  val mkc : ('a,'b t) comp -> ('a,'b) trep
  val extract : ('a,'b) trep -> ('a,'b t) code
  val letbt : ('a,'b) rep -> (('a,'b) rep -> ('a,'c) trep) -> ('a,'c) trep
  val lettt : ('a,'b) trep -> (('a,'b) trep -> ('a,'c) trep) -> ('a,'c) trep
  val lettb : ('a,'b) trep -> (('a,'b) trep -> ('a,'c) rep) -> ('a,'c) rep
end

module type TRep = sig
  include TupleRep
  type ('a,'b) rep (* inner *)
end

module type Unfoldable = sig
  include Repr.REP
  include TupleRep
  type ('a,'b) trep
  val dim : int
  val unfold : ('a,'b) trep -> ('a,'b) rep list
  val of_list : ('a,'b) rep list -> ('a,'b) trep
end

let retN x k = lift_code .< let v = .~x in .~(k .<v>.)>.

module MakeStagedTuple( R: TRep ) = struct
  type ('a,'b) trep = { stn : ('a,'b) R.rep R.t option; stl: ('a, 'b R.t) comp }

  let mkc c = {stn = None; stl = c}
  let extract x = snd x.stl
  let lettt z f = match z.stl with
    | (Constant, _) -> f z
    | (Comp, x) -> let v = f z in {stn = v.stn; 
          stl = retN x (fun v -> extract (f (mkc (Constant, v)))) }
  let letbt z f = match z.later with
    | (Constant, _) -> f z
    | (Comp, x) -> let v = f z in {stn = v.stn;
          stl = retN x (fun v -> extract (f (of_const v))) }
  let lettb z f = match z.stn with
    | Some _ -> f z
    | None   -> (match z.stl with
      | (Constant, _) -> f z
      | (Comp, x ) -> let v = f z in {now = v.now;
          later = retN x (fun v -> to_code (f (mkc (Constant, v)))) } )
end

module LetFuns = struct
  let lettt z f = f z
  let letbt z f = f z
  let lettb z f = f z
end

let genint n = 
  let rec f = function
  | 0            -> []
  | n when n < 0 -> failwith "cannot generate a list of negative integers"
  | n            -> let k = n-1 in k :: f k
  in List.rev (f n)

(* Must be used with care since it uses of_const, not of_comp *)
let l1 f = fun z -> to_code (f (of_const z))
let l2 f = fun z z' -> to_code (f (of_const z) (of_const z'))
  (* only on 2nd arg *)
let l2' f = fun z z' -> f z (of_const z')

module GenericFolds (S : Unfoldable) = struct
  include S
  let init f = S.of_list (List.map f (genint S.dim))
  let proj v i = List.nth (S.unfold v) i

  let map f t = S.of_list ( List.map f ( S.unfold t ) )
  let map2 f t t' = S.of_list (List.map2 f (S.unfold t) (S.unfold t'))
  let fold f zer t = List.fold_left f zer (S.unfold t)
  let mapfold m f zer t = List.fold_left (fun z y -> f z (m y)) zer (S.unfold t)
  let map2fold m f zer t t' = List.fold_left2 (fun z x y -> f z (m x y)) zer (S.unfold t) (S.unfold t')
end

module MkCGen(B:TRep with type ('a,'b) rep = ('a,'b) staged)
             (I:TUPLE with type 'a t = 'a B.t and type ('a,'b) rep = 'b and type ('a,'b) trep = 'b B.t)
             (C:TUPLE with type 'a t = 'a B.t and type ('a,'b) rep = ('a,'b) code and type ('a,'b) trep = ('a,'b B.t) code) = struct
  include Repr.GenRep(Repr.CGen)
  include MakeStagedTuple( B )

  let mkt v = {stn = Some v; 
               stl = lift_code (C.of_list (List.map to_code (I.unfold v)))}
  let dim = I.dim
  type 'a t = 'a B.t

  let unfold_c t = List.map of_comp (C.unfold (extract t))

  let of_list l =
    {stn = Some (I.of_list l); 
     stl = lift_code (C.of_list (List.map to_code l))}
  let unfold v = match v.stn with
    | Some x -> I.unfold x
    | None   -> unfold_c v

  let init f = of_list (List.map f (genint I.dim))
  let proj v i = match v.stn with
    | Some w -> I.proj w i
    | None   -> of_comp (C.proj (extract v) i)

  let map f t = 
    let x = apply_op (I.map f) t.stn in
    match x with
    | Some y -> mkt y
    | None -> {stn = x;
               stl = lift_code (C.map (l1 f) (extract t))}

  let map2 f t t' = 
    let x = apply2_op (I.map2 f) t.stn t'.stn in 
    match x with
    | Some y -> mkt y
    | None   -> {stn = x;
                 stl = lift_code (C.map2 (l2 f) (extract t) (extract t'))}

  let fold f z t =  match t.stn with
    | Some x -> I.fold f z x
    | None   -> List.fold_left f z (unfold_c t)

  let mapfold m f z t =  match t.stn with
    | Some x -> I.mapfold m f z x
    | None   -> List.fold_left (fun z y -> f z (m y)) z (unfold_c t)

  let map2fold m f z t t' =  match (t.stn,t'.stn) with
    | (Some x, Some x') -> I.map2fold m f z x x'
    | _                 -> List.fold_left2 (fun z x y -> f z (m x y)) z (unfold_c t) (unfold_c t')
end

(* ******************************************** *)
(* 1D tuple *)

module Base1D = struct
  type 'a t = 'a
  let dim = 1
end

module R1DImmType = struct
  include Base1D
  include Repr.GenRep(Repr.Imm)
  type ('a,'b) trep = 'b t
  let unfold x = [x]
  let of_list = function
    | [a] -> a
    | _   -> failwith "of_list/1 needs exactly 1 arg"
end
 
module R1DImm = struct
  include GenericFolds(R1DImmType)
  include LetFuns
end

module R1DCGenType = struct
  include Repr.GenRep(Repr.CGen)
  include Base1D
  let unfold x = [x]
  let of_list = function
    | [a] -> a
    | _   -> failwith "of_list/1 needs exactly 1 arg"
end

module R1DCodeType = struct
  include Repr.GenRep(Repr.Code)
  include Base1D
  type ('a,'b) trep = ('a, 'b t) code
  let of_list = function
    | [a] -> .< .~a >.
    | _     -> failwith "of_list/tup1 needs exactly 1 arg"
  let unfold r = [ .< .~r >. ]
end

module R1DCode = struct
  include GenericFolds(R1DCodeType)
  include LetFuns
end

module Tuple1D = MkCGen(R1DCGenType)(R1DImm)(R1DCode)

(* ******************************************** *)
type 'a rec2_type = { c0 : 'a ; c1 : 'a }

module BaseR2D = struct
  type 'a t = 'a rec2_type
  let dim = 2
end

module R2DImmType = struct
  include Repr.GenRep(Repr.Imm)
  include BaseR2D
  type ('a,'b) trep = 'b t
  let unfold {c0=x;c1=y} = [x;y]
  let of_list = function
    | [a;b] -> {c0=a; c1=b}
    | _     -> failwith "of_list/rec2 needs exactly 2 args"
end
 
module R2DImm = struct
  include GenericFolds(R2DImmType)
  include LetFuns
end

module R2DCodeType = struct
  include Repr.GenRep(Repr.Code)
  include BaseR2D
  type ('a,'b) trep = ('a, 'b t) code

  let of_list = function
    | [a;b] -> .<{ c0 = .~a; c1 = .~b }>.
    | _     -> failwith "of_list/rec2 needs exactly 2 args"
  let unfold r = [ .<(.~r).c0>. ; .<(.~r).c1>. ]
end

module R2DCode = struct
  include GenericFolds(R2DCodeType)
  include LetFuns
end

module R2DCGenType = struct
  include Repr.GenRep(Repr.CGen)
  include BaseR2D
end
 
module Record2D = MkCGen(R2DCGenType)(R2DImm)(R2DCode)

module BaseP2D = struct
  type 'a t = 'a * 'a
  let dim = 2
end

module P2DImmType = struct
  include Repr.GenRep(Repr.Imm)
  include BaseP2D
  type ('a,'b) trep = 'b t
  let unfold (x,y) = [x;y]
  let of_list = function
    | [a;b] -> (a,b)
    | _     -> failwith "of_list/pair2 needs exactly 2 args"
end
 
module P2DImm = struct
  include GenericFolds(P2DImmType)
  include LetFuns
end

(* This one is different, it uses CPS, it can't be merged right now *)
module P2DCode = struct
  include Repr.GenRep(Repr.Code)
  include LetFuns
  include BaseP2D
  type ('a,'b) trep = ('a, 'b t) code

  (* Implementation *)
  let of_list = function
    | [a;b] -> .<(.~a, .~b)>.
    | _     -> failwith "of_list/pair2 needs exactly 2 args"
  let unfoldk r k = .< let (x,y) = .~r in .~(k [.<x>. ; .<y>. ]) >.
  let unfold r = [ .< fst .~r>. ; .< snd .~r >. ]

  let init f = of_list (List.map f (genint dim))
  let proj v i = unfoldk v (fun l -> List.nth l i)

  let map f t = unfoldk t (fun l -> of_list (List.map f l))
  let map2 f t t' = unfoldk t (fun l -> unfoldk t' (fun l' -> 
      of_list (List.map2 f l l')))
  let fold f zer t = unfoldk t (List.fold_left f zer)
  let mapfold m f zer t = unfoldk t (List.fold_left (fun z y -> f z (m y)) zer)
  let map2fold m f zer t t' = unfoldk t (fun l -> unfoldk t' (
    List.fold_left2 (fun z x y -> f z (m x y)) zer l))
end

module P2DCGenType = struct
  include Repr.GenRep(Repr.CGen)
  include BaseP2D
end
 
module Pair2D = MkCGen(P2DCGenType)(P2DImm)(P2DCode)

(* Tuple 3D *)
type 'a rec3_type = { x : 'a ; y : 'a ; z : 'a }

module BaseR3D = struct
  type 'a t = 'a rec3_type
  let dim = 3
end

module R3DImmType = struct
  include Repr.GenRep(Repr.Imm)
  include BaseR3D
  type ('a,'b) trep = 'b rec3_type
  let unfold r = [r.x; r.y; r.z]
  let of_list = function
    | [a;b;c] -> { x = a; y = b; z = c }
    | _     -> failwith "of_list/rec3 needs exactly 3 args"
end

module R3DCGenType = struct
  include Repr.GenRep(Repr.CGen)
  include BaseR3D
end
 
module R3DImm = struct
  include GenericFolds(R3DImmType)
  include LetFuns
end

module R3DCodeType = struct
  include Repr.GenRep(Repr.Code)
  include BaseR3D
  type ('a,'b) trep = ('a, 'b t) code
  let of_list = function
    | [a;b;c] -> .<{ x = .~a; y = .~b; z = .~c }>.
    | _       -> failwith "of_list/rec3 needs exactly 3 args"
  let unfold r = [ .<(.~r).x>. ; .<(.~r).y>. ; .<(.~r).z>. ]
end

module R3DCode = struct
  include GenericFolds(R3DCodeType)
  include LetFuns
end

module Record3D = MkCGen(R3DCGenType)(R3DImm)(R3DCode)
