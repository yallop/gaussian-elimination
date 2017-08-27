open Gausselim_types

let ret v () = v
let liftRef x = .< ref .~x >. 
let liftGet x = .< ! .~x >. 
let liftPair x = (.< fst .~x >., .< snd .~x >.)
let liftPPair x = (.< fst (fst .~x) >., .< snd (fst .~x) >., .< snd .~x >.)
effect GenLet : 'a code -> 'a code

let handle f =
  try f () with effect (GenLet e) k -> .< let t = .~e in .~(continue k .<t>.) >.
    
let genlet e = perform (GenLet e)
(* code combinators using effects, mostly unused *)
let retMatchM o s n =  .< match .~o with Some i -> .~(handle (s .<i>.))
                                       | None -> .~(handle n) >.
let retWhileM c b = .< while .~(handle c) do .~(handle b) done >.
let retLoopM l h b = .< for j = .~l to .~h do .~(handle (b .<j>.)) done >.
let seqM x y = .< begin .~(handle x) ; .~(handle y) end >. 
let ifM c t e = .< if .~(handle c) then .~(handle t) else .~(handle e) >.
let whenM c t = .< if .~(handle c) then .~(handle t) else () >.
type 'a env = 'a list ref
let newenv () = ref []
let store r v = r := v :: !r
let fetch = (!)

let runM m = handle m
let (>>) x y = .< begin .~(handle x) ; .~(handle y) end >.

(* Define the actual module types and instances *)
module type DOMAIN = sig
  type v
  type kind (* Field or Ring ? *)
  type vc = v code
  val zero : vc
  val one : vc
  val plus : vc -> vc -> vc
  val times : vc -> vc -> vc
  val minus : vc -> vc -> vc
  val uminus : vc -> vc
  val div : vc -> vc -> vc
  val better_than : (vc -> vc -> bool code) option
  val normalizerf : ((v -> v) code ) option
  val normalizerg : vc -> vc
end 

(* The kind of the domain: a ring or a field *)
type domain_is_field (* abstract *)
type domain_is_ring  (* abstract *)

module FloatDomain = 
  struct
    type v = float
    type kind = domain_is_field
    type vc = v code
    let zero = .< 0. >.  
    let one = .< 1. >. 
    let plus x y = .<.~x +. .~y>. 
    let times x y = .<.~x *. .~y>.
    let minus x y = .<.~x -. .~y>.
    let uminus x = .<-. .~x>.
    let div x y = .<.~x /. .~y>. 
    let better_than = Some (fun x y -> .<abs_float .~x < abs_float .~y >. )
    let normalizerf = None 
    let normalizerg = fun x -> x
end

module IntegerDomain = 
  struct
    type v = int
    type kind = domain_is_ring
    type vc = v code
    let zero = .< 0 >.  
    let one = .< 1 >. 
    let plus x y = .<.~x + .~y>. 
    let times x y = .<.~x * .~y>.
    let minus x y = .<.~x - .~y>.
    let uminus x = .< - .~x>.
    let div x y = .<.~x / .~y>. 
    let better_than = Some (fun x y -> .<abs .~x > abs .~y >. )
    let normalizerf = None 
    let normalizerg = fun x -> x
end

module RationalDomain = 
  struct
    type v = Num.num
    type kind = domain_is_field
    type vc = v code
    let zero = let zero = Num.num_of_int 0 in .< zero >.  
    let one = let one = Num.num_of_int 1 in .< one >. 
    let plus x y = .<Num.add_num .~x .~y >.
    let times x y = .<Num.mult_num .~x .~y>.
    let minus x y = .<Num.sub_num .~x .~y>.
    let uminus x = .<Num.minus_num .~x>.
    let div x y = .<Num.div_num .~x .~y>. 
    let better_than = None (* no such thing here *)
    let normalizerf = None 
    let normalizerg = fun x -> x
end

module type CONTAINER2D = functor(Dom:DOMAIN) -> sig
  type contr
  type vc = contr code
  type vo = Dom.v code
  val get : 's env -> vc -> int code -> int code -> vo
  val get' : vc -> int code -> int code -> vo
  val set : 's env -> vc -> int code -> int code -> vo -> unit code
  val set' : vc -> int code -> int code -> vo -> unit code
  val dim1 : vc -> int code
  val dim2 : vc -> int code
  val mapper : (Dom.v->Dom.v) code option -> vc -> vc
  val copy : vc -> vc
  val swap_rows_stmt : vc -> int code -> int code -> 
                       unit code
  val swap_cols_stmt : vc -> int code -> int code -> 
                       unit code
end

module GenericArrayContainer(Dom:DOMAIN) =
  struct
  type contr = Dom.v array array (* Array of rows *)
  type vc = contr code
  type vo = Dom.v code
  let get' x n m = .< (.~x).(.~n).(.~m) >.
  let get env x n m = get' x n m
  let set' x n m y = .< (.~x).(.~n).(.~m) <- .~y >.
  let set env x n m y = set' x n m y
  let dim2 x = .< Array.length .~x >.       (* number of rows *)
  let dim1 x = .< Array.length (.~x).(0) >. (* number of cols *)
  let mapper g a = match g with
      | Some f -> .< Array.map (fun x -> Array.map .~f x) .~a >.
      | None   -> a
  let copy = (fun a -> .<Array.map (fun x -> Array.copy x) 
                       (Array.copy .~a) >. )
  (* this can be optimized with a swap_rows_from if it is known that
     everything before that is already = Dom.zero *)
  let swap_rows_stmt a r1 r2 =
      .< let t = (.~a).(.~r1) in
         begin 
             (.~a).(.~r1) <- (.~a).(.~r2);
             (.~a).(.~r2) <- t
         end >.
  let swap_cols_stmt a c1 c2 = .< 
      for r = 0 to .~(dim2 a)-1 do
          let t = (.~a).(r).(.~c1) in
          begin 
              (.~a).(r).(.~c1) <- (.~a).(r).(.~c2);
              (.~a).(r).(.~c2) <- t
          end
      done  >.
end

module GenericVectorContainer(Dom:DOMAIN) =
  struct
  type contr = Dom.v container2dfromvector
  type vc = contr code
  type vo = Dom.v code
  let get' x n m = .< ((.~x).arr).(.~n* (.~x).m + .~m) >.
  let get _ x n m = get' x n m
  let set' x n m y = .< ((.~x).arr).(.~n* (.~x).m + .~m) <- .~y >.
  let set _ x n m y = set' x n m y
  let dim2 x = .< (.~x).n >.
  let dim1 x = .< (.~x).m >.
  let mapper g a = match g with
      | Some f -> .< { (.~a) with arr = Array.map .~f (.~a).arr} >.
      | None   -> a
  let copy a = .< { (.~a) with arr = Array.copy (.~a).arr} >.
  let swap_rows_stmt b r1 r2 = .<
      let a = (.~b).arr and n = (.~b).n and m = (.~b).m in
      let i1 = .~r1*m and i2 = .~r2*m in
      for i = 0 to m-1 do
          let t = a.(i1 + i) in
          begin 
              a.(i1 + i) <- a.(i2 + i);
              a.(i2 + i) <- t
          end
      done  >.
  let swap_cols_stmt b c1 c2 = .<
      let a = (.~b).arr and nm = (.~b).n * (.~b).m and m = (.~b).m in
      let rec loop i1 i2 =
	if i2 < nm then
	  let t = a.(i1) in
	  begin
	    a.(i1) <- a.(i2);
	    a.(i2) <- t;
	    loop (i1 + m) (i2 + m)
	  end
      in loop .~c1 .~c2
     >.
end

(* set up some very general algebra that can be reused though not
   so much in the current code (yet?) 
type ('a,'b) abstract = Ground of 'b | Code of ('a, 'b) code
let concretize = function
    | Ground x -> .<x>.
    | Code x   -> x
*)

(* monadic logic code combinators *)
module LogicCode = struct
  let not a = .< not .~a >.
  let equal a b = .< .~a = .~ b >.
  let and_ a b = .< .~a && .~b >. 
end

(* operations on code indices *)
module Idx = struct
  let zero = .< 0 >.
  let succ a = .< .~a + 1 >.
  let pred a = .< .~a - 1 >.
  let less a b = .< .~a < .~b >.
end

(* code generators *)
module Code = struct
  let update a f = let b = f (liftGet a) in fun () -> .< .~a := .~b >.
end

module type DETERMINANT = sig
  type indet
  type outdet
  type tdet = outdet ref
  type lstate
  val decl : ([> `TDet of lstate ] as 's) env -> unit
  val upd_sign : ([> `TDet of lstate ] as 's) env ->  unit -> unit code
  val zero_sign : ([> `TDet of lstate ] as 's) env -> unit code
  val acc : ([> `TDet of lstate ] as 's) env -> indet code -> unit -> unit code
  val get : ([> `TDet of lstate ] as 's) env -> tdet code
  val set : ([> `TDet of lstate ] as 's) env -> indet code -> unit code
  val fin : ([> `TDet of lstate ] as 's) env -> outdet code
end

(* no need to make the type abstract here - just leads to other problems *)
module type RANK = sig
  type lstate = int ref code
  val rfetch : ([> `TRan of lstate ] as 's) env -> (int ref) code
  val decl : ([> `TRan of lstate ] as 's) env -> (int ref) code
  val succ : ([> `TRan of lstate ] as 's) env -> unit -> unit code
  val fin : ([> `TRan of lstate ] as 's) env -> int code
end

(* Even if no rank is output, it needs to be tracked, as the rank
   is also the outer loop index! *)
module TrackRank = 
  struct
  type lstate = (int ref) code
  let rec fetch_iter = function
      | `TRan x :: _ -> x
      |  _ :: t -> fetch_iter t
      | [] -> raise Not_found
  let rfetch env = fetch_iter (fetch env)
  let rstore env v = store env (`TRan v)
  let decl env = let rdecl = genlet (liftRef Idx.zero) in
                  let () = rstore env rdecl in
                  rdecl
  let succ env () = let r = rfetch env in .<.~r := (! .~r) + 1>.
end

module Rank:RANK = struct
  include TrackRank
  let fin env = liftGet (rfetch env)
end

module NoRank:RANK = struct
  include TrackRank
  let fin _ = .< -1 >.
end

(* In the case of a non-fraction-free algorithm with no Det
   output, it is possible to not track the determinant, but
   in all other cases it is needed.

   This module is just for deep type sharing.  The actual 
   implementations are completely different.  *)
module DetTypes(Dom: DOMAIN) = 
  struct
  type indet = Dom.v
  type outdet = indet
  type tdet = outdet ref
  (* the first part of the state is an integer: which is +1, 0, -1:
     the sign of the determinant *)
  type lstate = (int ref) code * (tdet) code
end

(* we need the domain anyways to get things to type properly *)
module NoDet(Dom:DOMAIN) =
  struct
  module TD = DetTypes(Dom)
  type indet = Dom.v
  type outdet = unit
  type tdet = outdet ref
  type lstate = TD.lstate
  let decl _ = ()
  let upd_sign _ () = .< () >.
  let zero_sign _ = .< () >.
  let acc _ v () = .< () >.
  let get _ = liftRef .< () >.
  let set _ v = .< () >.
  let fin _ = .< () >.
end

module AbstractDet(Dom: DOMAIN) =
  struct
  module TD = DetTypes(Dom)
  type indet = TD.indet
  type outdet = TD.outdet
  type tdet = TD.tdet
  type lstate = TD.lstate
  let rec fetch_iter (s : [> `TDet of lstate] list) =
    match List.hd s with
      `TDet x -> x
    |  _ -> fetch_iter (List.tl s)
  let dfetch env = fetch_iter (fetch env)
  let dstore env v = store env (`TDet v)
  let decl env = 
      let ddecl = genlet (liftRef Dom.one) in
      let dsdecl = genlet (liftRef .<1>.) in
      dstore env (dsdecl,ddecl)
  let upd_sign env () =
    let det1, _ = dfetch env in .< .~det1 := - (! .~det1)>.
  let zero_sign env =
    let (det1, _) = dfetch env in .<.~det1 := 0>.
  let acc env v () =
    let _, det2 = dfetch env in
    let r = Dom.times (liftGet det2) v in
    .<.~det2 := .~r>.
  let get env = let _, det2 = dfetch env in .<.~det2>.
  let set env v = let _, det2 = dfetch env in .<.~det2 := .~v>.
  let fin env =
      let (det_sign,det) = dfetch env in
      .< if (! .~det_sign) = 0 then .~Dom.zero else
         if (! .~det_sign) = 1 then .~(liftGet det)
         else .~(Dom.uminus (liftGet det)) >.
end

module type UPDATE = sig
    type baseobj
    type ctr
    type idx = int code
    module D : DETERMINANT
    val update : ([> `TDet of D.lstate] as 's) env -> ctr code -> idx -> idx -> idx -> idx -> unit code
    val update_det : ([> `TDet of D.lstate] as 's) env -> baseobj code -> unit code
end

(* What is the update formula? *)
module DivisionUpdate
    (Dom:DOMAIN with type kind = domain_is_field)
    (C:CONTAINER2D)
    (Det:DETERMINANT with type indet=Dom.v) = 
  struct
  module Ctr = C(Dom)
  type baseobj = Det.indet
  type ctr = Ctr.contr
  type idx = int code
  module D = Det
  let update env b r c i k =
      let x1 = Ctr.get env b i c in
      let x2 = Ctr.get env b r c in
      let t = Dom.div x1 x2 in
      let x3 = Ctr.get env b r k in
      let l = Dom.times t x3 in
      let x4 = Ctr.get env b i k in
      let y = Dom.minus x4 l in
      Ctr.set env b i k (Dom.normalizerg y)
  let update_det v b = Det.acc v b ()
end

module FractionFreeUpdate(Dom:DOMAIN)(C:CONTAINER2D)
    (Det:DETERMINANT with type indet=Dom.v and type outdet=Dom.v) =
  struct
  module Ctr = C(Dom)
  type baseobj = Dom.v
  type ctr = Ctr.contr
  type idx = int code
  module D = Det
  let update env b r c i k =
      let x1 = Ctr.get env b i k in
      let x2 = Ctr.get env b r c in
      let x = Dom.times x1 x2 in
      let x3 = Ctr.get env b r k in
      let x4 = Ctr.get env b i r in
      let y = Dom.times x3 x4 in
      let z = Dom.minus x y in
      let t = Dom.normalizerg z in
      let d = Det.get env in
      let ov = Dom.div t (liftGet d) in
      Ctr.set env b i k ov
  let update_det env v = Det.set env v
end

(* This type is needed for the output, and is tracked during
   pivoting. *)
type perm = RowSwap of (int * int) | ColSwap of (int * int)
 
module type TRACKPIVOT = sig
  type lstate
  val decl : ([> `TPivot of lstate] as 's) env -> unit
  val add : ([> `TPivot of lstate] as 's) env -> perm code -> unit code
  val fin : ([> `TPivot of lstate] as 's) env -> (perm list) code
end

module TrackPivot = 
  struct
  type lstate = (perm list ref) code
  let rec fetch_iter = function
    | `TPivot x :: _ -> x
    |  _ :: tl -> fetch_iter tl
    | _ -> raise Not_found
  let pfetch env = fetch_iter (fetch env)
  let pstore env v = store env (`TPivot v)
  let decl env = pstore env (genlet (liftRef .< [] >.))
  let add env v =
    let p = pfetch env in
    .<.~p := .~v::(! .~p) >.
end

module KeepPivot:TRACKPIVOT = struct
  include TrackPivot
  let fin env = liftGet (pfetch env)
end

module DiscardPivot:TRACKPIVOT = struct
  type lstate = (perm list ref) code
  let decl _ = ()
  let add _ v = .< () >.
  let fin _ = .< [] >.
end

module type OUTPUT = sig
  type contr
  type res
  module D : DETERMINANT
  module R : RANK
  module P : TRACKPIVOT
  val make_result :
    ([> `TDet of D.lstate | `TRan of R.lstate | `TPivot of P.lstate] as 's) env ->
    contr code -> res code
end

(* What to return *)
module OutJustMatrix(Dom:DOMAIN)(C: CONTAINER2D)(Det : DETERMINANT) =
  struct
  module Ctr = C(Dom)
  type contr = Ctr.contr
  type res = contr
  module D = Det
  module R = NoRank
  module P = DiscardPivot
  let make_result _ b = b
end

module OutDet(Dom:DOMAIN)(C: CONTAINER2D)
    (Det : DETERMINANT with type indet = Dom.v and type outdet = Dom.v) =
  struct
  module Ctr = C(Dom)
  type contr = Ctr.contr
  type res = contr * Det.outdet
  module D = Det
  module R = NoRank
  module P = DiscardPivot
  let make_result env b =
    let det = D.fin env in
    .< ( .~b, .~det ) >.
end

module OutRank(Dom:DOMAIN)(C: CONTAINER2D)(Rank : RANK) =
  struct
  module Ctr = C(Dom)
  type contr = Ctr.contr
  type res = contr * int
  module D = NoDet(Dom)
  module R = Rank
  module P = DiscardPivot
  let make_result env b =
    let rank = R.fin env in
    .< ( .~b, .~rank ) >.
end

module OutDetRank(Dom:DOMAIN)(C: CONTAINER2D)
    (Det : DETERMINANT with type indet = Dom.v and type outdet = Dom.v)
    (Rank : RANK) =
  struct
  module Ctr = C(Dom)
  type contr = Ctr.contr
  type res = contr * Det.outdet * int
  module D = Det
  module R = Rank
  module P = DiscardPivot
  let make_result env b =
    let det = D.fin env in
    let rank = R.fin env in
    .< ( .~b, .~det, .~rank ) >.
end

module OutDetRankPivot(Dom:DOMAIN)(C: CONTAINER2D)
    (Det : DETERMINANT with type indet = Dom.v and type outdet = Dom.v)
    (Rank : RANK) =
  struct
  module Ctr = C(Dom)
  type contr = Ctr.contr
  type res = contr * Det.outdet * int * perm list
  module D = Det
  module R = Rank
  module P = KeepPivot
  let make_result env b =
    let det = D.fin env in
    let rank = R.fin env in
    let pivmat = P.fin env in
    .< ( .~b, .~det, .~rank, .~pivmat ) >.
end

module FDet = AbstractDet(FloatDomain)
module IDet = AbstractDet(IntegerDomain)
module RDet = AbstractDet(RationalDomain)

module type PIVOT = 
    functor (Dom: DOMAIN) -> 
      functor (C: CONTAINER2D) ->
        functor (D: DETERMINANT with type indet = Dom.v) -> 
sig
 (* Find the pivot within [r,m-1] rows and [c,(n-1)] columns
    of containrer b.
    If pivot is found, permute the matrix rows and columns so that the pivot
    becomes the element (r,c) of the matrix,
    Return the value of the pivot option. Or zero?
    When we permute the rows of columns, we update the sign of the det.
 *)
 val findpivot : ([> `TDet of D.lstate] as 's) env ->
   C(Dom).vc -> int code -> int code -> 
   int code -> int code ->
   (Dom.v option) code
end

module RowPivot(Dom: DOMAIN)(C: CONTAINER2D)
   (D: DETERMINANT with type indet = Dom.v) =
struct
   module Ctr = C(Dom)
   let findpivot env b r m c n =
     let pivot = genlet (liftRef .< None >. ) in
       (* If no better_than procedure defined, we just search for
	  non-zero element. Any non-zero element is a good pivot.
	  If better_than is defined, we search then for the best element *)
       ((match Dom.better_than with
         Some sel -> fun () ->
         .< for j = .~r to .~(Idx.pred n) do
              let t = .~(Ctr.get env b .<j>. c) in
              if .~(LogicCode.not (LogicCode.equal .<t>. Dom.zero)) then
                match .~(liftGet pivot) with
                | Some i ->
                   if .~(sel .<snd i>. .<t>.)
                   then .~pivot := Some (j,t)
                   else ()
                | None -> .~pivot := Some (j,t)
              else ()
            done >.
         | None -> fun () ->
            let brc = genlet (Ctr.get env b r c) in
            .< if not (.~brc = .~Dom.zero)
               then .~pivot := Some (.~r,.~brc)
               else .~(handle @@ fun () ->
                let _s = fetch env in
                .< let rec loop j =
                     if j < .~n then 
                       let bjc = .~(Ctr.get' b .<j>. c) in
                       if bjc = .~Dom.zero then loop (j+1)
                       else .~pivot := Some (j,bjc)
                       in loop (.~r+1) >.) >.)
        >> fun () ->
           .< match .~(liftGet pivot) with
              | Some i ->
                 .~(let (i,bic) = liftPair .<i>. in
                    .< ((if .~i <> .~r
                         then .~((fun () -> Ctr.swap_rows_stmt b r i) >>
                                 D.upd_sign env)
                         else ());
                        Some .~bic) >.)
              | None -> None >.)
end

module FullPivot(Dom: DOMAIN)(C: CONTAINER2D)
   (D: DETERMINANT with type indet = Dom.v) =
struct
   module Ctr = C(Dom)
   let findpivot env b r m c n =
     let pivot = genlet (liftRef .< None >. ) in
     .< ((for j = .~r to .~n-1 do .~(
          let j' = .<j>. in
          (* (The code's written like this, with both loop variables
             named 'j', so that the generated code matches the original
             output.  When that's no longer an issue it can be simplified.) *)
              .< for j = .~c to .~m-1 do
                   let t (* bjk *) = .~(Ctr.get env b j' .<j>.) in
                   if not (t = .~Dom.zero) then
                     .~(match (Dom.better_than) with
                        | Some sel ->
                           .< match .~(liftGet pivot) with
                                Some i -> 
                                .~(let (pr,pc,brc) = liftPPair .<i>. in
                                   .< if .~(sel brc .<t>.)
                                      then .~pivot := Some ((.~j',j),t)
                                      else () >.)
                              | None -> .~pivot := Some ((.~j',j),t) >.
                              | None ->
                                 (.< .~pivot := Some ((.~j',j),t) >.)
                     ) else ()  done >.) done);
         (* finished the loop *)
         .~(handle @@ fun () ->
                .< match .~(liftGet pivot) with
                   Some i -> 
                   .~(let (pr,pc,brc) = liftPPair .<i>. in
                      .<( (if .~pc <> .~c
                           then .~((fun () -> Ctr.swap_cols_stmt b c pc) >>
                                   D.upd_sign env)
                           else ());
                          ((if .~pr <> .~r 
                            then .~((fun () -> Ctr.swap_rows_stmt b r pr) >>
                                    D.upd_sign env)
                            else ());
                           (Some .~brc))
                      )>.)
                   | None -> None >.)) >.
end

module NoPivot(Dom: DOMAIN)(C: CONTAINER2D)
   (D: DETERMINANT with type indet = Dom.v) =
struct
   module Ctr = C(Dom)
   (* In this case, we assume diagonal dominance, and so
      just take the diagonal as ``pivot'' *)
   let findpivot env b r m c n = .< Some (.~(Ctr.get env b r c)) >.
end

module Gen(Dom: DOMAIN)(C: CONTAINER2D)(PivotF: PIVOT)
          (Update: UPDATE with type baseobj = Dom.v and type ctr = C(Dom).contr)
          (Out: OUTPUT with type contr = C(Dom).contr and type D.indet = Dom.v 
                        and type D.lstate = Update.D.lstate) =
   struct
    module Ctr = C(Dom)
    module Pivot = PivotF(Dom)(C)(Out.D)
    type v = Dom.v
    let gen =
      let zerobelow env b r c m n brc =
        let innerbody env i () =
            let bic = Ctr.get env b i c in
            .< if .~(LogicCode.not (LogicCode.equal bic Dom.zero))
               then (for j = .~(Idx.succ c) to .~(Idx.pred m)
                     do .~(handle @@ fun () -> Update.update env b r c i .<j>.) done;
                     .~(handle @@ fun () -> Ctr.set env b i c Dom.zero))
               else () >.
        in 
        .< (for j = .~(Idx.succ r) to .~(Idx.pred n) do .~(handle @@ innerbody env .<j>.) done;
            .~(Update.update_det env brc)) >. in
      let dogen env a () =
          let r = Out.R.decl env in
          let c = genlet (liftRef Idx.zero) in
          let b = genlet (Ctr.mapper Dom.normalizerf (Ctr.copy a)) in
          let m = genlet (Ctr.dim1 a) in
          let n = genlet (Ctr.dim2 a) in
          let () = Update.D.decl env in
          let () = Out.P.decl env in
          .< ((while .~(handle @@ fun () ->
                        LogicCode.and_ (Idx.less (liftGet c) m)
                                       (Idx.less (liftGet r) n)) do
                 .~(handle @@ fun () ->
                    let rr = genlet (liftGet r) in
                    let cc = genlet (liftGet c) in
                    let pivot = genlet (Pivot.findpivot env b rr m cc n) in
                    .< ((match .~pivot with
                         | Some i -> .~((fun () -> zerobelow env b rr cc m n .<i>.) >>
                                        (Out.R.succ env))
                         | None -> .~(Update.D.zero_sign env));
                        .~(handle @@ Code.update c Idx.succ)) >.)
               done);
              .~(handle @@ fun () -> Out.make_result env b)) >.
    in
    .<fun a -> .~(runM (dogen (newenv ()) .<a>.)) >.
end

module GenFA1 = Gen(FloatDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (DivisionUpdate(FloatDomain)(GenericArrayContainer)(NoDet(FloatDomain)))
                   (OutJustMatrix(FloatDomain)(GenericArrayContainer)(NoDet(FloatDomain)))

module GenFA2 = Gen(FloatDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (DivisionUpdate(FloatDomain)(GenericArrayContainer)(FDet))
                   (OutDet(FloatDomain)(GenericArrayContainer)(FDet))
module GenFA3 = Gen(FloatDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (DivisionUpdate(FloatDomain)(GenericArrayContainer)(NoDet(FloatDomain)))
                   (OutRank(FloatDomain)(GenericArrayContainer)(Rank))
module GenFA4 = Gen(FloatDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (DivisionUpdate(FloatDomain)(GenericArrayContainer)(FDet))
                   (OutDetRank(FloatDomain)(GenericArrayContainer)(FDet)(Rank))
module GenFV1 = Gen(FloatDomain)
                   (GenericVectorContainer)
                   (RowPivot)
                   (DivisionUpdate(FloatDomain)(GenericVectorContainer)(FDet))
                   (OutJustMatrix(FloatDomain)(GenericVectorContainer)(FDet))
module GenFV2 = Gen(FloatDomain)
                   (GenericVectorContainer)
                   (RowPivot)
                   (DivisionUpdate(FloatDomain)(GenericVectorContainer)(FDet))
                   (OutDet(FloatDomain)(GenericVectorContainer)(FDet))
module GenFV3 = Gen(FloatDomain)
                   (GenericVectorContainer)
                   (RowPivot)
                   (DivisionUpdate(FloatDomain)(GenericVectorContainer)(NoDet(FloatDomain)))
                   (OutRank(FloatDomain)(GenericVectorContainer)(Rank))
module GenFV4 = Gen(FloatDomain)
                   (GenericVectorContainer)
                   (RowPivot)
                   (DivisionUpdate(FloatDomain)(GenericVectorContainer)(FDet))
                   (OutDetRank(FloatDomain)(GenericVectorContainer)(FDet)(Rank))
module GenFV5 = Gen(FloatDomain)
                   (GenericVectorContainer)
                   (FullPivot)
                   (DivisionUpdate(FloatDomain)(GenericVectorContainer)(FDet))
                   (OutDetRank(FloatDomain)(GenericVectorContainer)(FDet)(Rank))

(* But this is an error!
module GenIA1 = Gen(IntegerDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (DivisionUpdate(IntegerDomain)(GenericArrayContainer)(IDet))
                   (OutJustMatrix(IntegerDomain)(GenericArrayContainer)(IDet))
*)
module GenIA1 = Gen(IntegerDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (FractionFreeUpdate(IntegerDomain)(GenericArrayContainer)(IDet))
                   (OutJustMatrix(IntegerDomain)(GenericArrayContainer)(IDet))
module GenIA2 = Gen(IntegerDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (FractionFreeUpdate(IntegerDomain)(GenericArrayContainer)(IDet))
                   (OutDet(IntegerDomain)(GenericArrayContainer)(IDet))
module GenIA3 = Gen(IntegerDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (FractionFreeUpdate(IntegerDomain)(GenericArrayContainer)(IDet))
                   (OutRank(IntegerDomain)(GenericArrayContainer)(Rank))
module GenIA4 = Gen(IntegerDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (FractionFreeUpdate(IntegerDomain)(GenericArrayContainer)(IDet))
                   (OutDetRank(IntegerDomain)(GenericArrayContainer)(IDet)(Rank))
module GenIV1 = Gen(IntegerDomain)
                   (GenericVectorContainer)
                   (RowPivot)
                   (FractionFreeUpdate(IntegerDomain)(GenericVectorContainer)(IDet))
                   (OutJustMatrix(IntegerDomain)(GenericVectorContainer)(NoDet(IntegerDomain)))
module GenIV2 = Gen(IntegerDomain)
                   (GenericVectorContainer)
                   (RowPivot)
                   (FractionFreeUpdate(IntegerDomain)(GenericVectorContainer)(IDet))
                   (OutDet(IntegerDomain)(GenericVectorContainer)(IDet))
module GenIV3 = Gen(IntegerDomain)
                   (GenericVectorContainer)
                   (RowPivot)
                   (FractionFreeUpdate(IntegerDomain)(GenericVectorContainer)(IDet))
                   (OutRank(IntegerDomain)(GenericVectorContainer)(Rank))
module GenIV4 = Gen(IntegerDomain)
                   (GenericVectorContainer)
                   (RowPivot)
                   (FractionFreeUpdate(IntegerDomain)(GenericVectorContainer)(IDet))
                   (OutDetRank(IntegerDomain)(GenericVectorContainer)(IDet)(Rank))
module GenIV5 = Gen(IntegerDomain)
                   (GenericVectorContainer)
                   (FullPivot)
                   (FractionFreeUpdate(IntegerDomain)(GenericVectorContainer)(IDet))
                   (OutDetRank(IntegerDomain)(GenericVectorContainer)(IDet)(Rank))
module GenFA11 = Gen(FloatDomain)
                   (GenericArrayContainer)
                   (FullPivot)
                   (DivisionUpdate(FloatDomain)(GenericArrayContainer)(NoDet(FloatDomain)))
                   (OutJustMatrix(FloatDomain)(GenericArrayContainer)(NoDet(FloatDomain)))
module GenFA12 = Gen(FloatDomain)
                   (GenericArrayContainer)
                   (FullPivot)
                   (DivisionUpdate(FloatDomain)(GenericArrayContainer)(FDet))
                   (OutDet(FloatDomain)(GenericArrayContainer)(FDet))
module GenFA13 = Gen(FloatDomain)
                   (GenericArrayContainer)
                   (FullPivot)
                   (DivisionUpdate(FloatDomain)(GenericArrayContainer)(NoDet(FloatDomain)))
                   (OutRank(FloatDomain)(GenericArrayContainer)(Rank))
module GenFA14 = Gen(FloatDomain)
                   (GenericArrayContainer)
                   (FullPivot)
                   (DivisionUpdate(FloatDomain)(GenericArrayContainer)(FDet))
                   (OutDetRank(FloatDomain)(GenericArrayContainer)(FDet)(Rank))

module GenFA24 = Gen(FloatDomain)
                    (GenericArrayContainer)
                    (RowPivot)
                    (DivisionUpdate(FloatDomain)(GenericArrayContainer)(FDet))
                    (OutDetRankPivot(FloatDomain)(GenericArrayContainer)(FDet)(Rank))
module GenRA1 = Gen(RationalDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (DivisionUpdate(RationalDomain)(GenericArrayContainer)(RDet))
                   (OutJustMatrix(RationalDomain)(GenericArrayContainer)(RDet))
module GenRA2 = Gen(RationalDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (DivisionUpdate(RationalDomain)(GenericArrayContainer)(RDet))
                   (OutDet(RationalDomain)(GenericArrayContainer)(RDet))
module GenRA3 = Gen(RationalDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (DivisionUpdate(RationalDomain)(GenericArrayContainer)(RDet))
                   (OutRank(RationalDomain)(GenericArrayContainer)(Rank))
module GenRA4 = Gen(RationalDomain)
                   (GenericArrayContainer)
                   (RowPivot)
                   (DivisionUpdate(RationalDomain)(GenericArrayContainer)(RDet))
                   (OutDetRank(RationalDomain)(GenericArrayContainer)(RDet)(Rank))
