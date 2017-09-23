open Domains
open Container

module Impl(Dom:Domains.S with type 'a exp = 'a code) : Cont2D with type 'a rep = 'a Dom.exp = struct
  module Dom = Dom
  type contr = Dom.v array array (* Array of rows *)
  type vc = contr code
  type vo = Dom.v code
  type 'a rep = 'a code
  let get x n m = .< (.~x).(.~n).(.~m) >.
  let dim2 x = .< Array.length .~x >.       (* number of rows *)
  let dim1 x = .< Array.length (.~x).(0) >. (* number of cols *)
  let map (g:(vo -> vo) option) a = match g with
      | Some f -> .< Array.map (fun x -> Array.map (fun z -> .~(f .<z>.)) x) .~a >.
      | None   -> a
  let copy = (fun a -> .<Array.map (fun x -> Array.copy x)
                       (Array.copy .~a) >. )
  let init n m = .< Array.init .~n (fun _ -> Array.make .~m .~(Dom.zero)) >.
  let augment a ma na b nb = .<
      Array.init .~ma (fun i -> Array.init (.~na + .~nb)
          (fun j -> if j< .~na then .~(get a .<i>. .<j>.)
                               else .~(get b .<i>. .<j - .~na>. ))) >.
  let identity n m = .< Array.init .~n (fun i -> Array.init .~m
      (fun j -> if (i=j) then .~(Dom.one) else .~(Dom.zero))) >.
  (* this can be optimized with a swap_rows_from if it is known that
     everything before that is already = Dom.zero *)
  let swap_rows_stmt a _ r1 r2 =
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
  (* this is list an iterator's start *)
  let row_head = get
  (* only set the head of the current column *)
  let col_head_set x n m y = .< (.~x).(.~n).(.~m) <- .~y >.
end
