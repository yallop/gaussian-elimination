open Algebra
open Vector
open Tuple

module RModule (C:  Repr.REPR)
          (N : RING with type ('a,'b) rep = ('a,'b) C.rep)
          (T : TUPLE with type ('a,'b) rep = ('a,'b) C.rep)
    (* : RMODULE *) = struct
  include Repr.GenRep(C)
  type n = N.n
  type 'a t = 'a T.t
  type ('a,'b) trep = ('a,'b) T.trep
  type ('a,'b) vector = ('a, 'b) T.trep
  type coordinate_enum = int
  let dim = T.dim
  let zero () = T.init (fun _ -> N.zero)
  (* let ones () = T.init (fun _ -> N.one) *)

  let coord v i = T.proj v i
  let of_coords l = T.of_list l

  let mirror v = T.map N.neg v
  (* vector [+-] vector -> vector *)
  let add v0 v1 = T.map2 N.add v0 v1
  let sub v0 v1 = T.map2 N.sub v0 v1
  (* vector [./] scalar -> vector *)
  let scale v s = T.letbt s (fun s' -> T.map (fun x -> N.mul s' x) v)
  (* dot = sum_i (c^0_i * c^1_i) *)
  let dot v0 v1 = T.map2fold N.mul N.add N.zero v0 v1
  let length2 v = T.lettb v 
    (fun v -> T.mapfold (fun x -> N.mul x x) N.add N.zero v)
  (* subtract the position vectors *)
  let gcross = function
  | [v0; v1] ->
    if dim = 3 then
      let a0 = coord v0 0 and a1 = coord v0 1
      and a2 = coord v0 2
      and b0 = coord v1 0 and b1 = coord v1 1
      and b2 = coord v1 2 in
      let c0 = N.sub (N.mul a1 b2) (N.mul a2 b1)
      and c1 = N.sub (N.mul a2 b0) (N.mul a0 b2)
      and c2 = N.sub (N.mul a0 b1) (N.mul a1 b0) in
      of_coords [ c0; c1; c2 ]
    else
        failwith "Vectoren.gcross: only for 2 vectors in 3D"
  | _ -> failwith "Vectoren.gcross: got more than 2 vectors"
  let letvv v f = f v
  let letvn v f = f v
end

module Vector (C:  Repr.REPR)
          (N : FIELD with type ('a,'b) rep = ('a,'b) C.rep)
          (T : TUPLE with type ('a,'b) rep = ('a,'b) C.rep)
    (* : VECTOR *) = struct
  include RModule(C)(N)(T)
  let shrink v s = T.letbt s (fun s -> T.map (fun x -> N.div x s) v)
end

module NormedVector (C:  Repr.REPR)
          (N : REALFIELD with type ('a,'b) rep = ('a,'b) C.rep)
          (T : TUPLE with type ('a,'b) rep = ('a,'b) C.rep)
    = struct
  include Vector(C)(N)(T)

  let length v = N.sqrt (length2 v)
  (* let direction v = shrink v (length v) *)
  let direction v = T.lettt v (fun v -> shrink v (length v))
end
