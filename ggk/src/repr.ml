open Staged

module type REPR = sig
  type ('a,'b) rep
end

module type REP = sig
  include REPR
  type ('a,'b,'c) unary_fun = ('a,'b) rep -> ('a,'c) rep
  type ('a,'b,'c,'d) binary_fun = ('a,'b) rep -> ('a,'c) rep -> ('a,'d) rep
  type ('a,'b) rel = ('a,'b,'b,bool) binary_fun
  type ('a,'b) una = ('a,'b,'b) unary_fun
  type ('a,'b) bin = ('a,'b,'b,'b) binary_fun
end

module GenRep(C:REPR) = struct
  include C
  type ('a,'b,'c) unary_fun = ('a,'b) C.rep -> ('a,'c) C.rep
  type ('a,'b,'c,'d) binary_fun = ('a,'b) C.rep -> ('a,'c) C.rep -> ('a,'d) C.rep
  type ('a,'b) rel = ('a,'b,'b,bool) binary_fun
  type ('a,'b) una = ('a,'b,'b) unary_fun
  type ('a,'b) bin = ('a,'b,'b,'b) binary_fun
end

(* useful items from an underlying programming language *)
module type LANG = sig
  type ('a,'b) l (* should be rep *)
  val let_ : ('a,'b) l -> (('a,'b) l -> ('a, 'c) l) -> ('a,'c) l
  val ife : ('a,bool) l -> ('a,'b) l -> ('a,'b) l -> ('a,'b) l
end

module type LREP = sig
  include REP
  include LANG with type ('a,'b) l = ('a,'b) rep
end

module ImmRep = struct type ('a,'b) rep = 'b end
module ImmLang = struct
  type ('a,'b) l = 'b
  let let_ a b = let x = a in b x
  let ife a b c = if a then b else c
end
module Imm = struct include GenRep(ImmRep) include ImmLang end

module CodeRep = struct type ('a,'b) rep = ('a,'b) code end
module CodeLang = struct
  type ('a,'b) l = ('a,'b) code
  let let_ ce exp = 
    .< let _v = .~ce in .~(let r = exp .<_v>. in r) >.
  let ife c a b = .< if .~c then .~a else .~b >.
end
module Code = struct include GenRep(CodeRep) include CodeLang end

module CGenRep = struct type ('a,'b) rep = ('a,'b) staged end
module CGenLang = struct
  type ('a,'b) l = ('a,'b) staged
  let let_ ce exp = exp ce
  let ife c a b = match c.now with
    | Some cond -> if cond then a else b
    | None -> of_comp .< if .~(to_code c) then .~(to_code a) else .~(to_code b) >.
end
module CGen = struct include GenRep(CGenRep) include CGenLang end
