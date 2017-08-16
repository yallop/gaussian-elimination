(* @NOTE generated code will have cross-stage persistency *)

(* a code which can either be a 'computation' or a 'constant'.
   It is safe to duplicate constants, but not computations.
   Note that 'named computations' (aka variables) are 
   constants (they are 'pointers' in a sense) *)

type choice = Comp | Constant
type ('a,'b) comp = choice * ('a,'b) code

type ('a,'b) staged = { now : 'b option ; later : ('a,'b) comp }

let lift_const cst = { now = Some cst; later = (Constant, .<cst>.) }
let lift_code x = (Comp,x)

let of_atom = lift_const
let of_comp x = { now = None; later = (Comp, x) }
let of_const x = { now = None; later = (Constant, x) }
let of_marked x = { now = None; later = x}

let to_code x = snd x.later

let stage x = fst x

let apply_op f = function
  | Some x -> Some (f x)
  | None   -> None

let apply2_op f x y = match x,y with
  | (Some x), (Some y) -> Some (f x y)
  | _                  -> None

module LiftCode = struct
  let unary f = fun x -> lift_code (f (to_code x))
  let binary f = fun x y -> lift_code (f (to_code x) (to_code y))
end

let unary fnow flater x = 
  let y = apply_op fnow x.now in 
  match y with
  | Some z -> lift_const z
  | None -> { now = y; later = LiftCode.unary flater x }

let binary bnow blater x y = 
  let w = apply2_op bnow x.now y.now in 
  match w with
  | Some z -> lift_const z
  | None -> { now = w; later = LiftCode.binary blater x y}
