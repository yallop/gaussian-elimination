type field (* abstract *)
type ring  (* abstract *)

module type S =
sig
  type v
  type kind (* Field or Ring ? *)
  type _ exp
  val zero : v exp
  val one : v exp
  val plus : v exp -> v exp -> v exp
  val times : v exp -> v exp -> v exp
  val minus : v exp -> v exp -> v exp
  val uminus : v exp -> v exp
  val div : v exp -> v exp -> v exp
  val better_than : (v exp -> v exp -> bool exp) option
  val normalizerf : (v -> v) exp option
  val normalizerg : v exp -> v exp
end
