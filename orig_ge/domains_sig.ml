(* Declarations of domains and containers *)

type domain_kind = Domain_is_Ring | Domain_is_Field

module S(T:
  sig
	(* Representation type of values,  to be specified *)
    type 'b rep
  end) = struct

open T

module type DOMAIN = sig
  type v
  val kind : domain_kind
  val zero : v
  val one : v
  val plus : v -> v -> v
  val times : v -> v -> v
  val minus : v -> v -> v
  val uminus : v -> v
  val div : v -> v -> v
  val better_than : (v -> v -> bool) option
  val normalizer : (v -> v) option
end 


(* Lift *)
module type DOMAINL = sig
  include DOMAIN
  type vc = v rep
  val zeroL : vc
  val oneL : vc
  val ( +^ ) : vc -> vc -> vc
  val ( *^ ) : vc -> vc -> vc
  val ( -^ ) : vc -> vc -> vc
  val uminusL : vc -> vc
  val divL : vc -> vc -> vc
  val better_thanL : (vc -> vc -> bool rep) option
  val normalizerL : (vc -> vc) option
end 

module type CONTAINER2D = sig
  module Dom:DOMAINL
  type contr
  type vc = contr rep
  type vo = Dom.v rep
  val getL : vc -> (int) rep -> (int) rep -> vo
  val dim1 : vc -> (int) rep
  val dim2 : vc -> (int) rep
  val mapper : (vo -> vo) option -> vc -> vc
  val copy : vc -> vc
  val init : (int) rep -> ( int) rep -> vc
  val augment : vc -> (int) rep -> (int) rep -> vc ->
                (int) rep -> vc
  val identity : (int) rep -> (int) rep -> vc
  val swap_rows_stmt : vc -> (int) rep option -> 
                       (int) rep -> (int) rep -> (unit) rep
  val swap_cols_stmt : vc -> (int) rep -> (int) rep -> 
                       (unit) rep
  val row_head : vc -> (int) rep -> (int) rep -> vo
  val col_head_set : vc -> (int) rep -> (int) rep -> vo -> 
            (unit) rep
end

end
