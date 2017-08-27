open Domains

(* A signature of 2D containers.  Right now, fairly ad hoc 
  (but represents what is used?).  Should be rationalized.
*)
module type Cont2D = sig
  module Dom : Domains.S
  type contr
  type _ rep
  val get : contr rep -> int rep -> int rep -> Dom.v rep
  val dim1 : contr rep -> int rep
  val dim2 : contr rep -> int rep
  val map : (Dom.v rep -> Dom.v rep) option -> contr rep -> contr rep
  val copy : contr rep -> contr rep
  val init : int rep -> int rep -> contr rep
  val augment : contr rep -> int rep -> int rep -> contr rep ->
                int rep -> contr rep
  val identity : int rep -> int rep -> contr rep
  val swap_rows_stmt : contr rep -> int rep option -> 
                       int rep -> int rep -> unit rep
  val swap_cols_stmt : contr rep -> int rep -> int rep -> 
                       unit rep
  val row_head : contr rep -> int rep -> int rep -> Dom.v rep
  val col_head_set : contr rep -> int rep -> int rep -> Dom.v rep -> 
            unit rep
end
