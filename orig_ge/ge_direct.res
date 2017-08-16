BER MetaOCaml toplevel, version N 102
        OCaml version 4.02.1

#                 module GEF :
  sig
    module D :
      sig
        module type DOMAIN =
          sig
            type v
            val kind : Domains_sig.domain_kind
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
        module type DOMAINL =
          sig
            type v
            val kind : Domains_sig.domain_kind
            val zero : v
            val one : v
            val plus : v -> v -> v
            val times : v -> v -> v
            val minus : v -> v -> v
            val uminus : v -> v
            val div : v -> v -> v
            val better_than : (v -> v -> bool) option
            val normalizer : (v -> v) option
            type vc = v Direct.abstract
            val zeroL : vc
            val oneL : vc
            val ( +^ ) : vc -> vc -> vc
            val ( *^ ) : vc -> vc -> vc
            val ( -^ ) : vc -> vc -> vc
            val uminusL : vc -> vc
            val divL : vc -> vc -> vc
            val better_thanL : (vc -> vc -> bool Direct.abstract) option
            val normalizerL : (vc -> vc) option
          end
        module type CONTAINER2D =
          sig
            module Dom : DOMAINL
            type contr
            type vc = contr Direct.abstract
            type vo = Dom.v Direct.abstract
            val getL : vc -> int Direct.abstract -> int Direct.abstract -> vo
            val dim1 : vc -> int Direct.abstract
            val dim2 : vc -> int Direct.abstract
            val mapper : (vo -> vo) option -> vc -> vc
            val copy : vc -> vc
            val init : int Direct.abstract -> int Direct.abstract -> vc
            val augment :
              vc ->
              int Direct.abstract ->
              int Direct.abstract -> vc -> int Direct.abstract -> vc
            val identity : int Direct.abstract -> int Direct.abstract -> vc
            val swap_rows_stmt :
              vc ->
              int Direct.abstract option ->
              int Direct.abstract ->
              int Direct.abstract -> unit Direct.abstract
            val swap_cols_stmt :
              vc ->
              int Direct.abstract ->
              int Direct.abstract -> unit Direct.abstract
            val row_head :
              vc -> int Direct.abstract -> int Direct.abstract -> vo
            val col_head_set :
              vc ->
              int Direct.abstract ->
              int Direct.abstract -> vo -> unit Direct.abstract
          end
      end
    type ('a, 'b) cmonad_constraint = unit
      constraint 'a = < answer : 'w; state : 's; .. >
      constraint 'b = < answer : 'w Direct.abstract; state : 's list >
    type ('a, 'v) cmonad =
        (< answer : 'b Direct.abstract; state : 'c list >,
         'v Direct.abstract)
        StateCPSMonad.monad
      constraint 'a = < answer : 'b; state : 'c; .. >
    type ('a, 'v) omonad =
        (< answer : 'b Direct.abstract; state : 'c list >,
         'v Direct.abstract option)
        StateCPSMonad.monad
      constraint 'a = < answer : 'b; state : 'c; .. >
    module Iters :
      sig
        val row_iter :
          'a ->
          'b ->
          int Direct.abstract ->
          int Direct.abstract ->
          ('a -> int Direct.abstract -> 'b -> 'c Direct.abstract) ->
          (int Direct.abstract ->
           'c Direct.abstract ->
           (< answer : 'd Direct.abstract; state : 'e; .. >,
            'd Direct.abstract)
           StateCPSMonad.monad) ->
          Prelude.dir -> 'e -> ('e -> unit Direct.abstract -> 'f) -> 'f
        val col_iter :
          'a ->
          'b ->
          int Direct.abstract ->
          int Direct.abstract ->
          ('a -> 'b -> int Direct.abstract -> 'c) ->
          (int Direct.abstract ->
           'c ->
           (< answer : 'd Direct.abstract; state : 'e; .. >,
            'd Direct.abstract)
           StateCPSMonad.monad) ->
          Prelude.dir -> 'e -> ('e -> unit Direct.abstract -> 'f) -> 'f
      end
    module TrackRank :
      sig
        type lstate = int ref Direct.abstract
        type tag_lstate_ = [ `TRan of lstate ]
        type tag_lstate = tag_lstate_
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> tag_lstate ]; .. >
        val ip :
          ('a -> [> `TRan of 'a ]) * ([> `TRan of 'b ] -> 'b option) * string
        val decl :
          unit ->
          (< answer : 'a Direct.abstract;
             state : [> `TRan of int ref Direct.abstract ] list; .. >,
           int ref Direct.abstract)
          StateCPSMonad.monad
        val succ :
          unit ->
          (< answer : 'a; state : [> `TRan of int ref Direct.abstract ] list;
             .. >,
           unit Direct.abstract)
          StateCPSMonad.monad
        module type RANK =
          sig
            type tag_lstate = tag_lstate_
            val decl :
              unit ->
              (< answer : 'a; state : [> tag_lstate ]; .. >, int ref) lm
            val succ :
              unit -> (< answer : 'a; state : [> tag_lstate ]; .. >, unit) lm
            val fin :
              unit -> (< answer : 'a; state : [> tag_lstate ]; .. >, int) lm
          end
      end
    module Rank :
      sig
        type lstate = int ref Direct.abstract
        type tag_lstate_ = [ `TRan of lstate ]
        type tag_lstate = tag_lstate_
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> tag_lstate ]; .. >
        val ip :
          ('a -> [> `TRan of 'a ]) * ([> `TRan of 'b ] -> 'b option) * string
        val decl :
          unit ->
          (< answer : 'a Direct.abstract;
             state : [> `TRan of int ref Direct.abstract ] list; .. >,
           int ref Direct.abstract)
          StateCPSMonad.monad
        val succ :
          unit ->
          (< answer : 'a; state : [> `TRan of int ref Direct.abstract ] list;
             .. >,
           unit Direct.abstract)
          StateCPSMonad.monad
        module type RANK =
          sig
            type tag_lstate = tag_lstate_
            val decl :
              unit ->
              (< answer : 'a; state : [> tag_lstate ]; .. >, int ref) lm
            val succ :
              unit -> (< answer : 'a; state : [> tag_lstate ]; .. >, unit) lm
            val fin :
              unit -> (< answer : 'a; state : [> tag_lstate ]; .. >, int) lm
          end
        val fin :
          unit ->
          (< answer : 'a; state : [> `TRan of 'b ref Direct.abstract ] list;
             .. >,
           'b Direct.abstract)
          StateCPSMonad.monad
      end
    module NoRank :
      sig
        type lstate = int ref Direct.abstract
        type tag_lstate_ = [ `TRan of lstate ]
        type tag_lstate = tag_lstate_
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> tag_lstate ]; .. >
        val ip :
          ('a -> [> `TRan of 'a ]) * ([> `TRan of 'b ] -> 'b option) * string
        val decl :
          unit ->
          (< answer : 'a Direct.abstract;
             state : [> `TRan of int ref Direct.abstract ] list; .. >,
           int ref Direct.abstract)
          StateCPSMonad.monad
        val succ :
          unit ->
          (< answer : 'a; state : [> `TRan of int ref Direct.abstract ] list;
             .. >,
           unit Direct.abstract)
          StateCPSMonad.monad
        module type RANK =
          sig
            type tag_lstate = tag_lstate_
            val decl :
              unit ->
              (< answer : 'a; state : [> tag_lstate ]; .. >, int ref) lm
            val succ :
              unit -> (< answer : 'a; state : [> tag_lstate ]; .. >, unit) lm
            val fin :
              unit -> (< answer : 'a; state : [> tag_lstate ]; .. >, int) lm
          end
        val fin : unit -> 'a
      end
    module type PIVOTKIND =
      sig
        type perm_rep
        type ira = int Direct.abstract
        type fra
        type pra = perm_rep Direct.abstract
        val add : fra -> pra -> pra
        val empty : ira -> pra
        val rowrep : ira -> ira -> fra
        val colrep : ira -> ira -> fra
      end
    module PermList :
      sig
        type flip_rep = Prelude.perm
        type perm_rep = Prelude.perm list
        type ira = int Direct.abstract
        type fra = flip_rep Direct.abstract
        type pra = perm_rep Direct.abstract
        val add :
          'a Direct.abstract ->
          'a list Direct.abstract -> 'a list Direct.abstract
        val empty : 'a -> pra
        val rowrep :
          int Direct.abstract ->
          int Direct.abstract -> Prelude.perm Direct.abstract
        val colrep :
          int Direct.abstract ->
          int Direct.abstract -> Prelude.perm Direct.abstract
      end
    module RowVectorPerm :
      sig
        type flip_rep = int * int
        type perm_rep = int array
        type ira = int Direct.abstract
        type fra = flip_rep Direct.abstract
        type pra = perm_rep Direct.abstract
        val add :
          (int * int) Direct.abstract ->
          int array Direct.abstract -> int array Direct.abstract
        val empty : int Direct.abstract -> int array Direct.abstract
        val rowrep :
          'a Direct.abstract ->
          'b Direct.abstract -> ('a * 'b) Direct.abstract
        val colrep :
          'a Direct.abstract ->
          'b Direct.abstract -> ('a * 'b) Direct.abstract
      end
    module type TRACKPIVOT =
      sig
        type perm_rep
        type ira = int Direct.abstract
        type fra
        type pra
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TPivot of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> `TPivot of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
        val rowrep : ira -> ira -> fra
        val colrep : ira -> ira -> fra
        val decl :
          int Direct.abstract ->
          < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
        val add :
          fra ->
          (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit) omonad
        val fin :
          unit ->
          (< answer : 'a; state : [> `TPivot of lstate ]; .. >, perm_rep) lm
      end
    module PivotCommon :
      functor (PK : PIVOTKIND) ->
        sig
          type perm_rep = PK.perm_rep
          type ira = PK.ira
          type fra = PK.fra
          type pra = PK.pra
          type lstate = PK.perm_rep ref Direct.abstract
          type 'a pc_constraint = unit
            constraint 'a = < state : [> `TPivot of lstate ]; .. >
          type ('a, 'v) lm = ('a, 'v) cmonad
            constraint 'a =
              < answer : 'b; state : [> `TPivot of lstate ]; .. >
          type 'a nm =
              (< answer : 'b Direct.abstract; state : 'c list >, unit)
              StateCPSMonad.monad
            constraint 'a =
              < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
          val rowrep : PK.ira -> PK.ira -> PK.fra
          val colrep : PK.ira -> PK.ira -> PK.fra
          val ip :
            ('a -> [> `TPivot of 'a ]) * ([> `TPivot of 'b ] -> 'b option) *
            string
        end
    module KeepPivot :
      functor (PK : PIVOTKIND) ->
        sig
          type perm_rep = PK.perm_rep
          type ira = PK.ira
          type fra = PK.fra
          type pra = PK.pra
          type lstate = PK.perm_rep ref Direct.abstract
          type 'a pc_constraint = unit
            constraint 'a = < state : [> `TPivot of lstate ]; .. >
          type ('a, 'v) lm = ('a, 'v) cmonad
            constraint 'a =
              < answer : 'b; state : [> `TPivot of lstate ]; .. >
          type 'a nm =
              (< answer : 'b Direct.abstract; state : 'c list >, unit)
              StateCPSMonad.monad
            constraint 'a =
              < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
          val rowrep : PK.ira -> PK.ira -> PK.fra
          val colrep : PK.ira -> PK.ira -> PK.fra
          val ip :
            ('a -> [> `TPivot of 'a ]) * ([> `TPivot of 'b ] -> 'b option) *
            string
          val decl :
            PK.ira ->
            (< answer : 'a Direct.abstract;
               state : [> `TPivot of PK.perm_rep ref Direct.abstract ] list;
               .. >,
             unit)
            StateCPSMonad.monad
          val add :
            PK.fra ->
            (< answer : 'a;
               state : [> `TPivot of PK.perm_rep ref Direct.abstract ] list;
               .. >,
             unit Direct.abstract option)
            StateCPSMonad.monad
          val fin :
            unit ->
            (< answer : 'a;
               state : [> `TPivot of 'b ref Direct.abstract ] list; .. >,
             'b Direct.abstract)
            StateCPSMonad.monad
        end
    module DiscardPivot :
      sig
        type perm_rep = PermList.perm_rep
        type ira = PermList.ira
        type fra = PermList.fra
        type pra = PermList.pra
        type lstate = PermList.perm_rep ref Direct.abstract
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TPivot of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> `TPivot of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
        val rowrep : PermList.ira -> PermList.ira -> PermList.fra
        val colrep : PermList.ira -> PermList.ira -> PermList.fra
        val ip :
          ('a -> [> `TPivot of 'a ]) * ([> `TPivot of 'b ] -> 'b option) *
          string
        val decl :
          'a -> (< answer : 'b; state : 'c; .. >, unit) StateCPSMonad.monad
        val add :
          'a ->
          (< answer : 'b; state : 'c; .. >, 'd option) StateCPSMonad.monad
        val fin : unit -> 'a
      end
    module GenLA :
      functor (C : D.CONTAINER2D) ->
        sig
          type wmatrix =
            Ge.LAMake(Direct).GenLA(C).wmatrix = {
            matrix : C.vc;
            numrow : int Direct.abstract;
            numcol : int Direct.abstract;
          }
          type curpos =
            Ge.LAMake(Direct).GenLA(C).curpos = {
            rowpos : int Direct.abstract;
            colpos : int Direct.abstract;
          }
          type curposval =
            Ge.LAMake(Direct).GenLA(C).curposval = {
            p : curpos;
            curval : C.Dom.v Direct.abstract;
          }
          module type DETERMINANT =
            sig
              type tdet = C.Dom.v ref
              type lstate
              type 'a pc_constraint = unit
                constraint 'a = < state : [> `TDet of lstate ]; .. >
              type ('a, 'v) lm = ('a, 'v) cmonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type ('a, 'v) om = ('a, 'v) omonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type 'a nm =
                  (< answer : 'b Direct.abstract; state : 'c list >, unit)
                  StateCPSMonad.monad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
              val decl :
                unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
              val upd_sign :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
              val zero_sign :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val acc_magn :
                C.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val get_magn :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
              val set_magn :
                C.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val fin :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, C.Dom.v)
                lm
            end
          module type LOWER =
            sig
              type lstate = C.contr Direct.abstract
              type ('a, 'v) lm = ('a, 'v) cmonad
                constraint 'a =
                  < answer : 'b; state : [> `TLower of lstate ]; .. >
              val decl :
                C.contr Direct.abstract ->
                (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                 C.contr)
                lm
              val updt :
                C.vc ->
                int Direct.abstract ->
                int Direct.abstract ->
                C.vo ->
                C.Dom.vc ->
                (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                lm option
              val fin :
                unit ->
                (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                 C.contr)
                lm
              val wants_pack : bool
            end
          module type PIVOT =
            functor (D : DETERMINANT) (P : TRACKPIVOT) (L : LOWER) ->
              sig
                val findpivot :
                  wmatrix ->
                  curpos ->
                  (< answer : 'a;
                     state : [> `TDet of D.lstate | `TPivot of P.lstate ];
                     .. >,
                   C.Dom.v option)
                  cmonad
              end
          module NoDet :
            sig
              type tdet = C.Dom.v ref
              type lstate = Ge.LAMake(Direct).GenLA(C).NoDet.lstate
              type 'a pc_constraint = unit
                constraint 'a = < state : [> `TDet of lstate ]; .. >
              type ('a, 'v) lm = ('a, 'v) cmonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type ('a, 'v) om = ('a, 'v) omonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type 'a nm =
                  (< answer : 'b Direct.abstract; state : 'c list >, unit)
                  StateCPSMonad.monad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
              val decl :
                unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
              val upd_sign :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
              val zero_sign :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val acc_magn :
                C.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val get_magn :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
              val set_magn :
                C.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val fin :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, C.Dom.v)
                lm
            end
          module AbstractDet :
            sig
              type tdet = C.Dom.v ref
              type lstate = Ge.LAMake(Direct).GenLA(C).AbstractDet.lstate
              type 'a pc_constraint = unit
                constraint 'a = < state : [> `TDet of lstate ]; .. >
              type ('a, 'v) lm = ('a, 'v) cmonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type ('a, 'v) om = ('a, 'v) omonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type 'a nm =
                  (< answer : 'b Direct.abstract; state : 'c list >, unit)
                  StateCPSMonad.monad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
              val decl :
                unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
              val upd_sign :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
              val zero_sign :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val acc_magn :
                C.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val get_magn :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
              val set_magn :
                C.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val fin :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, C.Dom.v)
                lm
            end
          module type UPDATE =
            functor (D : DETERMINANT) ->
              sig
                type in_val = C.Dom.vc
                val update :
                  in_val ->
                  in_val ->
                  in_val ->
                  in_val ->
                  (in_val -> unit Direct.abstract) ->
                  C.Dom.v ref Direct.abstract ->
                  (< answer : 'a; state : 'b; .. >, unit) cmonad
                val update_det :
                  in_val ->
                  (< answer : 'a; state : [> `TDet of D.lstate ]; .. >, unit)
                  D.lm
                val upd_kind : Ge.update_kind
              end
          module GE :
            sig
              module DivisionUpdate :
                functor (Det : DETERMINANT) ->
                  sig
                    type in_val = C.Dom.vc
                    val update :
                      C.Dom.vc ->
                      C.Dom.vc ->
                      C.Dom.vc ->
                      C.Dom.vc ->
                      (C.Dom.vc -> 'a) ->
                      'b ->
                      (< answer : 'c; state : 'd; .. >, 'a)
                      StateCPSMonad.monad
                    val update_det :
                      C.Dom.v Direct.abstract ->
                      (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >,
                       unit)
                      Det.lm
                    val upd_kind : Ge.update_kind
                  end
              module FractionFreeUpdate :
                functor (Det : DETERMINANT) ->
                  sig
                    type in_val = C.Dom.vc
                    val update :
                      C.Dom.vc ->
                      C.Dom.vc ->
                      C.Dom.vc ->
                      C.Dom.vc ->
                      (C.Dom.vc -> 'a) ->
                      C.Dom.v ref Direct.abstract ->
                      (< answer : 'b; state : 'c; .. >, 'a)
                      StateCPSMonad.monad
                    val update_det :
                      C.Dom.v Direct.abstract ->
                      (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >,
                       unit)
                      Det.lm
                    val upd_kind : Ge.update_kind
                  end
              module TrackLower :
                sig
                  type lstate = C.contr Direct.abstract
                  type ('a, 'v) lm = ('a, 'v) cmonad
                    constraint 'a =
                      < answer : 'b; state : [> `TLower of lstate ]; .. >
                  val ip :
                    ('a -> [> `TLower of 'a ]) *
                    ([> `TLower of 'b ] -> 'b option) * string
                end
              module SeparateLower :
                sig
                  type lstate = C.contr Direct.abstract
                  type ('a, 'v) lm = ('a, 'v) cmonad
                    constraint 'a =
                      < answer : 'b; state : [> `TLower of lstate ]; .. >
                  val ip :
                    ('a -> [> `TLower of 'a ]) *
                    ([> `TLower of 'b ] -> 'b option) * string
                  val decl :
                    'a Direct.abstract ->
                    (< answer : 'b Direct.abstract;
                       state : [> `TLower of 'a Direct.abstract ] list; .. >,
                     'a Direct.abstract)
                    StateCPSMonad.monad
                  val updt :
                    C.vc ->
                    int Direct.abstract ->
                    int Direct.abstract ->
                    C.vo ->
                    C.vo ->
                    (< answer : 'a; state : [> `TLower of C.vc ] list; .. >,
                     unit Direct.abstract)
                    StateCPSMonad.monad option
                  val fin :
                    unit ->
                    (< answer : 'a; state : [> `TLower of 'b ] list; .. >,
                     'b)
                    StateCPSMonad.monad
                  val wants_pack : bool
                end
              module PackedLower :
                sig
                  type lstate = C.contr Direct.abstract
                  type ('a, 'v) lm = ('a, 'v) cmonad
                    constraint 'a =
                      < answer : 'b; state : [> `TLower of lstate ]; .. >
                  val ip :
                    ('a -> [> `TLower of 'a ]) *
                    ([> `TLower of 'b ] -> 'b option) * string
                  val decl :
                    'a ->
                    (< answer : 'b; state : [> `TLower of 'a ] list; .. >,
                     'a)
                    StateCPSMonad.monad
                  val updt : 'a -> 'b -> 'c -> 'd -> 'e -> 'f option
                  val fin :
                    unit ->
                    (< answer : 'a; state : [> `TLower of 'b ] list; .. >,
                     'b)
                    StateCPSMonad.monad
                  val wants_pack : bool
                end
              module NoLower :
                sig
                  type lstate = C.contr Direct.abstract
                  type ('a, 'v) lm = ('a, 'v) cmonad
                    constraint 'a =
                      < answer : 'b; state : [> `TLower of lstate ]; .. >
                  val ip :
                    ('a -> [> `TLower of 'a ]) *
                    ([> `TLower of 'b ] -> 'b option) * string
                  val decl :
                    'a ->
                    (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
                  val updt :
                    C.vc ->
                    int Direct.abstract ->
                    int Direct.abstract ->
                    C.vo ->
                    'a ->
                    (< answer : 'b; state : 'c; .. >, unit Direct.abstract)
                    StateCPSMonad.monad option
                  val fin : unit -> 'a
                  val wants_pack : bool
                end
              module type INPUT =
                sig
                  type inp
                  val get_input :
                    inp Direct.abstract ->
                    (< answer : 'a; state : 'b; .. >,
                     C.contr Direct.abstract * int Direct.abstract * bool)
                    StateCPSMonad.monad
                end
              module InpJustMatrix :
                sig
                  type inp = C.contr
                  val get_input :
                    C.vc ->
                    (< answer : 'a; state : 'b; .. >,
                     C.vc * int Direct.abstract * bool)
                    StateCPSMonad.monad
                end
              module InpMatrixMargin :
                sig
                  type inp = C.contr * int
                  val get_input :
                    ('a * 'b) Direct.abstract ->
                    (< answer : 'c; state : 'd; .. >,
                     'a Direct.abstract * 'b Direct.abstract * bool)
                    StateCPSMonad.monad
                end
              module RowPivot :
                functor (Det : DETERMINANT) (P : TRACKPIVOT) (L : LOWER) ->
                  sig
                    val optim : 'a -> 'a option
                    val findpivot :
                      wmatrix ->
                      curpos ->
                      (< answer : 'a Direct.abstract;
                         state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                                 list;
                         .. >,
                       C.Dom.v option Direct.abstract)
                      StateCPSMonad.monad
                  end
              module FullPivot :
                functor (Det : DETERMINANT) (P : TRACKPIVOT) (L : LOWER) ->
                  sig
                    val optim : 'a -> 'a option
                    val findpivot :
                      wmatrix ->
                      curpos ->
                      (< answer : 'a Direct.abstract;
                         state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                                 list;
                         .. >,
                       C.Dom.v option Direct.abstract)
                      StateCPSMonad.monad
                  end
              module NoPivot :
                functor (Det : DETERMINANT) (P : TRACKPIVOT) (L : LOWER) ->
                  sig
                    val findpivot :
                      wmatrix ->
                      curpos ->
                      (< answer : 'a; state : 'b; .. >,
                       C.Dom.v option Direct.abstract)
                      StateCPSMonad.monad
                  end
              module type OUTPUTDEP =
                sig module PivotRep : PIVOTKIND module Det : DETERMINANT end
              module OutJustMatrix :
                functor (OD : OUTPUTDEP) ->
                  sig
                    module IF :
                      sig
                        module R = NoRank
                        module P = DiscardPivot
                        module L = NoLower
                      end
                    type res = C.contr
                    val make_result :
                      wmatrix ->
                      (< answer : 'a; state : 'b; .. >, C.vc)
                      StateCPSMonad.monad
                  end
              module OutDet :
                functor (OD : OUTPUTDEP) ->
                  sig
                    module IF :
                      sig
                        module R = NoRank
                        module P = DiscardPivot
                        module L = NoLower
                      end
                    type res = C.contr * C.Dom.v
                    val make_result :
                      wmatrix ->
                      (< answer : 'a Direct.abstract;
                         state : [> `TDet of OD.Det.lstate ] list; .. >,
                       (C.contr * C.Dom.v) Direct.abstract)
                      StateCPSMonad.monad
                  end
              module OutRank :
                functor (OD : OUTPUTDEP) ->
                  sig
                    module IF :
                      sig
                        module R = Rank
                        module P = DiscardPivot
                        module L = NoLower
                      end
                    type res = C.contr * int
                    val make_result :
                      wmatrix ->
                      (< answer : 'a;
                         state : [> `TRan of 'b ref Direct.abstract ] list;
                         .. >,
                       (C.contr * 'b) Direct.abstract)
                      StateCPSMonad.monad
                  end
              module OutDetRank :
                functor (OD : OUTPUTDEP) ->
                  sig
                    module IF :
                      sig
                        module R = Rank
                        module P = DiscardPivot
                        module L = NoLower
                      end
                    type res = C.contr * C.Dom.v * int
                    val make_result :
                      wmatrix ->
                      (< answer : 'a Direct.abstract;
                         state : [> `TDet of OD.Det.lstate
                                  | `TRan of 'b ref Direct.abstract ]
                                 list;
                         .. >,
                       (C.contr * C.Dom.v * 'b) Direct.abstract)
                      StateCPSMonad.monad
                  end
              module OutDetRankPivot :
                functor (OD : OUTPUTDEP) ->
                  sig
                    module IF :
                      sig
                        module R = Rank
                        module P :
                          sig
                            type perm_rep = OD.PivotRep.perm_rep
                            type ira = OD.PivotRep.ira
                            type fra = OD.PivotRep.fra
                            type pra = OD.PivotRep.pra
                            type lstate =
                                OD.PivotRep.perm_rep ref Direct.abstract
                            type 'a pc_constraint = unit
                              constraint 'a =
                                < state : [> `TPivot of lstate ]; .. >
                            type ('a, 'v) lm = ('a, 'v) cmonad
                              constraint 'a =
                                < answer : 'b;
                                  state : [> `TPivot of lstate ]; .. >
                            type 'a nm =
                                (< answer : 'b Direct.abstract;
                                   state : 'c list >,
                                 unit)
                                StateCPSMonad.monad
                              constraint 'a =
                                < answer : 'b;
                                  state : [> `TPivot of lstate ] as 'c; .. >
                            val rowrep :
                              OD.PivotRep.ira ->
                              OD.PivotRep.ira -> OD.PivotRep.fra
                            val colrep :
                              OD.PivotRep.ira ->
                              OD.PivotRep.ira -> OD.PivotRep.fra
                            val ip :
                              ('a -> [> `TPivot of 'a ]) *
                              ([> `TPivot of 'b ] -> 'b option) * string
                            val decl :
                              OD.PivotRep.ira ->
                              (< answer : 'a Direct.abstract;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Direct.abstract ]
                                         list;
                                 .. >,
                               unit)
                              StateCPSMonad.monad
                            val add :
                              OD.PivotRep.fra ->
                              (< answer : 'a;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Direct.abstract ]
                                         list;
                                 .. >,
                               unit Direct.abstract option)
                              StateCPSMonad.monad
                            val fin :
                              unit ->
                              (< answer : 'a;
                                 state : [> `TPivot of 'b ref Direct.abstract ]
                                         list;
                                 .. >,
                               'b Direct.abstract)
                              StateCPSMonad.monad
                          end
                        module L = NoLower
                      end
                    type res = C.contr * C.Dom.v * int * IF.P.perm_rep
                    val make_result :
                      wmatrix ->
                      (< answer : 'a Direct.abstract;
                         state : [> `TDet of OD.Det.lstate
                                  | `TPivot of 'b ref Direct.abstract
                                  | `TRan of 'c ref Direct.abstract ]
                                 list;
                         .. >,
                       (C.contr * C.Dom.v * 'c * 'b) Direct.abstract)
                      StateCPSMonad.monad
                  end
              module Out_L_U :
                functor (OD : OUTPUTDEP) ->
                  sig
                    module IF :
                      sig
                        module R = NoRank
                        module P :
                          sig
                            type perm_rep = OD.PivotRep.perm_rep
                            type ira = OD.PivotRep.ira
                            type fra = OD.PivotRep.fra
                            type pra = OD.PivotRep.pra
                            type lstate =
                                OD.PivotRep.perm_rep ref Direct.abstract
                            type 'a pc_constraint = unit
                              constraint 'a =
                                < state : [> `TPivot of lstate ]; .. >
                            type ('a, 'v) lm = ('a, 'v) cmonad
                              constraint 'a =
                                < answer : 'b;
                                  state : [> `TPivot of lstate ]; .. >
                            type 'a nm =
                                (< answer : 'b Direct.abstract;
                                   state : 'c list >,
                                 unit)
                                StateCPSMonad.monad
                              constraint 'a =
                                < answer : 'b;
                                  state : [> `TPivot of lstate ] as 'c; .. >
                            val rowrep :
                              OD.PivotRep.ira ->
                              OD.PivotRep.ira -> OD.PivotRep.fra
                            val colrep :
                              OD.PivotRep.ira ->
                              OD.PivotRep.ira -> OD.PivotRep.fra
                            val ip :
                              ('a -> [> `TPivot of 'a ]) *
                              ([> `TPivot of 'b ] -> 'b option) * string
                            val decl :
                              OD.PivotRep.ira ->
                              (< answer : 'a Direct.abstract;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Direct.abstract ]
                                         list;
                                 .. >,
                               unit)
                              StateCPSMonad.monad
                            val add :
                              OD.PivotRep.fra ->
                              (< answer : 'a;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Direct.abstract ]
                                         list;
                                 .. >,
                               unit Direct.abstract option)
                              StateCPSMonad.monad
                            val fin :
                              unit ->
                              (< answer : 'a;
                                 state : [> `TPivot of 'b ref Direct.abstract ]
                                         list;
                                 .. >,
                               'b Direct.abstract)
                              StateCPSMonad.monad
                          end
                        module L = SeparateLower
                      end
                    type res = C.contr * C.contr * IF.P.perm_rep
                    val make_result :
                      wmatrix ->
                      (< answer : 'a;
                         state : [> `TLower of 'b Direct.abstract
                                  | `TPivot of 'c ref Direct.abstract ]
                                 list;
                         .. >,
                       (C.contr * 'b * 'c) Direct.abstract)
                      StateCPSMonad.monad
                  end
              module Out_LU_Packed :
                functor (OD : OUTPUTDEP) ->
                  sig
                    module IF :
                      sig
                        module R = NoRank
                        module P :
                          sig
                            type perm_rep = OD.PivotRep.perm_rep
                            type ira = OD.PivotRep.ira
                            type fra = OD.PivotRep.fra
                            type pra = OD.PivotRep.pra
                            type lstate =
                                OD.PivotRep.perm_rep ref Direct.abstract
                            type 'a pc_constraint = unit
                              constraint 'a =
                                < state : [> `TPivot of lstate ]; .. >
                            type ('a, 'v) lm = ('a, 'v) cmonad
                              constraint 'a =
                                < answer : 'b;
                                  state : [> `TPivot of lstate ]; .. >
                            type 'a nm =
                                (< answer : 'b Direct.abstract;
                                   state : 'c list >,
                                 unit)
                                StateCPSMonad.monad
                              constraint 'a =
                                < answer : 'b;
                                  state : [> `TPivot of lstate ] as 'c; .. >
                            val rowrep :
                              OD.PivotRep.ira ->
                              OD.PivotRep.ira -> OD.PivotRep.fra
                            val colrep :
                              OD.PivotRep.ira ->
                              OD.PivotRep.ira -> OD.PivotRep.fra
                            val ip :
                              ('a -> [> `TPivot of 'a ]) *
                              ([> `TPivot of 'b ] -> 'b option) * string
                            val decl :
                              OD.PivotRep.ira ->
                              (< answer : 'a Direct.abstract;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Direct.abstract ]
                                         list;
                                 .. >,
                               unit)
                              StateCPSMonad.monad
                            val add :
                              OD.PivotRep.fra ->
                              (< answer : 'a;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Direct.abstract ]
                                         list;
                                 .. >,
                               unit Direct.abstract option)
                              StateCPSMonad.monad
                            val fin :
                              unit ->
                              (< answer : 'a;
                                 state : [> `TPivot of 'b ref Direct.abstract ]
                                         list;
                                 .. >,
                               'b Direct.abstract)
                              StateCPSMonad.monad
                          end
                        module L = PackedLower
                      end
                    type res = C.contr * IF.P.perm_rep
                    val make_result :
                      'a ->
                      (< answer : 'b;
                         state : [> `TLower of 'c Direct.abstract
                                  | `TPivot of 'd ref Direct.abstract ]
                                 list;
                         .. >,
                       ('c * 'd) Direct.abstract)
                      StateCPSMonad.monad
                  end
              module type INTERNAL_FEATURES =
                sig
                  module R : TrackRank.RANK
                  module P : TRACKPIVOT
                  module L : LOWER
                end
              module type OUTPUT =
                functor (OD : OUTPUTDEP) ->
                  sig
                    module IF : INTERNAL_FEATURES
                    type res
                    val make_result :
                      wmatrix ->
                      (< answer : 'a;
                         state : [> `TDet of OD.Det.lstate
                                  | `TLower of IF.L.lstate
                                  | `TPivot of IF.P.lstate
                                  | `TRan of TrackRank.lstate ];
                         .. >,
                       res)
                      cmonad
                  end
              module type FEATURES =
                sig
                  module Det : DETERMINANT
                  module PivotF : PIVOT
                  module PivotRep : PIVOTKIND
                  module Update : UPDATE
                  module Input : INPUT
                  module Output : OUTPUT
                end
              module GenGE :
                functor (F : FEATURES) ->
                  sig
                    module O :
                      sig
                        module IF :
                          sig
                            module R :
                              sig
                                type tag_lstate = TrackRank.tag_lstate_
                                val decl :
                                  unit ->
                                  (< answer : 'a;
                                     state : [> TrackRank.tag_lstate ]; .. >,
                                   int ref)
                                  TrackRank.lm
                                val succ :
                                  unit ->
                                  (< answer : 'a;
                                     state : [> TrackRank.tag_lstate ]; .. >,
                                   unit)
                                  TrackRank.lm
                                val fin :
                                  unit ->
                                  (< answer : 'a;
                                     state : [> TrackRank.tag_lstate ]; .. >,
                                   int)
                                  TrackRank.lm
                              end
                            module P :
                              sig
                                type perm_rep = F.Output(F).IF.P.perm_rep
                                type ira = int Direct.abstract
                                type fra = F.Output(F).IF.P.fra
                                type pra = F.Output(F).IF.P.pra
                                type lstate = F.Output(F).IF.P.lstate
                                type 'a pc_constraint = unit
                                  constraint 'a =
                                    < state : [> `TPivot of lstate ]; .. >
                                type ('a, 'v) lm = ('a, 'v) cmonad
                                  constraint 'a =
                                    < answer : 'b;
                                      state : [> `TPivot of lstate ]; .. >
                                type 'a nm =
                                    (< answer : 'b Direct.abstract;
                                       state : 'c list >,
                                     unit)
                                    StateCPSMonad.monad
                                  constraint 'a =
                                    < answer : 'b;
                                      state : [> `TPivot of lstate ] as 'c;
                                      .. >
                                val rowrep : ira -> ira -> fra
                                val colrep : ira -> ira -> fra
                                val decl :
                                  int Direct.abstract ->
                                  < answer : 'a;
                                    state : [> `TPivot of lstate ]; .. >
                                  nm
                                val add :
                                  fra ->
                                  (< answer : 'a;
                                     state : [> `TPivot of lstate ]; .. >,
                                   unit)
                                  omonad
                                val fin :
                                  unit ->
                                  (< answer : 'a;
                                     state : [> `TPivot of lstate ]; .. >,
                                   perm_rep)
                                  lm
                              end
                            module L :
                              sig
                                type lstate = C.contr Direct.abstract
                                type ('a, 'v) lm = ('a, 'v) cmonad
                                  constraint 'a =
                                    < answer : 'b;
                                      state : [> `TLower of lstate ]; .. >
                                val decl :
                                  C.contr Direct.abstract ->
                                  (< answer : 'a;
                                     state : [> `TLower of lstate ]; .. >,
                                   C.contr)
                                  lm
                                val updt :
                                  C.vc ->
                                  int Direct.abstract ->
                                  int Direct.abstract ->
                                  C.vo ->
                                  C.Dom.vc ->
                                  (< answer : 'a;
                                     state : [> `TLower of lstate ]; .. >,
                                   unit)
                                  lm option
                                val fin :
                                  unit ->
                                  (< answer : 'a;
                                     state : [> `TLower of lstate ]; .. >,
                                   C.contr)
                                  lm
                                val wants_pack : bool
                              end
                          end
                        type res = F.Output(F).res
                        val make_result :
                          wmatrix ->
                          (< answer : 'a;
                             state : [> `TDet of F.Det.lstate
                                      | `TLower of IF.L.lstate
                                      | `TPivot of IF.P.lstate
                                      | `TRan of TrackRank.lstate ];
                             .. >,
                           res)
                          cmonad
                      end
                    val wants_pack : bool
                    val can_pack : bool
                    val zerobelow :
                      wmatrix ->
                      curposval ->
                      ([> `TDet of F.Det.lstate
                        | `TLower of C.contr Direct.abstract ]
                       as 'a)
                      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                    val init :
                      F.Input.inp Direct.abstract ->
                      (< answer : 'a Direct.abstract;
                         state : [> `TDet of F.Det.lstate
                                  | `TLower of C.contr Direct.abstract
                                  | `TPivot of F.Output(F).IF.P.lstate
                                  | `TRan of TrackRank.lstate ]
                                 list;
                         .. >,
                       wmatrix * int ref Direct.abstract *
                       int ref Direct.abstract * int Direct.abstract)
                      StateCPSMonad.monad
                    val forward_elim :
                      wmatrix * int ref Direct.abstract *
                      int ref Direct.abstract * int Direct.abstract ->
                      ([> `TDet of F.Det.lstate
                        | `TLower of C.contr Direct.abstract
                        | `TPivot of F.Output(F).IF.P.lstate
                        | `TRan of TrackRank.lstate ]
                       as 'a)
                      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                    val gen :
                      F.Input.inp Direct.abstract ->
                      (< answer : 'a Direct.abstract;
                         state : [> `TDet of F.Det.lstate
                                  | `TLower of O.IF.L.lstate
                                  | `TPivot of O.IF.P.lstate
                                  | `TRan of TrackRank.lstate ]
                                 list;
                         .. >,
                       O.res Direct.abstract)
                      StateCPSMonad.monad
                  end
            end
          module Solve :
            sig
              module type INPUT =
                sig
                  type inp
                  type rhs = C.contr
                  val get_input :
                    inp Direct.abstract ->
                    (< answer : 'a; state : 'b; .. >,
                     C.contr Direct.abstract * rhs Direct.abstract)
                    StateCPSMonad.monad
                end
              module InpMatrixVector :
                sig
                  type inp = C.contr * C.contr
                  type rhs = C.contr
                  val get_input :
                    ('a * 'b) Direct.abstract ->
                    (< answer : 'c Direct.abstract; state : 'd; .. >,
                     'a Direct.abstract * 'b Direct.abstract)
                    StateCPSMonad.monad
                end
              module type OUTPUT =
                sig
                  type res
                  val make_result :
                    C.contr Direct.abstract ->
                    C.contr Direct.abstract ->
                    int Direct.abstract ->
                    int Direct.abstract ->
                    int Direct.abstract ->
                    (< answer : 'a; state : 'b; .. >, res) cmonad
                end
              module OutJustAnswer :
                sig
                  type res = C.contr
                  val make_result :
                    C.vc ->
                    C.vc ->
                    int Direct.abstract ->
                    int Direct.abstract ->
                    int Direct.abstract ->
                    'a -> ('a -> C.contr Direct.abstract -> 'b) -> 'b
                end
              module type FEATURES =
                sig
                  module Det : DETERMINANT
                  module PivotF : PIVOT
                  module Input : INPUT
                  module Output : OUTPUT
                end
              module GenSolve :
                functor (F : FEATURES) ->
                  sig
                    module GE' :
                      sig
                        module O :
                          sig
                            module IF :
                              sig
                                module R :
                                  sig
                                    type tag_lstate = TrackRank.tag_lstate_
                                    val decl :
                                      unit ->
                                      (< answer : 'a;
                                         state : [> TrackRank.tag_lstate ];
                                         .. >,
                                       int ref)
                                      TrackRank.lm
                                    val succ :
                                      unit ->
                                      (< answer : 'a;
                                         state : [> TrackRank.tag_lstate ];
                                         .. >,
                                       unit)
                                      TrackRank.lm
                                    val fin :
                                      unit ->
                                      (< answer : 'a;
                                         state : [> TrackRank.tag_lstate ];
                                         .. >,
                                       int)
                                      TrackRank.lm
                                  end
                                module P :
                                  sig
                                    type perm_rep = PermList.perm_rep
                                    type ira = int Direct.abstract
                                    type fra = PermList.fra
                                    type pra = PermList.pra
                                    type lstate =
                                        PermList.perm_rep ref Direct.abstract
                                    type 'a pc_constraint = unit
                                      constraint 'a =
                                        < state : [> `TPivot of lstate ];
                                          .. >
                                    type ('a, 'v) lm = ('a, 'v) cmonad
                                      constraint 'a =
                                        < answer : 'b;
                                          state : [> `TPivot of lstate ];
                                          .. >
                                    type 'a nm =
                                        (< answer : 'b Direct.abstract;
                                           state : 'c list >,
                                         unit)
                                        StateCPSMonad.monad
                                      constraint 'a =
                                        < answer : 'b;
                                          state : [> `TPivot of lstate ]
                                                  as 'c;
                                          .. >
                                    val rowrep : ira -> ira -> fra
                                    val colrep : ira -> ira -> fra
                                    val decl :
                                      int Direct.abstract ->
                                      < answer : 'a;
                                        state : [> `TPivot of lstate ]; .. >
                                      nm
                                    val add :
                                      fra ->
                                      (< answer : 'a;
                                         state : [> `TPivot of lstate ]; .. >,
                                       unit)
                                      omonad
                                    val fin :
                                      unit ->
                                      (< answer : 'a;
                                         state : [> `TPivot of lstate ]; .. >,
                                       perm_rep)
                                      lm
                                  end
                                module L :
                                  sig
                                    type lstate = C.contr Direct.abstract
                                    type ('a, 'v) lm = ('a, 'v) cmonad
                                      constraint 'a =
                                        < answer : 'b;
                                          state : [> `TLower of lstate ];
                                          .. >
                                    val decl :
                                      C.contr Direct.abstract ->
                                      (< answer : 'a;
                                         state : [> `TLower of lstate ]; .. >,
                                       C.contr)
                                      lm
                                    val updt :
                                      C.vc ->
                                      int Direct.abstract ->
                                      int Direct.abstract ->
                                      C.vo ->
                                      C.Dom.vc ->
                                      (< answer : 'a;
                                         state : [> `TLower of lstate ]; .. >,
                                       unit)
                                      lm option
                                    val fin :
                                      unit ->
                                      (< answer : 'a;
                                         state : [> `TLower of lstate ]; .. >,
                                       C.contr)
                                      lm
                                    val wants_pack : bool
                                  end
                              end
                            type res = C.contr
                            val make_result :
                              wmatrix ->
                              (< answer : 'a;
                                 state : [> `TDet of F.Det.lstate
                                          | `TLower of IF.L.lstate
                                          | `TPivot of IF.P.lstate
                                          | `TRan of TrackRank.lstate ];
                                 .. >,
                               res)
                              cmonad
                          end
                        val wants_pack : bool
                        val can_pack : bool
                        val zerobelow :
                          wmatrix ->
                          curposval ->
                          ([> `TDet of F.Det.lstate
                            | `TLower of C.contr Direct.abstract ]
                           as 'a)
                          list ->
                          ('a list -> unit Direct.abstract -> 'b) -> 'b
                        val init :
                          (C.contr * int) Direct.abstract ->
                          (< answer : 'a Direct.abstract;
                             state : [> `TDet of F.Det.lstate
                                      | `TLower of C.contr Direct.abstract
                                      | `TPivot of
                                          PermList.perm_rep ref
                                          Direct.abstract
                                      | `TRan of TrackRank.lstate ]
                                     list;
                             .. >,
                           wmatrix * int ref Direct.abstract *
                           int ref Direct.abstract * int Direct.abstract)
                          StateCPSMonad.monad
                        val forward_elim :
                          wmatrix * int ref Direct.abstract *
                          int ref Direct.abstract * int Direct.abstract ->
                          ([> `TDet of F.Det.lstate
                            | `TLower of C.contr Direct.abstract
                            | `TPivot of
                                PermList.perm_rep ref Direct.abstract
                            | `TRan of TrackRank.lstate ]
                           as 'a)
                          list ->
                          ('a list -> unit Direct.abstract -> 'b) -> 'b
                        val gen :
                          (C.contr * int) Direct.abstract ->
                          (< answer : 'a Direct.abstract;
                             state : [> `TDet of F.Det.lstate
                                      | `TLower of O.IF.L.lstate
                                      | `TPivot of O.IF.P.lstate
                                      | `TRan of TrackRank.lstate ]
                                     list;
                             .. >,
                           O.res Direct.abstract)
                          StateCPSMonad.monad
                      end
                    val init :
                      F.Input.inp Direct.abstract ->
                      (< answer : 'a; state : 'b; .. >,
                       C.contr Direct.abstract * F.Input.rhs Direct.abstract)
                      StateCPSMonad.monad
                    val back_elim :
                      C.vc ->
                      int Direct.abstract ->
                      int Direct.abstract ->
                      'a -> ('a -> C.contr Direct.abstract -> 'b) -> 'b
                    val gen :
                      F.Input.inp Direct.abstract ->
                      (< answer : 'a Direct.abstract;
                         state : [> `TDet of F.Det.lstate
                                  | `TLower of GE'.O.IF.L.lstate
                                  | `TPivot of GE'.O.IF.P.lstate
                                  | `TRan of TrackRank.lstate ]
                                 list;
                         .. >,
                       F.Output.res Direct.abstract)
                      StateCPSMonad.monad
                  end
            end
        end
  end
val instantiate :
  ((unit -> 'a) -> 'b list -> ('c -> 'd -> 'd) -> unit -> 'e) -> 'a -> 'e =
  <fun>
#   type 'b pr = { pf : 'b; }
# val runit : 'a pr -> 'a = <fun>
#   * * * * * * * * *     module Z3 :
  sig
    type v = int
    val kind : Domains_sig.domain_kind
    val zero : int
    val one : int
    val plus : int -> int -> int
    val times : int -> int -> int
    val minus : int -> int -> int
    val uminus : int -> int
    val extended_gcd : int -> int -> int * int
    val div : int -> int -> int
    val normalizer : 'a option
    val better_than : 'a option
    type vc = v Domains_direct.DirectRep.rep
    val zeroL : unit -> int
    val oneL : unit -> int
    val ( +^ ) : (unit -> int) -> (unit -> int) -> unit -> int
    val ( *^ ) : (unit -> int) -> (unit -> int) -> unit -> int
    val ( -^ ) : (unit -> int) -> (unit -> int) -> unit -> int
    val uminusL : (unit -> int) -> unit -> int
    val divL : (unit -> int) -> (unit -> int) -> unit -> int
    val better_thanL : 'a option
    val normalizerL : 'a option
  end
module Z19 :
  sig
    type v = int
    val kind : Domains_sig.domain_kind
    val zero : int
    val one : int
    val plus : int -> int -> int
    val times : int -> int -> int
    val minus : int -> int -> int
    val uminus : int -> int
    val extended_gcd : int -> int -> int * int
    val div : int -> int -> int
    val normalizer : 'a option
    val better_than : 'a option
    type vc = v Domains_direct.DirectRep.rep
    val zeroL : unit -> int
    val oneL : unit -> int
    val ( +^ ) : (unit -> int) -> (unit -> int) -> unit -> int
    val ( *^ ) : (unit -> int) -> (unit -> int) -> unit -> int
    val ( -^ ) : (unit -> int) -> (unit -> int) -> unit -> int
    val uminusL : (unit -> int) -> unit -> int
    val divL : (unit -> int) -> (unit -> int) -> unit -> int
    val better_thanL : 'a option
    val normalizerL : 'a option
  end
module GAC_F :
  sig
    module Dom :
      sig
        type v = Domains_direct.FloatDomainL.v
        val kind : Domains_sig.domain_kind
        val zero : v
        val one : v
        val plus : v -> v -> v
        val times : v -> v -> v
        val minus : v -> v -> v
        val uminus : v -> v
        val div : v -> v -> v
        val better_than : (v -> v -> bool) option
        val normalizer : (v -> v) option
        type vc = v Domains_direct.DirectRep.rep
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL :
          (vc -> vc -> bool Domains_direct.DirectRep.rep) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v array array
    type vc = contr Domains_direct.DirectRep.rep
    type vo = Dom.v Domains_direct.DirectRep.rep
    val getL :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val dim2 : (unit -> 'a array) -> unit -> int
    val dim1 : (unit -> 'a array array) -> unit -> int
    val mapper :
      (vo -> vo) option ->
      (unit -> Dom.v array array) -> unit -> Dom.v array array
    val copy : (unit -> 'a array array) -> unit -> 'a array array
    val init : (unit -> int) -> (unit -> int) -> unit -> Dom.v array array
    val augment :
      (unit -> 'a array array) ->
      (unit -> int) ->
      (unit -> int) ->
      (unit -> 'a array array) -> (unit -> int) -> unit -> 'a array array
    val identity :
      (unit -> int) -> (unit -> int) -> unit -> Dom.v array array
    val swap_rows_stmt :
      (unit -> 'a array) ->
      'b -> (unit -> int) -> (unit -> int) -> unit -> unit
    val swap_cols_stmt :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> unit -> unit
    val row_head :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val col_head_set :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> (unit -> 'a) -> unit -> unit
  end
module GVC_F :
  sig
    module Dom :
      sig
        type v = Domains_direct.FloatDomainL.v
        val kind : Domains_sig.domain_kind
        val zero : v
        val one : v
        val plus : v -> v -> v
        val times : v -> v -> v
        val minus : v -> v -> v
        val uminus : v -> v
        val div : v -> v -> v
        val better_than : (v -> v -> bool) option
        val normalizer : (v -> v) option
        type vc = v Domains_direct.DirectRep.rep
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL :
          (vc -> vc -> bool Domains_direct.DirectRep.rep) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v Prelude.container2dfromvector
    type vc = contr Domains_direct.DirectRep.rep
    type vo = Dom.v Domains_direct.DirectRep.rep
    val getL :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val dim2 : (unit -> 'a Prelude.container2dfromvector) -> unit -> int
    val dim1 : (unit -> 'a Prelude.container2dfromvector) -> unit -> int
    val mapper :
      ((unit -> 'a) -> unit -> 'a) option ->
      (unit -> 'a Prelude.container2dfromvector) ->
      unit -> 'a Prelude.container2dfromvector
    val copy :
      (unit -> 'a Prelude.container2dfromvector) ->
      unit -> 'a Prelude.container2dfromvector
    val init :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val augment :
      (unit -> Dom.v Prelude.container2dfromvector) ->
      (unit -> int) ->
      (unit -> int) ->
      (unit -> Dom.v Prelude.container2dfromvector) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val identity :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val index_default : (unit -> int) option -> int
    val swap_rows_stmt :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) option -> (unit -> int) -> (unit -> int) -> unit -> unit
    val swap_cols_stmt :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> unit
    val row_head :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val col_head_set :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> (unit -> 'a) -> unit -> unit
  end
module GAC_I :
  sig
    module Dom :
      sig
        type v = Domains_direct.IntegerDomainL.v
        val kind : Domains_sig.domain_kind
        val zero : v
        val one : v
        val plus : v -> v -> v
        val times : v -> v -> v
        val minus : v -> v -> v
        val uminus : v -> v
        val div : v -> v -> v
        val better_than : (v -> v -> bool) option
        val normalizer : (v -> v) option
        type vc = v Domains_direct.DirectRep.rep
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL :
          (vc -> vc -> bool Domains_direct.DirectRep.rep) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v array array
    type vc = contr Domains_direct.DirectRep.rep
    type vo = Dom.v Domains_direct.DirectRep.rep
    val getL :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val dim2 : (unit -> 'a array) -> unit -> int
    val dim1 : (unit -> 'a array array) -> unit -> int
    val mapper :
      (vo -> vo) option ->
      (unit -> Dom.v array array) -> unit -> Dom.v array array
    val copy : (unit -> 'a array array) -> unit -> 'a array array
    val init : (unit -> int) -> (unit -> int) -> unit -> Dom.v array array
    val augment :
      (unit -> 'a array array) ->
      (unit -> int) ->
      (unit -> int) ->
      (unit -> 'a array array) -> (unit -> int) -> unit -> 'a array array
    val identity :
      (unit -> int) -> (unit -> int) -> unit -> Dom.v array array
    val swap_rows_stmt :
      (unit -> 'a array) ->
      'b -> (unit -> int) -> (unit -> int) -> unit -> unit
    val swap_cols_stmt :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> unit -> unit
    val row_head :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val col_head_set :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> (unit -> 'a) -> unit -> unit
  end
module GVC_I :
  sig
    module Dom :
      sig
        type v = Domains_direct.IntegerDomainL.v
        val kind : Domains_sig.domain_kind
        val zero : v
        val one : v
        val plus : v -> v -> v
        val times : v -> v -> v
        val minus : v -> v -> v
        val uminus : v -> v
        val div : v -> v -> v
        val better_than : (v -> v -> bool) option
        val normalizer : (v -> v) option
        type vc = v Domains_direct.DirectRep.rep
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL :
          (vc -> vc -> bool Domains_direct.DirectRep.rep) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v Prelude.container2dfromvector
    type vc = contr Domains_direct.DirectRep.rep
    type vo = Dom.v Domains_direct.DirectRep.rep
    val getL :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val dim2 : (unit -> 'a Prelude.container2dfromvector) -> unit -> int
    val dim1 : (unit -> 'a Prelude.container2dfromvector) -> unit -> int
    val mapper :
      ((unit -> 'a) -> unit -> 'a) option ->
      (unit -> 'a Prelude.container2dfromvector) ->
      unit -> 'a Prelude.container2dfromvector
    val copy :
      (unit -> 'a Prelude.container2dfromvector) ->
      unit -> 'a Prelude.container2dfromvector
    val init :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val augment :
      (unit -> Dom.v Prelude.container2dfromvector) ->
      (unit -> int) ->
      (unit -> int) ->
      (unit -> Dom.v Prelude.container2dfromvector) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val identity :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val index_default : (unit -> int) option -> int
    val swap_rows_stmt :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) option -> (unit -> int) -> (unit -> int) -> unit -> unit
    val swap_cols_stmt :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> unit
    val row_head :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val col_head_set :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> (unit -> 'a) -> unit -> unit
  end
module GAC_R :
  sig
    module Dom :
      sig
        type v = Domains_direct.RationalDomainL.v
        val kind : Domains_sig.domain_kind
        val zero : v
        val one : v
        val plus : v -> v -> v
        val times : v -> v -> v
        val minus : v -> v -> v
        val uminus : v -> v
        val div : v -> v -> v
        val better_than : (v -> v -> bool) option
        val normalizer : (v -> v) option
        type vc = v Domains_direct.DirectRep.rep
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL :
          (vc -> vc -> bool Domains_direct.DirectRep.rep) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v array array
    type vc = contr Domains_direct.DirectRep.rep
    type vo = Dom.v Domains_direct.DirectRep.rep
    val getL :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val dim2 : (unit -> 'a array) -> unit -> int
    val dim1 : (unit -> 'a array array) -> unit -> int
    val mapper :
      (vo -> vo) option ->
      (unit -> Dom.v array array) -> unit -> Dom.v array array
    val copy : (unit -> 'a array array) -> unit -> 'a array array
    val init : (unit -> int) -> (unit -> int) -> unit -> Dom.v array array
    val augment :
      (unit -> 'a array array) ->
      (unit -> int) ->
      (unit -> int) ->
      (unit -> 'a array array) -> (unit -> int) -> unit -> 'a array array
    val identity :
      (unit -> int) -> (unit -> int) -> unit -> Dom.v array array
    val swap_rows_stmt :
      (unit -> 'a array) ->
      'b -> (unit -> int) -> (unit -> int) -> unit -> unit
    val swap_cols_stmt :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> unit -> unit
    val row_head :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val col_head_set :
      (unit -> 'a array array) ->
      (unit -> int) -> (unit -> int) -> (unit -> 'a) -> unit -> unit
  end
module GVC_Z3 :
  sig
    module Dom :
      sig
        type v = Z3.v
        val kind : Domains_sig.domain_kind
        val zero : v
        val one : v
        val plus : v -> v -> v
        val times : v -> v -> v
        val minus : v -> v -> v
        val uminus : v -> v
        val div : v -> v -> v
        val better_than : (v -> v -> bool) option
        val normalizer : (v -> v) option
        type vc = v Domains_direct.DirectRep.rep
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL :
          (vc -> vc -> bool Domains_direct.DirectRep.rep) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v Prelude.container2dfromvector
    type vc = contr Domains_direct.DirectRep.rep
    type vo = Dom.v Domains_direct.DirectRep.rep
    val getL :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val dim2 : (unit -> 'a Prelude.container2dfromvector) -> unit -> int
    val dim1 : (unit -> 'a Prelude.container2dfromvector) -> unit -> int
    val mapper :
      ((unit -> 'a) -> unit -> 'a) option ->
      (unit -> 'a Prelude.container2dfromvector) ->
      unit -> 'a Prelude.container2dfromvector
    val copy :
      (unit -> 'a Prelude.container2dfromvector) ->
      unit -> 'a Prelude.container2dfromvector
    val init :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val augment :
      (unit -> Dom.v Prelude.container2dfromvector) ->
      (unit -> int) ->
      (unit -> int) ->
      (unit -> Dom.v Prelude.container2dfromvector) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val identity :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val index_default : (unit -> int) option -> int
    val swap_rows_stmt :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) option -> (unit -> int) -> (unit -> int) -> unit -> unit
    val swap_cols_stmt :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> unit
    val row_head :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val col_head_set :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> (unit -> 'a) -> unit -> unit
  end
module GVC_Z19 :
  sig
    module Dom :
      sig
        type v = Z19.v
        val kind : Domains_sig.domain_kind
        val zero : v
        val one : v
        val plus : v -> v -> v
        val times : v -> v -> v
        val minus : v -> v -> v
        val uminus : v -> v
        val div : v -> v -> v
        val better_than : (v -> v -> bool) option
        val normalizer : (v -> v) option
        type vc = v Domains_direct.DirectRep.rep
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL :
          (vc -> vc -> bool Domains_direct.DirectRep.rep) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v Prelude.container2dfromvector
    type vc = contr Domains_direct.DirectRep.rep
    type vo = Dom.v Domains_direct.DirectRep.rep
    val getL :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val dim2 : (unit -> 'a Prelude.container2dfromvector) -> unit -> int
    val dim1 : (unit -> 'a Prelude.container2dfromvector) -> unit -> int
    val mapper :
      ((unit -> 'a) -> unit -> 'a) option ->
      (unit -> 'a Prelude.container2dfromvector) ->
      unit -> 'a Prelude.container2dfromvector
    val copy :
      (unit -> 'a Prelude.container2dfromvector) ->
      unit -> 'a Prelude.container2dfromvector
    val init :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val augment :
      (unit -> Dom.v Prelude.container2dfromvector) ->
      (unit -> int) ->
      (unit -> int) ->
      (unit -> Dom.v Prelude.container2dfromvector) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val identity :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromvector
    val index_default : (unit -> int) option -> int
    val swap_rows_stmt :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) option -> (unit -> int) -> (unit -> int) -> unit -> unit
    val swap_cols_stmt :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> unit
    val row_head :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val col_head_set :
      (unit -> 'a Prelude.container2dfromvector) ->
      (unit -> int) -> (unit -> int) -> (unit -> 'a) -> unit -> unit
  end
module GFC_F :
  sig
    module Dom :
      sig
        type v = Domains_direct.FloatDomainL.v
        val kind : Domains_sig.domain_kind
        val zero : v
        val one : v
        val plus : v -> v -> v
        val times : v -> v -> v
        val minus : v -> v -> v
        val uminus : v -> v
        val div : v -> v -> v
        val better_than : (v -> v -> bool) option
        val normalizer : (v -> v) option
        type vc = v Domains_direct.DirectRep.rep
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL :
          (vc -> vc -> bool Domains_direct.DirectRep.rep) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v Prelude.container2dfromFvector
    type vc = contr Domains_direct.DirectRep.rep
    type vo = Dom.v Domains_direct.DirectRep.rep
    val unpack :
      (unit -> 'a Prelude.container2dfromFvector) ->
      ((unit -> 'a array) -> (unit -> int) -> (unit -> int) -> unit -> 'b) ->
      unit -> 'b
    val getL :
      (unit -> 'a Prelude.container2dfromFvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val dim2 : (unit -> 'a Prelude.container2dfromFvector) -> unit -> int
    val dim1 : (unit -> 'a Prelude.container2dfromFvector) -> unit -> int
    val mapper :
      ((unit -> 'a) -> unit -> 'a) option ->
      (unit -> 'a Prelude.container2dfromFvector) ->
      unit -> 'a Prelude.container2dfromFvector
    val copy :
      (unit -> 'a Prelude.container2dfromFvector) ->
      unit -> 'a Prelude.container2dfromFvector
    val init :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromFvector
    val augment :
      (unit -> Dom.v Prelude.container2dfromFvector) ->
      (unit -> int) ->
      (unit -> int) ->
      (unit -> Dom.v Prelude.container2dfromFvector) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromFvector
    val identity :
      (unit -> int) ->
      (unit -> int) -> unit -> Dom.v Prelude.container2dfromFvector
    val index_default : (unit -> int) option -> int
    val swap_rows_stmt :
      (unit -> 'a Prelude.container2dfromFvector) ->
      (unit -> int) option -> (unit -> int) -> (unit -> int) -> unit -> unit
    val swap_cols_stmt :
      (unit -> 'a Prelude.container2dfromFvector) ->
      (unit -> int) -> (unit -> int) -> unit -> unit
    val row_head :
      (unit -> 'a Prelude.container2dfromFvector) ->
      (unit -> int) -> (unit -> int) -> unit -> 'a
    val col_head_set :
      (unit -> 'a Prelude.container2dfromFvector) ->
      (unit -> int) -> (unit -> int) -> (unit -> 'a) -> unit -> unit
  end
module G_GAC_F :
  sig
    type wmatrix =
      Ge.LAMake(Direct).GenLA(GAC_F).wmatrix = {
      matrix : GAC_F.vc;
      numrow : int Direct.abstract;
      numcol : int Direct.abstract;
    }
    type curpos =
      Ge.LAMake(Direct).GenLA(GAC_F).curpos = {
      rowpos : int Direct.abstract;
      colpos : int Direct.abstract;
    }
    type curposval =
      Ge.LAMake(Direct).GenLA(GAC_F).curposval = {
      p : curpos;
      curval : GAC_F.Dom.v Direct.abstract;
    }
    module type DETERMINANT =
      sig
        type tdet = GAC_F.Dom.v ref
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GAC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_F.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GAC_F.contr Direct.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GAC_F.contr Direct.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GAC_F.contr)
          lm
        val updt :
          GAC_F.vc ->
          int Direct.abstract ->
          int Direct.abstract ->
          GAC_F.vo ->
          GAC_F.Dom.vc ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit) lm
          option
        val fin :
          unit ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GAC_F.contr)
          lm
        val wants_pack : bool
      end
    module type PIVOT =
      functor (D : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
        sig
          val findpivot :
            wmatrix ->
            curpos ->
            (< answer : 'a;
               state : [> `TDet of D.lstate | `TPivot of P.lstate ]; .. >,
             GAC_F.Dom.v option)
            GEF.cmonad
        end
    module NoDet :
      sig
        type tdet = GAC_F.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GAC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_F.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GAC_F.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GAC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_F.Dom.v) lm
      end
    module type UPDATE =
      functor (D : DETERMINANT) ->
        sig
          type in_val = GAC_F.Dom.vc
          val update :
            in_val ->
            in_val ->
            in_val ->
            in_val ->
            (in_val -> unit Direct.abstract) ->
            GAC_F.Dom.v ref Direct.abstract ->
            (< answer : 'a; state : 'b; .. >, unit) GEF.cmonad
          val update_det :
            in_val ->
            (< answer : 'a; state : [> `TDet of D.lstate ]; .. >, unit) D.lm
          val upd_kind : Ge.update_kind
        end
    module GE :
      sig
        module DivisionUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GAC_F.Dom.vc
              val update :
                GAC_F.Dom.vc ->
                GAC_F.Dom.vc ->
                GAC_F.Dom.vc ->
                GAC_F.Dom.vc ->
                (GAC_F.Dom.vc -> 'a) ->
                'b ->
                (< answer : 'c; state : 'd; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GAC_F.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module FractionFreeUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GAC_F.Dom.vc
              val update :
                GAC_F.Dom.vc ->
                GAC_F.Dom.vc ->
                GAC_F.Dom.vc ->
                GAC_F.Dom.vc ->
                (GAC_F.Dom.vc -> 'a) ->
                GAC_F.Dom.v ref Direct.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GAC_F.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GAC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GAC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Direct.abstract ->
              (< answer : 'b Direct.abstract;
                 state : [> `TLower of 'a Direct.abstract ] list; .. >,
               'a Direct.abstract)
              StateCPSMonad.monad
            val updt :
              GAC_F.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GAC_F.vo ->
              GAC_F.vo ->
              (< answer : 'a; state : [> `TLower of GAC_F.vc ] list; .. >,
               unit Direct.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GAC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a ->
              (< answer : 'b; state : [> `TLower of 'a ] list; .. >, 'a)
              StateCPSMonad.monad
            val updt : 'a -> 'b -> 'c -> 'd -> 'e -> 'f option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module NoLower :
          sig
            type lstate = GAC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a -> (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
            val updt :
              GAC_F.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GAC_F.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Direct.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_F.contr Direct.abstract * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GAC_F.contr
            val get_input :
              GAC_F.vc ->
              (< answer : 'a; state : 'b; .. >,
               GAC_F.vc * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GAC_F.contr * int
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_F.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_F.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_F.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module type OUTPUTDEP =
          sig module PivotRep : GEF.PIVOTKIND module Det : DETERMINANT end
        module OutJustMatrix :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_F.contr
              val make_result :
                wmatrix ->
                (< answer : 'a; state : 'b; .. >, GAC_F.vc)
                StateCPSMonad.monad
            end
        module OutDet :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_F.contr * GAC_F.Dom.v
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GAC_F.contr * GAC_F.Dom.v) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_F.contr * int
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TRan of 'b ref Direct.abstract ] list; .. >,
                 (GAC_F.contr * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_F.contr * GAC_F.Dom.v * int
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Direct.abstract ]
                           list;
                   .. >,
                 (GAC_F.contr * GAC_F.Dom.v * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRankPivot :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GAC_F.contr * GAC_F.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Direct.abstract
                            | `TRan of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GAC_F.contr * GAC_F.Dom.v * 'c * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_L_U :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GAC_F.contr * GAC_F.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Direct.abstract
                            | `TPivot of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GAC_F.contr * 'b * 'c) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_LU_Packed :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GAC_F.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Direct.abstract
                            | `TPivot of 'd ref Direct.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Direct.abstract)
                StateCPSMonad.monad
            end
        module type INTERNAL_FEATURES =
          sig
            module R : GEF.TrackRank.RANK
            module P : GEF.TRACKPIVOT
            module L : LOWER
          end
        module type OUTPUT =
          functor (OD : OUTPUTDEP) ->
            sig
              module IF : INTERNAL_FEATURES
              type res
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TDet of OD.Det.lstate
                            | `TLower of IF.L.lstate
                            | `TPivot of IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ];
                   .. >,
                 res)
                GEF.cmonad
            end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module PivotRep : GEF.PIVOTKIND
            module Update : UPDATE
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenGE :
          functor (F : FEATURES) ->
            sig
              module O :
                sig
                  module IF :
                    sig
                      module R :
                        sig
                          type tag_lstate = GEF.TrackRank.tag_lstate_
                          val decl :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int ref)
                            GEF.TrackRank.lm
                          val succ :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             unit)
                            GEF.TrackRank.lm
                          val fin :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int)
                            GEF.TrackRank.lm
                        end
                      module P :
                        sig
                          type perm_rep = F.Output(F).IF.P.perm_rep
                          type ira = int Direct.abstract
                          type fra = F.Output(F).IF.P.fra
                          type pra = F.Output(F).IF.P.pra
                          type lstate = F.Output(F).IF.P.lstate
                          type 'a pc_constraint = unit
                            constraint 'a =
                              < state : [> `TPivot of lstate ]; .. >
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TPivot of lstate ];
                                .. >
                          type 'a nm =
                              (< answer : 'b Direct.abstract;
                                 state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Direct.abstract ->
                            < answer : 'a; state : [> `TPivot of lstate ];
                              .. >
                            nm
                          val add :
                            fra ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             unit)
                            GEF.omonad
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             perm_rep)
                            lm
                        end
                      module L :
                        sig
                          type lstate = GAC_F.contr Direct.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GAC_F.contr Direct.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GAC_F.contr)
                            lm
                          val updt :
                            GAC_F.vc ->
                            int Direct.abstract ->
                            int Direct.abstract ->
                            GAC_F.vo ->
                            GAC_F.Dom.vc ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             unit)
                            lm option
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GAC_F.contr)
                            lm
                          val wants_pack : bool
                        end
                    end
                  type res = F.Output(F).res
                  val make_result :
                    wmatrix ->
                    (< answer : 'a;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of IF.L.lstate
                                | `TPivot of IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ];
                       .. >,
                     res)
                    GEF.cmonad
                end
              val wants_pack : bool
              val can_pack : bool
              val zerobelow :
                wmatrix ->
                curposval ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GAC_F.contr Direct.abstract ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GAC_F.contr Direct.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Direct.abstract *
                 int ref Direct.abstract * int Direct.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Direct.abstract * int ref Direct.abstract *
                int Direct.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
    module Solve :
      sig
        module type INPUT =
          sig
            type inp
            type rhs = GAC_F.contr
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_F.contr Direct.abstract * rhs Direct.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GAC_F.contr * GAC_F.contr
            type rhs = GAC_F.contr
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c Direct.abstract; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GAC_F.contr Direct.abstract ->
              GAC_F.contr Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GAC_F.contr
            val make_result :
              GAC_F.vc ->
              GAC_F.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              'a -> ('a -> GAC_F.contr Direct.abstract -> 'b) -> 'b
          end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenSolve :
          functor (F : FEATURES) ->
            sig
              module GE' :
                sig
                  module O :
                    sig
                      module IF :
                        sig
                          module R :
                            sig
                              type tag_lstate = GEF.TrackRank.tag_lstate_
                              val decl :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int ref)
                                GEF.TrackRank.lm
                              val succ :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 unit)
                                GEF.TrackRank.lm
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int)
                                GEF.TrackRank.lm
                            end
                          module P :
                            sig
                              type perm_rep = GEF.PermList.perm_rep
                              type ira = int Direct.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Direct.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Direct.abstract;
                                     state : 'c list >,
                                   unit)
                                  StateCPSMonad.monad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ] as 'c;
                                    .. >
                              val rowrep : ira -> ira -> fra
                              val colrep : ira -> ira -> fra
                              val decl :
                                int Direct.abstract ->
                                < answer : 'a;
                                  state : [> `TPivot of lstate ]; .. >
                                nm
                              val add :
                                fra ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 unit)
                                GEF.omonad
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 perm_rep)
                                lm
                            end
                          module L :
                            sig
                              type lstate = GAC_F.contr Direct.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GAC_F.contr Direct.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GAC_F.contr)
                                lm
                              val updt :
                                GAC_F.vc ->
                                int Direct.abstract ->
                                int Direct.abstract ->
                                GAC_F.vo ->
                                GAC_F.Dom.vc ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 unit)
                                lm option
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GAC_F.contr)
                                lm
                              val wants_pack : bool
                            end
                        end
                      type res = GAC_F.contr
                      val make_result :
                        wmatrix ->
                        (< answer : 'a;
                           state : [> `TDet of F.Det.lstate
                                    | `TLower of IF.L.lstate
                                    | `TPivot of IF.P.lstate
                                    | `TRan of GEF.TrackRank.lstate ];
                           .. >,
                         res)
                        GEF.cmonad
                    end
                  val wants_pack : bool
                  val can_pack : bool
                  val zerobelow :
                    wmatrix ->
                    curposval ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GAC_F.contr Direct.abstract ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val init :
                    (GAC_F.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GAC_F.contr Direct.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Direct.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Direct.abstract *
                     int ref Direct.abstract * int Direct.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Direct.abstract *
                    int ref Direct.abstract * int Direct.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GAC_F.contr Direct.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val gen :
                    (GAC_F.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Direct.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_F.contr Direct.abstract * F.Input.rhs Direct.abstract)
                StateCPSMonad.monad
              val back_elim :
                GAC_F.vc ->
                int Direct.abstract ->
                int Direct.abstract ->
                'a -> ('a -> GAC_F.contr Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GVC_F :
  sig
    type wmatrix =
      Ge.LAMake(Direct).GenLA(GVC_F).wmatrix = {
      matrix : GVC_F.vc;
      numrow : int Direct.abstract;
      numcol : int Direct.abstract;
    }
    type curpos =
      Ge.LAMake(Direct).GenLA(GVC_F).curpos = {
      rowpos : int Direct.abstract;
      colpos : int Direct.abstract;
    }
    type curposval =
      Ge.LAMake(Direct).GenLA(GVC_F).curposval = {
      p : curpos;
      curval : GVC_F.Dom.v Direct.abstract;
    }
    module type DETERMINANT =
      sig
        type tdet = GVC_F.Dom.v ref
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_F.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GVC_F.contr Direct.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GVC_F.contr Direct.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GVC_F.contr)
          lm
        val updt :
          GVC_F.vc ->
          int Direct.abstract ->
          int Direct.abstract ->
          GVC_F.vo ->
          GVC_F.Dom.vc ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit) lm
          option
        val fin :
          unit ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GVC_F.contr)
          lm
        val wants_pack : bool
      end
    module type PIVOT =
      functor (D : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
        sig
          val findpivot :
            wmatrix ->
            curpos ->
            (< answer : 'a;
               state : [> `TDet of D.lstate | `TPivot of P.lstate ]; .. >,
             GVC_F.Dom.v option)
            GEF.cmonad
        end
    module NoDet :
      sig
        type tdet = GVC_F.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_F.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GVC_F.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_F.Dom.v) lm
      end
    module type UPDATE =
      functor (D : DETERMINANT) ->
        sig
          type in_val = GVC_F.Dom.vc
          val update :
            in_val ->
            in_val ->
            in_val ->
            in_val ->
            (in_val -> unit Direct.abstract) ->
            GVC_F.Dom.v ref Direct.abstract ->
            (< answer : 'a; state : 'b; .. >, unit) GEF.cmonad
          val update_det :
            in_val ->
            (< answer : 'a; state : [> `TDet of D.lstate ]; .. >, unit) D.lm
          val upd_kind : Ge.update_kind
        end
    module GE :
      sig
        module DivisionUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GVC_F.Dom.vc
              val update :
                GVC_F.Dom.vc ->
                GVC_F.Dom.vc ->
                GVC_F.Dom.vc ->
                GVC_F.Dom.vc ->
                (GVC_F.Dom.vc -> 'a) ->
                'b ->
                (< answer : 'c; state : 'd; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_F.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module FractionFreeUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GVC_F.Dom.vc
              val update :
                GVC_F.Dom.vc ->
                GVC_F.Dom.vc ->
                GVC_F.Dom.vc ->
                GVC_F.Dom.vc ->
                (GVC_F.Dom.vc -> 'a) ->
                GVC_F.Dom.v ref Direct.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_F.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GVC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GVC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Direct.abstract ->
              (< answer : 'b Direct.abstract;
                 state : [> `TLower of 'a Direct.abstract ] list; .. >,
               'a Direct.abstract)
              StateCPSMonad.monad
            val updt :
              GVC_F.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GVC_F.vo ->
              GVC_F.vo ->
              (< answer : 'a; state : [> `TLower of GVC_F.vc ] list; .. >,
               unit Direct.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GVC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a ->
              (< answer : 'b; state : [> `TLower of 'a ] list; .. >, 'a)
              StateCPSMonad.monad
            val updt : 'a -> 'b -> 'c -> 'd -> 'e -> 'f option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module NoLower :
          sig
            type lstate = GVC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a -> (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
            val updt :
              GVC_F.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GVC_F.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Direct.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_F.contr Direct.abstract * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GVC_F.contr
            val get_input :
              GVC_F.vc ->
              (< answer : 'a; state : 'b; .. >,
               GVC_F.vc * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GVC_F.contr * int
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_F.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_F.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_F.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module type OUTPUTDEP =
          sig module PivotRep : GEF.PIVOTKIND module Det : DETERMINANT end
        module OutJustMatrix :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_F.contr
              val make_result :
                wmatrix ->
                (< answer : 'a; state : 'b; .. >, GVC_F.vc)
                StateCPSMonad.monad
            end
        module OutDet :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_F.contr * GVC_F.Dom.v
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GVC_F.contr * GVC_F.Dom.v) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_F.contr * int
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TRan of 'b ref Direct.abstract ] list; .. >,
                 (GVC_F.contr * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_F.contr * GVC_F.Dom.v * int
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_F.contr * GVC_F.Dom.v * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRankPivot :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GVC_F.contr * GVC_F.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Direct.abstract
                            | `TRan of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_F.contr * GVC_F.Dom.v * 'c * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_L_U :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GVC_F.contr * GVC_F.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Direct.abstract
                            | `TPivot of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_F.contr * 'b * 'c) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_LU_Packed :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GVC_F.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Direct.abstract
                            | `TPivot of 'd ref Direct.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Direct.abstract)
                StateCPSMonad.monad
            end
        module type INTERNAL_FEATURES =
          sig
            module R : GEF.TrackRank.RANK
            module P : GEF.TRACKPIVOT
            module L : LOWER
          end
        module type OUTPUT =
          functor (OD : OUTPUTDEP) ->
            sig
              module IF : INTERNAL_FEATURES
              type res
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TDet of OD.Det.lstate
                            | `TLower of IF.L.lstate
                            | `TPivot of IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ];
                   .. >,
                 res)
                GEF.cmonad
            end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module PivotRep : GEF.PIVOTKIND
            module Update : UPDATE
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenGE :
          functor (F : FEATURES) ->
            sig
              module O :
                sig
                  module IF :
                    sig
                      module R :
                        sig
                          type tag_lstate = GEF.TrackRank.tag_lstate_
                          val decl :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int ref)
                            GEF.TrackRank.lm
                          val succ :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             unit)
                            GEF.TrackRank.lm
                          val fin :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int)
                            GEF.TrackRank.lm
                        end
                      module P :
                        sig
                          type perm_rep = F.Output(F).IF.P.perm_rep
                          type ira = int Direct.abstract
                          type fra = F.Output(F).IF.P.fra
                          type pra = F.Output(F).IF.P.pra
                          type lstate = F.Output(F).IF.P.lstate
                          type 'a pc_constraint = unit
                            constraint 'a =
                              < state : [> `TPivot of lstate ]; .. >
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TPivot of lstate ];
                                .. >
                          type 'a nm =
                              (< answer : 'b Direct.abstract;
                                 state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Direct.abstract ->
                            < answer : 'a; state : [> `TPivot of lstate ];
                              .. >
                            nm
                          val add :
                            fra ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             unit)
                            GEF.omonad
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             perm_rep)
                            lm
                        end
                      module L :
                        sig
                          type lstate = GVC_F.contr Direct.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GVC_F.contr Direct.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_F.contr)
                            lm
                          val updt :
                            GVC_F.vc ->
                            int Direct.abstract ->
                            int Direct.abstract ->
                            GVC_F.vo ->
                            GVC_F.Dom.vc ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             unit)
                            lm option
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_F.contr)
                            lm
                          val wants_pack : bool
                        end
                    end
                  type res = F.Output(F).res
                  val make_result :
                    wmatrix ->
                    (< answer : 'a;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of IF.L.lstate
                                | `TPivot of IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ];
                       .. >,
                     res)
                    GEF.cmonad
                end
              val wants_pack : bool
              val can_pack : bool
              val zerobelow :
                wmatrix ->
                curposval ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_F.contr Direct.abstract ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GVC_F.contr Direct.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Direct.abstract *
                 int ref Direct.abstract * int Direct.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Direct.abstract * int ref Direct.abstract *
                int Direct.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_F.contr Direct.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
    module Solve :
      sig
        module type INPUT =
          sig
            type inp
            type rhs = GVC_F.contr
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_F.contr Direct.abstract * rhs Direct.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GVC_F.contr * GVC_F.contr
            type rhs = GVC_F.contr
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c Direct.abstract; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GVC_F.contr Direct.abstract ->
              GVC_F.contr Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GVC_F.contr
            val make_result :
              GVC_F.vc ->
              GVC_F.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              'a -> ('a -> GVC_F.contr Direct.abstract -> 'b) -> 'b
          end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenSolve :
          functor (F : FEATURES) ->
            sig
              module GE' :
                sig
                  module O :
                    sig
                      module IF :
                        sig
                          module R :
                            sig
                              type tag_lstate = GEF.TrackRank.tag_lstate_
                              val decl :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int ref)
                                GEF.TrackRank.lm
                              val succ :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 unit)
                                GEF.TrackRank.lm
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int)
                                GEF.TrackRank.lm
                            end
                          module P :
                            sig
                              type perm_rep = GEF.PermList.perm_rep
                              type ira = int Direct.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Direct.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Direct.abstract;
                                     state : 'c list >,
                                   unit)
                                  StateCPSMonad.monad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ] as 'c;
                                    .. >
                              val rowrep : ira -> ira -> fra
                              val colrep : ira -> ira -> fra
                              val decl :
                                int Direct.abstract ->
                                < answer : 'a;
                                  state : [> `TPivot of lstate ]; .. >
                                nm
                              val add :
                                fra ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 unit)
                                GEF.omonad
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 perm_rep)
                                lm
                            end
                          module L :
                            sig
                              type lstate = GVC_F.contr Direct.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GVC_F.contr Direct.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_F.contr)
                                lm
                              val updt :
                                GVC_F.vc ->
                                int Direct.abstract ->
                                int Direct.abstract ->
                                GVC_F.vo ->
                                GVC_F.Dom.vc ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 unit)
                                lm option
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_F.contr)
                                lm
                              val wants_pack : bool
                            end
                        end
                      type res = GVC_F.contr
                      val make_result :
                        wmatrix ->
                        (< answer : 'a;
                           state : [> `TDet of F.Det.lstate
                                    | `TLower of IF.L.lstate
                                    | `TPivot of IF.P.lstate
                                    | `TRan of GEF.TrackRank.lstate ];
                           .. >,
                         res)
                        GEF.cmonad
                    end
                  val wants_pack : bool
                  val can_pack : bool
                  val zerobelow :
                    wmatrix ->
                    curposval ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_F.contr Direct.abstract ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val init :
                    (GVC_F.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GVC_F.contr Direct.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Direct.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Direct.abstract *
                     int ref Direct.abstract * int Direct.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Direct.abstract *
                    int ref Direct.abstract * int Direct.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_F.contr Direct.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val gen :
                    (GVC_F.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Direct.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_F.contr Direct.abstract * F.Input.rhs Direct.abstract)
                StateCPSMonad.monad
              val back_elim :
                GVC_F.vc ->
                int Direct.abstract ->
                int Direct.abstract ->
                'a -> ('a -> GVC_F.contr Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GAC_I :
  sig
    type wmatrix =
      Ge.LAMake(Direct).GenLA(GAC_I).wmatrix = {
      matrix : GAC_I.vc;
      numrow : int Direct.abstract;
      numcol : int Direct.abstract;
    }
    type curpos =
      Ge.LAMake(Direct).GenLA(GAC_I).curpos = {
      rowpos : int Direct.abstract;
      colpos : int Direct.abstract;
    }
    type curposval =
      Ge.LAMake(Direct).GenLA(GAC_I).curposval = {
      p : curpos;
      curval : GAC_I.Dom.v Direct.abstract;
    }
    module type DETERMINANT =
      sig
        type tdet = GAC_I.Dom.v ref
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GAC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_I.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GAC_I.contr Direct.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GAC_I.contr Direct.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GAC_I.contr)
          lm
        val updt :
          GAC_I.vc ->
          int Direct.abstract ->
          int Direct.abstract ->
          GAC_I.vo ->
          GAC_I.Dom.vc ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit) lm
          option
        val fin :
          unit ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GAC_I.contr)
          lm
        val wants_pack : bool
      end
    module type PIVOT =
      functor (D : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
        sig
          val findpivot :
            wmatrix ->
            curpos ->
            (< answer : 'a;
               state : [> `TDet of D.lstate | `TPivot of P.lstate ]; .. >,
             GAC_I.Dom.v option)
            GEF.cmonad
        end
    module NoDet :
      sig
        type tdet = GAC_I.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GAC_I).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GAC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_I.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GAC_I.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GAC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_I.Dom.v) lm
      end
    module type UPDATE =
      functor (D : DETERMINANT) ->
        sig
          type in_val = GAC_I.Dom.vc
          val update :
            in_val ->
            in_val ->
            in_val ->
            in_val ->
            (in_val -> unit Direct.abstract) ->
            GAC_I.Dom.v ref Direct.abstract ->
            (< answer : 'a; state : 'b; .. >, unit) GEF.cmonad
          val update_det :
            in_val ->
            (< answer : 'a; state : [> `TDet of D.lstate ]; .. >, unit) D.lm
          val upd_kind : Ge.update_kind
        end
    module GE :
      sig
        module DivisionUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GAC_I.Dom.vc
              val update :
                GAC_I.Dom.vc ->
                GAC_I.Dom.vc ->
                GAC_I.Dom.vc ->
                GAC_I.Dom.vc ->
                (GAC_I.Dom.vc -> 'a) ->
                'b ->
                (< answer : 'c; state : 'd; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GAC_I.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module FractionFreeUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GAC_I.Dom.vc
              val update :
                GAC_I.Dom.vc ->
                GAC_I.Dom.vc ->
                GAC_I.Dom.vc ->
                GAC_I.Dom.vc ->
                (GAC_I.Dom.vc -> 'a) ->
                GAC_I.Dom.v ref Direct.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GAC_I.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GAC_I.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GAC_I.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Direct.abstract ->
              (< answer : 'b Direct.abstract;
                 state : [> `TLower of 'a Direct.abstract ] list; .. >,
               'a Direct.abstract)
              StateCPSMonad.monad
            val updt :
              GAC_I.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GAC_I.vo ->
              GAC_I.vo ->
              (< answer : 'a; state : [> `TLower of GAC_I.vc ] list; .. >,
               unit Direct.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GAC_I.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a ->
              (< answer : 'b; state : [> `TLower of 'a ] list; .. >, 'a)
              StateCPSMonad.monad
            val updt : 'a -> 'b -> 'c -> 'd -> 'e -> 'f option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module NoLower :
          sig
            type lstate = GAC_I.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a -> (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
            val updt :
              GAC_I.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GAC_I.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Direct.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_I.contr Direct.abstract * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GAC_I.contr
            val get_input :
              GAC_I.vc ->
              (< answer : 'a; state : 'b; .. >,
               GAC_I.vc * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GAC_I.contr * int
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_I.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_I.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_I.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module type OUTPUTDEP =
          sig module PivotRep : GEF.PIVOTKIND module Det : DETERMINANT end
        module OutJustMatrix :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_I.contr
              val make_result :
                wmatrix ->
                (< answer : 'a; state : 'b; .. >, GAC_I.vc)
                StateCPSMonad.monad
            end
        module OutDet :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_I.contr * GAC_I.Dom.v
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GAC_I.contr * GAC_I.Dom.v) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_I.contr * int
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TRan of 'b ref Direct.abstract ] list; .. >,
                 (GAC_I.contr * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_I.contr * GAC_I.Dom.v * int
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Direct.abstract ]
                           list;
                   .. >,
                 (GAC_I.contr * GAC_I.Dom.v * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRankPivot :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GAC_I.contr * GAC_I.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Direct.abstract
                            | `TRan of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GAC_I.contr * GAC_I.Dom.v * 'c * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_L_U :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GAC_I.contr * GAC_I.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Direct.abstract
                            | `TPivot of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GAC_I.contr * 'b * 'c) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_LU_Packed :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GAC_I.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Direct.abstract
                            | `TPivot of 'd ref Direct.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Direct.abstract)
                StateCPSMonad.monad
            end
        module type INTERNAL_FEATURES =
          sig
            module R : GEF.TrackRank.RANK
            module P : GEF.TRACKPIVOT
            module L : LOWER
          end
        module type OUTPUT =
          functor (OD : OUTPUTDEP) ->
            sig
              module IF : INTERNAL_FEATURES
              type res
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TDet of OD.Det.lstate
                            | `TLower of IF.L.lstate
                            | `TPivot of IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ];
                   .. >,
                 res)
                GEF.cmonad
            end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module PivotRep : GEF.PIVOTKIND
            module Update : UPDATE
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenGE :
          functor (F : FEATURES) ->
            sig
              module O :
                sig
                  module IF :
                    sig
                      module R :
                        sig
                          type tag_lstate = GEF.TrackRank.tag_lstate_
                          val decl :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int ref)
                            GEF.TrackRank.lm
                          val succ :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             unit)
                            GEF.TrackRank.lm
                          val fin :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int)
                            GEF.TrackRank.lm
                        end
                      module P :
                        sig
                          type perm_rep = F.Output(F).IF.P.perm_rep
                          type ira = int Direct.abstract
                          type fra = F.Output(F).IF.P.fra
                          type pra = F.Output(F).IF.P.pra
                          type lstate = F.Output(F).IF.P.lstate
                          type 'a pc_constraint = unit
                            constraint 'a =
                              < state : [> `TPivot of lstate ]; .. >
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TPivot of lstate ];
                                .. >
                          type 'a nm =
                              (< answer : 'b Direct.abstract;
                                 state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Direct.abstract ->
                            < answer : 'a; state : [> `TPivot of lstate ];
                              .. >
                            nm
                          val add :
                            fra ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             unit)
                            GEF.omonad
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             perm_rep)
                            lm
                        end
                      module L :
                        sig
                          type lstate = GAC_I.contr Direct.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GAC_I.contr Direct.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GAC_I.contr)
                            lm
                          val updt :
                            GAC_I.vc ->
                            int Direct.abstract ->
                            int Direct.abstract ->
                            GAC_I.vo ->
                            GAC_I.Dom.vc ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             unit)
                            lm option
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GAC_I.contr)
                            lm
                          val wants_pack : bool
                        end
                    end
                  type res = F.Output(F).res
                  val make_result :
                    wmatrix ->
                    (< answer : 'a;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of IF.L.lstate
                                | `TPivot of IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ];
                       .. >,
                     res)
                    GEF.cmonad
                end
              val wants_pack : bool
              val can_pack : bool
              val zerobelow :
                wmatrix ->
                curposval ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GAC_I.contr Direct.abstract ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GAC_I.contr Direct.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Direct.abstract *
                 int ref Direct.abstract * int Direct.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Direct.abstract * int ref Direct.abstract *
                int Direct.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GAC_I.contr Direct.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
    module Solve :
      sig
        module type INPUT =
          sig
            type inp
            type rhs = GAC_I.contr
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_I.contr Direct.abstract * rhs Direct.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GAC_I.contr * GAC_I.contr
            type rhs = GAC_I.contr
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c Direct.abstract; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GAC_I.contr Direct.abstract ->
              GAC_I.contr Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GAC_I.contr
            val make_result :
              GAC_I.vc ->
              GAC_I.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              'a -> ('a -> GAC_I.contr Direct.abstract -> 'b) -> 'b
          end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenSolve :
          functor (F : FEATURES) ->
            sig
              module GE' :
                sig
                  module O :
                    sig
                      module IF :
                        sig
                          module R :
                            sig
                              type tag_lstate = GEF.TrackRank.tag_lstate_
                              val decl :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int ref)
                                GEF.TrackRank.lm
                              val succ :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 unit)
                                GEF.TrackRank.lm
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int)
                                GEF.TrackRank.lm
                            end
                          module P :
                            sig
                              type perm_rep = GEF.PermList.perm_rep
                              type ira = int Direct.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Direct.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Direct.abstract;
                                     state : 'c list >,
                                   unit)
                                  StateCPSMonad.monad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ] as 'c;
                                    .. >
                              val rowrep : ira -> ira -> fra
                              val colrep : ira -> ira -> fra
                              val decl :
                                int Direct.abstract ->
                                < answer : 'a;
                                  state : [> `TPivot of lstate ]; .. >
                                nm
                              val add :
                                fra ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 unit)
                                GEF.omonad
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 perm_rep)
                                lm
                            end
                          module L :
                            sig
                              type lstate = GAC_I.contr Direct.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GAC_I.contr Direct.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GAC_I.contr)
                                lm
                              val updt :
                                GAC_I.vc ->
                                int Direct.abstract ->
                                int Direct.abstract ->
                                GAC_I.vo ->
                                GAC_I.Dom.vc ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 unit)
                                lm option
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GAC_I.contr)
                                lm
                              val wants_pack : bool
                            end
                        end
                      type res = GAC_I.contr
                      val make_result :
                        wmatrix ->
                        (< answer : 'a;
                           state : [> `TDet of F.Det.lstate
                                    | `TLower of IF.L.lstate
                                    | `TPivot of IF.P.lstate
                                    | `TRan of GEF.TrackRank.lstate ];
                           .. >,
                         res)
                        GEF.cmonad
                    end
                  val wants_pack : bool
                  val can_pack : bool
                  val zerobelow :
                    wmatrix ->
                    curposval ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GAC_I.contr Direct.abstract ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val init :
                    (GAC_I.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GAC_I.contr Direct.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Direct.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Direct.abstract *
                     int ref Direct.abstract * int Direct.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Direct.abstract *
                    int ref Direct.abstract * int Direct.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GAC_I.contr Direct.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val gen :
                    (GAC_I.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Direct.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_I.contr Direct.abstract * F.Input.rhs Direct.abstract)
                StateCPSMonad.monad
              val back_elim :
                GAC_I.vc ->
                int Direct.abstract ->
                int Direct.abstract ->
                'a -> ('a -> GAC_I.contr Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GVC_I :
  sig
    type wmatrix =
      Ge.LAMake(Direct).GenLA(GVC_I).wmatrix = {
      matrix : GVC_I.vc;
      numrow : int Direct.abstract;
      numcol : int Direct.abstract;
    }
    type curpos =
      Ge.LAMake(Direct).GenLA(GVC_I).curpos = {
      rowpos : int Direct.abstract;
      colpos : int Direct.abstract;
    }
    type curposval =
      Ge.LAMake(Direct).GenLA(GVC_I).curposval = {
      p : curpos;
      curval : GVC_I.Dom.v Direct.abstract;
    }
    module type DETERMINANT =
      sig
        type tdet = GVC_I.Dom.v ref
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_I.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GVC_I.contr Direct.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GVC_I.contr Direct.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GVC_I.contr)
          lm
        val updt :
          GVC_I.vc ->
          int Direct.abstract ->
          int Direct.abstract ->
          GVC_I.vo ->
          GVC_I.Dom.vc ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit) lm
          option
        val fin :
          unit ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GVC_I.contr)
          lm
        val wants_pack : bool
      end
    module type PIVOT =
      functor (D : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
        sig
          val findpivot :
            wmatrix ->
            curpos ->
            (< answer : 'a;
               state : [> `TDet of D.lstate | `TPivot of P.lstate ]; .. >,
             GVC_I.Dom.v option)
            GEF.cmonad
        end
    module NoDet :
      sig
        type tdet = GVC_I.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GVC_I).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_I.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GVC_I.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_I.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_I.Dom.v) lm
      end
    module type UPDATE =
      functor (D : DETERMINANT) ->
        sig
          type in_val = GVC_I.Dom.vc
          val update :
            in_val ->
            in_val ->
            in_val ->
            in_val ->
            (in_val -> unit Direct.abstract) ->
            GVC_I.Dom.v ref Direct.abstract ->
            (< answer : 'a; state : 'b; .. >, unit) GEF.cmonad
          val update_det :
            in_val ->
            (< answer : 'a; state : [> `TDet of D.lstate ]; .. >, unit) D.lm
          val upd_kind : Ge.update_kind
        end
    module GE :
      sig
        module DivisionUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GVC_I.Dom.vc
              val update :
                GVC_I.Dom.vc ->
                GVC_I.Dom.vc ->
                GVC_I.Dom.vc ->
                GVC_I.Dom.vc ->
                (GVC_I.Dom.vc -> 'a) ->
                'b ->
                (< answer : 'c; state : 'd; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_I.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module FractionFreeUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GVC_I.Dom.vc
              val update :
                GVC_I.Dom.vc ->
                GVC_I.Dom.vc ->
                GVC_I.Dom.vc ->
                GVC_I.Dom.vc ->
                (GVC_I.Dom.vc -> 'a) ->
                GVC_I.Dom.v ref Direct.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_I.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GVC_I.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GVC_I.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Direct.abstract ->
              (< answer : 'b Direct.abstract;
                 state : [> `TLower of 'a Direct.abstract ] list; .. >,
               'a Direct.abstract)
              StateCPSMonad.monad
            val updt :
              GVC_I.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GVC_I.vo ->
              GVC_I.vo ->
              (< answer : 'a; state : [> `TLower of GVC_I.vc ] list; .. >,
               unit Direct.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GVC_I.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a ->
              (< answer : 'b; state : [> `TLower of 'a ] list; .. >, 'a)
              StateCPSMonad.monad
            val updt : 'a -> 'b -> 'c -> 'd -> 'e -> 'f option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module NoLower :
          sig
            type lstate = GVC_I.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a -> (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
            val updt :
              GVC_I.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GVC_I.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Direct.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_I.contr Direct.abstract * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GVC_I.contr
            val get_input :
              GVC_I.vc ->
              (< answer : 'a; state : 'b; .. >,
               GVC_I.vc * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GVC_I.contr * int
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_I.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_I.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_I.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module type OUTPUTDEP =
          sig module PivotRep : GEF.PIVOTKIND module Det : DETERMINANT end
        module OutJustMatrix :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_I.contr
              val make_result :
                wmatrix ->
                (< answer : 'a; state : 'b; .. >, GVC_I.vc)
                StateCPSMonad.monad
            end
        module OutDet :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_I.contr * GVC_I.Dom.v
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GVC_I.contr * GVC_I.Dom.v) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_I.contr * int
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TRan of 'b ref Direct.abstract ] list; .. >,
                 (GVC_I.contr * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_I.contr * GVC_I.Dom.v * int
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_I.contr * GVC_I.Dom.v * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRankPivot :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GVC_I.contr * GVC_I.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Direct.abstract
                            | `TRan of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_I.contr * GVC_I.Dom.v * 'c * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_L_U :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GVC_I.contr * GVC_I.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Direct.abstract
                            | `TPivot of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_I.contr * 'b * 'c) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_LU_Packed :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GVC_I.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Direct.abstract
                            | `TPivot of 'd ref Direct.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Direct.abstract)
                StateCPSMonad.monad
            end
        module type INTERNAL_FEATURES =
          sig
            module R : GEF.TrackRank.RANK
            module P : GEF.TRACKPIVOT
            module L : LOWER
          end
        module type OUTPUT =
          functor (OD : OUTPUTDEP) ->
            sig
              module IF : INTERNAL_FEATURES
              type res
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TDet of OD.Det.lstate
                            | `TLower of IF.L.lstate
                            | `TPivot of IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ];
                   .. >,
                 res)
                GEF.cmonad
            end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module PivotRep : GEF.PIVOTKIND
            module Update : UPDATE
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenGE :
          functor (F : FEATURES) ->
            sig
              module O :
                sig
                  module IF :
                    sig
                      module R :
                        sig
                          type tag_lstate = GEF.TrackRank.tag_lstate_
                          val decl :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int ref)
                            GEF.TrackRank.lm
                          val succ :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             unit)
                            GEF.TrackRank.lm
                          val fin :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int)
                            GEF.TrackRank.lm
                        end
                      module P :
                        sig
                          type perm_rep = F.Output(F).IF.P.perm_rep
                          type ira = int Direct.abstract
                          type fra = F.Output(F).IF.P.fra
                          type pra = F.Output(F).IF.P.pra
                          type lstate = F.Output(F).IF.P.lstate
                          type 'a pc_constraint = unit
                            constraint 'a =
                              < state : [> `TPivot of lstate ]; .. >
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TPivot of lstate ];
                                .. >
                          type 'a nm =
                              (< answer : 'b Direct.abstract;
                                 state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Direct.abstract ->
                            < answer : 'a; state : [> `TPivot of lstate ];
                              .. >
                            nm
                          val add :
                            fra ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             unit)
                            GEF.omonad
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             perm_rep)
                            lm
                        end
                      module L :
                        sig
                          type lstate = GVC_I.contr Direct.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GVC_I.contr Direct.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_I.contr)
                            lm
                          val updt :
                            GVC_I.vc ->
                            int Direct.abstract ->
                            int Direct.abstract ->
                            GVC_I.vo ->
                            GVC_I.Dom.vc ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             unit)
                            lm option
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_I.contr)
                            lm
                          val wants_pack : bool
                        end
                    end
                  type res = F.Output(F).res
                  val make_result :
                    wmatrix ->
                    (< answer : 'a;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of IF.L.lstate
                                | `TPivot of IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ];
                       .. >,
                     res)
                    GEF.cmonad
                end
              val wants_pack : bool
              val can_pack : bool
              val zerobelow :
                wmatrix ->
                curposval ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_I.contr Direct.abstract ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GVC_I.contr Direct.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Direct.abstract *
                 int ref Direct.abstract * int Direct.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Direct.abstract * int ref Direct.abstract *
                int Direct.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_I.contr Direct.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
    module Solve :
      sig
        module type INPUT =
          sig
            type inp
            type rhs = GVC_I.contr
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_I.contr Direct.abstract * rhs Direct.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GVC_I.contr * GVC_I.contr
            type rhs = GVC_I.contr
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c Direct.abstract; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GVC_I.contr Direct.abstract ->
              GVC_I.contr Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GVC_I.contr
            val make_result :
              GVC_I.vc ->
              GVC_I.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              'a -> ('a -> GVC_I.contr Direct.abstract -> 'b) -> 'b
          end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenSolve :
          functor (F : FEATURES) ->
            sig
              module GE' :
                sig
                  module O :
                    sig
                      module IF :
                        sig
                          module R :
                            sig
                              type tag_lstate = GEF.TrackRank.tag_lstate_
                              val decl :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int ref)
                                GEF.TrackRank.lm
                              val succ :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 unit)
                                GEF.TrackRank.lm
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int)
                                GEF.TrackRank.lm
                            end
                          module P :
                            sig
                              type perm_rep = GEF.PermList.perm_rep
                              type ira = int Direct.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Direct.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Direct.abstract;
                                     state : 'c list >,
                                   unit)
                                  StateCPSMonad.monad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ] as 'c;
                                    .. >
                              val rowrep : ira -> ira -> fra
                              val colrep : ira -> ira -> fra
                              val decl :
                                int Direct.abstract ->
                                < answer : 'a;
                                  state : [> `TPivot of lstate ]; .. >
                                nm
                              val add :
                                fra ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 unit)
                                GEF.omonad
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 perm_rep)
                                lm
                            end
                          module L :
                            sig
                              type lstate = GVC_I.contr Direct.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GVC_I.contr Direct.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_I.contr)
                                lm
                              val updt :
                                GVC_I.vc ->
                                int Direct.abstract ->
                                int Direct.abstract ->
                                GVC_I.vo ->
                                GVC_I.Dom.vc ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 unit)
                                lm option
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_I.contr)
                                lm
                              val wants_pack : bool
                            end
                        end
                      type res = GVC_I.contr
                      val make_result :
                        wmatrix ->
                        (< answer : 'a;
                           state : [> `TDet of F.Det.lstate
                                    | `TLower of IF.L.lstate
                                    | `TPivot of IF.P.lstate
                                    | `TRan of GEF.TrackRank.lstate ];
                           .. >,
                         res)
                        GEF.cmonad
                    end
                  val wants_pack : bool
                  val can_pack : bool
                  val zerobelow :
                    wmatrix ->
                    curposval ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_I.contr Direct.abstract ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val init :
                    (GVC_I.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GVC_I.contr Direct.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Direct.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Direct.abstract *
                     int ref Direct.abstract * int Direct.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Direct.abstract *
                    int ref Direct.abstract * int Direct.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_I.contr Direct.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val gen :
                    (GVC_I.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Direct.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_I.contr Direct.abstract * F.Input.rhs Direct.abstract)
                StateCPSMonad.monad
              val back_elim :
                GVC_I.vc ->
                int Direct.abstract ->
                int Direct.abstract ->
                'a -> ('a -> GVC_I.contr Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GAC_R :
  sig
    type wmatrix =
      Ge.LAMake(Direct).GenLA(GAC_R).wmatrix = {
      matrix : GAC_R.vc;
      numrow : int Direct.abstract;
      numcol : int Direct.abstract;
    }
    type curpos =
      Ge.LAMake(Direct).GenLA(GAC_R).curpos = {
      rowpos : int Direct.abstract;
      colpos : int Direct.abstract;
    }
    type curposval =
      Ge.LAMake(Direct).GenLA(GAC_R).curposval = {
      p : curpos;
      curval : GAC_R.Dom.v Direct.abstract;
    }
    module type DETERMINANT =
      sig
        type tdet = GAC_R.Dom.v ref
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GAC_R.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_R.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_R.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GAC_R.contr Direct.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GAC_R.contr Direct.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GAC_R.contr)
          lm
        val updt :
          GAC_R.vc ->
          int Direct.abstract ->
          int Direct.abstract ->
          GAC_R.vo ->
          GAC_R.Dom.vc ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit) lm
          option
        val fin :
          unit ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GAC_R.contr)
          lm
        val wants_pack : bool
      end
    module type PIVOT =
      functor (D : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
        sig
          val findpivot :
            wmatrix ->
            curpos ->
            (< answer : 'a;
               state : [> `TDet of D.lstate | `TPivot of P.lstate ]; .. >,
             GAC_R.Dom.v option)
            GEF.cmonad
        end
    module NoDet :
      sig
        type tdet = GAC_R.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GAC_R.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_R.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_R.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GAC_R.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GAC_R.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_R.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_R.Dom.v) lm
      end
    module type UPDATE =
      functor (D : DETERMINANT) ->
        sig
          type in_val = GAC_R.Dom.vc
          val update :
            in_val ->
            in_val ->
            in_val ->
            in_val ->
            (in_val -> unit Direct.abstract) ->
            GAC_R.Dom.v ref Direct.abstract ->
            (< answer : 'a; state : 'b; .. >, unit) GEF.cmonad
          val update_det :
            in_val ->
            (< answer : 'a; state : [> `TDet of D.lstate ]; .. >, unit) D.lm
          val upd_kind : Ge.update_kind
        end
    module GE :
      sig
        module DivisionUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GAC_R.Dom.vc
              val update :
                GAC_R.Dom.vc ->
                GAC_R.Dom.vc ->
                GAC_R.Dom.vc ->
                GAC_R.Dom.vc ->
                (GAC_R.Dom.vc -> 'a) ->
                'b ->
                (< answer : 'c; state : 'd; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GAC_R.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module FractionFreeUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GAC_R.Dom.vc
              val update :
                GAC_R.Dom.vc ->
                GAC_R.Dom.vc ->
                GAC_R.Dom.vc ->
                GAC_R.Dom.vc ->
                (GAC_R.Dom.vc -> 'a) ->
                GAC_R.Dom.v ref Direct.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GAC_R.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GAC_R.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GAC_R.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Direct.abstract ->
              (< answer : 'b Direct.abstract;
                 state : [> `TLower of 'a Direct.abstract ] list; .. >,
               'a Direct.abstract)
              StateCPSMonad.monad
            val updt :
              GAC_R.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GAC_R.vo ->
              GAC_R.vo ->
              (< answer : 'a; state : [> `TLower of GAC_R.vc ] list; .. >,
               unit Direct.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GAC_R.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a ->
              (< answer : 'b; state : [> `TLower of 'a ] list; .. >, 'a)
              StateCPSMonad.monad
            val updt : 'a -> 'b -> 'c -> 'd -> 'e -> 'f option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module NoLower :
          sig
            type lstate = GAC_R.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a -> (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
            val updt :
              GAC_R.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GAC_R.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Direct.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_R.contr Direct.abstract * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GAC_R.contr
            val get_input :
              GAC_R.vc ->
              (< answer : 'a; state : 'b; .. >,
               GAC_R.vc * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GAC_R.contr * int
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_R.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_R.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_R.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module type OUTPUTDEP =
          sig module PivotRep : GEF.PIVOTKIND module Det : DETERMINANT end
        module OutJustMatrix :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_R.contr
              val make_result :
                wmatrix ->
                (< answer : 'a; state : 'b; .. >, GAC_R.vc)
                StateCPSMonad.monad
            end
        module OutDet :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_R.contr * GAC_R.Dom.v
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GAC_R.contr * GAC_R.Dom.v) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_R.contr * int
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TRan of 'b ref Direct.abstract ] list; .. >,
                 (GAC_R.contr * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GAC_R.contr * GAC_R.Dom.v * int
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Direct.abstract ]
                           list;
                   .. >,
                 (GAC_R.contr * GAC_R.Dom.v * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRankPivot :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GAC_R.contr * GAC_R.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Direct.abstract
                            | `TRan of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GAC_R.contr * GAC_R.Dom.v * 'c * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_L_U :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GAC_R.contr * GAC_R.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Direct.abstract
                            | `TPivot of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GAC_R.contr * 'b * 'c) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_LU_Packed :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GAC_R.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Direct.abstract
                            | `TPivot of 'd ref Direct.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Direct.abstract)
                StateCPSMonad.monad
            end
        module type INTERNAL_FEATURES =
          sig
            module R : GEF.TrackRank.RANK
            module P : GEF.TRACKPIVOT
            module L : LOWER
          end
        module type OUTPUT =
          functor (OD : OUTPUTDEP) ->
            sig
              module IF : INTERNAL_FEATURES
              type res
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TDet of OD.Det.lstate
                            | `TLower of IF.L.lstate
                            | `TPivot of IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ];
                   .. >,
                 res)
                GEF.cmonad
            end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module PivotRep : GEF.PIVOTKIND
            module Update : UPDATE
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenGE :
          functor (F : FEATURES) ->
            sig
              module O :
                sig
                  module IF :
                    sig
                      module R :
                        sig
                          type tag_lstate = GEF.TrackRank.tag_lstate_
                          val decl :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int ref)
                            GEF.TrackRank.lm
                          val succ :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             unit)
                            GEF.TrackRank.lm
                          val fin :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int)
                            GEF.TrackRank.lm
                        end
                      module P :
                        sig
                          type perm_rep = F.Output(F).IF.P.perm_rep
                          type ira = int Direct.abstract
                          type fra = F.Output(F).IF.P.fra
                          type pra = F.Output(F).IF.P.pra
                          type lstate = F.Output(F).IF.P.lstate
                          type 'a pc_constraint = unit
                            constraint 'a =
                              < state : [> `TPivot of lstate ]; .. >
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TPivot of lstate ];
                                .. >
                          type 'a nm =
                              (< answer : 'b Direct.abstract;
                                 state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Direct.abstract ->
                            < answer : 'a; state : [> `TPivot of lstate ];
                              .. >
                            nm
                          val add :
                            fra ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             unit)
                            GEF.omonad
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             perm_rep)
                            lm
                        end
                      module L :
                        sig
                          type lstate = GAC_R.contr Direct.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GAC_R.contr Direct.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GAC_R.contr)
                            lm
                          val updt :
                            GAC_R.vc ->
                            int Direct.abstract ->
                            int Direct.abstract ->
                            GAC_R.vo ->
                            GAC_R.Dom.vc ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             unit)
                            lm option
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GAC_R.contr)
                            lm
                          val wants_pack : bool
                        end
                    end
                  type res = F.Output(F).res
                  val make_result :
                    wmatrix ->
                    (< answer : 'a;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of IF.L.lstate
                                | `TPivot of IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ];
                       .. >,
                     res)
                    GEF.cmonad
                end
              val wants_pack : bool
              val can_pack : bool
              val zerobelow :
                wmatrix ->
                curposval ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GAC_R.contr Direct.abstract ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GAC_R.contr Direct.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Direct.abstract *
                 int ref Direct.abstract * int Direct.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Direct.abstract * int ref Direct.abstract *
                int Direct.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GAC_R.contr Direct.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
    module Solve :
      sig
        module type INPUT =
          sig
            type inp
            type rhs = GAC_R.contr
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_R.contr Direct.abstract * rhs Direct.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GAC_R.contr * GAC_R.contr
            type rhs = GAC_R.contr
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c Direct.abstract; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GAC_R.contr Direct.abstract ->
              GAC_R.contr Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GAC_R.contr
            val make_result :
              GAC_R.vc ->
              GAC_R.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              'a -> ('a -> GAC_R.contr Direct.abstract -> 'b) -> 'b
          end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenSolve :
          functor (F : FEATURES) ->
            sig
              module GE' :
                sig
                  module O :
                    sig
                      module IF :
                        sig
                          module R :
                            sig
                              type tag_lstate = GEF.TrackRank.tag_lstate_
                              val decl :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int ref)
                                GEF.TrackRank.lm
                              val succ :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 unit)
                                GEF.TrackRank.lm
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int)
                                GEF.TrackRank.lm
                            end
                          module P :
                            sig
                              type perm_rep = GEF.PermList.perm_rep
                              type ira = int Direct.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Direct.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Direct.abstract;
                                     state : 'c list >,
                                   unit)
                                  StateCPSMonad.monad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ] as 'c;
                                    .. >
                              val rowrep : ira -> ira -> fra
                              val colrep : ira -> ira -> fra
                              val decl :
                                int Direct.abstract ->
                                < answer : 'a;
                                  state : [> `TPivot of lstate ]; .. >
                                nm
                              val add :
                                fra ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 unit)
                                GEF.omonad
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 perm_rep)
                                lm
                            end
                          module L :
                            sig
                              type lstate = GAC_R.contr Direct.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GAC_R.contr Direct.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GAC_R.contr)
                                lm
                              val updt :
                                GAC_R.vc ->
                                int Direct.abstract ->
                                int Direct.abstract ->
                                GAC_R.vo ->
                                GAC_R.Dom.vc ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 unit)
                                lm option
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GAC_R.contr)
                                lm
                              val wants_pack : bool
                            end
                        end
                      type res = GAC_R.contr
                      val make_result :
                        wmatrix ->
                        (< answer : 'a;
                           state : [> `TDet of F.Det.lstate
                                    | `TLower of IF.L.lstate
                                    | `TPivot of IF.P.lstate
                                    | `TRan of GEF.TrackRank.lstate ];
                           .. >,
                         res)
                        GEF.cmonad
                    end
                  val wants_pack : bool
                  val can_pack : bool
                  val zerobelow :
                    wmatrix ->
                    curposval ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GAC_R.contr Direct.abstract ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val init :
                    (GAC_R.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GAC_R.contr Direct.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Direct.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Direct.abstract *
                     int ref Direct.abstract * int Direct.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Direct.abstract *
                    int ref Direct.abstract * int Direct.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GAC_R.contr Direct.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val gen :
                    (GAC_R.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Direct.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_R.contr Direct.abstract * F.Input.rhs Direct.abstract)
                StateCPSMonad.monad
              val back_elim :
                GAC_R.vc ->
                int Direct.abstract ->
                int Direct.abstract ->
                'a -> ('a -> GAC_R.contr Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GVC_Z3 :
  sig
    type wmatrix =
      Ge.LAMake(Direct).GenLA(GVC_Z3).wmatrix = {
      matrix : GVC_Z3.vc;
      numrow : int Direct.abstract;
      numcol : int Direct.abstract;
    }
    type curpos =
      Ge.LAMake(Direct).GenLA(GVC_Z3).curpos = {
      rowpos : int Direct.abstract;
      colpos : int Direct.abstract;
    }
    type curposval =
      Ge.LAMake(Direct).GenLA(GVC_Z3).curposval = {
      p : curpos;
      curval : GVC_Z3.Dom.v Direct.abstract;
    }
    module type DETERMINANT =
      sig
        type tdet = GVC_Z3.Dom.v ref
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_Z3.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z3.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z3.Dom.v)
          lm
      end
    module type LOWER =
      sig
        type lstate = GVC_Z3.contr Direct.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GVC_Z3.contr Direct.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GVC_Z3.contr)
          lm
        val updt :
          GVC_Z3.vc ->
          int Direct.abstract ->
          int Direct.abstract ->
          GVC_Z3.vo ->
          GVC_Z3.Dom.vc ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit) lm
          option
        val fin :
          unit ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GVC_Z3.contr)
          lm
        val wants_pack : bool
      end
    module type PIVOT =
      functor (D : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
        sig
          val findpivot :
            wmatrix ->
            curpos ->
            (< answer : 'a;
               state : [> `TDet of D.lstate | `TPivot of P.lstate ]; .. >,
             GVC_Z3.Dom.v option)
            GEF.cmonad
        end
    module NoDet :
      sig
        type tdet = GVC_Z3.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GVC_Z3).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_Z3.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z3.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z3.Dom.v)
          lm
      end
    module AbstractDet :
      sig
        type tdet = GVC_Z3.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GVC_Z3).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_Z3.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z3.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z3.Dom.v)
          lm
      end
    module type UPDATE =
      functor (D : DETERMINANT) ->
        sig
          type in_val = GVC_Z3.Dom.vc
          val update :
            in_val ->
            in_val ->
            in_val ->
            in_val ->
            (in_val -> unit Direct.abstract) ->
            GVC_Z3.Dom.v ref Direct.abstract ->
            (< answer : 'a; state : 'b; .. >, unit) GEF.cmonad
          val update_det :
            in_val ->
            (< answer : 'a; state : [> `TDet of D.lstate ]; .. >, unit) D.lm
          val upd_kind : Ge.update_kind
        end
    module GE :
      sig
        module DivisionUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GVC_Z3.Dom.vc
              val update :
                GVC_Z3.Dom.vc ->
                GVC_Z3.Dom.vc ->
                GVC_Z3.Dom.vc ->
                GVC_Z3.Dom.vc ->
                (GVC_Z3.Dom.vc -> 'a) ->
                'b ->
                (< answer : 'c; state : 'd; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_Z3.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module FractionFreeUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GVC_Z3.Dom.vc
              val update :
                GVC_Z3.Dom.vc ->
                GVC_Z3.Dom.vc ->
                GVC_Z3.Dom.vc ->
                GVC_Z3.Dom.vc ->
                (GVC_Z3.Dom.vc -> 'a) ->
                GVC_Z3.Dom.v ref Direct.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_Z3.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GVC_Z3.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GVC_Z3.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Direct.abstract ->
              (< answer : 'b Direct.abstract;
                 state : [> `TLower of 'a Direct.abstract ] list; .. >,
               'a Direct.abstract)
              StateCPSMonad.monad
            val updt :
              GVC_Z3.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GVC_Z3.vo ->
              GVC_Z3.vo ->
              (< answer : 'a; state : [> `TLower of GVC_Z3.vc ] list; .. >,
               unit Direct.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GVC_Z3.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a ->
              (< answer : 'b; state : [> `TLower of 'a ] list; .. >, 'a)
              StateCPSMonad.monad
            val updt : 'a -> 'b -> 'c -> 'd -> 'e -> 'f option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module NoLower :
          sig
            type lstate = GVC_Z3.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a -> (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
            val updt :
              GVC_Z3.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GVC_Z3.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Direct.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z3.contr Direct.abstract * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GVC_Z3.contr
            val get_input :
              GVC_Z3.vc ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z3.vc * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GVC_Z3.contr * int
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_Z3.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_Z3.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_Z3.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module type OUTPUTDEP =
          sig module PivotRep : GEF.PIVOTKIND module Det : DETERMINANT end
        module OutJustMatrix :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_Z3.contr
              val make_result :
                wmatrix ->
                (< answer : 'a; state : 'b; .. >, GVC_Z3.vc)
                StateCPSMonad.monad
            end
        module OutDet :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_Z3.contr * GVC_Z3.Dom.v
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GVC_Z3.contr * GVC_Z3.Dom.v) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_Z3.contr * int
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TRan of 'b ref Direct.abstract ] list; .. >,
                 (GVC_Z3.contr * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_Z3.contr * GVC_Z3.Dom.v * int
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_Z3.contr * GVC_Z3.Dom.v * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRankPivot :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GVC_Z3.contr * GVC_Z3.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Direct.abstract
                            | `TRan of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_Z3.contr * GVC_Z3.Dom.v * 'c * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_L_U :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GVC_Z3.contr * GVC_Z3.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Direct.abstract
                            | `TPivot of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_Z3.contr * 'b * 'c) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_LU_Packed :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GVC_Z3.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Direct.abstract
                            | `TPivot of 'd ref Direct.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Direct.abstract)
                StateCPSMonad.monad
            end
        module type INTERNAL_FEATURES =
          sig
            module R : GEF.TrackRank.RANK
            module P : GEF.TRACKPIVOT
            module L : LOWER
          end
        module type OUTPUT =
          functor (OD : OUTPUTDEP) ->
            sig
              module IF : INTERNAL_FEATURES
              type res
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TDet of OD.Det.lstate
                            | `TLower of IF.L.lstate
                            | `TPivot of IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ];
                   .. >,
                 res)
                GEF.cmonad
            end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module PivotRep : GEF.PIVOTKIND
            module Update : UPDATE
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenGE :
          functor (F : FEATURES) ->
            sig
              module O :
                sig
                  module IF :
                    sig
                      module R :
                        sig
                          type tag_lstate = GEF.TrackRank.tag_lstate_
                          val decl :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int ref)
                            GEF.TrackRank.lm
                          val succ :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             unit)
                            GEF.TrackRank.lm
                          val fin :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int)
                            GEF.TrackRank.lm
                        end
                      module P :
                        sig
                          type perm_rep = F.Output(F).IF.P.perm_rep
                          type ira = int Direct.abstract
                          type fra = F.Output(F).IF.P.fra
                          type pra = F.Output(F).IF.P.pra
                          type lstate = F.Output(F).IF.P.lstate
                          type 'a pc_constraint = unit
                            constraint 'a =
                              < state : [> `TPivot of lstate ]; .. >
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TPivot of lstate ];
                                .. >
                          type 'a nm =
                              (< answer : 'b Direct.abstract;
                                 state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Direct.abstract ->
                            < answer : 'a; state : [> `TPivot of lstate ];
                              .. >
                            nm
                          val add :
                            fra ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             unit)
                            GEF.omonad
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             perm_rep)
                            lm
                        end
                      module L :
                        sig
                          type lstate = GVC_Z3.contr Direct.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GVC_Z3.contr Direct.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_Z3.contr)
                            lm
                          val updt :
                            GVC_Z3.vc ->
                            int Direct.abstract ->
                            int Direct.abstract ->
                            GVC_Z3.vo ->
                            GVC_Z3.Dom.vc ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             unit)
                            lm option
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_Z3.contr)
                            lm
                          val wants_pack : bool
                        end
                    end
                  type res = F.Output(F).res
                  val make_result :
                    wmatrix ->
                    (< answer : 'a;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of IF.L.lstate
                                | `TPivot of IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ];
                       .. >,
                     res)
                    GEF.cmonad
                end
              val wants_pack : bool
              val can_pack : bool
              val zerobelow :
                wmatrix ->
                curposval ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_Z3.contr Direct.abstract ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GVC_Z3.contr Direct.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Direct.abstract *
                 int ref Direct.abstract * int Direct.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Direct.abstract * int ref Direct.abstract *
                int Direct.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_Z3.contr Direct.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
    module Solve :
      sig
        module type INPUT =
          sig
            type inp
            type rhs = GVC_Z3.contr
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z3.contr Direct.abstract * rhs Direct.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GVC_Z3.contr * GVC_Z3.contr
            type rhs = GVC_Z3.contr
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c Direct.abstract; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GVC_Z3.contr Direct.abstract ->
              GVC_Z3.contr Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GVC_Z3.contr
            val make_result :
              GVC_Z3.vc ->
              GVC_Z3.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              'a -> ('a -> GVC_Z3.contr Direct.abstract -> 'b) -> 'b
          end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenSolve :
          functor (F : FEATURES) ->
            sig
              module GE' :
                sig
                  module O :
                    sig
                      module IF :
                        sig
                          module R :
                            sig
                              type tag_lstate = GEF.TrackRank.tag_lstate_
                              val decl :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int ref)
                                GEF.TrackRank.lm
                              val succ :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 unit)
                                GEF.TrackRank.lm
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int)
                                GEF.TrackRank.lm
                            end
                          module P :
                            sig
                              type perm_rep = GEF.PermList.perm_rep
                              type ira = int Direct.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Direct.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Direct.abstract;
                                     state : 'c list >,
                                   unit)
                                  StateCPSMonad.monad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ] as 'c;
                                    .. >
                              val rowrep : ira -> ira -> fra
                              val colrep : ira -> ira -> fra
                              val decl :
                                int Direct.abstract ->
                                < answer : 'a;
                                  state : [> `TPivot of lstate ]; .. >
                                nm
                              val add :
                                fra ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 unit)
                                GEF.omonad
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 perm_rep)
                                lm
                            end
                          module L :
                            sig
                              type lstate = GVC_Z3.contr Direct.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GVC_Z3.contr Direct.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_Z3.contr)
                                lm
                              val updt :
                                GVC_Z3.vc ->
                                int Direct.abstract ->
                                int Direct.abstract ->
                                GVC_Z3.vo ->
                                GVC_Z3.Dom.vc ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 unit)
                                lm option
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_Z3.contr)
                                lm
                              val wants_pack : bool
                            end
                        end
                      type res = GVC_Z3.contr
                      val make_result :
                        wmatrix ->
                        (< answer : 'a;
                           state : [> `TDet of F.Det.lstate
                                    | `TLower of IF.L.lstate
                                    | `TPivot of IF.P.lstate
                                    | `TRan of GEF.TrackRank.lstate ];
                           .. >,
                         res)
                        GEF.cmonad
                    end
                  val wants_pack : bool
                  val can_pack : bool
                  val zerobelow :
                    wmatrix ->
                    curposval ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_Z3.contr Direct.abstract ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val init :
                    (GVC_Z3.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GVC_Z3.contr Direct.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Direct.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Direct.abstract *
                     int ref Direct.abstract * int Direct.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Direct.abstract *
                    int ref Direct.abstract * int Direct.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_Z3.contr Direct.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val gen :
                    (GVC_Z3.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Direct.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_Z3.contr Direct.abstract * F.Input.rhs Direct.abstract)
                StateCPSMonad.monad
              val back_elim :
                GVC_Z3.vc ->
                int Direct.abstract ->
                int Direct.abstract ->
                'a -> ('a -> GVC_Z3.contr Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GVC_Z19 :
  sig
    type wmatrix =
      Ge.LAMake(Direct).GenLA(GVC_Z19).wmatrix = {
      matrix : GVC_Z19.vc;
      numrow : int Direct.abstract;
      numcol : int Direct.abstract;
    }
    type curpos =
      Ge.LAMake(Direct).GenLA(GVC_Z19).curpos = {
      rowpos : int Direct.abstract;
      colpos : int Direct.abstract;
    }
    type curposval =
      Ge.LAMake(Direct).GenLA(GVC_Z19).curposval = {
      p : curpos;
      curval : GVC_Z19.Dom.v Direct.abstract;
    }
    module type DETERMINANT =
      sig
        type tdet = GVC_Z19.Dom.v ref
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_Z19.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z19.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z19.Dom.v)
          lm
      end
    module type LOWER =
      sig
        type lstate = GVC_Z19.contr Direct.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GVC_Z19.contr Direct.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >,
           GVC_Z19.contr)
          lm
        val updt :
          GVC_Z19.vc ->
          int Direct.abstract ->
          int Direct.abstract ->
          GVC_Z19.vo ->
          GVC_Z19.Dom.vc ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit) lm
          option
        val fin :
          unit ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >,
           GVC_Z19.contr)
          lm
        val wants_pack : bool
      end
    module type PIVOT =
      functor (D : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
        sig
          val findpivot :
            wmatrix ->
            curpos ->
            (< answer : 'a;
               state : [> `TDet of D.lstate | `TPivot of P.lstate ]; .. >,
             GVC_Z19.Dom.v option)
            GEF.cmonad
        end
    module NoDet :
      sig
        type tdet = GVC_Z19.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GVC_Z19).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_Z19.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z19.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z19.Dom.v)
          lm
      end
    module AbstractDet :
      sig
        type tdet = GVC_Z19.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GVC_Z19).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GVC_Z19.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z19.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z19.Dom.v)
          lm
      end
    module type UPDATE =
      functor (D : DETERMINANT) ->
        sig
          type in_val = GVC_Z19.Dom.vc
          val update :
            in_val ->
            in_val ->
            in_val ->
            in_val ->
            (in_val -> unit Direct.abstract) ->
            GVC_Z19.Dom.v ref Direct.abstract ->
            (< answer : 'a; state : 'b; .. >, unit) GEF.cmonad
          val update_det :
            in_val ->
            (< answer : 'a; state : [> `TDet of D.lstate ]; .. >, unit) D.lm
          val upd_kind : Ge.update_kind
        end
    module GE :
      sig
        module DivisionUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GVC_Z19.Dom.vc
              val update :
                GVC_Z19.Dom.vc ->
                GVC_Z19.Dom.vc ->
                GVC_Z19.Dom.vc ->
                GVC_Z19.Dom.vc ->
                (GVC_Z19.Dom.vc -> 'a) ->
                'b ->
                (< answer : 'c; state : 'd; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_Z19.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module FractionFreeUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GVC_Z19.Dom.vc
              val update :
                GVC_Z19.Dom.vc ->
                GVC_Z19.Dom.vc ->
                GVC_Z19.Dom.vc ->
                GVC_Z19.Dom.vc ->
                (GVC_Z19.Dom.vc -> 'a) ->
                GVC_Z19.Dom.v ref Direct.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_Z19.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GVC_Z19.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GVC_Z19.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Direct.abstract ->
              (< answer : 'b Direct.abstract;
                 state : [> `TLower of 'a Direct.abstract ] list; .. >,
               'a Direct.abstract)
              StateCPSMonad.monad
            val updt :
              GVC_Z19.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GVC_Z19.vo ->
              GVC_Z19.vo ->
              (< answer : 'a; state : [> `TLower of GVC_Z19.vc ] list; .. >,
               unit Direct.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GVC_Z19.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a ->
              (< answer : 'b; state : [> `TLower of 'a ] list; .. >, 'a)
              StateCPSMonad.monad
            val updt : 'a -> 'b -> 'c -> 'd -> 'e -> 'f option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module NoLower :
          sig
            type lstate = GVC_Z19.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a -> (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
            val updt :
              GVC_Z19.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GVC_Z19.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Direct.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z19.contr Direct.abstract * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GVC_Z19.contr
            val get_input :
              GVC_Z19.vc ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z19.vc * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GVC_Z19.contr * int
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_Z19.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_Z19.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_Z19.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module type OUTPUTDEP =
          sig module PivotRep : GEF.PIVOTKIND module Det : DETERMINANT end
        module OutJustMatrix :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_Z19.contr
              val make_result :
                wmatrix ->
                (< answer : 'a; state : 'b; .. >, GVC_Z19.vc)
                StateCPSMonad.monad
            end
        module OutDet :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_Z19.contr * GVC_Z19.Dom.v
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GVC_Z19.contr * GVC_Z19.Dom.v) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_Z19.contr * int
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TRan of 'b ref Direct.abstract ] list; .. >,
                 (GVC_Z19.contr * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GVC_Z19.contr * GVC_Z19.Dom.v * int
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_Z19.contr * GVC_Z19.Dom.v * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRankPivot :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GVC_Z19.contr * GVC_Z19.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Direct.abstract
                            | `TRan of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_Z19.contr * GVC_Z19.Dom.v * 'c * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_L_U :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GVC_Z19.contr * GVC_Z19.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Direct.abstract
                            | `TPivot of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GVC_Z19.contr * 'b * 'c) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_LU_Packed :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GVC_Z19.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Direct.abstract
                            | `TPivot of 'd ref Direct.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Direct.abstract)
                StateCPSMonad.monad
            end
        module type INTERNAL_FEATURES =
          sig
            module R : GEF.TrackRank.RANK
            module P : GEF.TRACKPIVOT
            module L : LOWER
          end
        module type OUTPUT =
          functor (OD : OUTPUTDEP) ->
            sig
              module IF : INTERNAL_FEATURES
              type res
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TDet of OD.Det.lstate
                            | `TLower of IF.L.lstate
                            | `TPivot of IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ];
                   .. >,
                 res)
                GEF.cmonad
            end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module PivotRep : GEF.PIVOTKIND
            module Update : UPDATE
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenGE :
          functor (F : FEATURES) ->
            sig
              module O :
                sig
                  module IF :
                    sig
                      module R :
                        sig
                          type tag_lstate = GEF.TrackRank.tag_lstate_
                          val decl :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int ref)
                            GEF.TrackRank.lm
                          val succ :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             unit)
                            GEF.TrackRank.lm
                          val fin :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int)
                            GEF.TrackRank.lm
                        end
                      module P :
                        sig
                          type perm_rep = F.Output(F).IF.P.perm_rep
                          type ira = int Direct.abstract
                          type fra = F.Output(F).IF.P.fra
                          type pra = F.Output(F).IF.P.pra
                          type lstate = F.Output(F).IF.P.lstate
                          type 'a pc_constraint = unit
                            constraint 'a =
                              < state : [> `TPivot of lstate ]; .. >
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TPivot of lstate ];
                                .. >
                          type 'a nm =
                              (< answer : 'b Direct.abstract;
                                 state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Direct.abstract ->
                            < answer : 'a; state : [> `TPivot of lstate ];
                              .. >
                            nm
                          val add :
                            fra ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             unit)
                            GEF.omonad
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             perm_rep)
                            lm
                        end
                      module L :
                        sig
                          type lstate = GVC_Z19.contr Direct.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GVC_Z19.contr Direct.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_Z19.contr)
                            lm
                          val updt :
                            GVC_Z19.vc ->
                            int Direct.abstract ->
                            int Direct.abstract ->
                            GVC_Z19.vo ->
                            GVC_Z19.Dom.vc ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             unit)
                            lm option
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_Z19.contr)
                            lm
                          val wants_pack : bool
                        end
                    end
                  type res = F.Output(F).res
                  val make_result :
                    wmatrix ->
                    (< answer : 'a;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of IF.L.lstate
                                | `TPivot of IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ];
                       .. >,
                     res)
                    GEF.cmonad
                end
              val wants_pack : bool
              val can_pack : bool
              val zerobelow :
                wmatrix ->
                curposval ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_Z19.contr Direct.abstract ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GVC_Z19.contr Direct.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Direct.abstract *
                 int ref Direct.abstract * int Direct.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Direct.abstract * int ref Direct.abstract *
                int Direct.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_Z19.contr Direct.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
    module Solve :
      sig
        module type INPUT =
          sig
            type inp
            type rhs = GVC_Z19.contr
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z19.contr Direct.abstract * rhs Direct.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GVC_Z19.contr * GVC_Z19.contr
            type rhs = GVC_Z19.contr
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c Direct.abstract; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GVC_Z19.contr Direct.abstract ->
              GVC_Z19.contr Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GVC_Z19.contr
            val make_result :
              GVC_Z19.vc ->
              GVC_Z19.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              'a -> ('a -> GVC_Z19.contr Direct.abstract -> 'b) -> 'b
          end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenSolve :
          functor (F : FEATURES) ->
            sig
              module GE' :
                sig
                  module O :
                    sig
                      module IF :
                        sig
                          module R :
                            sig
                              type tag_lstate = GEF.TrackRank.tag_lstate_
                              val decl :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int ref)
                                GEF.TrackRank.lm
                              val succ :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 unit)
                                GEF.TrackRank.lm
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int)
                                GEF.TrackRank.lm
                            end
                          module P :
                            sig
                              type perm_rep = GEF.PermList.perm_rep
                              type ira = int Direct.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Direct.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Direct.abstract;
                                     state : 'c list >,
                                   unit)
                                  StateCPSMonad.monad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ] as 'c;
                                    .. >
                              val rowrep : ira -> ira -> fra
                              val colrep : ira -> ira -> fra
                              val decl :
                                int Direct.abstract ->
                                < answer : 'a;
                                  state : [> `TPivot of lstate ]; .. >
                                nm
                              val add :
                                fra ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 unit)
                                GEF.omonad
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 perm_rep)
                                lm
                            end
                          module L :
                            sig
                              type lstate = GVC_Z19.contr Direct.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GVC_Z19.contr Direct.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_Z19.contr)
                                lm
                              val updt :
                                GVC_Z19.vc ->
                                int Direct.abstract ->
                                int Direct.abstract ->
                                GVC_Z19.vo ->
                                GVC_Z19.Dom.vc ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 unit)
                                lm option
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_Z19.contr)
                                lm
                              val wants_pack : bool
                            end
                        end
                      type res = GVC_Z19.contr
                      val make_result :
                        wmatrix ->
                        (< answer : 'a;
                           state : [> `TDet of F.Det.lstate
                                    | `TLower of IF.L.lstate
                                    | `TPivot of IF.P.lstate
                                    | `TRan of GEF.TrackRank.lstate ];
                           .. >,
                         res)
                        GEF.cmonad
                    end
                  val wants_pack : bool
                  val can_pack : bool
                  val zerobelow :
                    wmatrix ->
                    curposval ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_Z19.contr Direct.abstract ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val init :
                    (GVC_Z19.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GVC_Z19.contr Direct.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Direct.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Direct.abstract *
                     int ref Direct.abstract * int Direct.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Direct.abstract *
                    int ref Direct.abstract * int Direct.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_Z19.contr Direct.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val gen :
                    (GVC_Z19.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Direct.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_Z19.contr Direct.abstract * F.Input.rhs Direct.abstract)
                StateCPSMonad.monad
              val back_elim :
                GVC_Z19.vc ->
                int Direct.abstract ->
                int Direct.abstract ->
                'a -> ('a -> GVC_Z19.contr Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GFC_F :
  sig
    type wmatrix =
      Ge.LAMake(Direct).GenLA(GFC_F).wmatrix = {
      matrix : GFC_F.vc;
      numrow : int Direct.abstract;
      numcol : int Direct.abstract;
    }
    type curpos =
      Ge.LAMake(Direct).GenLA(GFC_F).curpos = {
      rowpos : int Direct.abstract;
      colpos : int Direct.abstract;
    }
    type curposval =
      Ge.LAMake(Direct).GenLA(GFC_F).curposval = {
      p : curpos;
      curval : GFC_F.Dom.v Direct.abstract;
    }
    module type DETERMINANT =
      sig
        type tdet = GFC_F.Dom.v ref
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GFC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GFC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GFC_F.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GFC_F.contr Direct.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GFC_F.contr Direct.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GFC_F.contr)
          lm
        val updt :
          GFC_F.vc ->
          int Direct.abstract ->
          int Direct.abstract ->
          GFC_F.vo ->
          GFC_F.Dom.vc ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit) lm
          option
        val fin :
          unit ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GFC_F.contr)
          lm
        val wants_pack : bool
      end
    module type PIVOT =
      functor (D : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
        sig
          val findpivot :
            wmatrix ->
            curpos ->
            (< answer : 'a;
               state : [> `TDet of D.lstate | `TPivot of P.lstate ]; .. >,
             GFC_F.Dom.v option)
            GEF.cmonad
        end
    module NoDet :
      sig
        type tdet = GFC_F.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GFC_F).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GFC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GFC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GFC_F.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GFC_F.Dom.v ref
        type lstate = Ge.LAMake(Direct).GenLA(GFC_F).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Direct.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TDet of lstate ] as 'c; .. >
        val decl :
          unit -> < answer : 'a; state : [> `TDet of lstate ]; .. > nm
        val upd_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) om
        val zero_sign :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val acc_magn :
          GFC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GFC_F.Dom.v Direct.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GFC_F.Dom.v) lm
      end
    module type UPDATE =
      functor (D : DETERMINANT) ->
        sig
          type in_val = GFC_F.Dom.vc
          val update :
            in_val ->
            in_val ->
            in_val ->
            in_val ->
            (in_val -> unit Direct.abstract) ->
            GFC_F.Dom.v ref Direct.abstract ->
            (< answer : 'a; state : 'b; .. >, unit) GEF.cmonad
          val update_det :
            in_val ->
            (< answer : 'a; state : [> `TDet of D.lstate ]; .. >, unit) D.lm
          val upd_kind : Ge.update_kind
        end
    module GE :
      sig
        module DivisionUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GFC_F.Dom.vc
              val update :
                GFC_F.Dom.vc ->
                GFC_F.Dom.vc ->
                GFC_F.Dom.vc ->
                GFC_F.Dom.vc ->
                (GFC_F.Dom.vc -> 'a) ->
                'b ->
                (< answer : 'c; state : 'd; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GFC_F.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module FractionFreeUpdate :
          functor (Det : DETERMINANT) ->
            sig
              type in_val = GFC_F.Dom.vc
              val update :
                GFC_F.Dom.vc ->
                GFC_F.Dom.vc ->
                GFC_F.Dom.vc ->
                GFC_F.Dom.vc ->
                (GFC_F.Dom.vc -> 'a) ->
                GFC_F.Dom.v ref Direct.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GFC_F.Dom.v Direct.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GFC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GFC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Direct.abstract ->
              (< answer : 'b Direct.abstract;
                 state : [> `TLower of 'a Direct.abstract ] list; .. >,
               'a Direct.abstract)
              StateCPSMonad.monad
            val updt :
              GFC_F.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GFC_F.vo ->
              GFC_F.vo ->
              (< answer : 'a; state : [> `TLower of GFC_F.vc ] list; .. >,
               unit Direct.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GFC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a ->
              (< answer : 'b; state : [> `TLower of 'a ] list; .. >, 'a)
              StateCPSMonad.monad
            val updt : 'a -> 'b -> 'c -> 'd -> 'e -> 'f option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module NoLower :
          sig
            type lstate = GFC_F.contr Direct.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a -> (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
            val updt :
              GFC_F.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              GFC_F.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Direct.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GFC_F.contr Direct.abstract * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GFC_F.contr
            val get_input :
              GFC_F.vc ->
              (< answer : 'a; state : 'b; .. >,
               GFC_F.vc * int Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GFC_F.contr * int
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GFC_F.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GFC_F.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GFC_F.Dom.v option Direct.abstract)
                StateCPSMonad.monad
            end
        module type OUTPUTDEP =
          sig module PivotRep : GEF.PIVOTKIND module Det : DETERMINANT end
        module OutJustMatrix :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GFC_F.contr
              val make_result :
                wmatrix ->
                (< answer : 'a; state : 'b; .. >, GFC_F.vc)
                StateCPSMonad.monad
            end
        module OutDet :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GFC_F.contr * GFC_F.Dom.v
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GFC_F.contr * GFC_F.Dom.v) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GFC_F.contr * int
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TRan of 'b ref Direct.abstract ] list; .. >,
                 (GFC_F.contr * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRank :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P = GEF.DiscardPivot
                  module L = NoLower
                end
              type res = GFC_F.contr * GFC_F.Dom.v * int
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Direct.abstract ]
                           list;
                   .. >,
                 (GFC_F.contr * GFC_F.Dom.v * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module OutDetRankPivot :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.Rank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GFC_F.contr * GFC_F.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Direct.abstract
                            | `TRan of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GFC_F.contr * GFC_F.Dom.v * 'c * 'b) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_L_U :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GFC_F.contr * GFC_F.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Direct.abstract
                            | `TPivot of 'c ref Direct.abstract ]
                           list;
                   .. >,
                 (GFC_F.contr * 'b * 'c) Direct.abstract)
                StateCPSMonad.monad
            end
        module Out_LU_Packed :
          functor (OD : OUTPUTDEP) ->
            sig
              module IF :
                sig
                  module R = GEF.NoRank
                  module P :
                    sig
                      type perm_rep = OD.PivotRep.perm_rep
                      type ira = OD.PivotRep.ira
                      type fra = OD.PivotRep.fra
                      type pra = OD.PivotRep.pra
                      type lstate = OD.PivotRep.perm_rep ref Direct.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Direct.abstract; state : 'c list >,
                           unit)
                          StateCPSMonad.monad
                        constraint 'a =
                          < answer : 'b;
                            state : [> `TPivot of lstate ] as 'c; .. >
                      val rowrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val colrep :
                        OD.PivotRep.ira -> OD.PivotRep.ira -> OD.PivotRep.fra
                      val ip :
                        ('a -> [> `TPivot of 'a ]) *
                        ([> `TPivot of 'b ] -> 'b option) * string
                      val decl :
                        OD.PivotRep.ira ->
                        (< answer : 'a Direct.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Direct.abstract ]
                                   list;
                           .. >,
                         unit Direct.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Direct.abstract ]
                                   list;
                           .. >,
                         'b Direct.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GFC_F.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Direct.abstract
                            | `TPivot of 'd ref Direct.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Direct.abstract)
                StateCPSMonad.monad
            end
        module type INTERNAL_FEATURES =
          sig
            module R : GEF.TrackRank.RANK
            module P : GEF.TRACKPIVOT
            module L : LOWER
          end
        module type OUTPUT =
          functor (OD : OUTPUTDEP) ->
            sig
              module IF : INTERNAL_FEATURES
              type res
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TDet of OD.Det.lstate
                            | `TLower of IF.L.lstate
                            | `TPivot of IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ];
                   .. >,
                 res)
                GEF.cmonad
            end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module PivotRep : GEF.PIVOTKIND
            module Update : UPDATE
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenGE :
          functor (F : FEATURES) ->
            sig
              module O :
                sig
                  module IF :
                    sig
                      module R :
                        sig
                          type tag_lstate = GEF.TrackRank.tag_lstate_
                          val decl :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int ref)
                            GEF.TrackRank.lm
                          val succ :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             unit)
                            GEF.TrackRank.lm
                          val fin :
                            unit ->
                            (< answer : 'a;
                               state : [> GEF.TrackRank.tag_lstate ]; .. >,
                             int)
                            GEF.TrackRank.lm
                        end
                      module P :
                        sig
                          type perm_rep = F.Output(F).IF.P.perm_rep
                          type ira = int Direct.abstract
                          type fra = F.Output(F).IF.P.fra
                          type pra = F.Output(F).IF.P.pra
                          type lstate = F.Output(F).IF.P.lstate
                          type 'a pc_constraint = unit
                            constraint 'a =
                              < state : [> `TPivot of lstate ]; .. >
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TPivot of lstate ];
                                .. >
                          type 'a nm =
                              (< answer : 'b Direct.abstract;
                                 state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Direct.abstract ->
                            < answer : 'a; state : [> `TPivot of lstate ];
                              .. >
                            nm
                          val add :
                            fra ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             unit)
                            GEF.omonad
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TPivot of lstate ];
                               .. >,
                             perm_rep)
                            lm
                        end
                      module L :
                        sig
                          type lstate = GFC_F.contr Direct.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GFC_F.contr Direct.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GFC_F.contr)
                            lm
                          val updt :
                            GFC_F.vc ->
                            int Direct.abstract ->
                            int Direct.abstract ->
                            GFC_F.vo ->
                            GFC_F.Dom.vc ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             unit)
                            lm option
                          val fin :
                            unit ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GFC_F.contr)
                            lm
                          val wants_pack : bool
                        end
                    end
                  type res = F.Output(F).res
                  val make_result :
                    wmatrix ->
                    (< answer : 'a;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of IF.L.lstate
                                | `TPivot of IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ];
                       .. >,
                     res)
                    GEF.cmonad
                end
              val wants_pack : bool
              val can_pack : bool
              val zerobelow :
                wmatrix ->
                curposval ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GFC_F.contr Direct.abstract ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GFC_F.contr Direct.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Direct.abstract *
                 int ref Direct.abstract * int Direct.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Direct.abstract * int ref Direct.abstract *
                int Direct.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GFC_F.contr Direct.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
    module Solve :
      sig
        module type INPUT =
          sig
            type inp
            type rhs = GFC_F.contr
            val get_input :
              inp Direct.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GFC_F.contr Direct.abstract * rhs Direct.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GFC_F.contr * GFC_F.contr
            type rhs = GFC_F.contr
            val get_input :
              ('a * 'b) Direct.abstract ->
              (< answer : 'c Direct.abstract; state : 'd; .. >,
               'a Direct.abstract * 'b Direct.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GFC_F.contr Direct.abstract ->
              GFC_F.contr Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GFC_F.contr
            val make_result :
              GFC_F.vc ->
              GFC_F.vc ->
              int Direct.abstract ->
              int Direct.abstract ->
              int Direct.abstract ->
              'a -> ('a -> GFC_F.contr Direct.abstract -> 'b) -> 'b
          end
        module type FEATURES =
          sig
            module Det : DETERMINANT
            module PivotF : PIVOT
            module Input : INPUT
            module Output : OUTPUT
          end
        module GenSolve :
          functor (F : FEATURES) ->
            sig
              module GE' :
                sig
                  module O :
                    sig
                      module IF :
                        sig
                          module R :
                            sig
                              type tag_lstate = GEF.TrackRank.tag_lstate_
                              val decl :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int ref)
                                GEF.TrackRank.lm
                              val succ :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 unit)
                                GEF.TrackRank.lm
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> GEF.TrackRank.tag_lstate ];
                                   .. >,
                                 int)
                                GEF.TrackRank.lm
                            end
                          module P :
                            sig
                              type perm_rep = GEF.PermList.perm_rep
                              type ira = int Direct.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Direct.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Direct.abstract;
                                     state : 'c list >,
                                   unit)
                                  StateCPSMonad.monad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ] as 'c;
                                    .. >
                              val rowrep : ira -> ira -> fra
                              val colrep : ira -> ira -> fra
                              val decl :
                                int Direct.abstract ->
                                < answer : 'a;
                                  state : [> `TPivot of lstate ]; .. >
                                nm
                              val add :
                                fra ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 unit)
                                GEF.omonad
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TPivot of lstate ]; .. >,
                                 perm_rep)
                                lm
                            end
                          module L :
                            sig
                              type lstate = GFC_F.contr Direct.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GFC_F.contr Direct.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GFC_F.contr)
                                lm
                              val updt :
                                GFC_F.vc ->
                                int Direct.abstract ->
                                int Direct.abstract ->
                                GFC_F.vo ->
                                GFC_F.Dom.vc ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 unit)
                                lm option
                              val fin :
                                unit ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GFC_F.contr)
                                lm
                              val wants_pack : bool
                            end
                        end
                      type res = GFC_F.contr
                      val make_result :
                        wmatrix ->
                        (< answer : 'a;
                           state : [> `TDet of F.Det.lstate
                                    | `TLower of IF.L.lstate
                                    | `TPivot of IF.P.lstate
                                    | `TRan of GEF.TrackRank.lstate ];
                           .. >,
                         res)
                        GEF.cmonad
                    end
                  val wants_pack : bool
                  val can_pack : bool
                  val zerobelow :
                    wmatrix ->
                    curposval ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GFC_F.contr Direct.abstract ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val init :
                    (GFC_F.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GFC_F.contr Direct.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Direct.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Direct.abstract *
                     int ref Direct.abstract * int Direct.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Direct.abstract *
                    int ref Direct.abstract * int Direct.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GFC_F.contr Direct.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
                  val gen :
                    (GFC_F.contr * int) Direct.abstract ->
                    (< answer : 'a Direct.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Direct.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Direct.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GFC_F.contr Direct.abstract * F.Input.rhs Direct.abstract)
                StateCPSMonad.monad
              val back_elim :
                GFC_F.vc ->
                int Direct.abstract ->
                int Direct.abstract ->
                'a -> ('a -> GFC_F.contr Direct.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Direct.abstract ->
                (< answer : 'a Direct.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Direct.abstract)
                StateCPSMonad.monad
            end
      end
  end
module GenFA1 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA2 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * GAC_F.Dom.v
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA3 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * int
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA4 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * GAC_F.Dom.v * int
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA11 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA12 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * GAC_F.Dom.v
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA13 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * int
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA14 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * GAC_F.Dom.v * int
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA24 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = Prelude.perm list
                type ira = int Direct.abstract
                type fra = Prelude.perm Direct.abstract
                type pra = Prelude.perm list Direct.abstract
                type lstate = Prelude.perm list ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * GAC_F.Dom.v * int * Prelude.perm list
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of Prelude.perm list ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of Prelude.perm list ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA25 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = int array
                type ira = int Direct.abstract
                type fra = (int * int) Direct.abstract
                type pra = int array Direct.abstract
                type lstate = int array ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * GAC_F.Dom.v * int * int array
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of int array ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of int array ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA26 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA5 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      (GAC_F.contr * int) Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      (GAC_F.contr * int) Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA6 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * GAC_F.Dom.v
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      (GAC_F.contr * int) Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      (GAC_F.contr * int) Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA7 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * int
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      (GAC_F.contr * int) Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      (GAC_F.contr * int) Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA8 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * GAC_F.Dom.v * int
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      (GAC_F.contr * int) Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      (GAC_F.contr * int) Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA9 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = Prelude.perm list
                type ira = int Direct.abstract
                type fra = Prelude.perm Direct.abstract
                type pra = Prelude.perm list Direct.abstract
                type lstate = Prelude.perm list ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * Prelude.perm list
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of Prelude.perm list ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of Prelude.perm list ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA31 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = Prelude.perm list
                type ira = int Direct.abstract
                type fra = Prelude.perm Direct.abstract
                type pra = Prelude.perm list Direct.abstract
                type lstate = Prelude.perm list ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * GAC_F.contr * Prelude.perm list
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of Prelude.perm list ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of Prelude.perm list ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFA32 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = Prelude.perm list
                type ira = int Direct.abstract
                type fra = Prelude.perm Direct.abstract
                type pra = Prelude.perm list Direct.abstract
                type lstate = Prelude.perm list ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_F.vo ->
                  GAC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_F.contr * Prelude.perm list
        val make_result :
          G_GAC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_F.wmatrix ->
      G_GAC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Direct.abstract
                  | `TPivot of Prelude.perm list ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Direct.abstract
        | `TPivot of Prelude.perm list ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFV1 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_F.vo ->
                  GVC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_F.contr
        val make_result :
          G_GVC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_F.wmatrix ->
      G_GVC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                  | `TLower of GVC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFV2 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_F.vo ->
                  GVC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_F.contr * GVC_F.Dom.v
        val make_result :
          G_GVC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_F.wmatrix ->
      G_GVC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of GVC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFV3 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_F.vo ->
                  GVC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_F.contr * int
        val make_result :
          G_GVC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_F.wmatrix ->
      G_GVC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                  | `TLower of GVC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFV4 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_F.vo ->
                  GVC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_F.contr * GVC_F.Dom.v * int
        val make_result :
          G_GVC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_F.wmatrix ->
      G_GVC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of GVC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFV5 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_F.vo ->
                  GVC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_F.contr * GVC_F.Dom.v * int
        val make_result :
          G_GVC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_F.wmatrix ->
      G_GVC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of GVC_F.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFV6 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = Prelude.perm list
                type ira = int Direct.abstract
                type fra = Prelude.perm Direct.abstract
                type pra = Prelude.perm list Direct.abstract
                type lstate = Prelude.perm list ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_F.vo ->
                  GVC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_F.contr * GVC_F.contr * Prelude.perm list
        val make_result :
          G_GVC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_F.wmatrix ->
      G_GVC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                  | `TLower of GVC_F.contr Direct.abstract
                  | `TPivot of Prelude.perm list ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Direct.abstract
        | `TPivot of Prelude.perm list ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenFV7 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = Prelude.perm list
                type ira = int Direct.abstract
                type fra = Prelude.perm Direct.abstract
                type pra = Prelude.perm list Direct.abstract
                type lstate = Prelude.perm list ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_F.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_F.vo ->
                  GVC_F.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_F.contr * Prelude.perm list
        val make_result :
          G_GVC_F.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_F.wmatrix ->
      G_GVC_F.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                  | `TLower of GVC_F.contr Direct.abstract
                  | `TPivot of Prelude.perm list ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Direct.abstract
        | `TPivot of Prelude.perm list ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GVC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenIA1 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val updt :
                  GAC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_I.vo ->
                  GAC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_I.contr
        val make_result :
          G_GAC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_I.wmatrix ->
      G_GAC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of GAC_I.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
- : unit = ()
module GenIA2 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val updt :
                  GAC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_I.vo ->
                  GAC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_I.contr * GAC_I.Dom.v
        val make_result :
          G_GAC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_I.wmatrix ->
      G_GAC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of GAC_I.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenIA3 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val updt :
                  GAC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_I.vo ->
                  GAC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_I.contr * int
        val make_result :
          G_GAC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_I.wmatrix ->
      G_GAC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of GAC_I.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenIA4 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val updt :
                  GAC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_I.vo ->
                  GAC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_I.contr * GAC_I.Dom.v * int
        val make_result :
          G_GAC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_I.wmatrix ->
      G_GAC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of GAC_I.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
- : unit = ()
- : unit = ()
module GenIV1 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_I.vo ->
                  GVC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_I.contr
        val make_result :
          G_GVC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_I.wmatrix ->
      G_GVC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenIV2 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_I.vo ->
                  GVC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_I.contr * GVC_I.Dom.v
        val make_result :
          G_GVC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_I.wmatrix ->
      G_GVC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenIV3 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_I.vo ->
                  GVC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_I.contr * int
        val make_result :
          G_GVC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_I.wmatrix ->
      G_GVC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenIV4 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_I.vo ->
                  GVC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_I.contr * GVC_I.Dom.v * int
        val make_result :
          G_GVC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_I.wmatrix ->
      G_GVC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenIV5 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_I.vo ->
                  GVC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_I.contr * GVC_I.Dom.v * int
        val make_result :
          G_GVC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_I.wmatrix ->
      G_GVC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenIV6 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = Prelude.perm list
                type ira = int Direct.abstract
                type fra = Prelude.perm Direct.abstract
                type pra = Prelude.perm list Direct.abstract
                type lstate = Prelude.perm list ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_I.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_I.vo ->
                  GVC_I.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_I.contr * GVC_I.Dom.v * int * Prelude.perm list
        val make_result :
          G_GVC_I.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_I.wmatrix ->
      G_GVC_I.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Direct.abstract
                  | `TPivot of Prelude.perm list ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Direct.abstract
        | `TPivot of Prelude.perm list ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenRA1 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_R.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_R.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val updt :
                  GAC_R.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_R.vo ->
                  GAC_R.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_R.contr
        val make_result :
          G_GAC_R.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_R.wmatrix ->
      G_GAC_R.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
        | `TLower of GAC_R.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_R.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
                  | `TLower of GAC_R.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_R.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_R.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
        | `TLower of GAC_R.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_R.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenRA2 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_R.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_R.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val updt :
                  GAC_R.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_R.vo ->
                  GAC_R.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_R.contr * GAC_R.Dom.v
        val make_result :
          G_GAC_R.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_R.wmatrix ->
      G_GAC_R.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
        | `TLower of GAC_R.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_R.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
                  | `TLower of GAC_R.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_R.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_R.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
        | `TLower of GAC_R.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_R.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenRA3 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_R.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_R.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val updt :
                  GAC_R.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_R.vo ->
                  GAC_R.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_R.contr * int
        val make_result :
          G_GAC_R.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_R.wmatrix ->
      G_GAC_R.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
        | `TLower of GAC_R.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_R.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
                  | `TLower of GAC_R.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_R.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_R.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
        | `TLower of GAC_R.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_R.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenRA4 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = GEF.PermList.perm_rep
                type ira = int Direct.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GAC_R.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_R.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val updt :
                  GAC_R.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GAC_R.vo ->
                  GAC_R.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GAC_R.contr * GAC_R.Dom.v * int
        val make_result :
          G_GAC_R.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GAC_R.wmatrix ->
      G_GAC_R.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
        | `TLower of GAC_R.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GAC_R.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
                  | `TLower of GAC_R.contr Direct.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_R.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_R.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
        | `TLower of GAC_R.contr Direct.abstract
        | `TPivot of GEF.PermList.perm_rep ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GAC_R.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GAC_R).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenZp3 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = Prelude.perm list
                type ira = int Direct.abstract
                type fra = Prelude.perm Direct.abstract
                type pra = Prelude.perm list Direct.abstract
                type lstate = Prelude.perm list ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_Z3.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_Z3.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_Z3.contr)
                  lm
                val updt :
                  GVC_Z3.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_Z3.vo ->
                  GVC_Z3.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_Z3.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_Z3.contr * GVC_Z3.Dom.v * int * Prelude.perm list
        val make_result :
          G_GVC_Z3.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_Z3).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_Z3.wmatrix ->
      G_GVC_Z3.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_Z3).AbstractDet.lstate
        | `TLower of GVC_Z3.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_Z3.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_Z3).AbstractDet.lstate
                  | `TLower of GVC_Z3.contr Direct.abstract
                  | `TPivot of Prelude.perm list ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_Z3.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
       int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_Z3.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_Z3).AbstractDet.lstate
        | `TLower of GVC_Z3.contr Direct.abstract
        | `TPivot of Prelude.perm list ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_Z3.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_Z3).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
module GenZp19 :
  sig
    module O :
      sig
        module IF :
          sig
            module R :
              sig
                type tag_lstate = GEF.TrackRank.tag_lstate_
                val decl :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int ref)
                  GEF.TrackRank.lm
                val succ :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   unit)
                  GEF.TrackRank.lm
                val fin :
                  unit ->
                  (< answer : 'a; state : [> GEF.TrackRank.tag_lstate ]; .. >,
                   int)
                  GEF.TrackRank.lm
              end
            module P :
              sig
                type perm_rep = Prelude.perm list
                type ira = int Direct.abstract
                type fra = Prelude.perm Direct.abstract
                type pra = Prelude.perm list Direct.abstract
                type lstate = Prelude.perm list ref Direct.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Direct.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Direct.abstract ->
                  < answer : 'a; state : [> `TPivot of lstate ]; .. > nm
                val add :
                  fra ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >, unit)
                  GEF.omonad
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TPivot of lstate ]; .. >,
                   perm_rep)
                  lm
              end
            module L :
              sig
                type lstate = GVC_Z19.contr Direct.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_Z19.contr Direct.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_Z19.contr)
                  lm
                val updt :
                  GVC_Z19.vc ->
                  int Direct.abstract ->
                  int Direct.abstract ->
                  GVC_Z19.vo ->
                  GVC_Z19.Dom.vc ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >, unit)
                  lm option
                val fin :
                  unit ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_Z19.contr)
                  lm
                val wants_pack : bool
              end
          end
        type res = GVC_Z19.contr * GVC_Z19.Dom.v * int * Prelude.perm list
        val make_result :
          G_GVC_Z19.wmatrix ->
          (< answer : 'a;
             state : [> `TDet of
                          Ge.LAMake(Direct).GenLA(GVC_Z19).AbstractDet.lstate
                      | `TLower of IF.L.lstate
                      | `TPivot of IF.P.lstate
                      | `TRan of GEF.TrackRank.lstate ];
             .. >,
           res)
          GEF.cmonad
      end
    val wants_pack : bool
    val can_pack : bool
    val zerobelow :
      G_GVC_Z19.wmatrix ->
      G_GVC_Z19.curposval ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_Z19).AbstractDet.lstate
        | `TLower of GVC_Z19.contr Direct.abstract ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val init :
      GVC_Z19.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_Z19).AbstractDet.lstate
                  | `TLower of GVC_Z19.contr Direct.abstract
                  | `TPivot of Prelude.perm list ref Direct.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_Z19.wmatrix * int ref Direct.abstract *
       int ref Direct.abstract * int Direct.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_Z19.wmatrix * int ref Direct.abstract * int ref Direct.abstract *
      int Direct.abstract ->
      ([> `TDet of Ge.LAMake(Direct).GenLA(GVC_Z19).AbstractDet.lstate
        | `TLower of GVC_Z19.contr Direct.abstract
        | `TPivot of Prelude.perm list ref Direct.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Direct.abstract -> 'b) -> 'b
    val gen :
      GVC_Z19.contr Direct.abstract ->
      (< answer : 'a Direct.abstract;
         state : [> `TDet of
                      Ge.LAMake(Direct).GenLA(GVC_Z19).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Direct.abstract)
      StateCPSMonad.monad
  end
val resFA1 : GAC_F.contr -> GenFA1.O.res = <fun>
val resFA2 : GAC_F.contr -> GenFA2.O.res = <fun>
val resFA3 : GAC_F.contr -> GenFA3.O.res = <fun>
val resFA4 : GAC_F.contr -> GenFA4.O.res = <fun>
val resFV1 : GVC_F.contr -> GenFV1.O.res = <fun>
val resFV2 : GVC_F.contr -> GenFV2.O.res = <fun>
val resFV3 : GVC_F.contr -> GenFV3.O.res = <fun>
val resFV4 : GVC_F.contr -> GenFV4.O.res = <fun>
val resFV5 : GVC_F.contr -> GenFV5.O.res = <fun>
val resIA1 : GAC_I.contr -> GenIA1.O.res = <fun>
val resIA2 : GAC_I.contr -> GenIA2.O.res = <fun>
val resIA3 : GAC_I.contr -> GenIA3.O.res = <fun>
val resIA4 : GAC_I.contr -> GenIA4.O.res = <fun>
val resIV1 : GVC_I.contr -> GenIV1.O.res = <fun>
val resIV2 : GVC_I.contr -> GenIV2.O.res = <fun>
val resIV3 : GVC_I.contr -> GenIV3.O.res = <fun>
val resIV4 : GVC_I.contr -> GenIV4.O.res = <fun>
val resIV5 : GVC_I.contr -> GenIV5.O.res = <fun>
val resIV6 : GVC_I.contr -> GenIV6.O.res = <fun>
val resFA11 : GAC_F.contr -> GenFA11.O.res = <fun>
val resFA12 : GAC_F.contr -> GenFA12.O.res = <fun>
val resFA13 : GAC_F.contr -> GenFA13.O.res = <fun>
val resFA14 : GAC_F.contr -> GenFA14.O.res = <fun>
val resFA24 : GAC_F.contr -> GenFA24.O.res = <fun>
val resFA25 : GAC_F.contr -> GenFA25.O.res = <fun>
val resFA26 : GAC_F.contr -> GenFA26.O.res = <fun>
val resRA1 : GAC_R.contr -> GenRA1.O.res = <fun>
val resRA2 : GAC_R.contr -> GenRA2.O.res = <fun>
val resRA3 : GAC_R.contr -> GenRA3.O.res = <fun>
val resRA4 : GAC_R.contr -> GenRA4.O.res = <fun>
val resFA5 : GAC_F.contr * int -> GenFA5.O.res = <fun>
val resFA6 : GAC_F.contr * int -> GenFA6.O.res = <fun>
val resFA7 : GAC_F.contr * int -> GenFA7.O.res = <fun>
val resFA8 : GAC_F.contr * int -> GenFA8.O.res = <fun>
val resFA9 : GAC_F.contr -> GenFA9.O.res = <fun>
val resFA31 : GAC_F.contr -> GenFA31.O.res = <fun>
val resFA32 : GAC_F.contr -> GenFA32.O.res = <fun>
val resZp3 : GVC_Z3.contr -> GenZp3.O.res = <fun>
val resZp19 : GVC_Z19.contr -> GenZp19.O.res = <fun>
val rFA1 : GAC_F.contr -> GenFA1.O.res = <fun>
val rFA2 : GAC_F.contr -> GenFA2.O.res = <fun>
val rFA3 : GAC_F.contr -> GenFA3.O.res = <fun>
val rFA4 : GAC_F.contr -> GenFA4.O.res = <fun>
val rFV1 : GVC_F.contr -> GenFV1.O.res = <fun>
val rFV2 : GVC_F.contr -> GenFV2.O.res = <fun>
val rFV3 : GVC_F.contr -> GenFV3.O.res = <fun>
val rFV4 : GVC_F.contr -> GenFV4.O.res = <fun>
val rFV5 : GVC_F.contr -> GenFV5.O.res = <fun>
val rIA1 : GAC_I.contr -> GenIA1.O.res = <fun>
val rIA2 : GAC_I.contr -> GenIA2.O.res = <fun>
val rIA3 : GAC_I.contr -> GenIA3.O.res = <fun>
val rIA4 : GAC_I.contr -> GenIA4.O.res = <fun>
val rIV1 : GVC_I.contr -> GenIV1.O.res = <fun>
val rIV2 : GVC_I.contr -> GenIV2.O.res = <fun>
val rIV3 : GVC_I.contr -> GenIV3.O.res = <fun>
val rIV4 : GVC_I.contr -> GenIV4.O.res = <fun>
val rIV5 : GVC_I.contr -> GenIV5.O.res = <fun>
val rIV6 : GVC_I.contr -> GenIV6.O.res = <fun>
val rFA11 : GAC_F.contr -> GenFA11.O.res = <fun>
val rFA12 : GAC_F.contr -> GenFA12.O.res = <fun>
val rFA13 : GAC_F.contr -> GenFA13.O.res = <fun>
val rFA14 : GAC_F.contr -> GenFA14.O.res = <fun>
val rFA24 : GAC_F.contr -> GenFA24.O.res = <fun>
val rFA25 : GAC_F.contr -> GenFA25.O.res = <fun>
val rFA26 : GAC_F.contr -> GenFA26.O.res = <fun>
val rRA1 : GAC_R.contr -> GenRA1.O.res = <fun>
val rRA2 : GAC_R.contr -> GenRA2.O.res = <fun>
val rRA3 : GAC_R.contr -> GenRA3.O.res = <fun>
val rRA4 : GAC_R.contr -> GenRA4.O.res = <fun>
val rFA5 : GAC_F.contr * int -> GenFA5.O.res = <fun>
val rFA6 : GAC_F.contr * int -> GenFA6.O.res = <fun>
val rFA7 : GAC_F.contr * int -> GenFA7.O.res = <fun>
val rFA8 : GAC_F.contr * int -> GenFA8.O.res = <fun>
val rFA9 : GAC_F.contr -> GenFA9.O.res = <fun>
val rFA31 : GAC_F.contr -> GenFA31.O.res = <fun>
val rFA32 : GAC_F.contr -> GenFA32.O.res = <fun>
val rZp3 : GVC_Z3.contr -> GenZp3.O.res = <fun>
val rZp19 : GVC_Z19.contr -> GenZp19.O.res = <fun>
val ia0 : int array array = [|[|1|]|]
val ia1 : int array array = [|[|1; 2; 3|]; [|4; 13; 5|]; [|-1; 3; 0|]|]
val ia2 : int array array =
  [|[|1; 2; 3; 0|]; [|4; 13; 5; 0|]; [|-1; 3; 0; 0|]|]
val ia3 : int array array =
  [|[|1; 2; 3|]; [|4; 13; 5|]; [|-1; 3; 0|]; [|0; 0; 0|]|]
val ia4 : int array array = [|[|0; 2; 3|]; [|0; 13; 5|]; [|0; 3; 0|]|]
val ia5 : int array array list =
  [[|[|1|]|]; [|[|1; 2; 3|]; [|4; 13; 5|]; [|-1; 3; 0|]|];
   [|[|1; 2; 3; 0|]; [|4; 13; 5; 0|]; [|-1; 3; 0; 0|]|];
   [|[|1; 2; 3|]; [|4; 13; 5|]; [|-1; 3; 0|]; [|0; 0; 0|]|];
   [|[|0; 2; 3|]; [|0; 13; 5|]; [|0; 3; 0|]|]]
val resI11 : GenIA1.O.res list =
  [[|[|1|]|]; [|[|1; 2; 3|]; [|0; 5; -7|]; [|0; 0; 50|]|];
   [|[|1; 2; 3; 0|]; [|0; 5; -7; 0|]; [|0; 0; 50; 0|]|];
   [|[|1; 2; 3|]; [|0; 5; -7|]; [|0; 0; 50|]; [|0; 0; 0|]|];
   [|[|0; 2; 3|]; [|0; 0; -9|]; [|0; 0; 0|]|]]
val resI12 : GenIA2.O.res list =
  [([|[|1|]|], 1); ([|[|1; 2; 3|]; [|0; 5; -7|]; [|0; 0; 50|]|], 50);
   ([|[|1; 2; 3; 0|]; [|0; 5; -7; 0|]; [|0; 0; 50; 0|]|], 50);
   ([|[|1; 2; 3|]; [|0; 5; -7|]; [|0; 0; 50|]; [|0; 0; 0|]|], 50);
   ([|[|0; 2; 3|]; [|0; 0; -9|]; [|0; 0; 0|]|], 0)]
val resI13 : GenIA3.O.res list =
  [([|[|1|]|], 1); ([|[|1; 2; 3|]; [|0; 5; -7|]; [|0; 0; 50|]|], 3);
   ([|[|1; 2; 3; 0|]; [|0; 5; -7; 0|]; [|0; 0; 50; 0|]|], 3);
   ([|[|1; 2; 3|]; [|0; 5; -7|]; [|0; 0; 50|]; [|0; 0; 0|]|], 3);
   ([|[|0; 2; 3|]; [|0; 0; -9|]; [|0; 0; 0|]|], 2)]
val resI14 : GenIA4.O.res list =
  [([|[|1|]|], 1, 1); ([|[|1; 2; 3|]; [|0; 5; -7|]; [|0; 0; 50|]|], 50, 3);
   ([|[|1; 2; 3; 0|]; [|0; 5; -7; 0|]; [|0; 0; 50; 0|]|], 50, 3);
   ([|[|1; 2; 3|]; [|0; 5; -7|]; [|0; 0; 50|]; [|0; 0; 0|]|], 50, 3);
   ([|[|0; 2; 3|]; [|0; 0; -9|]; [|0; 0; 0|]|], 0, 2)]
val iv0 : int Prelude.container2dfromvector = {arr = [|1|]; n = 1; m = 1}
val iv1 : int Prelude.container2dfromvector =
  {arr = [|1; 2; 3; 4; 13; 5; -1; 3; 0|]; n = 3; m = 3}
val iv2 : int Prelude.container2dfromvector =
  {arr = [|1; 2; 3; 0; 4; 13; 5; 0; -1; 3; 0; 0|]; n = 3; m = 4}
val iv4 : int Prelude.container2dfromvector =
  {arr = [|0; 2; 3; 0; 13; 5; 0; 3; 0|]; n = 3; m = 3}
val iv5 : int Prelude.container2dfromvector list =
  [{arr = [|1|]; n = 1; m = 1};
   {arr = [|1; 2; 3; 4; 13; 5; -1; 3; 0|]; n = 3; m = 3};
   {arr = [|1; 2; 3; 0; 4; 13; 5; 0; -1; 3; 0; 0|]; n = 3; m = 4};
   {arr = [|0; 2; 3; 0; 13; 5; 0; 3; 0|]; n = 3; m = 3}]
val resI21 : GenIV1.O.res list =
  [{arr = [|1|]; n = 1; m = 1};
   {arr = [|1; 2; 3; 0; 5; -7; 0; 0; 50|]; n = 3; m = 3};
   {arr = [|1; 2; 3; 0; 0; 5; -7; 0; 0; 0; 50; 0|]; n = 3; m = 4};
   {arr = [|0; 2; 3; 0; 0; -9; 0; 0; 0|]; n = 3; m = 3}]
val resI22 : GenIV2.O.res list =
  [({arr = [|1|]; n = 1; m = 1}, 1);
   ({arr = [|1; 2; 3; 0; 5; -7; 0; 0; 50|]; n = 3; m = 3}, 50);
   ({arr = [|1; 2; 3; 0; 0; 5; -7; 0; 0; 0; 50; 0|]; n = 3; m = 4}, 50);
   ({arr = [|0; 2; 3; 0; 0; -9; 0; 0; 0|]; n = 3; m = 3}, 0)]
val resI23 : GenIV3.O.res list =
  [({arr = [|1|]; n = 1; m = 1}, 1);
   ({arr = [|1; 2; 3; 0; 5; -7; 0; 0; 50|]; n = 3; m = 3}, 3);
   ({arr = [|1; 2; 3; 0; 0; 5; -7; 0; 0; 0; 50; 0|]; n = 3; m = 4}, 3);
   ({arr = [|0; 2; 3; 0; 0; -9; 0; 0; 0|]; n = 3; m = 3}, 2)]
val resI24 : GenIV4.O.res list =
  [({arr = [|1|]; n = 1; m = 1}, 1, 1);
   ({arr = [|1; 2; 3; 0; 5; -7; 0; 0; 50|]; n = 3; m = 3}, 50, 3);
   ({arr = [|1; 2; 3; 0; 0; 5; -7; 0; 0; 0; 50; 0|]; n = 3; m = 4}, 50, 3);
   ({arr = [|0; 2; 3; 0; 0; -9; 0; 0; 0|]; n = 3; m = 3}, 0, 2)]
val resI25 : GenIV5.O.res list =
  [({arr = [|1|]; n = 1; m = 1}, 1, 1);
   ({arr = [|1; 3; 2; 0; 3; 5; 0; 0; 50|]; n = 3; m = 3}, 50, 3);
   ({arr = [|1; 3; 2; 0; 0; 3; 5; 0; 0; 0; 50; 0|]; n = 3; m = 4}, 50, 3);
   ({arr = [|2; 3; 0; 0; -9; 0; 0; 0; 0|]; n = 3; m = 3}, 0, 2)]
val resI26 : GenIV6.O.res list =
  [({arr = [|1|]; n = 1; m = 1}, 1, 1, []);
   ({arr = [|1; 3; 2; 0; 3; 5; 0; 0; 50|]; n = 3; m = 3}, 50, 3,
    [RowSwap (2, 1); ColSwap (2, 1)]);
   ({arr = [|1; 3; 2; 0; 0; 3; 5; 0; 0; 0; 50; 0|]; n = 3; m = 4}, 50, 3,
    [RowSwap (2, 1); ColSwap (2, 1)]);
   ({arr = [|2; 3; 0; 0; -9; 0; 0; 0; 0|]; n = 3; m = 3}, 0, 2,
    [RowSwap (2, 1); ColSwap (2, 1); ColSwap (1, 0)])]
val fa0 : float array array = [|[|1.|]|]
val fa1 : float array array =
  [|[|1.; 2.; 3.|]; [|4.; 13.; 5.|]; [|-1.; 3.; 0.|]|]
val fa2 : float array array =
  [|[|1.; 2.; 3.; 0.|]; [|4.; 13.; 5.; 0.|]; [|-1.; 3.; 0.; 0.|]|]
val fa3 : float array array =
  [|[|1.; 2.; 3.|]; [|4.; 13.; 5.|]; [|-1.; 3.; 0.|]; [|0.; 0.; 0.|]|]
val fa4 : float array array =
  [|[|0.; 2.; 3.|]; [|0.; 10.; 5.|]; [|0.; 3.; 0.|]|]
val fa5 : float array array list =
  [[|[|1.|]|]; [|[|1.; 2.; 3.|]; [|4.; 13.; 5.|]; [|-1.; 3.; 0.|]|];
   [|[|1.; 2.; 3.; 0.|]; [|4.; 13.; 5.; 0.|]; [|-1.; 3.; 0.; 0.|]|];
   [|[|1.; 2.; 3.|]; [|4.; 13.; 5.|]; [|-1.; 3.; 0.|]; [|0.; 0.; 0.|]|];
   [|[|0.; 2.; 3.|]; [|0.; 10.; 5.|]; [|0.; 3.; 0.|]|]]
val fa6 : float array array = [|[|1.; 1.|]|]
val fa7 : float array array =
  [|[|1.; 2.; 3.; 1.; 0.; 0.|]; [|4.; 13.; 5.; 0.; 1.; 0.|];
    [|-1.; 3.; 0.; 0.; 0.; 1.|]|]
- : unit = ()
- : unit = ()
- : unit = ()
- : unit = ()
- : unit = ()
- : unit = ()
val resFA9 : GenFA9.O.res =
  ([|[|4.; 13.; 5.|]; [|-1.; 6.25; 1.25|]; [|1.; -1.25; 2.|]|],
   [RowSwap (2, 1); RowSwap (1, 0)])
- : unit = ()
- : unit = ()
- : unit = ()
val resF1 : GenFA1.O.res list =
  [[|[|1.|]|]; [|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]|];
   [|[|4.; 13.; 5.; 0.|]; [|0.; 6.25; 1.25; 0.|]; [|0.; 0.; 2.; 0.|]|];
   [|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|];
   [|[|0.; 10.; 5.|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|]]
- : unit = ()
- : unit = ()
- : unit = ()
val resFA31 : GenFA31.O.res list =
  [([|[|1.|]|], [|[|1.|]|], []);
   ([|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]|],
    [|[|1.; 0.; 0.|]; [|0.25; 1.; 0.|]; [|-0.25; -0.2; 1.|]|],
    [RowSwap (2, 1); RowSwap (1, 0)]);
   ([|[|4.; 13.; 5.; 0.|]; [|0.; 6.25; 1.25; 0.|]; [|0.; 0.; 2.; 0.|]|],
    [|[|1.; 0.; 0.; 0.|]; [|0.25; 1.; 0.; 0.|]; [|-0.25; -0.2; 1.; 0.|]|],
    [RowSwap (2, 1); RowSwap (1, 0)]);
   ([|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|],
    [|[|1.; 0.; 0.|]; [|0.25; 1.; 0.|]; [|-0.25; -0.2; 1.|]; [|0.; 0.; 0.|]|],
    [RowSwap (2, 1); RowSwap (1, 0)]);
   ([|[|0.; 10.; 5.|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|],
    [|[|1.; 0.; 0.|]; [|0.; 0.2; 0.|]; [|0.; 0.3; -0.75|]|],
    [RowSwap (1, 0)])]
val resFA32 : GenFA32.O.res list =
  [([|[|1.|]|], []);
   ([|[|4.; 13.; 5.|]; [|-1.; 6.25; 1.25|]; [|1.; -1.25; 2.|]|],
    [RowSwap (2, 1); RowSwap (1, 0)]);
   ([|[|4.; 13.; 5.; 0.|]; [|-1.; 6.25; 1.25; 0.|]; [|1.; -1.25; 2.; 0.|]|],
    [RowSwap (2, 1); RowSwap (1, 0)]);
   ([|[|4.; 13.; 5.|]; [|-1.; 6.25; 1.25|]; [|1.; -1.25; 2.|];
      [|0.; 0.; 0.|]|],
    [RowSwap (2, 1); RowSwap (1, 0)]);
   ([|[|0.; 10.; 5.|]; [|0.; 2.; 2.|]; [|0.; 3.; -1.5|]|], [RowSwap (1, 0)])]
val a2v : 'a array array -> 'a Prelude.container2dfromvector = <fun>
val xxx : GAC_F.Dom.v Prelude.container2dfromvector list =
  [{arr = [|1.|]; n = 1; m = 1};
   {arr = [|1.; 2.; 3.; 4.; 13.; 5.; -1.; 3.; 0.|]; n = 3; m = 3};
   {arr = [|1.; 2.; 3.; 0.; 4.; 13.; 5.; 0.; -1.; 3.; 0.; 0.|]; n = 3; m = 4};
   {arr = [|1.; 2.; 3.; 4.; 13.; 5.; -1.; 3.; 0.; 0.; 0.; 0.|]; n = 4; m = 3};
   {arr = [|0.; 2.; 3.; 0.; 10.; 5.; 0.; 3.; 0.|]; n = 3; m = 3}]
- : unit = ()
val resFV5 : GenFV5.O.res list =
  [({arr = [|1.|]; n = 1; m = 1}, 1., 1);
   ({arr =
      [|13.; 5.; 4.; 0.; 2.23076923076923084; 0.384615384615384581; 0.; 0.;
        -1.72413793103448287|];
     n = 3; m = 3},
    50., 3);
   ({arr =
      [|13.; 5.; 4.; 0.; 0.; 2.23076923076923084; 0.384615384615384581; 0.;
        0.; 0.; -1.72413793103448287; 0.|];
     n = 3; m = 4},
    50., 3);
   ({arr =
      [|13.; 5.; 4.; 0.; 2.23076923076923084; 0.384615384615384581; 0.; 0.;
        -1.72413793103448287; 0.; 0.; 0.|];
     n = 4; m = 3},
    50., 3);
   ({arr = [|10.; 5.; 0.; 0.; 2.; 0.; 0.; 0.; 0.|]; n = 3; m = 3}, 0., 2)]
val resF11 : GenFA11.O.res list =
  [[|[|1.|]|];
   [|[|13.; 5.; 4.|]; [|0.; 2.23076923076923084; 0.384615384615384581|];
     [|0.; 0.; -1.72413793103448287|]|];
   [|[|13.; 5.; 4.; 0.|];
     [|0.; 2.23076923076923084; 0.384615384615384581; 0.|];
     [|0.; 0.; -1.72413793103448287; 0.|]|];
   [|[|13.; 5.; 4.|]; [|0.; 2.23076923076923084; 0.384615384615384581|];
     [|0.; 0.; -1.72413793103448287|]; [|0.; 0.; 0.|]|];
   [|[|10.; 5.; 0.|]; [|0.; 2.; 0.|]; [|0.; 0.; 0.|]|]]
val resF12 : GenFA12.O.res list =
  [([|[|1.|]|], 1.);
   ([|[|13.; 5.; 4.|]; [|0.; 2.23076923076923084; 0.384615384615384581|];
      [|0.; 0.; -1.72413793103448287|]|],
    50.);
   ([|[|13.; 5.; 4.; 0.|];
      [|0.; 2.23076923076923084; 0.384615384615384581; 0.|];
      [|0.; 0.; -1.72413793103448287; 0.|]|],
    50.);
   ([|[|13.; 5.; 4.|]; [|0.; 2.23076923076923084; 0.384615384615384581|];
      [|0.; 0.; -1.72413793103448287|]; [|0.; 0.; 0.|]|],
    50.);
   ([|[|10.; 5.; 0.|]; [|0.; 2.; 0.|]; [|0.; 0.; 0.|]|], 0.)]
val resF13 : GenFA13.O.res list =
  [([|[|1.|]|], 1);
   ([|[|13.; 5.; 4.|]; [|0.; 2.23076923076923084; 0.384615384615384581|];
      [|0.; 0.; -1.72413793103448287|]|],
    3);
   ([|[|13.; 5.; 4.; 0.|];
      [|0.; 2.23076923076923084; 0.384615384615384581; 0.|];
      [|0.; 0.; -1.72413793103448287; 0.|]|],
    3);
   ([|[|13.; 5.; 4.|]; [|0.; 2.23076923076923084; 0.384615384615384581|];
      [|0.; 0.; -1.72413793103448287|]; [|0.; 0.; 0.|]|],
    3);
   ([|[|10.; 5.; 0.|]; [|0.; 2.; 0.|]; [|0.; 0.; 0.|]|], 2)]
val resF14 : GenFA14.O.res list =
  [([|[|1.|]|], 1., 1);
   ([|[|13.; 5.; 4.|]; [|0.; 2.23076923076923084; 0.384615384615384581|];
      [|0.; 0.; -1.72413793103448287|]|],
    50., 3);
   ([|[|13.; 5.; 4.; 0.|];
      [|0.; 2.23076923076923084; 0.384615384615384581; 0.|];
      [|0.; 0.; -1.72413793103448287; 0.|]|],
    50., 3);
   ([|[|13.; 5.; 4.|]; [|0.; 2.23076923076923084; 0.384615384615384581|];
      [|0.; 0.; -1.72413793103448287|]; [|0.; 0.; 0.|]|],
    50., 3);
   ([|[|10.; 5.; 0.|]; [|0.; 2.; 0.|]; [|0.; 0.; 0.|]|], 0., 2)]
val resF24 : GenFA24.O.res list =
  [([|[|1.|]|], 1., 1, []);
   ([|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]|], 50., 3,
    [RowSwap (2, 1); RowSwap (1, 0)]);
   ([|[|4.; 13.; 5.; 0.|]; [|0.; 6.25; 1.25; 0.|]; [|0.; 0.; 2.; 0.|]|], 50.,
    3, [RowSwap (2, 1); RowSwap (1, 0)]);
   ([|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|],
    50., 3, [RowSwap (2, 1); RowSwap (1, 0)]);
   ([|[|0.; 10.; 5.|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|], 0., 2,
    [RowSwap (1, 0)])]
val resF25 : GenFA25.O.res list =
  [([|[|1.|]|], 1., 1, [|0|]);
   ([|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]|], 50., 3,
    [|1; 2; 0|]);
   ([|[|4.; 13.; 5.; 0.|]; [|0.; 6.25; 1.25; 0.|]; [|0.; 0.; 2.; 0.|]|], 50.,
    3, [|1; 2; 0|]);
   ([|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|],
    50., 3, [|1; 2; 0; 3|]);
   ([|[|0.; 10.; 5.|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|], 0., 2, [|1; 0; 2|])]
val resF26 : GenFA26.O.res list =
  [[|[|1.|]|]; [|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]|];
   [|[|4.; 13.; 5.; 0.|]; [|0.; 6.25; 1.25; 0.|]; [|0.; 0.; 2.; 0.|]|];
   [|[|4.; 13.; 5.|]; [|0.; 6.25; 1.25|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|];
   [|[|0.; 10.; 5.|]; [|0.; 0.; 2.|]; [|0.; 0.; 0.|]|]]
val ra0 : Num.num array array = [|[|Num.Int 1|]|]
val ra1 : Num.num array array =
  [|[|Num.Int 1; Num.Int 2; Num.Int 3|];
    [|Num.Int 4; Num.Int 13; Num.Int 5|];
    [|Num.Int (-1); Num.Int 3; Num.Int 0|]|]
val ra2 : Num.num array array =
  [|[|Num.Int 1; Num.Int 2; Num.Int 3; Num.Int 0|];
    [|Num.Int 4; Num.Int 13; Num.Int 5; Num.Int 0|];
    [|Num.Int (-1); Num.Int 3; Num.Int 0; Num.Int 0|]|]
val ra3 : Num.num array array =
  [|[|Num.Int 1; Num.Int 2; Num.Int 3|];
    [|Num.Int 4; Num.Int 13; Num.Int 5|];
    [|Num.Int (-1); Num.Int 3; Num.Int 0|];
    [|Num.Int 0; Num.Int 0; Num.Int 0|]|]
val ra4 : Num.num array array =
  [|[|Num.Int 0; Num.Int 2; Num.Int 3|];
    [|Num.Int 0; Num.Int 13; Num.Int 5|];
    [|Num.Int 0; Num.Int 3; Num.Int 0|]|]
val ra5 : Num.num array array list =
  [[|[|Num.Int 1|]|];
   [|[|Num.Int 1; Num.Int 2; Num.Int 3|];
     [|Num.Int 4; Num.Int 13; Num.Int 5|];
     [|Num.Int (-1); Num.Int 3; Num.Int 0|]|];
   [|[|Num.Int 1; Num.Int 2; Num.Int 3; Num.Int 0|];
     [|Num.Int 4; Num.Int 13; Num.Int 5; Num.Int 0|];
     [|Num.Int (-1); Num.Int 3; Num.Int 0; Num.Int 0|]|];
   [|[|Num.Int 1; Num.Int 2; Num.Int 3|];
     [|Num.Int 4; Num.Int 13; Num.Int 5|];
     [|Num.Int (-1); Num.Int 3; Num.Int 0|];
     [|Num.Int 0; Num.Int 0; Num.Int 0|]|];
   [|[|Num.Int 0; Num.Int 2; Num.Int 3|];
     [|Num.Int 0; Num.Int 13; Num.Int 5|];
     [|Num.Int 0; Num.Int 3; Num.Int 0|]|]]
val resR11 : GenRA1.O.res list =
  [[|[|Num.Int 1|]|];
   [|[|Num.Int 1; Num.Int 2; Num.Int 3|];
     [|Num.Int 0; Num.Int 5; Num.Int (-7)|];
     [|Num.Int 0; Num.Int 0; Num.Int 10|]|];
   [|[|Num.Int 1; Num.Int 2; Num.Int 3; Num.Int 0|];
     [|Num.Int 0; Num.Int 5; Num.Int (-7); Num.Int 0|];
     [|Num.Int 0; Num.Int 0; Num.Int 10; Num.Int 0|]|];
   [|[|Num.Int 1; Num.Int 2; Num.Int 3|];
     [|Num.Int 0; Num.Int 5; Num.Int (-7)|];
     [|Num.Int 0; Num.Int 0; Num.Int 10|];
     [|Num.Int 0; Num.Int 0; Num.Int 0|]|];
   [|[|Num.Int 0; Num.Int 2; Num.Int 3|];
     [|Num.Int 0; Num.Int 0; Num.Ratio <abstr>|];
     [|Num.Int 0; Num.Int 0; Num.Int 0|]|]]
val resR12 : GenRA2.O.res list =
  [([|[|Num.Int 1|]|], Num.Int 1);
   ([|[|Num.Int 1; Num.Int 2; Num.Int 3|];
      [|Num.Int 0; Num.Int 5; Num.Int (-7)|];
      [|Num.Int 0; Num.Int 0; Num.Int 10|]|],
    Num.Int 50);
   ([|[|Num.Int 1; Num.Int 2; Num.Int 3; Num.Int 0|];
      [|Num.Int 0; Num.Int 5; Num.Int (-7); Num.Int 0|];
      [|Num.Int 0; Num.Int 0; Num.Int 10; Num.Int 0|]|],
    Num.Int 50);
   ([|[|Num.Int 1; Num.Int 2; Num.Int 3|];
      [|Num.Int 0; Num.Int 5; Num.Int (-7)|];
      [|Num.Int 0; Num.Int 0; Num.Int 10|];
      [|Num.Int 0; Num.Int 0; Num.Int 0|]|],
    Num.Int 50);
   ([|[|Num.Int 0; Num.Int 2; Num.Int 3|];
      [|Num.Int 0; Num.Int 0; Num.Ratio <abstr>|];
      [|Num.Int 0; Num.Int 0; Num.Int 0|]|],
    Num.Int 0)]
val resR13 : GenRA3.O.res list =
  [([|[|Num.Int 1|]|], 1);
   ([|[|Num.Int 1; Num.Int 2; Num.Int 3|];
      [|Num.Int 0; Num.Int 5; Num.Int (-7)|];
      [|Num.Int 0; Num.Int 0; Num.Int 10|]|],
    3);
   ([|[|Num.Int 1; Num.Int 2; Num.Int 3; Num.Int 0|];
      [|Num.Int 0; Num.Int 5; Num.Int (-7); Num.Int 0|];
      [|Num.Int 0; Num.Int 0; Num.Int 10; Num.Int 0|]|],
    3);
   ([|[|Num.Int 1; Num.Int 2; Num.Int 3|];
      [|Num.Int 0; Num.Int 5; Num.Int (-7)|];
      [|Num.Int 0; Num.Int 0; Num.Int 10|];
      [|Num.Int 0; Num.Int 0; Num.Int 0|]|],
    3);
   ([|[|Num.Int 0; Num.Int 2; Num.Int 3|];
      [|Num.Int 0; Num.Int 0; Num.Ratio <abstr>|];
      [|Num.Int 0; Num.Int 0; Num.Int 0|]|],
    2)]
val resR14 : GenRA4.O.res list =
  [([|[|Num.Int 1|]|], Num.Int 1, 1);
   ([|[|Num.Int 1; Num.Int 2; Num.Int 3|];
      [|Num.Int 0; Num.Int 5; Num.Int (-7)|];
      [|Num.Int 0; Num.Int 0; Num.Int 10|]|],
    Num.Int 50, 3);
   ([|[|Num.Int 1; Num.Int 2; Num.Int 3; Num.Int 0|];
      [|Num.Int 0; Num.Int 5; Num.Int (-7); Num.Int 0|];
      [|Num.Int 0; Num.Int 0; Num.Int 10; Num.Int 0|]|],
    Num.Int 50, 3);
   ([|[|Num.Int 1; Num.Int 2; Num.Int 3|];
      [|Num.Int 0; Num.Int 5; Num.Int (-7)|];
      [|Num.Int 0; Num.Int 0; Num.Int 10|];
      [|Num.Int 0; Num.Int 0; Num.Int 0|]|],
    Num.Int 50, 3);
   ([|[|Num.Int 0; Num.Int 2; Num.Int 3|];
      [|Num.Int 0; Num.Int 0; Num.Ratio <abstr>|];
      [|Num.Int 0; Num.Int 0; Num.Int 0|]|],
    Num.Int 0, 2)]
# 
