BER MetaOCaml toplevel, version N 102
        OCaml version 4.02.1

#             module GEF :
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
            type vc = v Code.abstract
            val zeroL : vc
            val oneL : vc
            val ( +^ ) : vc -> vc -> vc
            val ( *^ ) : vc -> vc -> vc
            val ( -^ ) : vc -> vc -> vc
            val uminusL : vc -> vc
            val divL : vc -> vc -> vc
            val better_thanL : (vc -> vc -> bool Code.abstract) option
            val normalizerL : (vc -> vc) option
          end
        module type CONTAINER2D =
          sig
            module Dom : DOMAINL
            type contr
            type vc = contr Code.abstract
            type vo = Dom.v Code.abstract
            val getL : vc -> int Code.abstract -> int Code.abstract -> vo
            val dim1 : vc -> int Code.abstract
            val dim2 : vc -> int Code.abstract
            val mapper : (vo -> vo) option -> vc -> vc
            val copy : vc -> vc
            val init : int Code.abstract -> int Code.abstract -> vc
            val augment :
              vc ->
              int Code.abstract ->
              int Code.abstract -> vc -> int Code.abstract -> vc
            val identity : int Code.abstract -> int Code.abstract -> vc
            val swap_rows_stmt :
              vc ->
              int Code.abstract option ->
              int Code.abstract -> int Code.abstract -> unit Code.abstract
            val swap_cols_stmt :
              vc ->
              int Code.abstract -> int Code.abstract -> unit Code.abstract
            val row_head : vc -> int Code.abstract -> int Code.abstract -> vo
            val col_head_set :
              vc ->
              int Code.abstract ->
              int Code.abstract -> vo -> unit Code.abstract
          end
      end
    type ('a, 'b) cmonad_constraint = unit
      constraint 'a = < answer : 'w; state : 's; .. >
      constraint 'b = < answer : 'w Code.abstract; state : 's list >
    type ('a, 'v) cmonad =
        (< answer : 'b Code.abstract; state : 'c list >, 'v Code.abstract)
        StateCPSMonad.monad
      constraint 'a = < answer : 'b; state : 'c; .. >
    type ('a, 'v) omonad =
        (< answer : 'b Code.abstract; state : 'c list >,
         'v Code.abstract option)
        StateCPSMonad.monad
      constraint 'a = < answer : 'b; state : 'c; .. >
    module Iters :
      sig
        val row_iter :
          'a ->
          'b ->
          int Code.abstract ->
          int Code.abstract ->
          ('a -> int Code.abstract -> 'b -> 'c Code.abstract) ->
          (int Code.abstract ->
           'c Code.abstract ->
           (< answer : 'd Code.abstract; state : 'e; .. >, 'd Code.abstract)
           StateCPSMonad.monad) ->
          Prelude.dir -> 'e -> ('e -> unit Code.abstract -> 'f) -> 'f
        val col_iter :
          'a ->
          'b ->
          int Code.abstract ->
          int Code.abstract ->
          ('a -> 'b -> int Code.abstract -> 'c) ->
          (int Code.abstract ->
           'c ->
           (< answer : 'd Code.abstract; state : 'e; .. >, 'd Code.abstract)
           StateCPSMonad.monad) ->
          Prelude.dir -> 'e -> ('e -> unit Code.abstract -> 'f) -> 'f
      end
    module TrackRank :
      sig
        type lstate = int ref Code.abstract
        type tag_lstate_ = [ `TRan of lstate ]
        type tag_lstate = tag_lstate_
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> tag_lstate ]; .. >
        val ip :
          ('a -> [> `TRan of 'a ]) * ([> `TRan of 'b ] -> 'b option) * string
        val decl :
          unit ->
          (< answer : 'a Code.abstract;
             state : [> `TRan of int ref Code.abstract ] list; .. >,
           int ref Code.abstract)
          StateCPSMonad.monad
        val succ :
          unit ->
          (< answer : 'a; state : [> `TRan of int ref Code.abstract ] list;
             .. >,
           unit Code.abstract)
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
        type lstate = int ref Code.abstract
        type tag_lstate_ = [ `TRan of lstate ]
        type tag_lstate = tag_lstate_
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> tag_lstate ]; .. >
        val ip :
          ('a -> [> `TRan of 'a ]) * ([> `TRan of 'b ] -> 'b option) * string
        val decl :
          unit ->
          (< answer : 'a Code.abstract;
             state : [> `TRan of int ref Code.abstract ] list; .. >,
           int ref Code.abstract)
          StateCPSMonad.monad
        val succ :
          unit ->
          (< answer : 'a; state : [> `TRan of int ref Code.abstract ] list;
             .. >,
           unit Code.abstract)
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
          (< answer : 'a; state : [> `TRan of 'b ref Code.abstract ] list;
             .. >,
           'b Code.abstract)
          StateCPSMonad.monad
      end
    module NoRank :
      sig
        type lstate = int ref Code.abstract
        type tag_lstate_ = [ `TRan of lstate ]
        type tag_lstate = tag_lstate_
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> tag_lstate ]; .. >
        val ip :
          ('a -> [> `TRan of 'a ]) * ([> `TRan of 'b ] -> 'b option) * string
        val decl :
          unit ->
          (< answer : 'a Code.abstract;
             state : [> `TRan of int ref Code.abstract ] list; .. >,
           int ref Code.abstract)
          StateCPSMonad.monad
        val succ :
          unit ->
          (< answer : 'a; state : [> `TRan of int ref Code.abstract ] list;
             .. >,
           unit Code.abstract)
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
        type ira = int Code.abstract
        type fra
        type pra = perm_rep Code.abstract
        val add : fra -> pra -> pra
        val empty : ira -> pra
        val rowrep : ira -> ira -> fra
        val colrep : ira -> ira -> fra
      end
    module PermList :
      sig
        type flip_rep = Prelude.perm
        type perm_rep = Prelude.perm list
        type ira = int Code.abstract
        type fra = flip_rep Code.abstract
        type pra = perm_rep Code.abstract
        val add :
          'a Code.abstract -> 'a list Code.abstract -> 'a list Code.abstract
        val empty : 'a -> pra
        val rowrep :
          int Code.abstract ->
          int Code.abstract -> Prelude.perm Code.abstract
        val colrep :
          int Code.abstract ->
          int Code.abstract -> Prelude.perm Code.abstract
      end
    module RowVectorPerm :
      sig
        type flip_rep = int * int
        type perm_rep = int array
        type ira = int Code.abstract
        type fra = flip_rep Code.abstract
        type pra = perm_rep Code.abstract
        val add :
          (int * int) Code.abstract ->
          int array Code.abstract -> int array Code.abstract
        val empty : int Code.abstract -> int array Code.abstract
        val rowrep :
          'a Code.abstract -> 'b Code.abstract -> ('a * 'b) Code.abstract
        val colrep :
          'a Code.abstract -> 'b Code.abstract -> ('a * 'b) Code.abstract
      end
    module type TRACKPIVOT =
      sig
        type perm_rep
        type ira = int Code.abstract
        type fra
        type pra
        type lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TPivot of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> `TPivot of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
            StateCPSMonad.monad
          constraint 'a =
            < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
        val rowrep : ira -> ira -> fra
        val colrep : ira -> ira -> fra
        val decl :
          int Code.abstract ->
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
          type lstate = PK.perm_rep ref Code.abstract
          type 'a pc_constraint = unit
            constraint 'a = < state : [> `TPivot of lstate ]; .. >
          type ('a, 'v) lm = ('a, 'v) cmonad
            constraint 'a =
              < answer : 'b; state : [> `TPivot of lstate ]; .. >
          type 'a nm =
              (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          type lstate = PK.perm_rep ref Code.abstract
          type 'a pc_constraint = unit
            constraint 'a = < state : [> `TPivot of lstate ]; .. >
          type ('a, 'v) lm = ('a, 'v) cmonad
            constraint 'a =
              < answer : 'b; state : [> `TPivot of lstate ]; .. >
          type 'a nm =
              (< answer : 'b Code.abstract; state : 'c list >, unit)
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
            (< answer : 'a Code.abstract;
               state : [> `TPivot of PK.perm_rep ref Code.abstract ] list;
               .. >,
             unit)
            StateCPSMonad.monad
          val add :
            PK.fra ->
            (< answer : 'a;
               state : [> `TPivot of PK.perm_rep ref Code.abstract ] list;
               .. >,
             unit Code.abstract option)
            StateCPSMonad.monad
          val fin :
            unit ->
            (< answer : 'a;
               state : [> `TPivot of 'b ref Code.abstract ] list; .. >,
             'b Code.abstract)
            StateCPSMonad.monad
        end
    module DiscardPivot :
      sig
        type perm_rep = PermList.perm_rep
        type ira = PermList.ira
        type fra = PermList.fra
        type pra = PermList.pra
        type lstate = PermList.perm_rep ref Code.abstract
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TPivot of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) cmonad
          constraint 'a = < answer : 'b; state : [> `TPivot of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
            Ge.LAMake(Code).GenLA(C).wmatrix = {
            matrix : C.vc;
            numrow : int Code.abstract;
            numcol : int Code.abstract;
          }
          type curpos =
            Ge.LAMake(Code).GenLA(C).curpos = {
            rowpos : int Code.abstract;
            colpos : int Code.abstract;
          }
          type curposval =
            Ge.LAMake(Code).GenLA(C).curposval = {
            p : curpos;
            curval : C.Dom.v Code.abstract;
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
                  (< answer : 'b Code.abstract; state : 'c list >, unit)
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
                C.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val get_magn :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
              val set_magn :
                C.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val fin :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, C.Dom.v)
                lm
            end
          module type LOWER =
            sig
              type lstate = C.contr Code.abstract
              type ('a, 'v) lm = ('a, 'v) cmonad
                constraint 'a =
                  < answer : 'b; state : [> `TLower of lstate ]; .. >
              val decl :
                C.contr Code.abstract ->
                (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                 C.contr)
                lm
              val updt :
                C.vc ->
                int Code.abstract ->
                int Code.abstract ->
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
              type lstate = Ge.LAMake(Code).GenLA(C).NoDet.lstate
              type 'a pc_constraint = unit
                constraint 'a = < state : [> `TDet of lstate ]; .. >
              type ('a, 'v) lm = ('a, 'v) cmonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type ('a, 'v) om = ('a, 'v) omonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type 'a nm =
                  (< answer : 'b Code.abstract; state : 'c list >, unit)
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
                C.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val get_magn :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
              val set_magn :
                C.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val fin :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, C.Dom.v)
                lm
            end
          module AbstractDet :
            sig
              type tdet = C.Dom.v ref
              type lstate = Ge.LAMake(Code).GenLA(C).AbstractDet.lstate
              type 'a pc_constraint = unit
                constraint 'a = < state : [> `TDet of lstate ]; .. >
              type ('a, 'v) lm = ('a, 'v) cmonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type ('a, 'v) om = ('a, 'v) omonad
                constraint 'a =
                  < answer : 'b; state : [> `TDet of lstate ]; .. >
              type 'a nm =
                  (< answer : 'b Code.abstract; state : 'c list >, unit)
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
                C.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
              val get_magn :
                unit ->
                (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
              val set_magn :
                C.Dom.v Code.abstract ->
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
                  (in_val -> unit Code.abstract) ->
                  C.Dom.v ref Code.abstract ->
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
                      C.Dom.v Code.abstract ->
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
                      C.Dom.v ref Code.abstract ->
                      (< answer : 'b; state : 'c; .. >, 'a)
                      StateCPSMonad.monad
                    val update_det :
                      C.Dom.v Code.abstract ->
                      (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >,
                       unit)
                      Det.lm
                    val upd_kind : Ge.update_kind
                  end
              module TrackLower :
                sig
                  type lstate = C.contr Code.abstract
                  type ('a, 'v) lm = ('a, 'v) cmonad
                    constraint 'a =
                      < answer : 'b; state : [> `TLower of lstate ]; .. >
                  val ip :
                    ('a -> [> `TLower of 'a ]) *
                    ([> `TLower of 'b ] -> 'b option) * string
                end
              module SeparateLower :
                sig
                  type lstate = C.contr Code.abstract
                  type ('a, 'v) lm = ('a, 'v) cmonad
                    constraint 'a =
                      < answer : 'b; state : [> `TLower of lstate ]; .. >
                  val ip :
                    ('a -> [> `TLower of 'a ]) *
                    ([> `TLower of 'b ] -> 'b option) * string
                  val decl :
                    'a Code.abstract ->
                    (< answer : 'b Code.abstract;
                       state : [> `TLower of 'a Code.abstract ] list; .. >,
                     'a Code.abstract)
                    StateCPSMonad.monad
                  val updt :
                    C.vc ->
                    int Code.abstract ->
                    int Code.abstract ->
                    C.vo ->
                    C.vo ->
                    (< answer : 'a; state : [> `TLower of C.vc ] list; .. >,
                     unit Code.abstract)
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
                  type lstate = C.contr Code.abstract
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
                  type lstate = C.contr Code.abstract
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
                    int Code.abstract ->
                    int Code.abstract ->
                    C.vo ->
                    'a ->
                    (< answer : 'b; state : 'c; .. >, unit Code.abstract)
                    StateCPSMonad.monad option
                  val fin : unit -> 'a
                  val wants_pack : bool
                end
              module type INPUT =
                sig
                  type inp
                  val get_input :
                    inp Code.abstract ->
                    (< answer : 'a; state : 'b; .. >,
                     C.contr Code.abstract * int Code.abstract * bool)
                    StateCPSMonad.monad
                end
              module InpJustMatrix :
                sig
                  type inp = C.contr
                  val get_input :
                    C.vc ->
                    (< answer : 'a; state : 'b; .. >,
                     C.vc * int Code.abstract * bool)
                    StateCPSMonad.monad
                end
              module InpMatrixMargin :
                sig
                  type inp = C.contr * int
                  val get_input :
                    ('a * 'b) Code.abstract ->
                    (< answer : 'c; state : 'd; .. >,
                     'a Code.abstract * 'b Code.abstract * bool)
                    StateCPSMonad.monad
                end
              module RowPivot :
                functor (Det : DETERMINANT) (P : TRACKPIVOT) (L : LOWER) ->
                  sig
                    val optim : 'a -> 'a option
                    val findpivot :
                      wmatrix ->
                      curpos ->
                      (< answer : 'a Code.abstract;
                         state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                                 list;
                         .. >,
                       C.Dom.v option Code.abstract)
                      StateCPSMonad.monad
                  end
              module FullPivot :
                functor (Det : DETERMINANT) (P : TRACKPIVOT) (L : LOWER) ->
                  sig
                    val optim : 'a -> 'a option
                    val findpivot :
                      wmatrix ->
                      curpos ->
                      (< answer : 'a Code.abstract;
                         state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                                 list;
                         .. >,
                       C.Dom.v option Code.abstract)
                      StateCPSMonad.monad
                  end
              module NoPivot :
                functor (Det : DETERMINANT) (P : TRACKPIVOT) (L : LOWER) ->
                  sig
                    val findpivot :
                      wmatrix ->
                      curpos ->
                      (< answer : 'a; state : 'b; .. >,
                       C.Dom.v option Code.abstract)
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
                      (< answer : 'a Code.abstract;
                         state : [> `TDet of OD.Det.lstate ] list; .. >,
                       (C.contr * C.Dom.v) Code.abstract)
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
                         state : [> `TRan of 'b ref Code.abstract ] list;
                         .. >,
                       (C.contr * 'b) Code.abstract)
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
                      (< answer : 'a Code.abstract;
                         state : [> `TDet of OD.Det.lstate
                                  | `TRan of 'b ref Code.abstract ]
                                 list;
                         .. >,
                       (C.contr * C.Dom.v * 'b) Code.abstract)
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
                                OD.PivotRep.perm_rep ref Code.abstract
                            type 'a pc_constraint = unit
                              constraint 'a =
                                < state : [> `TPivot of lstate ]; .. >
                            type ('a, 'v) lm = ('a, 'v) cmonad
                              constraint 'a =
                                < answer : 'b;
                                  state : [> `TPivot of lstate ]; .. >
                            type 'a nm =
                                (< answer : 'b Code.abstract;
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
                              (< answer : 'a Code.abstract;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Code.abstract ]
                                         list;
                                 .. >,
                               unit)
                              StateCPSMonad.monad
                            val add :
                              OD.PivotRep.fra ->
                              (< answer : 'a;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Code.abstract ]
                                         list;
                                 .. >,
                               unit Code.abstract option)
                              StateCPSMonad.monad
                            val fin :
                              unit ->
                              (< answer : 'a;
                                 state : [> `TPivot of 'b ref Code.abstract ]
                                         list;
                                 .. >,
                               'b Code.abstract)
                              StateCPSMonad.monad
                          end
                        module L = NoLower
                      end
                    type res = C.contr * C.Dom.v * int * IF.P.perm_rep
                    val make_result :
                      wmatrix ->
                      (< answer : 'a Code.abstract;
                         state : [> `TDet of OD.Det.lstate
                                  | `TPivot of 'b ref Code.abstract
                                  | `TRan of 'c ref Code.abstract ]
                                 list;
                         .. >,
                       (C.contr * C.Dom.v * 'c * 'b) Code.abstract)
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
                                OD.PivotRep.perm_rep ref Code.abstract
                            type 'a pc_constraint = unit
                              constraint 'a =
                                < state : [> `TPivot of lstate ]; .. >
                            type ('a, 'v) lm = ('a, 'v) cmonad
                              constraint 'a =
                                < answer : 'b;
                                  state : [> `TPivot of lstate ]; .. >
                            type 'a nm =
                                (< answer : 'b Code.abstract;
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
                              (< answer : 'a Code.abstract;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Code.abstract ]
                                         list;
                                 .. >,
                               unit)
                              StateCPSMonad.monad
                            val add :
                              OD.PivotRep.fra ->
                              (< answer : 'a;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Code.abstract ]
                                         list;
                                 .. >,
                               unit Code.abstract option)
                              StateCPSMonad.monad
                            val fin :
                              unit ->
                              (< answer : 'a;
                                 state : [> `TPivot of 'b ref Code.abstract ]
                                         list;
                                 .. >,
                               'b Code.abstract)
                              StateCPSMonad.monad
                          end
                        module L = SeparateLower
                      end
                    type res = C.contr * C.contr * IF.P.perm_rep
                    val make_result :
                      wmatrix ->
                      (< answer : 'a;
                         state : [> `TLower of 'b Code.abstract
                                  | `TPivot of 'c ref Code.abstract ]
                                 list;
                         .. >,
                       (C.contr * 'b * 'c) Code.abstract)
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
                                OD.PivotRep.perm_rep ref Code.abstract
                            type 'a pc_constraint = unit
                              constraint 'a =
                                < state : [> `TPivot of lstate ]; .. >
                            type ('a, 'v) lm = ('a, 'v) cmonad
                              constraint 'a =
                                < answer : 'b;
                                  state : [> `TPivot of lstate ]; .. >
                            type 'a nm =
                                (< answer : 'b Code.abstract;
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
                              (< answer : 'a Code.abstract;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Code.abstract ]
                                         list;
                                 .. >,
                               unit)
                              StateCPSMonad.monad
                            val add :
                              OD.PivotRep.fra ->
                              (< answer : 'a;
                                 state : [> `TPivot of
                                              OD.PivotRep.perm_rep ref
                                              Code.abstract ]
                                         list;
                                 .. >,
                               unit Code.abstract option)
                              StateCPSMonad.monad
                            val fin :
                              unit ->
                              (< answer : 'a;
                                 state : [> `TPivot of 'b ref Code.abstract ]
                                         list;
                                 .. >,
                               'b Code.abstract)
                              StateCPSMonad.monad
                          end
                        module L = PackedLower
                      end
                    type res = C.contr * IF.P.perm_rep
                    val make_result :
                      'a ->
                      (< answer : 'b;
                         state : [> `TLower of 'c Code.abstract
                                  | `TPivot of 'd ref Code.abstract ]
                                 list;
                         .. >,
                       ('c * 'd) Code.abstract)
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
                                type ira = int Code.abstract
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
                                    (< answer : 'b Code.abstract;
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
                                  int Code.abstract ->
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
                                type lstate = C.contr Code.abstract
                                type ('a, 'v) lm = ('a, 'v) cmonad
                                  constraint 'a =
                                    < answer : 'b;
                                      state : [> `TLower of lstate ]; .. >
                                val decl :
                                  C.contr Code.abstract ->
                                  (< answer : 'a;
                                     state : [> `TLower of lstate ]; .. >,
                                   C.contr)
                                  lm
                                val updt :
                                  C.vc ->
                                  int Code.abstract ->
                                  int Code.abstract ->
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
                        | `TLower of C.contr Code.abstract ]
                       as 'a)
                      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                    val init :
                      F.Input.inp Code.abstract ->
                      (< answer : 'a Code.abstract;
                         state : [> `TDet of F.Det.lstate
                                  | `TLower of C.contr Code.abstract
                                  | `TPivot of F.Output(F).IF.P.lstate
                                  | `TRan of TrackRank.lstate ]
                                 list;
                         .. >,
                       wmatrix * int ref Code.abstract *
                       int ref Code.abstract * int Code.abstract)
                      StateCPSMonad.monad
                    val forward_elim :
                      wmatrix * int ref Code.abstract *
                      int ref Code.abstract * int Code.abstract ->
                      ([> `TDet of F.Det.lstate
                        | `TLower of C.contr Code.abstract
                        | `TPivot of F.Output(F).IF.P.lstate
                        | `TRan of TrackRank.lstate ]
                       as 'a)
                      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                    val gen :
                      F.Input.inp Code.abstract ->
                      (< answer : 'a Code.abstract;
                         state : [> `TDet of F.Det.lstate
                                  | `TLower of O.IF.L.lstate
                                  | `TPivot of O.IF.P.lstate
                                  | `TRan of TrackRank.lstate ]
                                 list;
                         .. >,
                       O.res Code.abstract)
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
                    inp Code.abstract ->
                    (< answer : 'a; state : 'b; .. >,
                     C.contr Code.abstract * rhs Code.abstract)
                    StateCPSMonad.monad
                end
              module InpMatrixVector :
                sig
                  type inp = C.contr * C.contr
                  type rhs = C.contr
                  val get_input :
                    ('a * 'b) Code.abstract ->
                    (< answer : 'c Code.abstract; state : 'd; .. >,
                     'a Code.abstract * 'b Code.abstract)
                    StateCPSMonad.monad
                end
              module type OUTPUT =
                sig
                  type res
                  val make_result :
                    C.contr Code.abstract ->
                    C.contr Code.abstract ->
                    int Code.abstract ->
                    int Code.abstract ->
                    int Code.abstract ->
                    (< answer : 'a; state : 'b; .. >, res) cmonad
                end
              module OutJustAnswer :
                sig
                  type res = C.contr
                  val make_result :
                    C.vc ->
                    C.vc ->
                    int Code.abstract ->
                    int Code.abstract ->
                    int Code.abstract ->
                    'a -> ('a -> C.contr Code.abstract -> 'b) -> 'b
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
                                    type ira = int Code.abstract
                                    type fra = PermList.fra
                                    type pra = PermList.pra
                                    type lstate =
                                        PermList.perm_rep ref Code.abstract
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
                                        (< answer : 'b Code.abstract;
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
                                      int Code.abstract ->
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
                                    type lstate = C.contr Code.abstract
                                    type ('a, 'v) lm = ('a, 'v) cmonad
                                      constraint 'a =
                                        < answer : 'b;
                                          state : [> `TLower of lstate ];
                                          .. >
                                    val decl :
                                      C.contr Code.abstract ->
                                      (< answer : 'a;
                                         state : [> `TLower of lstate ]; .. >,
                                       C.contr)
                                      lm
                                    val updt :
                                      C.vc ->
                                      int Code.abstract ->
                                      int Code.abstract ->
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
                            | `TLower of C.contr Code.abstract ]
                           as 'a)
                          list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                        val init :
                          (C.contr * int) Code.abstract ->
                          (< answer : 'a Code.abstract;
                             state : [> `TDet of F.Det.lstate
                                      | `TLower of C.contr Code.abstract
                                      | `TPivot of
                                          PermList.perm_rep ref Code.abstract
                                      | `TRan of TrackRank.lstate ]
                                     list;
                             .. >,
                           wmatrix * int ref Code.abstract *
                           int ref Code.abstract * int Code.abstract)
                          StateCPSMonad.monad
                        val forward_elim :
                          wmatrix * int ref Code.abstract *
                          int ref Code.abstract * int Code.abstract ->
                          ([> `TDet of F.Det.lstate
                            | `TLower of C.contr Code.abstract
                            | `TPivot of PermList.perm_rep ref Code.abstract
                            | `TRan of TrackRank.lstate ]
                           as 'a)
                          list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                        val gen :
                          (C.contr * int) Code.abstract ->
                          (< answer : 'a Code.abstract;
                             state : [> `TDet of F.Det.lstate
                                      | `TLower of O.IF.L.lstate
                                      | `TPivot of O.IF.P.lstate
                                      | `TRan of TrackRank.lstate ]
                                     list;
                             .. >,
                           O.res Code.abstract)
                          StateCPSMonad.monad
                      end
                    val init :
                      F.Input.inp Code.abstract ->
                      (< answer : 'a; state : 'b; .. >,
                       C.contr Code.abstract * F.Input.rhs Code.abstract)
                      StateCPSMonad.monad
                    val back_elim :
                      C.vc ->
                      int Code.abstract ->
                      int Code.abstract ->
                      'a -> ('a -> C.contr Code.abstract -> 'b) -> 'b
                    val gen :
                      F.Input.inp Code.abstract ->
                      (< answer : 'a Code.abstract;
                         state : [> `TDet of F.Det.lstate
                                  | `TLower of GE'.O.IF.L.lstate
                                  | `TPivot of GE'.O.IF.P.lstate
                                  | `TRan of TrackRank.lstate ]
                                 list;
                         .. >,
                       F.Output.res Code.abstract)
                      StateCPSMonad.monad
                  end
            end
        end
  end
type 'b pr = { pf : 'b code; }
#   val instantiate :
  ('a code -> 'b list -> ('c -> 'd -> 'd) -> 'e code) -> ('a -> 'e) code =
  <fun>
#   val runit : 'a pr -> 'a = <fun>
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
    type vc = v code
    val zeroL : int code
    val oneL : int code
    val ( +^ ) : int code -> int code -> int code
    val ( *^ ) : int code -> int code -> int code
    val ( -^ ) : int code -> int code -> int code
    val uminusL : int code -> int code
    val divL : int code -> int code -> int code
    val normalizerL : 'a option
    val better_thanL : 'a option
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
    type vc = v code
    val zeroL : int code
    val oneL : int code
    val ( +^ ) : int code -> int code -> int code
    val ( *^ ) : int code -> int code -> int code
    val ( -^ ) : int code -> int code -> int code
    val uminusL : int code -> int code
    val divL : int code -> int code -> int code
    val normalizerL : 'a option
    val better_thanL : 'a option
  end
module GAC_F :
  sig
    module Dom :
      sig
        type v = Domains_code.FloatDomainL.v
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
        type vc = v code
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL : (vc -> vc -> bool code) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v array array
    type vc = contr code
    type vo = Dom.v code
    val getL : 'a array array code -> int code -> int code -> 'a code
    val dim2 : 'a array code -> int code
    val dim1 : 'a array array code -> int code
    val mapper :
      (vo -> vo) option -> Dom.v array array code -> Dom.v array array code
    val copy : 'a array array code -> 'a array array code
    val init : int code -> int code -> Dom.v array array code
    val augment :
      'a array array code ->
      int code ->
      int code -> 'a array array code -> int code -> 'a array array code
    val identity : int code -> int code -> Dom.v array array code
    val swap_rows_stmt :
      'a array code -> 'b -> int code -> int code -> unit code
    val swap_cols_stmt :
      'a array array code -> int code -> int code -> unit code
    val row_head : 'a array array code -> int code -> int code -> 'a code
    val col_head_set :
      'a array array code -> int code -> int code -> 'a code -> unit code
  end
module GVC_F :
  sig
    module Dom :
      sig
        type v = Domains_code.FloatDomainL.v
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
        type vc = v code
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL : (vc -> vc -> bool code) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v Prelude.container2dfromvector
    type vc = contr code
    type vo = Dom.v code
    val getL :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code
    val dim2 : 'a Prelude.container2dfromvector code -> int code
    val dim1 : 'a Prelude.container2dfromvector code -> int code
    val mapper :
      ('a code -> 'a code) option ->
      'a Prelude.container2dfromvector code ->
      'a Prelude.container2dfromvector code
    val copy :
      'a Prelude.container2dfromvector code ->
      'a Prelude.container2dfromvector code
    val init :
      int code -> int code -> Dom.v Prelude.container2dfromvector code
    val augment :
      Dom.v Prelude.container2dfromvector code ->
      int code ->
      int code ->
      Dom.v Prelude.container2dfromvector code ->
      int code -> Dom.v Prelude.container2dfromvector code
    val identity :
      int code -> int code -> Dom.v Prelude.container2dfromvector code
    val index_default : int code option -> int code
    val swap_rows_stmt :
      'a Prelude.container2dfromvector code ->
      int code option -> int code -> int code -> unit code
    val swap_cols_stmt :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> unit code
    val row_head :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code
    val col_head_set :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code -> unit code
  end
module GAC_I :
  sig
    module Dom :
      sig
        type v = Domains_code.IntegerDomainL.v
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
        type vc = v code
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL : (vc -> vc -> bool code) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v array array
    type vc = contr code
    type vo = Dom.v code
    val getL : 'a array array code -> int code -> int code -> 'a code
    val dim2 : 'a array code -> int code
    val dim1 : 'a array array code -> int code
    val mapper :
      (vo -> vo) option -> Dom.v array array code -> Dom.v array array code
    val copy : 'a array array code -> 'a array array code
    val init : int code -> int code -> Dom.v array array code
    val augment :
      'a array array code ->
      int code ->
      int code -> 'a array array code -> int code -> 'a array array code
    val identity : int code -> int code -> Dom.v array array code
    val swap_rows_stmt :
      'a array code -> 'b -> int code -> int code -> unit code
    val swap_cols_stmt :
      'a array array code -> int code -> int code -> unit code
    val row_head : 'a array array code -> int code -> int code -> 'a code
    val col_head_set :
      'a array array code -> int code -> int code -> 'a code -> unit code
  end
module GVC_I :
  sig
    module Dom :
      sig
        type v = Domains_code.IntegerDomainL.v
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
        type vc = v code
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL : (vc -> vc -> bool code) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v Prelude.container2dfromvector
    type vc = contr code
    type vo = Dom.v code
    val getL :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code
    val dim2 : 'a Prelude.container2dfromvector code -> int code
    val dim1 : 'a Prelude.container2dfromvector code -> int code
    val mapper :
      ('a code -> 'a code) option ->
      'a Prelude.container2dfromvector code ->
      'a Prelude.container2dfromvector code
    val copy :
      'a Prelude.container2dfromvector code ->
      'a Prelude.container2dfromvector code
    val init :
      int code -> int code -> Dom.v Prelude.container2dfromvector code
    val augment :
      Dom.v Prelude.container2dfromvector code ->
      int code ->
      int code ->
      Dom.v Prelude.container2dfromvector code ->
      int code -> Dom.v Prelude.container2dfromvector code
    val identity :
      int code -> int code -> Dom.v Prelude.container2dfromvector code
    val index_default : int code option -> int code
    val swap_rows_stmt :
      'a Prelude.container2dfromvector code ->
      int code option -> int code -> int code -> unit code
    val swap_cols_stmt :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> unit code
    val row_head :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code
    val col_head_set :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code -> unit code
  end
module GAC_R :
  sig
    module Dom :
      sig
        type v = Domains_code.RationalDomainL.v
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
        type vc = v code
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL : (vc -> vc -> bool code) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v array array
    type vc = contr code
    type vo = Dom.v code
    val getL : 'a array array code -> int code -> int code -> 'a code
    val dim2 : 'a array code -> int code
    val dim1 : 'a array array code -> int code
    val mapper :
      (vo -> vo) option -> Dom.v array array code -> Dom.v array array code
    val copy : 'a array array code -> 'a array array code
    val init : int code -> int code -> Dom.v array array code
    val augment :
      'a array array code ->
      int code ->
      int code -> 'a array array code -> int code -> 'a array array code
    val identity : int code -> int code -> Dom.v array array code
    val swap_rows_stmt :
      'a array code -> 'b -> int code -> int code -> unit code
    val swap_cols_stmt :
      'a array array code -> int code -> int code -> unit code
    val row_head : 'a array array code -> int code -> int code -> 'a code
    val col_head_set :
      'a array array code -> int code -> int code -> 'a code -> unit code
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
        type vc = v code
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL : (vc -> vc -> bool code) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v Prelude.container2dfromvector
    type vc = contr code
    type vo = Dom.v code
    val getL :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code
    val dim2 : 'a Prelude.container2dfromvector code -> int code
    val dim1 : 'a Prelude.container2dfromvector code -> int code
    val mapper :
      ('a code -> 'a code) option ->
      'a Prelude.container2dfromvector code ->
      'a Prelude.container2dfromvector code
    val copy :
      'a Prelude.container2dfromvector code ->
      'a Prelude.container2dfromvector code
    val init :
      int code -> int code -> Dom.v Prelude.container2dfromvector code
    val augment :
      Dom.v Prelude.container2dfromvector code ->
      int code ->
      int code ->
      Dom.v Prelude.container2dfromvector code ->
      int code -> Dom.v Prelude.container2dfromvector code
    val identity :
      int code -> int code -> Dom.v Prelude.container2dfromvector code
    val index_default : int code option -> int code
    val swap_rows_stmt :
      'a Prelude.container2dfromvector code ->
      int code option -> int code -> int code -> unit code
    val swap_cols_stmt :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> unit code
    val row_head :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code
    val col_head_set :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code -> unit code
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
        type vc = v code
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL : (vc -> vc -> bool code) option
        val normalizerL : (vc -> vc) option
      end
    type contr = Dom.v Prelude.container2dfromvector
    type vc = contr code
    type vo = Dom.v code
    val getL :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code
    val dim2 : 'a Prelude.container2dfromvector code -> int code
    val dim1 : 'a Prelude.container2dfromvector code -> int code
    val mapper :
      ('a code -> 'a code) option ->
      'a Prelude.container2dfromvector code ->
      'a Prelude.container2dfromvector code
    val copy :
      'a Prelude.container2dfromvector code ->
      'a Prelude.container2dfromvector code
    val init :
      int code -> int code -> Dom.v Prelude.container2dfromvector code
    val augment :
      Dom.v Prelude.container2dfromvector code ->
      int code ->
      int code ->
      Dom.v Prelude.container2dfromvector code ->
      int code -> Dom.v Prelude.container2dfromvector code
    val identity :
      int code -> int code -> Dom.v Prelude.container2dfromvector code
    val index_default : int code option -> int code
    val swap_rows_stmt :
      'a Prelude.container2dfromvector code ->
      int code option -> int code -> int code -> unit code
    val swap_cols_stmt :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> unit code
    val row_head :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code
    val col_head_set :
      'a Prelude.container2dfromvector code ->
      int code -> int code -> 'a code -> unit code
  end
module GFC_F :
  sig
    module Dom :
      sig
        type v =
            Domains_code.FortranVectorContainer(Domains_code.FloatDomainL).Dom.v
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
        type vc = v code
        val zeroL : vc
        val oneL : vc
        val ( +^ ) : vc -> vc -> vc
        val ( *^ ) : vc -> vc -> vc
        val ( -^ ) : vc -> vc -> vc
        val uminusL : vc -> vc
        val divL : vc -> vc -> vc
        val better_thanL : (vc -> vc -> bool code) option
        val normalizerL : (vc -> vc) option
      end
    type contr =
        Domains_code.FortranVectorContainer(Domains_code.FloatDomainL).contr
    type vc = contr code
    type vo = Dom.v code
    val getL : vc -> int code -> int code -> vo
    val dim1 : vc -> int code
    val dim2 : vc -> int code
    val mapper : (vo -> vo) option -> vc -> vc
    val copy : vc -> vc
    val init : int code -> int code -> vc
    val augment : vc -> int code -> int code -> vc -> int code -> vc
    val identity : int code -> int code -> vc
    val swap_rows_stmt :
      vc -> int code option -> int code -> int code -> unit code
    val swap_cols_stmt : vc -> int code -> int code -> unit code
    val row_head : vc -> int code -> int code -> vo
    val col_head_set : vc -> int code -> int code -> vo -> unit code
  end
module G_GAC_F :
  sig
    type wmatrix =
      Ge.LAMake(Code).GenLA(GAC_F).wmatrix = {
      matrix : GAC_F.vc;
      numrow : int Code.abstract;
      numcol : int Code.abstract;
    }
    type curpos =
      Ge.LAMake(Code).GenLA(GAC_F).curpos = {
      rowpos : int Code.abstract;
      colpos : int Code.abstract;
    }
    type curposval =
      Ge.LAMake(Code).GenLA(GAC_F).curposval = {
      p : curpos;
      curval : GAC_F.Dom.v Code.abstract;
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
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GAC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_F.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GAC_F.contr Code.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GAC_F.contr Code.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GAC_F.contr)
          lm
        val updt :
          GAC_F.vc ->
          int Code.abstract ->
          int Code.abstract ->
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
        type lstate = Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GAC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_F.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GAC_F.Dom.v ref
        type lstate = Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GAC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_F.Dom.v Code.abstract ->
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
            (in_val -> unit Code.abstract) ->
            GAC_F.Dom.v ref Code.abstract ->
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
                GAC_F.Dom.v Code.abstract ->
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
                GAC_F.Dom.v ref Code.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GAC_F.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GAC_F.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GAC_F.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Code.abstract ->
              (< answer : 'b Code.abstract;
                 state : [> `TLower of 'a Code.abstract ] list; .. >,
               'a Code.abstract)
              StateCPSMonad.monad
            val updt :
              GAC_F.vc ->
              int Code.abstract ->
              int Code.abstract ->
              GAC_F.vo ->
              GAC_F.vo ->
              (< answer : 'a; state : [> `TLower of GAC_F.vc ] list; .. >,
               unit Code.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GAC_F.contr Code.abstract
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
            type lstate = GAC_F.contr Code.abstract
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
              int Code.abstract ->
              int Code.abstract ->
              GAC_F.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Code.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_F.contr Code.abstract * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GAC_F.contr
            val get_input :
              GAC_F.vc ->
              (< answer : 'a; state : 'b; .. >,
               GAC_F.vc * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GAC_F.contr * int
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_F.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_F.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_F.Dom.v option Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GAC_F.contr * GAC_F.Dom.v) Code.abstract)
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
                   state : [> `TRan of 'b ref Code.abstract ] list; .. >,
                 (GAC_F.contr * 'b) Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Code.abstract ]
                           list;
                   .. >,
                 (GAC_F.contr * GAC_F.Dom.v * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GAC_F.contr * GAC_F.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Code.abstract
                            | `TRan of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GAC_F.contr * GAC_F.Dom.v * 'c * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GAC_F.contr * GAC_F.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Code.abstract
                            | `TPivot of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GAC_F.contr * 'b * 'c) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GAC_F.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Code.abstract
                            | `TPivot of 'd ref Code.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Code.abstract)
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
                          type ira = int Code.abstract
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
                              (< answer : 'b Code.abstract; state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Code.abstract ->
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
                          type lstate = GAC_F.contr Code.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GAC_F.contr Code.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GAC_F.contr)
                            lm
                          val updt :
                            GAC_F.vc ->
                            int Code.abstract ->
                            int Code.abstract ->
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
                  | `TLower of GAC_F.contr Code.abstract ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GAC_F.contr Code.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Code.abstract * int ref Code.abstract *
                 int Code.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Code.abstract * int ref Code.abstract *
                int Code.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Code.abstract)
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
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_F.contr Code.abstract * rhs Code.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GAC_F.contr * GAC_F.contr
            type rhs = GAC_F.contr
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c Code.abstract; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GAC_F.contr Code.abstract ->
              GAC_F.contr Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GAC_F.contr
            val make_result :
              GAC_F.vc ->
              GAC_F.vc ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              'a -> ('a -> GAC_F.contr Code.abstract -> 'b) -> 'b
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
                              type ira = int Code.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Code.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Code.abstract;
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
                                int Code.abstract ->
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
                              type lstate = GAC_F.contr Code.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GAC_F.contr Code.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GAC_F.contr)
                                lm
                              val updt :
                                GAC_F.vc ->
                                int Code.abstract ->
                                int Code.abstract ->
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
                      | `TLower of GAC_F.contr Code.abstract ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val init :
                    (GAC_F.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GAC_F.contr Code.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Code.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Code.abstract *
                     int ref Code.abstract * int Code.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Code.abstract * int ref Code.abstract *
                    int Code.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GAC_F.contr Code.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val gen :
                    (GAC_F.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Code.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_F.contr Code.abstract * F.Input.rhs Code.abstract)
                StateCPSMonad.monad
              val back_elim :
                GAC_F.vc ->
                int Code.abstract ->
                int Code.abstract ->
                'a -> ('a -> GAC_F.contr Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Code.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GVC_F :
  sig
    type wmatrix =
      Ge.LAMake(Code).GenLA(GVC_F).wmatrix = {
      matrix : GVC_F.vc;
      numrow : int Code.abstract;
      numcol : int Code.abstract;
    }
    type curpos =
      Ge.LAMake(Code).GenLA(GVC_F).curpos = {
      rowpos : int Code.abstract;
      colpos : int Code.abstract;
    }
    type curposval =
      Ge.LAMake(Code).GenLA(GVC_F).curposval = {
      p : curpos;
      curval : GVC_F.Dom.v Code.abstract;
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
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_F.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GVC_F.contr Code.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GVC_F.contr Code.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GVC_F.contr)
          lm
        val updt :
          GVC_F.vc ->
          int Code.abstract ->
          int Code.abstract ->
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
        type lstate = Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_F.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GVC_F.Dom.v ref
        type lstate = Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_F.Dom.v Code.abstract ->
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
            (in_val -> unit Code.abstract) ->
            GVC_F.Dom.v ref Code.abstract ->
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
                GVC_F.Dom.v Code.abstract ->
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
                GVC_F.Dom.v ref Code.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_F.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GVC_F.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GVC_F.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Code.abstract ->
              (< answer : 'b Code.abstract;
                 state : [> `TLower of 'a Code.abstract ] list; .. >,
               'a Code.abstract)
              StateCPSMonad.monad
            val updt :
              GVC_F.vc ->
              int Code.abstract ->
              int Code.abstract ->
              GVC_F.vo ->
              GVC_F.vo ->
              (< answer : 'a; state : [> `TLower of GVC_F.vc ] list; .. >,
               unit Code.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GVC_F.contr Code.abstract
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
            type lstate = GVC_F.contr Code.abstract
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
              int Code.abstract ->
              int Code.abstract ->
              GVC_F.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Code.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_F.contr Code.abstract * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GVC_F.contr
            val get_input :
              GVC_F.vc ->
              (< answer : 'a; state : 'b; .. >,
               GVC_F.vc * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GVC_F.contr * int
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_F.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_F.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_F.Dom.v option Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GVC_F.contr * GVC_F.Dom.v) Code.abstract)
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
                   state : [> `TRan of 'b ref Code.abstract ] list; .. >,
                 (GVC_F.contr * 'b) Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_F.contr * GVC_F.Dom.v * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GVC_F.contr * GVC_F.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Code.abstract
                            | `TRan of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_F.contr * GVC_F.Dom.v * 'c * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GVC_F.contr * GVC_F.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Code.abstract
                            | `TPivot of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_F.contr * 'b * 'c) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GVC_F.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Code.abstract
                            | `TPivot of 'd ref Code.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Code.abstract)
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
                          type ira = int Code.abstract
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
                              (< answer : 'b Code.abstract; state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Code.abstract ->
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
                          type lstate = GVC_F.contr Code.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GVC_F.contr Code.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_F.contr)
                            lm
                          val updt :
                            GVC_F.vc ->
                            int Code.abstract ->
                            int Code.abstract ->
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
                  | `TLower of GVC_F.contr Code.abstract ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GVC_F.contr Code.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Code.abstract * int ref Code.abstract *
                 int Code.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Code.abstract * int ref Code.abstract *
                int Code.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_F.contr Code.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Code.abstract)
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
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_F.contr Code.abstract * rhs Code.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GVC_F.contr * GVC_F.contr
            type rhs = GVC_F.contr
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c Code.abstract; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GVC_F.contr Code.abstract ->
              GVC_F.contr Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GVC_F.contr
            val make_result :
              GVC_F.vc ->
              GVC_F.vc ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              'a -> ('a -> GVC_F.contr Code.abstract -> 'b) -> 'b
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
                              type ira = int Code.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Code.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Code.abstract;
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
                                int Code.abstract ->
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
                              type lstate = GVC_F.contr Code.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GVC_F.contr Code.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_F.contr)
                                lm
                              val updt :
                                GVC_F.vc ->
                                int Code.abstract ->
                                int Code.abstract ->
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
                      | `TLower of GVC_F.contr Code.abstract ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val init :
                    (GVC_F.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GVC_F.contr Code.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Code.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Code.abstract *
                     int ref Code.abstract * int Code.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Code.abstract * int ref Code.abstract *
                    int Code.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_F.contr Code.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val gen :
                    (GVC_F.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Code.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_F.contr Code.abstract * F.Input.rhs Code.abstract)
                StateCPSMonad.monad
              val back_elim :
                GVC_F.vc ->
                int Code.abstract ->
                int Code.abstract ->
                'a -> ('a -> GVC_F.contr Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Code.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GAC_I :
  sig
    type wmatrix =
      Ge.LAMake(Code).GenLA(GAC_I).wmatrix = {
      matrix : GAC_I.vc;
      numrow : int Code.abstract;
      numcol : int Code.abstract;
    }
    type curpos =
      Ge.LAMake(Code).GenLA(GAC_I).curpos = {
      rowpos : int Code.abstract;
      colpos : int Code.abstract;
    }
    type curposval =
      Ge.LAMake(Code).GenLA(GAC_I).curposval = {
      p : curpos;
      curval : GAC_I.Dom.v Code.abstract;
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
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GAC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_I.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GAC_I.contr Code.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GAC_I.contr Code.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GAC_I.contr)
          lm
        val updt :
          GAC_I.vc ->
          int Code.abstract ->
          int Code.abstract ->
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
        type lstate = Ge.LAMake(Code).GenLA(GAC_I).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GAC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_I.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GAC_I.Dom.v ref
        type lstate = Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GAC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_I.Dom.v Code.abstract ->
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
            (in_val -> unit Code.abstract) ->
            GAC_I.Dom.v ref Code.abstract ->
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
                GAC_I.Dom.v Code.abstract ->
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
                GAC_I.Dom.v ref Code.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GAC_I.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GAC_I.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GAC_I.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Code.abstract ->
              (< answer : 'b Code.abstract;
                 state : [> `TLower of 'a Code.abstract ] list; .. >,
               'a Code.abstract)
              StateCPSMonad.monad
            val updt :
              GAC_I.vc ->
              int Code.abstract ->
              int Code.abstract ->
              GAC_I.vo ->
              GAC_I.vo ->
              (< answer : 'a; state : [> `TLower of GAC_I.vc ] list; .. >,
               unit Code.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GAC_I.contr Code.abstract
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
            type lstate = GAC_I.contr Code.abstract
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
              int Code.abstract ->
              int Code.abstract ->
              GAC_I.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Code.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_I.contr Code.abstract * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GAC_I.contr
            val get_input :
              GAC_I.vc ->
              (< answer : 'a; state : 'b; .. >,
               GAC_I.vc * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GAC_I.contr * int
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_I.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_I.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_I.Dom.v option Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GAC_I.contr * GAC_I.Dom.v) Code.abstract)
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
                   state : [> `TRan of 'b ref Code.abstract ] list; .. >,
                 (GAC_I.contr * 'b) Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Code.abstract ]
                           list;
                   .. >,
                 (GAC_I.contr * GAC_I.Dom.v * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GAC_I.contr * GAC_I.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Code.abstract
                            | `TRan of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GAC_I.contr * GAC_I.Dom.v * 'c * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GAC_I.contr * GAC_I.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Code.abstract
                            | `TPivot of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GAC_I.contr * 'b * 'c) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GAC_I.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Code.abstract
                            | `TPivot of 'd ref Code.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Code.abstract)
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
                          type ira = int Code.abstract
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
                              (< answer : 'b Code.abstract; state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Code.abstract ->
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
                          type lstate = GAC_I.contr Code.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GAC_I.contr Code.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GAC_I.contr)
                            lm
                          val updt :
                            GAC_I.vc ->
                            int Code.abstract ->
                            int Code.abstract ->
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
                  | `TLower of GAC_I.contr Code.abstract ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GAC_I.contr Code.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Code.abstract * int ref Code.abstract *
                 int Code.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Code.abstract * int ref Code.abstract *
                int Code.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GAC_I.contr Code.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Code.abstract)
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
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_I.contr Code.abstract * rhs Code.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GAC_I.contr * GAC_I.contr
            type rhs = GAC_I.contr
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c Code.abstract; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GAC_I.contr Code.abstract ->
              GAC_I.contr Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GAC_I.contr
            val make_result :
              GAC_I.vc ->
              GAC_I.vc ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              'a -> ('a -> GAC_I.contr Code.abstract -> 'b) -> 'b
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
                              type ira = int Code.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Code.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Code.abstract;
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
                                int Code.abstract ->
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
                              type lstate = GAC_I.contr Code.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GAC_I.contr Code.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GAC_I.contr)
                                lm
                              val updt :
                                GAC_I.vc ->
                                int Code.abstract ->
                                int Code.abstract ->
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
                      | `TLower of GAC_I.contr Code.abstract ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val init :
                    (GAC_I.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GAC_I.contr Code.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Code.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Code.abstract *
                     int ref Code.abstract * int Code.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Code.abstract * int ref Code.abstract *
                    int Code.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GAC_I.contr Code.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val gen :
                    (GAC_I.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Code.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_I.contr Code.abstract * F.Input.rhs Code.abstract)
                StateCPSMonad.monad
              val back_elim :
                GAC_I.vc ->
                int Code.abstract ->
                int Code.abstract ->
                'a -> ('a -> GAC_I.contr Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Code.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GVC_I :
  sig
    type wmatrix =
      Ge.LAMake(Code).GenLA(GVC_I).wmatrix = {
      matrix : GVC_I.vc;
      numrow : int Code.abstract;
      numcol : int Code.abstract;
    }
    type curpos =
      Ge.LAMake(Code).GenLA(GVC_I).curpos = {
      rowpos : int Code.abstract;
      colpos : int Code.abstract;
    }
    type curposval =
      Ge.LAMake(Code).GenLA(GVC_I).curposval = {
      p : curpos;
      curval : GVC_I.Dom.v Code.abstract;
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
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_I.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GVC_I.contr Code.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GVC_I.contr Code.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GVC_I.contr)
          lm
        val updt :
          GVC_I.vc ->
          int Code.abstract ->
          int Code.abstract ->
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
        type lstate = Ge.LAMake(Code).GenLA(GVC_I).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_I.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GVC_I.Dom.v ref
        type lstate = Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_I.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_I.Dom.v Code.abstract ->
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
            (in_val -> unit Code.abstract) ->
            GVC_I.Dom.v ref Code.abstract ->
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
                GVC_I.Dom.v Code.abstract ->
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
                GVC_I.Dom.v ref Code.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_I.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GVC_I.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GVC_I.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Code.abstract ->
              (< answer : 'b Code.abstract;
                 state : [> `TLower of 'a Code.abstract ] list; .. >,
               'a Code.abstract)
              StateCPSMonad.monad
            val updt :
              GVC_I.vc ->
              int Code.abstract ->
              int Code.abstract ->
              GVC_I.vo ->
              GVC_I.vo ->
              (< answer : 'a; state : [> `TLower of GVC_I.vc ] list; .. >,
               unit Code.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GVC_I.contr Code.abstract
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
            type lstate = GVC_I.contr Code.abstract
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
              int Code.abstract ->
              int Code.abstract ->
              GVC_I.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Code.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_I.contr Code.abstract * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GVC_I.contr
            val get_input :
              GVC_I.vc ->
              (< answer : 'a; state : 'b; .. >,
               GVC_I.vc * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GVC_I.contr * int
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_I.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_I.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_I.Dom.v option Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GVC_I.contr * GVC_I.Dom.v) Code.abstract)
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
                   state : [> `TRan of 'b ref Code.abstract ] list; .. >,
                 (GVC_I.contr * 'b) Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_I.contr * GVC_I.Dom.v * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GVC_I.contr * GVC_I.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Code.abstract
                            | `TRan of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_I.contr * GVC_I.Dom.v * 'c * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GVC_I.contr * GVC_I.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Code.abstract
                            | `TPivot of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_I.contr * 'b * 'c) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GVC_I.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Code.abstract
                            | `TPivot of 'd ref Code.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Code.abstract)
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
                          type ira = int Code.abstract
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
                              (< answer : 'b Code.abstract; state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Code.abstract ->
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
                          type lstate = GVC_I.contr Code.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GVC_I.contr Code.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_I.contr)
                            lm
                          val updt :
                            GVC_I.vc ->
                            int Code.abstract ->
                            int Code.abstract ->
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
                  | `TLower of GVC_I.contr Code.abstract ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GVC_I.contr Code.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Code.abstract * int ref Code.abstract *
                 int Code.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Code.abstract * int ref Code.abstract *
                int Code.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_I.contr Code.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Code.abstract)
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
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_I.contr Code.abstract * rhs Code.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GVC_I.contr * GVC_I.contr
            type rhs = GVC_I.contr
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c Code.abstract; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GVC_I.contr Code.abstract ->
              GVC_I.contr Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GVC_I.contr
            val make_result :
              GVC_I.vc ->
              GVC_I.vc ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              'a -> ('a -> GVC_I.contr Code.abstract -> 'b) -> 'b
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
                              type ira = int Code.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Code.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Code.abstract;
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
                                int Code.abstract ->
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
                              type lstate = GVC_I.contr Code.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GVC_I.contr Code.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_I.contr)
                                lm
                              val updt :
                                GVC_I.vc ->
                                int Code.abstract ->
                                int Code.abstract ->
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
                      | `TLower of GVC_I.contr Code.abstract ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val init :
                    (GVC_I.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GVC_I.contr Code.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Code.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Code.abstract *
                     int ref Code.abstract * int Code.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Code.abstract * int ref Code.abstract *
                    int Code.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_I.contr Code.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val gen :
                    (GVC_I.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Code.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_I.contr Code.abstract * F.Input.rhs Code.abstract)
                StateCPSMonad.monad
              val back_elim :
                GVC_I.vc ->
                int Code.abstract ->
                int Code.abstract ->
                'a -> ('a -> GVC_I.contr Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Code.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GAC_R :
  sig
    type wmatrix =
      Ge.LAMake(Code).GenLA(GAC_R).wmatrix = {
      matrix : GAC_R.vc;
      numrow : int Code.abstract;
      numcol : int Code.abstract;
    }
    type curpos =
      Ge.LAMake(Code).GenLA(GAC_R).curpos = {
      rowpos : int Code.abstract;
      colpos : int Code.abstract;
    }
    type curposval =
      Ge.LAMake(Code).GenLA(GAC_R).curposval = {
      p : curpos;
      curval : GAC_R.Dom.v Code.abstract;
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
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GAC_R.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_R.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_R.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GAC_R.contr Code.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GAC_R.contr Code.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GAC_R.contr)
          lm
        val updt :
          GAC_R.vc ->
          int Code.abstract ->
          int Code.abstract ->
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
        type lstate = Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GAC_R.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_R.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GAC_R.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GAC_R.Dom.v ref
        type lstate = Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GAC_R.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GAC_R.Dom.v Code.abstract ->
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
            (in_val -> unit Code.abstract) ->
            GAC_R.Dom.v ref Code.abstract ->
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
                GAC_R.Dom.v Code.abstract ->
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
                GAC_R.Dom.v ref Code.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GAC_R.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GAC_R.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GAC_R.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Code.abstract ->
              (< answer : 'b Code.abstract;
                 state : [> `TLower of 'a Code.abstract ] list; .. >,
               'a Code.abstract)
              StateCPSMonad.monad
            val updt :
              GAC_R.vc ->
              int Code.abstract ->
              int Code.abstract ->
              GAC_R.vo ->
              GAC_R.vo ->
              (< answer : 'a; state : [> `TLower of GAC_R.vc ] list; .. >,
               unit Code.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GAC_R.contr Code.abstract
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
            type lstate = GAC_R.contr Code.abstract
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
              int Code.abstract ->
              int Code.abstract ->
              GAC_R.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Code.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_R.contr Code.abstract * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GAC_R.contr
            val get_input :
              GAC_R.vc ->
              (< answer : 'a; state : 'b; .. >,
               GAC_R.vc * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GAC_R.contr * int
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_R.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GAC_R.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_R.Dom.v option Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GAC_R.contr * GAC_R.Dom.v) Code.abstract)
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
                   state : [> `TRan of 'b ref Code.abstract ] list; .. >,
                 (GAC_R.contr * 'b) Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Code.abstract ]
                           list;
                   .. >,
                 (GAC_R.contr * GAC_R.Dom.v * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GAC_R.contr * GAC_R.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Code.abstract
                            | `TRan of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GAC_R.contr * GAC_R.Dom.v * 'c * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GAC_R.contr * GAC_R.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Code.abstract
                            | `TPivot of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GAC_R.contr * 'b * 'c) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GAC_R.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Code.abstract
                            | `TPivot of 'd ref Code.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Code.abstract)
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
                          type ira = int Code.abstract
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
                              (< answer : 'b Code.abstract; state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Code.abstract ->
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
                          type lstate = GAC_R.contr Code.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GAC_R.contr Code.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GAC_R.contr)
                            lm
                          val updt :
                            GAC_R.vc ->
                            int Code.abstract ->
                            int Code.abstract ->
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
                  | `TLower of GAC_R.contr Code.abstract ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GAC_R.contr Code.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Code.abstract * int ref Code.abstract *
                 int Code.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Code.abstract * int ref Code.abstract *
                int Code.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GAC_R.contr Code.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Code.abstract)
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
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GAC_R.contr Code.abstract * rhs Code.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GAC_R.contr * GAC_R.contr
            type rhs = GAC_R.contr
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c Code.abstract; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GAC_R.contr Code.abstract ->
              GAC_R.contr Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GAC_R.contr
            val make_result :
              GAC_R.vc ->
              GAC_R.vc ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              'a -> ('a -> GAC_R.contr Code.abstract -> 'b) -> 'b
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
                              type ira = int Code.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Code.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Code.abstract;
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
                                int Code.abstract ->
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
                              type lstate = GAC_R.contr Code.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GAC_R.contr Code.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GAC_R.contr)
                                lm
                              val updt :
                                GAC_R.vc ->
                                int Code.abstract ->
                                int Code.abstract ->
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
                      | `TLower of GAC_R.contr Code.abstract ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val init :
                    (GAC_R.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GAC_R.contr Code.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Code.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Code.abstract *
                     int ref Code.abstract * int Code.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Code.abstract * int ref Code.abstract *
                    int Code.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GAC_R.contr Code.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val gen :
                    (GAC_R.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Code.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GAC_R.contr Code.abstract * F.Input.rhs Code.abstract)
                StateCPSMonad.monad
              val back_elim :
                GAC_R.vc ->
                int Code.abstract ->
                int Code.abstract ->
                'a -> ('a -> GAC_R.contr Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Code.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GVC_Z3 :
  sig
    type wmatrix =
      Ge.LAMake(Code).GenLA(GVC_Z3).wmatrix = {
      matrix : GVC_Z3.vc;
      numrow : int Code.abstract;
      numcol : int Code.abstract;
    }
    type curpos =
      Ge.LAMake(Code).GenLA(GVC_Z3).curpos = {
      rowpos : int Code.abstract;
      colpos : int Code.abstract;
    }
    type curposval =
      Ge.LAMake(Code).GenLA(GVC_Z3).curposval = {
      p : curpos;
      curval : GVC_Z3.Dom.v Code.abstract;
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
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_Z3.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z3.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z3.Dom.v)
          lm
      end
    module type LOWER =
      sig
        type lstate = GVC_Z3.contr Code.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GVC_Z3.contr Code.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GVC_Z3.contr)
          lm
        val updt :
          GVC_Z3.vc ->
          int Code.abstract ->
          int Code.abstract ->
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
        type lstate = Ge.LAMake(Code).GenLA(GVC_Z3).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_Z3.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z3.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z3.Dom.v)
          lm
      end
    module AbstractDet :
      sig
        type tdet = GVC_Z3.Dom.v ref
        type lstate = Ge.LAMake(Code).GenLA(GVC_Z3).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_Z3.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z3.Dom.v Code.abstract ->
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
            (in_val -> unit Code.abstract) ->
            GVC_Z3.Dom.v ref Code.abstract ->
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
                GVC_Z3.Dom.v Code.abstract ->
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
                GVC_Z3.Dom.v ref Code.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_Z3.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GVC_Z3.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GVC_Z3.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Code.abstract ->
              (< answer : 'b Code.abstract;
                 state : [> `TLower of 'a Code.abstract ] list; .. >,
               'a Code.abstract)
              StateCPSMonad.monad
            val updt :
              GVC_Z3.vc ->
              int Code.abstract ->
              int Code.abstract ->
              GVC_Z3.vo ->
              GVC_Z3.vo ->
              (< answer : 'a; state : [> `TLower of GVC_Z3.vc ] list; .. >,
               unit Code.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GVC_Z3.contr Code.abstract
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
            type lstate = GVC_Z3.contr Code.abstract
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
              int Code.abstract ->
              int Code.abstract ->
              GVC_Z3.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Code.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z3.contr Code.abstract * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GVC_Z3.contr
            val get_input :
              GVC_Z3.vc ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z3.vc * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GVC_Z3.contr * int
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_Z3.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_Z3.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_Z3.Dom.v option Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GVC_Z3.contr * GVC_Z3.Dom.v) Code.abstract)
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
                   state : [> `TRan of 'b ref Code.abstract ] list; .. >,
                 (GVC_Z3.contr * 'b) Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_Z3.contr * GVC_Z3.Dom.v * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GVC_Z3.contr * GVC_Z3.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Code.abstract
                            | `TRan of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_Z3.contr * GVC_Z3.Dom.v * 'c * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GVC_Z3.contr * GVC_Z3.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Code.abstract
                            | `TPivot of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_Z3.contr * 'b * 'c) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GVC_Z3.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Code.abstract
                            | `TPivot of 'd ref Code.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Code.abstract)
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
                          type ira = int Code.abstract
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
                              (< answer : 'b Code.abstract; state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Code.abstract ->
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
                          type lstate = GVC_Z3.contr Code.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GVC_Z3.contr Code.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_Z3.contr)
                            lm
                          val updt :
                            GVC_Z3.vc ->
                            int Code.abstract ->
                            int Code.abstract ->
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
                  | `TLower of GVC_Z3.contr Code.abstract ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GVC_Z3.contr Code.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Code.abstract * int ref Code.abstract *
                 int Code.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Code.abstract * int ref Code.abstract *
                int Code.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_Z3.contr Code.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Code.abstract)
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
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z3.contr Code.abstract * rhs Code.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GVC_Z3.contr * GVC_Z3.contr
            type rhs = GVC_Z3.contr
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c Code.abstract; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GVC_Z3.contr Code.abstract ->
              GVC_Z3.contr Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GVC_Z3.contr
            val make_result :
              GVC_Z3.vc ->
              GVC_Z3.vc ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              'a -> ('a -> GVC_Z3.contr Code.abstract -> 'b) -> 'b
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
                              type ira = int Code.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Code.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Code.abstract;
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
                                int Code.abstract ->
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
                              type lstate = GVC_Z3.contr Code.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GVC_Z3.contr Code.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_Z3.contr)
                                lm
                              val updt :
                                GVC_Z3.vc ->
                                int Code.abstract ->
                                int Code.abstract ->
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
                      | `TLower of GVC_Z3.contr Code.abstract ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val init :
                    (GVC_Z3.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GVC_Z3.contr Code.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Code.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Code.abstract *
                     int ref Code.abstract * int Code.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Code.abstract * int ref Code.abstract *
                    int Code.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_Z3.contr Code.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val gen :
                    (GVC_Z3.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Code.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_Z3.contr Code.abstract * F.Input.rhs Code.abstract)
                StateCPSMonad.monad
              val back_elim :
                GVC_Z3.vc ->
                int Code.abstract ->
                int Code.abstract ->
                'a -> ('a -> GVC_Z3.contr Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Code.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GVC_Z19 :
  sig
    type wmatrix =
      Ge.LAMake(Code).GenLA(GVC_Z19).wmatrix = {
      matrix : GVC_Z19.vc;
      numrow : int Code.abstract;
      numcol : int Code.abstract;
    }
    type curpos =
      Ge.LAMake(Code).GenLA(GVC_Z19).curpos = {
      rowpos : int Code.abstract;
      colpos : int Code.abstract;
    }
    type curposval =
      Ge.LAMake(Code).GenLA(GVC_Z19).curposval = {
      p : curpos;
      curval : GVC_Z19.Dom.v Code.abstract;
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
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_Z19.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z19.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z19.Dom.v)
          lm
      end
    module type LOWER =
      sig
        type lstate = GVC_Z19.contr Code.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GVC_Z19.contr Code.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >,
           GVC_Z19.contr)
          lm
        val updt :
          GVC_Z19.vc ->
          int Code.abstract ->
          int Code.abstract ->
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
        type lstate = Ge.LAMake(Code).GenLA(GVC_Z19).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_Z19.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z19.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GVC_Z19.Dom.v)
          lm
      end
    module AbstractDet :
      sig
        type tdet = GVC_Z19.Dom.v ref
        type lstate = Ge.LAMake(Code).GenLA(GVC_Z19).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GVC_Z19.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GVC_Z19.Dom.v Code.abstract ->
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
            (in_val -> unit Code.abstract) ->
            GVC_Z19.Dom.v ref Code.abstract ->
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
                GVC_Z19.Dom.v Code.abstract ->
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
                GVC_Z19.Dom.v ref Code.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GVC_Z19.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GVC_Z19.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GVC_Z19.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Code.abstract ->
              (< answer : 'b Code.abstract;
                 state : [> `TLower of 'a Code.abstract ] list; .. >,
               'a Code.abstract)
              StateCPSMonad.monad
            val updt :
              GVC_Z19.vc ->
              int Code.abstract ->
              int Code.abstract ->
              GVC_Z19.vo ->
              GVC_Z19.vo ->
              (< answer : 'a; state : [> `TLower of GVC_Z19.vc ] list; .. >,
               unit Code.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GVC_Z19.contr Code.abstract
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
            type lstate = GVC_Z19.contr Code.abstract
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
              int Code.abstract ->
              int Code.abstract ->
              GVC_Z19.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Code.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z19.contr Code.abstract * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GVC_Z19.contr
            val get_input :
              GVC_Z19.vc ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z19.vc * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GVC_Z19.contr * int
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_Z19.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GVC_Z19.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_Z19.Dom.v option Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GVC_Z19.contr * GVC_Z19.Dom.v) Code.abstract)
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
                   state : [> `TRan of 'b ref Code.abstract ] list; .. >,
                 (GVC_Z19.contr * 'b) Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_Z19.contr * GVC_Z19.Dom.v * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GVC_Z19.contr * GVC_Z19.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Code.abstract
                            | `TRan of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_Z19.contr * GVC_Z19.Dom.v * 'c * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GVC_Z19.contr * GVC_Z19.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Code.abstract
                            | `TPivot of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GVC_Z19.contr * 'b * 'c) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GVC_Z19.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Code.abstract
                            | `TPivot of 'd ref Code.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Code.abstract)
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
                          type ira = int Code.abstract
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
                              (< answer : 'b Code.abstract; state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Code.abstract ->
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
                          type lstate = GVC_Z19.contr Code.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GVC_Z19.contr Code.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GVC_Z19.contr)
                            lm
                          val updt :
                            GVC_Z19.vc ->
                            int Code.abstract ->
                            int Code.abstract ->
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
                  | `TLower of GVC_Z19.contr Code.abstract ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GVC_Z19.contr Code.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Code.abstract * int ref Code.abstract *
                 int Code.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Code.abstract * int ref Code.abstract *
                int Code.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GVC_Z19.contr Code.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Code.abstract)
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
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GVC_Z19.contr Code.abstract * rhs Code.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GVC_Z19.contr * GVC_Z19.contr
            type rhs = GVC_Z19.contr
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c Code.abstract; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GVC_Z19.contr Code.abstract ->
              GVC_Z19.contr Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GVC_Z19.contr
            val make_result :
              GVC_Z19.vc ->
              GVC_Z19.vc ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              'a -> ('a -> GVC_Z19.contr Code.abstract -> 'b) -> 'b
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
                              type ira = int Code.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Code.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Code.abstract;
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
                                int Code.abstract ->
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
                              type lstate = GVC_Z19.contr Code.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GVC_Z19.contr Code.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GVC_Z19.contr)
                                lm
                              val updt :
                                GVC_Z19.vc ->
                                int Code.abstract ->
                                int Code.abstract ->
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
                      | `TLower of GVC_Z19.contr Code.abstract ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val init :
                    (GVC_Z19.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GVC_Z19.contr Code.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Code.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Code.abstract *
                     int ref Code.abstract * int Code.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Code.abstract * int ref Code.abstract *
                    int Code.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GVC_Z19.contr Code.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val gen :
                    (GVC_Z19.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Code.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GVC_Z19.contr Code.abstract * F.Input.rhs Code.abstract)
                StateCPSMonad.monad
              val back_elim :
                GVC_Z19.vc ->
                int Code.abstract ->
                int Code.abstract ->
                'a -> ('a -> GVC_Z19.contr Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Code.abstract)
                StateCPSMonad.monad
            end
      end
  end
module G_GFC_F :
  sig
    type wmatrix =
      Ge.LAMake(Code).GenLA(GFC_F).wmatrix = {
      matrix : GFC_F.vc;
      numrow : int Code.abstract;
      numcol : int Code.abstract;
    }
    type curpos =
      Ge.LAMake(Code).GenLA(GFC_F).curpos = {
      rowpos : int Code.abstract;
      colpos : int Code.abstract;
    }
    type curposval =
      Ge.LAMake(Code).GenLA(GFC_F).curposval = {
      p : curpos;
      curval : GFC_F.Dom.v Code.abstract;
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
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GFC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GFC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GFC_F.Dom.v) lm
      end
    module type LOWER =
      sig
        type lstate = GFC_F.contr Code.abstract
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TLower of lstate ]; .. >
        val decl :
          GFC_F.contr Code.abstract ->
          (< answer : 'a; state : [> `TLower of lstate ]; .. >, GFC_F.contr)
          lm
        val updt :
          GFC_F.vc ->
          int Code.abstract ->
          int Code.abstract ->
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
        type lstate = Ge.LAMake(Code).GenLA(GFC_F).NoDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GFC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GFC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val fin :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, GFC_F.Dom.v) lm
      end
    module AbstractDet :
      sig
        type tdet = GFC_F.Dom.v ref
        type lstate = Ge.LAMake(Code).GenLA(GFC_F).AbstractDet.lstate
        type 'a pc_constraint = unit
          constraint 'a = < state : [> `TDet of lstate ]; .. >
        type ('a, 'v) lm = ('a, 'v) GEF.cmonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type ('a, 'v) om = ('a, 'v) GEF.omonad
          constraint 'a = < answer : 'b; state : [> `TDet of lstate ]; .. >
        type 'a nm =
            (< answer : 'b Code.abstract; state : 'c list >, unit)
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
          GFC_F.Dom.v Code.abstract ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, unit) lm
        val get_magn :
          unit ->
          (< answer : 'a; state : [> `TDet of lstate ]; .. >, tdet) lm
        val set_magn :
          GFC_F.Dom.v Code.abstract ->
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
            (in_val -> unit Code.abstract) ->
            GFC_F.Dom.v ref Code.abstract ->
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
                GFC_F.Dom.v Code.abstract ->
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
                GFC_F.Dom.v ref Code.abstract ->
                (< answer : 'b; state : 'c; .. >, 'a) StateCPSMonad.monad
              val update_det :
                GFC_F.Dom.v Code.abstract ->
                (< answer : 'a; state : [> `TDet of Det.lstate ]; .. >, unit)
                Det.lm
              val upd_kind : Ge.update_kind
            end
        module TrackLower :
          sig
            type lstate = GFC_F.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
          end
        module SeparateLower :
          sig
            type lstate = GFC_F.contr Code.abstract
            type ('a, 'v) lm = ('a, 'v) GEF.cmonad
              constraint 'a =
                < answer : 'b; state : [> `TLower of lstate ]; .. >
            val ip :
              ('a -> [> `TLower of 'a ]) *
              ([> `TLower of 'b ] -> 'b option) * string
            val decl :
              'a Code.abstract ->
              (< answer : 'b Code.abstract;
                 state : [> `TLower of 'a Code.abstract ] list; .. >,
               'a Code.abstract)
              StateCPSMonad.monad
            val updt :
              GFC_F.vc ->
              int Code.abstract ->
              int Code.abstract ->
              GFC_F.vo ->
              GFC_F.vo ->
              (< answer : 'a; state : [> `TLower of GFC_F.vc ] list; .. >,
               unit Code.abstract)
              StateCPSMonad.monad option
            val fin :
              unit ->
              (< answer : 'a; state : [> `TLower of 'b ] list; .. >, 'b)
              StateCPSMonad.monad
            val wants_pack : bool
          end
        module PackedLower :
          sig
            type lstate = GFC_F.contr Code.abstract
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
            type lstate = GFC_F.contr Code.abstract
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
              int Code.abstract ->
              int Code.abstract ->
              GFC_F.vo ->
              'a ->
              (< answer : 'b; state : 'c; .. >, unit Code.abstract)
              StateCPSMonad.monad option
            val fin : unit -> 'a
            val wants_pack : bool
          end
        module type INPUT =
          sig
            type inp
            val get_input :
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GFC_F.contr Code.abstract * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpJustMatrix :
          sig
            type inp = GFC_F.contr
            val get_input :
              GFC_F.vc ->
              (< answer : 'a; state : 'b; .. >,
               GFC_F.vc * int Code.abstract * bool)
              StateCPSMonad.monad
          end
        module InpMatrixMargin :
          sig
            type inp = GFC_F.contr * int
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract * bool)
              StateCPSMonad.monad
          end
        module RowPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GFC_F.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module FullPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val optim : 'a -> 'a option
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of Det.lstate | `TPivot of P.lstate ]
                           list;
                   .. >,
                 GFC_F.Dom.v option Code.abstract)
                StateCPSMonad.monad
            end
        module NoPivot :
          functor (Det : DETERMINANT) (P : GEF.TRACKPIVOT) (L : LOWER) ->
            sig
              val findpivot :
                wmatrix ->
                curpos ->
                (< answer : 'a; state : 'b; .. >,
                 GFC_F.Dom.v option Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate ] list; .. >,
                 (GFC_F.contr * GFC_F.Dom.v) Code.abstract)
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
                   state : [> `TRan of 'b ref Code.abstract ] list; .. >,
                 (GFC_F.contr * 'b) Code.abstract)
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
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TRan of 'b ref Code.abstract ]
                           list;
                   .. >,
                 (GFC_F.contr * GFC_F.Dom.v * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = NoLower
                end
              type res = GFC_F.contr * GFC_F.Dom.v * int * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of OD.Det.lstate
                            | `TPivot of 'b ref Code.abstract
                            | `TRan of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GFC_F.contr * GFC_F.Dom.v * 'c * 'b) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = SeparateLower
                end
              type res = GFC_F.contr * GFC_F.contr * IF.P.perm_rep
              val make_result :
                wmatrix ->
                (< answer : 'a;
                   state : [> `TLower of 'b Code.abstract
                            | `TPivot of 'c ref Code.abstract ]
                           list;
                   .. >,
                 (GFC_F.contr * 'b * 'c) Code.abstract)
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
                      type lstate = OD.PivotRep.perm_rep ref Code.abstract
                      type 'a pc_constraint = unit
                        constraint 'a =
                          < state : [> `TPivot of lstate ]; .. >
                      type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                        constraint 'a =
                          < answer : 'b; state : [> `TPivot of lstate ]; .. >
                      type 'a nm =
                          (< answer : 'b Code.abstract; state : 'c list >,
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
                        (< answer : 'a Code.abstract;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit)
                        StateCPSMonad.monad
                      val add :
                        OD.PivotRep.fra ->
                        (< answer : 'a;
                           state : [> `TPivot of
                                        OD.PivotRep.perm_rep ref
                                        Code.abstract ]
                                   list;
                           .. >,
                         unit Code.abstract option)
                        StateCPSMonad.monad
                      val fin :
                        unit ->
                        (< answer : 'a;
                           state : [> `TPivot of 'b ref Code.abstract ] list;
                           .. >,
                         'b Code.abstract)
                        StateCPSMonad.monad
                    end
                  module L = PackedLower
                end
              type res = GFC_F.contr * IF.P.perm_rep
              val make_result :
                'a ->
                (< answer : 'b;
                   state : [> `TLower of 'c Code.abstract
                            | `TPivot of 'd ref Code.abstract ]
                           list;
                   .. >,
                 ('c * 'd) Code.abstract)
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
                          type ira = int Code.abstract
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
                              (< answer : 'b Code.abstract; state : 'c list >,
                               unit)
                              StateCPSMonad.monad
                            constraint 'a =
                              < answer : 'b;
                                state : [> `TPivot of lstate ] as 'c; .. >
                          val rowrep : ira -> ira -> fra
                          val colrep : ira -> ira -> fra
                          val decl :
                            int Code.abstract ->
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
                          type lstate = GFC_F.contr Code.abstract
                          type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                            constraint 'a =
                              < answer : 'b; state : [> `TLower of lstate ];
                                .. >
                          val decl :
                            GFC_F.contr Code.abstract ->
                            (< answer : 'a; state : [> `TLower of lstate ];
                               .. >,
                             GFC_F.contr)
                            lm
                          val updt :
                            GFC_F.vc ->
                            int Code.abstract ->
                            int Code.abstract ->
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
                  | `TLower of GFC_F.contr Code.abstract ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GFC_F.contr Code.abstract
                            | `TPivot of F.Output(F).IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 wmatrix * int ref Code.abstract * int ref Code.abstract *
                 int Code.abstract)
                StateCPSMonad.monad
              val forward_elim :
                wmatrix * int ref Code.abstract * int ref Code.abstract *
                int Code.abstract ->
                ([> `TDet of F.Det.lstate
                  | `TLower of GFC_F.contr Code.abstract
                  | `TPivot of F.Output(F).IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 as 'a)
                list -> ('a list -> unit Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of O.IF.L.lstate
                            | `TPivot of O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 O.res Code.abstract)
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
              inp Code.abstract ->
              (< answer : 'a; state : 'b; .. >,
               GFC_F.contr Code.abstract * rhs Code.abstract)
              StateCPSMonad.monad
          end
        module InpMatrixVector :
          sig
            type inp = GFC_F.contr * GFC_F.contr
            type rhs = GFC_F.contr
            val get_input :
              ('a * 'b) Code.abstract ->
              (< answer : 'c Code.abstract; state : 'd; .. >,
               'a Code.abstract * 'b Code.abstract)
              StateCPSMonad.monad
          end
        module type OUTPUT =
          sig
            type res
            val make_result :
              GFC_F.contr Code.abstract ->
              GFC_F.contr Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              (< answer : 'a; state : 'b; .. >, res) GEF.cmonad
          end
        module OutJustAnswer :
          sig
            type res = GFC_F.contr
            val make_result :
              GFC_F.vc ->
              GFC_F.vc ->
              int Code.abstract ->
              int Code.abstract ->
              int Code.abstract ->
              'a -> ('a -> GFC_F.contr Code.abstract -> 'b) -> 'b
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
                              type ira = int Code.abstract
                              type fra = GEF.PermList.fra
                              type pra = GEF.PermList.pra
                              type lstate =
                                  GEF.PermList.perm_rep ref Code.abstract
                              type 'a pc_constraint = unit
                                constraint 'a =
                                  < state : [> `TPivot of lstate ]; .. >
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TPivot of lstate ]; .. >
                              type 'a nm =
                                  (< answer : 'b Code.abstract;
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
                                int Code.abstract ->
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
                              type lstate = GFC_F.contr Code.abstract
                              type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                                constraint 'a =
                                  < answer : 'b;
                                    state : [> `TLower of lstate ]; .. >
                              val decl :
                                GFC_F.contr Code.abstract ->
                                (< answer : 'a;
                                   state : [> `TLower of lstate ]; .. >,
                                 GFC_F.contr)
                                lm
                              val updt :
                                GFC_F.vc ->
                                int Code.abstract ->
                                int Code.abstract ->
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
                      | `TLower of GFC_F.contr Code.abstract ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val init :
                    (GFC_F.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of GFC_F.contr Code.abstract
                                | `TPivot of
                                    GEF.PermList.perm_rep ref Code.abstract
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     wmatrix * int ref Code.abstract *
                     int ref Code.abstract * int Code.abstract)
                    StateCPSMonad.monad
                  val forward_elim :
                    wmatrix * int ref Code.abstract * int ref Code.abstract *
                    int Code.abstract ->
                    ([> `TDet of F.Det.lstate
                      | `TLower of GFC_F.contr Code.abstract
                      | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                      | `TRan of GEF.TrackRank.lstate ]
                     as 'a)
                    list -> ('a list -> unit Code.abstract -> 'b) -> 'b
                  val gen :
                    (GFC_F.contr * int) Code.abstract ->
                    (< answer : 'a Code.abstract;
                       state : [> `TDet of F.Det.lstate
                                | `TLower of O.IF.L.lstate
                                | `TPivot of O.IF.P.lstate
                                | `TRan of GEF.TrackRank.lstate ]
                               list;
                       .. >,
                     O.res Code.abstract)
                    StateCPSMonad.monad
                end
              val init :
                F.Input.inp Code.abstract ->
                (< answer : 'a; state : 'b; .. >,
                 GFC_F.contr Code.abstract * F.Input.rhs Code.abstract)
                StateCPSMonad.monad
              val back_elim :
                GFC_F.vc ->
                int Code.abstract ->
                int Code.abstract ->
                'a -> ('a -> GFC_F.contr Code.abstract -> 'b) -> 'b
              val gen :
                F.Input.inp Code.abstract ->
                (< answer : 'a Code.abstract;
                   state : [> `TDet of F.Det.lstate
                            | `TLower of GE'.O.IF.L.lstate
                            | `TPivot of GE'.O.IF.P.lstate
                            | `TRan of GEF.TrackRank.lstate ]
                           list;
                   .. >,
                 F.Output.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = Prelude.perm Code.abstract
                type pra = Prelude.perm list Code.abstract
                type lstate = Prelude.perm list ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of Prelude.perm list ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of Prelude.perm list ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = (int * int) Code.abstract
                type pra = int array Code.abstract
                type lstate = int array ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of int array ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of int array ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      (GAC_F.contr * int) Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      (GAC_F.contr * int) Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      (GAC_F.contr * int) Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      (GAC_F.contr * int) Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      (GAC_F.contr * int) Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      (GAC_F.contr * int) Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      (GAC_F.contr * int) Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      (GAC_F.contr * int) Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = Prelude.perm Code.abstract
                type pra = Prelude.perm list Code.abstract
                type lstate = Prelude.perm list ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of Prelude.perm list ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of Prelude.perm list ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = Prelude.perm Code.abstract
                type pra = Prelude.perm list Code.abstract
                type lstate = Prelude.perm list ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of Prelude.perm list ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of Prelude.perm list ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = Prelude.perm Code.abstract
                type pra = Prelude.perm list Code.abstract
                type lstate = Prelude.perm list ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_F.contr)
                  lm
                val updt :
                  GAC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of GAC_F.contr Code.abstract
                  | `TPivot of Prelude.perm list ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
        | `TLower of GAC_F.contr Code.abstract
        | `TPivot of Prelude.perm list ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
                  | `TLower of GVC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of GVC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
                  | `TLower of GVC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of GVC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of GVC_F.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
        | `TLower of GVC_F.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = Prelude.perm Code.abstract
                type pra = Prelude.perm list Code.abstract
                type lstate = Prelude.perm list ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
                  | `TLower of GVC_F.contr Code.abstract
                  | `TPivot of Prelude.perm list ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Code.abstract
        | `TPivot of Prelude.perm list ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = Prelude.perm Code.abstract
                type pra = Prelude.perm list Code.abstract
                type lstate = Prelude.perm list ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_F.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_F.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_F.contr)
                  lm
                val updt :
                  GVC_F.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
                  | `TLower of GVC_F.contr Code.abstract
                  | `TPivot of Prelude.perm list ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_F.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
        | `TLower of GVC_F.contr Code.abstract
        | `TPivot of Prelude.perm list ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_F.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_F).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val updt :
                  GAC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of GAC_I.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val updt :
                  GAC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of GAC_I.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val updt :
                  GAC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of GAC_I.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_I.contr)
                  lm
                val updt :
                  GAC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of GAC_I.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
        | `TLower of GAC_I.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = Prelude.perm Code.abstract
                type pra = Prelude.perm list Code.abstract
                type lstate = Prelude.perm list ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_I.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_I.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_I.contr)
                  lm
                val updt :
                  GVC_I.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of GVC_I.contr Code.abstract
                  | `TPivot of Prelude.perm list ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_I.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
        | `TLower of GVC_I.contr Code.abstract
        | `TPivot of Prelude.perm list ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_I.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_I).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_R.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_R.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val updt :
                  GAC_R.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
        | `TLower of GAC_R.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_R.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
                  | `TLower of GAC_R.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_R.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_R.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
        | `TLower of GAC_R.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_R.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_R.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_R.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val updt :
                  GAC_R.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
        | `TLower of GAC_R.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_R.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
                  | `TLower of GAC_R.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_R.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_R.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
        | `TLower of GAC_R.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_R.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_R.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_R.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val updt :
                  GAC_R.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
             state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
        | `TLower of GAC_R.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_R.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
                  | `TLower of GAC_R.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_R.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_R.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
        | `TLower of GAC_R.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_R.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).NoDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = GEF.PermList.fra
                type pra = GEF.PermList.pra
                type lstate = GEF.PermList.perm_rep ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GAC_R.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GAC_R.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GAC_R.contr)
                  lm
                val updt :
                  GAC_R.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
        | `TLower of GAC_R.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GAC_R.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
                  | `TLower of GAC_R.contr Code.abstract
                  | `TPivot of GEF.PermList.perm_rep ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GAC_R.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GAC_R.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
        | `TLower of GAC_R.contr Code.abstract
        | `TPivot of GEF.PermList.perm_rep ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GAC_R.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GAC_R).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = Prelude.perm Code.abstract
                type pra = Prelude.perm list Code.abstract
                type lstate = Prelude.perm list ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_Z3.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_Z3.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_Z3.contr)
                  lm
                val updt :
                  GVC_Z3.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_Z3).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_Z3).AbstractDet.lstate
        | `TLower of GVC_Z3.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_Z3.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_Z3).AbstractDet.lstate
                  | `TLower of GVC_Z3.contr Code.abstract
                  | `TPivot of Prelude.perm list ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_Z3.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_Z3.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_Z3).AbstractDet.lstate
        | `TLower of GVC_Z3.contr Code.abstract
        | `TPivot of Prelude.perm list ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_Z3.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of Ge.LAMake(Code).GenLA(GVC_Z3).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
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
                type ira = int Code.abstract
                type fra = Prelude.perm Code.abstract
                type pra = Prelude.perm list Code.abstract
                type lstate = Prelude.perm list ref Code.abstract
                type 'a pc_constraint = unit
                  constraint 'a = < state : [> `TPivot of lstate ]; .. >
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ]; .. >
                type 'a nm =
                    (< answer : 'b Code.abstract; state : 'c list >, unit)
                    StateCPSMonad.monad
                  constraint 'a =
                    < answer : 'b; state : [> `TPivot of lstate ] as 'c; .. >
                val rowrep : ira -> ira -> fra
                val colrep : ira -> ira -> fra
                val decl :
                  int Code.abstract ->
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
                type lstate = GVC_Z19.contr Code.abstract
                type ('a, 'v) lm = ('a, 'v) GEF.cmonad
                  constraint 'a =
                    < answer : 'b; state : [> `TLower of lstate ]; .. >
                val decl :
                  GVC_Z19.contr Code.abstract ->
                  (< answer : 'a; state : [> `TLower of lstate ]; .. >,
                   GVC_Z19.contr)
                  lm
                val updt :
                  GVC_Z19.vc ->
                  int Code.abstract ->
                  int Code.abstract ->
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
                          Ge.LAMake(Code).GenLA(GVC_Z19).AbstractDet.lstate
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
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_Z19).AbstractDet.lstate
        | `TLower of GVC_Z19.contr Code.abstract ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val init :
      GVC_Z19.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of
                      Ge.LAMake(Code).GenLA(GVC_Z19).AbstractDet.lstate
                  | `TLower of GVC_Z19.contr Code.abstract
                  | `TPivot of Prelude.perm list ref Code.abstract
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       G_GVC_Z19.wmatrix * int ref Code.abstract * int ref Code.abstract *
       int Code.abstract)
      StateCPSMonad.monad
    val forward_elim :
      G_GVC_Z19.wmatrix * int ref Code.abstract * int ref Code.abstract *
      int Code.abstract ->
      ([> `TDet of Ge.LAMake(Code).GenLA(GVC_Z19).AbstractDet.lstate
        | `TLower of GVC_Z19.contr Code.abstract
        | `TPivot of Prelude.perm list ref Code.abstract
        | `TRan of GEF.TrackRank.lstate ]
       as 'a)
      list -> ('a list -> unit Code.abstract -> 'b) -> 'b
    val gen :
      GVC_Z19.contr Code.abstract ->
      (< answer : 'a Code.abstract;
         state : [> `TDet of
                      Ge.LAMake(Code).GenLA(GVC_Z19).AbstractDet.lstate
                  | `TLower of O.IF.L.lstate
                  | `TPivot of O.IF.P.lstate
                  | `TRan of GEF.TrackRank.lstate ]
                 list;
         .. >,
       O.res Code.abstract)
      StateCPSMonad.monad
  end
val resFA1 : (GAC_F.contr -> GenFA1.O.res) code = .<
  fun a_1  ->
    let t_2 = Pervasives.ref 0 in
    let t_3 = Pervasives.ref 0 in
    let t_5 = Array.map (fun x_4  -> Array.copy x_4) (Array.copy a_1) in
    let t_6 = Array.length (a_1.(0)) in
    let t_7 = Array.length a_1 in
    while ((! t_3) < t_6) && ((! t_2) < t_7) do
      (let t_10 = ! t_2 in
       let t_11 = ! t_3 in
       let t_12 = Pervasives.ref None in
       let t_18 =
         for j_15 = t_10 to t_7 - 1 do
           (let t_16 = (t_5.(j_15)).(t_11) in
            if t_16 <> 0.
            then
              match ! t_12 with
              | Some i_17 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_17)) <
                       (Pervasives.abs_float t_16)
                   then t_12 := (Some (j_15, t_16)))
              | None  -> t_12 := (Some (j_15, t_16)))
         done;
         (match ! t_12 with
          | Some i_13 ->
              (if (Pervasives.fst i_13) <> t_10
               then
                 (let t_14 = t_5.(t_10) in
                  t_5.(t_10) <- t_5.(Pervasives.fst i_13);
                  t_5.(Pervasives.fst i_13) <- t_14);
               Some (Pervasives.snd i_13))
          | None  -> None) in
       (match t_18 with
        | Some i_19 ->
            ((for j_20 = t_10 + 1 to t_7 - 1 do
                (let t_21 = (t_5.(j_20)).(t_11) in
                 if t_21 <> 0.
                 then
                   (for j_22 = t_11 + 1 to t_6 - 1 do
                      (t_5.(j_20)).(j_22) <-
                      ((t_5.(j_20)).(j_22)) -.
                        ((t_21 /. i_19) *. ((t_5.(t_10)).(j_22)))
                    done;
                    (t_5.(j_20)).(t_11) <- 0.))
              done;
              ());
             t_2 := ((! t_2) + 1))
        | None  -> ());
       t_3 := ((! t_3) + 1))
      done;
    t_5>.
  
val resFA2 : (GAC_F.contr -> GenFA2.O.res) code = .<
  fun a_23  ->
    let t_24 = Pervasives.ref 0 in
    let t_25 = Pervasives.ref 0 in
    let t_27 = Array.map (fun x_26  -> Array.copy x_26) (Array.copy a_23) in
    let t_28 = Array.length (a_23.(0)) in
    let t_29 = Array.length a_23 in
    let t_30 = Pervasives.ref 1. in
    let t_31 = Pervasives.ref 1 in
    while ((! t_25) < t_28) && ((! t_24) < t_29) do
      (let t_34 = ! t_24 in
       let t_35 = ! t_25 in
       let t_36 = Pervasives.ref None in
       let t_42 =
         for j_39 = t_34 to t_29 - 1 do
           (let t_40 = (t_27.(j_39)).(t_35) in
            if t_40 <> 0.
            then
              match ! t_36 with
              | Some i_41 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_41)) <
                       (Pervasives.abs_float t_40)
                   then t_36 := (Some (j_39, t_40)))
              | None  -> t_36 := (Some (j_39, t_40)))
         done;
         (match ! t_36 with
          | Some i_37 ->
              (if (Pervasives.fst i_37) <> t_34
               then
                 ((let t_38 = t_27.(t_34) in
                   t_27.(t_34) <- t_27.(Pervasives.fst i_37);
                   t_27.(Pervasives.fst i_37) <- t_38);
                  t_31 := (- (! t_31)));
               Some (Pervasives.snd i_37))
          | None  -> None) in
       (match t_42 with
        | Some i_43 ->
            ((for j_44 = t_34 + 1 to t_29 - 1 do
                (let t_45 = (t_27.(j_44)).(t_35) in
                 if t_45 <> 0.
                 then
                   (for j_46 = t_35 + 1 to t_28 - 1 do
                      (t_27.(j_44)).(j_46) <-
                      ((t_27.(j_44)).(j_46)) -.
                        ((t_45 /. i_43) *. ((t_27.(t_34)).(j_46)))
                    done;
                    (t_27.(j_44)).(t_35) <- 0.))
              done;
              t_30 := ((! t_30) *. i_43));
             t_24 := ((! t_24) + 1))
        | None  -> t_31 := 0);
       t_25 := ((! t_25) + 1))
      done;
    (t_27,
      (if (! t_31) = 0
       then 0.
       else if (! t_31) = 1 then ! t_30 else -. (! t_30)))>.
  
val resFA3 : (GAC_F.contr -> GenFA3.O.res) code = .<
  fun a_47  ->
    let t_48 = Pervasives.ref 0 in
    let t_49 = Pervasives.ref 0 in
    let t_51 = Array.map (fun x_50  -> Array.copy x_50) (Array.copy a_47) in
    let t_52 = Array.length (a_47.(0)) in
    let t_53 = Array.length a_47 in
    while ((! t_49) < t_52) && ((! t_48) < t_53) do
      (let t_56 = ! t_48 in
       let t_57 = ! t_49 in
       let t_58 = Pervasives.ref None in
       let t_64 =
         for j_61 = t_56 to t_53 - 1 do
           (let t_62 = (t_51.(j_61)).(t_57) in
            if t_62 <> 0.
            then
              match ! t_58 with
              | Some i_63 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_63)) <
                       (Pervasives.abs_float t_62)
                   then t_58 := (Some (j_61, t_62)))
              | None  -> t_58 := (Some (j_61, t_62)))
         done;
         (match ! t_58 with
          | Some i_59 ->
              (if (Pervasives.fst i_59) <> t_56
               then
                 (let t_60 = t_51.(t_56) in
                  t_51.(t_56) <- t_51.(Pervasives.fst i_59);
                  t_51.(Pervasives.fst i_59) <- t_60);
               Some (Pervasives.snd i_59))
          | None  -> None) in
       (match t_64 with
        | Some i_65 ->
            ((for j_66 = t_56 + 1 to t_53 - 1 do
                (let t_67 = (t_51.(j_66)).(t_57) in
                 if t_67 <> 0.
                 then
                   (for j_68 = t_57 + 1 to t_52 - 1 do
                      (t_51.(j_66)).(j_68) <-
                      ((t_51.(j_66)).(j_68)) -.
                        ((t_67 /. i_65) *. ((t_51.(t_56)).(j_68)))
                    done;
                    (t_51.(j_66)).(t_57) <- 0.))
              done;
              ());
             t_48 := ((! t_48) + 1))
        | None  -> ());
       t_49 := ((! t_49) + 1))
      done;
    (t_51, (! t_48))>.
  
val resFA4 : (GAC_F.contr -> GenFA4.O.res) code = .<
  fun a_69  ->
    let t_70 = Pervasives.ref 0 in
    let t_71 = Pervasives.ref 0 in
    let t_73 = Array.map (fun x_72  -> Array.copy x_72) (Array.copy a_69) in
    let t_74 = Array.length (a_69.(0)) in
    let t_75 = Array.length a_69 in
    let t_76 = Pervasives.ref 1. in
    let t_77 = Pervasives.ref 1 in
    while ((! t_71) < t_74) && ((! t_70) < t_75) do
      (let t_80 = ! t_70 in
       let t_81 = ! t_71 in
       let t_82 = Pervasives.ref None in
       let t_88 =
         for j_85 = t_80 to t_75 - 1 do
           (let t_86 = (t_73.(j_85)).(t_81) in
            if t_86 <> 0.
            then
              match ! t_82 with
              | Some i_87 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_87)) <
                       (Pervasives.abs_float t_86)
                   then t_82 := (Some (j_85, t_86)))
              | None  -> t_82 := (Some (j_85, t_86)))
         done;
         (match ! t_82 with
          | Some i_83 ->
              (if (Pervasives.fst i_83) <> t_80
               then
                 ((let t_84 = t_73.(t_80) in
                   t_73.(t_80) <- t_73.(Pervasives.fst i_83);
                   t_73.(Pervasives.fst i_83) <- t_84);
                  t_77 := (- (! t_77)));
               Some (Pervasives.snd i_83))
          | None  -> None) in
       (match t_88 with
        | Some i_89 ->
            ((for j_90 = t_80 + 1 to t_75 - 1 do
                (let t_91 = (t_73.(j_90)).(t_81) in
                 if t_91 <> 0.
                 then
                   (for j_92 = t_81 + 1 to t_74 - 1 do
                      (t_73.(j_90)).(j_92) <-
                      ((t_73.(j_90)).(j_92)) -.
                        ((t_91 /. i_89) *. ((t_73.(t_80)).(j_92)))
                    done;
                    (t_73.(j_90)).(t_81) <- 0.))
              done;
              t_76 := ((! t_76) *. i_89));
             t_70 := ((! t_70) + 1))
        | None  -> t_77 := 0);
       t_71 := ((! t_71) + 1))
      done;
    (t_73,
      (if (! t_77) = 0
       then 0.
       else if (! t_77) = 1 then ! t_76 else -. (! t_76)), (! t_70))>.
  
val resFV1 : (GVC_F.contr -> GenFV1.O.res) code = .<
  fun a_93  ->
    let t_94 = Pervasives.ref 0 in
    let t_95 = Pervasives.ref 0 in
    let t_96 =
      { a_93 with Domains_common.arr = (Array.copy a_93.Domains_common.arr) } in
    let t_97 = a_93.Domains_common.m in
    let t_98 = a_93.Domains_common.n in
    while ((! t_95) < t_97) && ((! t_94) < t_98) do
      (let t_103 = ! t_94 in
       let t_104 = ! t_95 in
       let t_105 = Pervasives.ref None in
       let t_116 =
         for j_113 = t_103 to t_98 - 1 do
           (let t_114 =
              (t_96.Domains_common.arr).((j_113 * t_96.Domains_common.m) +
                                           t_104) in
            if t_114 <> 0.
            then
              match ! t_105 with
              | Some i_115 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_115)) <
                       (Pervasives.abs_float t_114)
                   then t_105 := (Some (j_113, t_114)))
              | None  -> t_105 := (Some (j_113, t_114)))
         done;
         (match ! t_105 with
          | Some i_106 ->
              (if (Pervasives.fst i_106) <> t_103
               then
                 (let a_107 = t_96.Domains_common.arr
                  and m_108 = t_96.Domains_common.m in
                  let i1_109 = t_103 * m_108
                  and i2_110 = (Pervasives.fst i_106) * m_108 in
                  for i_111 = t_104 to m_108 - 1 do
                    let t_112 = a_107.(i1_109 + i_111) in
                    a_107.(i1_109 + i_111) <- a_107.(i2_110 + i_111);
                    a_107.(i2_110 + i_111) <- t_112
                  done);
               Some (Pervasives.snd i_106))
          | None  -> None) in
       (match t_116 with
        | Some i_117 ->
            ((for j_118 = t_103 + 1 to t_98 - 1 do
                (let t_119 =
                   (t_96.Domains_common.arr).((j_118 * t_96.Domains_common.m)
                                                + t_104) in
                 if t_119 <> 0.
                 then
                   (for j_120 = t_104 + 1 to t_97 - 1 do
                      (t_96.Domains_common.arr).((j_118 *
                                                    t_96.Domains_common.m)
                                                   + j_120)
                      <-
                      ((t_96.Domains_common.arr).((j_118 *
                                                     t_96.Domains_common.m)
                                                    + j_120))
                        -.
                        ((t_119 /. i_117) *.
                           ((t_96.Domains_common.arr).((t_103 *
                                                          t_96.Domains_common.m)
                                                         + j_120)))
                    done;
                    (t_96.Domains_common.arr).((j_118 * t_96.Domains_common.m)
                                                 + t_104)
                    <- 0.))
              done;
              ());
             t_94 := ((! t_94) + 1))
        | None  -> ());
       t_95 := ((! t_95) + 1))
      done;
    t_96>.
  
val resFV2 : (GVC_F.contr -> GenFV2.O.res) code = .<
  fun a_121  ->
    let t_122 = Pervasives.ref 0 in
    let t_123 = Pervasives.ref 0 in
    let t_124 =
      { a_121 with Domains_common.arr = (Array.copy a_121.Domains_common.arr)
      } in
    let t_125 = a_121.Domains_common.m in
    let t_126 = a_121.Domains_common.n in
    let t_127 = Pervasives.ref 1. in
    let t_128 = Pervasives.ref 1 in
    while ((! t_123) < t_125) && ((! t_122) < t_126) do
      (let t_133 = ! t_122 in
       let t_134 = ! t_123 in
       let t_135 = Pervasives.ref None in
       let t_146 =
         for j_143 = t_133 to t_126 - 1 do
           (let t_144 =
              (t_124.Domains_common.arr).((j_143 * t_124.Domains_common.m) +
                                            t_134) in
            if t_144 <> 0.
            then
              match ! t_135 with
              | Some i_145 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_145)) <
                       (Pervasives.abs_float t_144)
                   then t_135 := (Some (j_143, t_144)))
              | None  -> t_135 := (Some (j_143, t_144)))
         done;
         (match ! t_135 with
          | Some i_136 ->
              (if (Pervasives.fst i_136) <> t_133
               then
                 ((let a_137 = t_124.Domains_common.arr
                   and m_138 = t_124.Domains_common.m in
                   let i1_139 = t_133 * m_138
                   and i2_140 = (Pervasives.fst i_136) * m_138 in
                   for i_141 = t_134 to m_138 - 1 do
                     let t_142 = a_137.(i1_139 + i_141) in
                     a_137.(i1_139 + i_141) <- a_137.(i2_140 + i_141);
                     a_137.(i2_140 + i_141) <- t_142
                   done);
                  t_128 := (- (! t_128)));
               Some (Pervasives.snd i_136))
          | None  -> None) in
       (match t_146 with
        | Some i_147 ->
            ((for j_148 = t_133 + 1 to t_126 - 1 do
                (let t_149 =
                   (t_124.Domains_common.arr).((j_148 *
                                                  t_124.Domains_common.m)
                                                 + t_134) in
                 if t_149 <> 0.
                 then
                   (for j_150 = t_134 + 1 to t_125 - 1 do
                      (t_124.Domains_common.arr).((j_148 *
                                                     t_124.Domains_common.m)
                                                    + j_150)
                      <-
                      ((t_124.Domains_common.arr).((j_148 *
                                                      t_124.Domains_common.m)
                                                     + j_150))
                        -.
                        ((t_149 /. i_147) *.
                           ((t_124.Domains_common.arr).((t_133 *
                                                           t_124.Domains_common.m)
                                                          + j_150)))
                    done;
                    (t_124.Domains_common.arr).((j_148 *
                                                   t_124.Domains_common.m)
                                                  + t_134)
                    <- 0.))
              done;
              t_127 := ((! t_127) *. i_147));
             t_122 := ((! t_122) + 1))
        | None  -> t_128 := 0);
       t_123 := ((! t_123) + 1))
      done;
    (t_124,
      (if (! t_128) = 0
       then 0.
       else if (! t_128) = 1 then ! t_127 else -. (! t_127)))>.
  
val resFV3 : (GVC_F.contr -> GenFV3.O.res) code = .<
  fun a_151  ->
    let t_152 = Pervasives.ref 0 in
    let t_153 = Pervasives.ref 0 in
    let t_154 =
      { a_151 with Domains_common.arr = (Array.copy a_151.Domains_common.arr)
      } in
    let t_155 = a_151.Domains_common.m in
    let t_156 = a_151.Domains_common.n in
    while ((! t_153) < t_155) && ((! t_152) < t_156) do
      (let t_161 = ! t_152 in
       let t_162 = ! t_153 in
       let t_163 = Pervasives.ref None in
       let t_174 =
         for j_171 = t_161 to t_156 - 1 do
           (let t_172 =
              (t_154.Domains_common.arr).((j_171 * t_154.Domains_common.m) +
                                            t_162) in
            if t_172 <> 0.
            then
              match ! t_163 with
              | Some i_173 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_173)) <
                       (Pervasives.abs_float t_172)
                   then t_163 := (Some (j_171, t_172)))
              | None  -> t_163 := (Some (j_171, t_172)))
         done;
         (match ! t_163 with
          | Some i_164 ->
              (if (Pervasives.fst i_164) <> t_161
               then
                 (let a_165 = t_154.Domains_common.arr
                  and m_166 = t_154.Domains_common.m in
                  let i1_167 = t_161 * m_166
                  and i2_168 = (Pervasives.fst i_164) * m_166 in
                  for i_169 = t_162 to m_166 - 1 do
                    let t_170 = a_165.(i1_167 + i_169) in
                    a_165.(i1_167 + i_169) <- a_165.(i2_168 + i_169);
                    a_165.(i2_168 + i_169) <- t_170
                  done);
               Some (Pervasives.snd i_164))
          | None  -> None) in
       (match t_174 with
        | Some i_175 ->
            ((for j_176 = t_161 + 1 to t_156 - 1 do
                (let t_177 =
                   (t_154.Domains_common.arr).((j_176 *
                                                  t_154.Domains_common.m)
                                                 + t_162) in
                 if t_177 <> 0.
                 then
                   (for j_178 = t_162 + 1 to t_155 - 1 do
                      (t_154.Domains_common.arr).((j_176 *
                                                     t_154.Domains_common.m)
                                                    + j_178)
                      <-
                      ((t_154.Domains_common.arr).((j_176 *
                                                      t_154.Domains_common.m)
                                                     + j_178))
                        -.
                        ((t_177 /. i_175) *.
                           ((t_154.Domains_common.arr).((t_161 *
                                                           t_154.Domains_common.m)
                                                          + j_178)))
                    done;
                    (t_154.Domains_common.arr).((j_176 *
                                                   t_154.Domains_common.m)
                                                  + t_162)
                    <- 0.))
              done;
              ());
             t_152 := ((! t_152) + 1))
        | None  -> ());
       t_153 := ((! t_153) + 1))
      done;
    (t_154, (! t_152))>.
  
val resFV4 : (GVC_F.contr -> GenFV4.O.res) code = .<
  fun a_179  ->
    let t_180 = Pervasives.ref 0 in
    let t_181 = Pervasives.ref 0 in
    let t_182 =
      { a_179 with Domains_common.arr = (Array.copy a_179.Domains_common.arr)
      } in
    let t_183 = a_179.Domains_common.m in
    let t_184 = a_179.Domains_common.n in
    let t_185 = Pervasives.ref 1. in
    let t_186 = Pervasives.ref 1 in
    while ((! t_181) < t_183) && ((! t_180) < t_184) do
      (let t_191 = ! t_180 in
       let t_192 = ! t_181 in
       let t_193 = Pervasives.ref None in
       let t_204 =
         for j_201 = t_191 to t_184 - 1 do
           (let t_202 =
              (t_182.Domains_common.arr).((j_201 * t_182.Domains_common.m) +
                                            t_192) in
            if t_202 <> 0.
            then
              match ! t_193 with
              | Some i_203 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_203)) <
                       (Pervasives.abs_float t_202)
                   then t_193 := (Some (j_201, t_202)))
              | None  -> t_193 := (Some (j_201, t_202)))
         done;
         (match ! t_193 with
          | Some i_194 ->
              (if (Pervasives.fst i_194) <> t_191
               then
                 ((let a_195 = t_182.Domains_common.arr
                   and m_196 = t_182.Domains_common.m in
                   let i1_197 = t_191 * m_196
                   and i2_198 = (Pervasives.fst i_194) * m_196 in
                   for i_199 = t_192 to m_196 - 1 do
                     let t_200 = a_195.(i1_197 + i_199) in
                     a_195.(i1_197 + i_199) <- a_195.(i2_198 + i_199);
                     a_195.(i2_198 + i_199) <- t_200
                   done);
                  t_186 := (- (! t_186)));
               Some (Pervasives.snd i_194))
          | None  -> None) in
       (match t_204 with
        | Some i_205 ->
            ((for j_206 = t_191 + 1 to t_184 - 1 do
                (let t_207 =
                   (t_182.Domains_common.arr).((j_206 *
                                                  t_182.Domains_common.m)
                                                 + t_192) in
                 if t_207 <> 0.
                 then
                   (for j_208 = t_192 + 1 to t_183 - 1 do
                      (t_182.Domains_common.arr).((j_206 *
                                                     t_182.Domains_common.m)
                                                    + j_208)
                      <-
                      ((t_182.Domains_common.arr).((j_206 *
                                                      t_182.Domains_common.m)
                                                     + j_208))
                        -.
                        ((t_207 /. i_205) *.
                           ((t_182.Domains_common.arr).((t_191 *
                                                           t_182.Domains_common.m)
                                                          + j_208)))
                    done;
                    (t_182.Domains_common.arr).((j_206 *
                                                   t_182.Domains_common.m)
                                                  + t_192)
                    <- 0.))
              done;
              t_185 := ((! t_185) *. i_205));
             t_180 := ((! t_180) + 1))
        | None  -> t_186 := 0);
       t_181 := ((! t_181) + 1))
      done;
    (t_182,
      (if (! t_186) = 0
       then 0.
       else if (! t_186) = 1 then ! t_185 else -. (! t_185)), (! t_180))>.
  
val resFV5 : (GVC_F.contr -> GenFV5.O.res) code = .<
  fun a_209  ->
    let t_210 = Pervasives.ref 0 in
    let t_211 = Pervasives.ref 0 in
    let t_212 =
      { a_209 with Domains_common.arr = (Array.copy a_209.Domains_common.arr)
      } in
    let t_213 = a_209.Domains_common.m in
    let t_214 = a_209.Domains_common.n in
    let t_215 = Pervasives.ref 1. in
    let t_216 = Pervasives.ref 1 in
    while ((! t_211) < t_213) && ((! t_210) < t_214) do
      (let t_221 = ! t_210 in
       let t_222 = ! t_211 in
       let t_223 = Pervasives.ref None in
       let t_242 =
         for j_238 = t_221 to t_214 - 1 do
           for j_239 = t_222 to t_213 - 1 do
             (let t_240 =
                (t_212.Domains_common.arr).((j_238 * t_212.Domains_common.m)
                                              + j_239) in
              if t_240 <> 0.
              then
                match ! t_223 with
                | Some i_241 ->
                    (if
                       (Pervasives.abs_float (Pervasives.snd i_241)) <
                         (Pervasives.abs_float t_240)
                     then t_223 := (Some ((j_238, j_239), t_240)))
                | None  -> t_223 := (Some ((j_238, j_239), t_240)))
           done
         done;
         (match ! t_223 with
          | Some i_224 ->
              (if (Pervasives.snd (Pervasives.fst i_224)) <> t_222
               then
                 ((let a_231 = t_212.Domains_common.arr
                   and nm_232 =
                     t_212.Domains_common.n * t_212.Domains_common.m
                   and m_233 = t_212.Domains_common.m in
                   let rec loop_234 i1_235 i2_236 =
                     if i2_236 < nm_232
                     then
                       let t_237 = a_231.(i1_235) in
                       (a_231.(i1_235) <- a_231.(i2_236);
                        a_231.(i2_236) <- t_237;
                        loop_234 (i1_235 + m_233) (i2_236 + m_233)) in
                   loop_234 t_222 (Pervasives.snd (Pervasives.fst i_224)));
                  t_216 := (- (! t_216)));
               if (Pervasives.fst (Pervasives.fst i_224)) <> t_221
               then
                 ((let a_225 = t_212.Domains_common.arr
                   and m_226 = t_212.Domains_common.m in
                   let i1_227 = t_221 * m_226
                   and i2_228 =
                     (Pervasives.snd (Pervasives.fst i_224)) * m_226 in
                   for i_229 = t_222 to m_226 - 1 do
                     let t_230 = a_225.(i1_227 + i_229) in
                     a_225.(i1_227 + i_229) <- a_225.(i2_228 + i_229);
                     a_225.(i2_228 + i_229) <- t_230
                   done);
                  t_216 := (- (! t_216)));
               Some (Pervasives.snd i_224))
          | None  -> None) in
       (match t_242 with
        | Some i_243 ->
            ((for j_244 = t_221 + 1 to t_214 - 1 do
                (let t_245 =
                   (t_212.Domains_common.arr).((j_244 *
                                                  t_212.Domains_common.m)
                                                 + t_222) in
                 if t_245 <> 0.
                 then
                   (for j_246 = t_222 + 1 to t_213 - 1 do
                      (t_212.Domains_common.arr).((j_244 *
                                                     t_212.Domains_common.m)
                                                    + j_246)
                      <-
                      ((t_212.Domains_common.arr).((j_244 *
                                                      t_212.Domains_common.m)
                                                     + j_246))
                        -.
                        ((t_245 /. i_243) *.
                           ((t_212.Domains_common.arr).((t_221 *
                                                           t_212.Domains_common.m)
                                                          + j_246)))
                    done;
                    (t_212.Domains_common.arr).((j_244 *
                                                   t_212.Domains_common.m)
                                                  + t_222)
                    <- 0.))
              done;
              t_215 := ((! t_215) *. i_243));
             t_210 := ((! t_210) + 1))
        | None  -> t_216 := 0);
       t_211 := ((! t_211) + 1))
      done;
    (t_212,
      (if (! t_216) = 0
       then 0.
       else if (! t_216) = 1 then ! t_215 else -. (! t_215)), (! t_210))>.
  
val resIA1 : (GAC_I.contr -> GenIA1.O.res) code = .<
  fun a_247  ->
    let t_248 = Pervasives.ref 0 in
    let t_249 = Pervasives.ref 0 in
    let t_251 = Array.map (fun x_250  -> Array.copy x_250) (Array.copy a_247) in
    let t_252 = Array.length (a_247.(0)) in
    let t_253 = Array.length a_247 in
    let t_254 = Pervasives.ref 1 in
    let t_255 = Pervasives.ref 1 in
    while ((! t_249) < t_252) && ((! t_248) < t_253) do
      (let t_258 = ! t_248 in
       let t_259 = ! t_249 in
       let t_260 = Pervasives.ref None in
       let t_266 =
         for j_263 = t_258 to t_253 - 1 do
           (let t_264 = (t_251.(j_263)).(t_259) in
            if t_264 <> 0
            then
              match ! t_260 with
              | Some i_265 ->
                  (if
                     (Pervasives.abs (Pervasives.snd i_265)) >
                       (Pervasives.abs t_264)
                   then t_260 := (Some (j_263, t_264)))
              | None  -> t_260 := (Some (j_263, t_264)))
         done;
         (match ! t_260 with
          | Some i_261 ->
              (if (Pervasives.fst i_261) <> t_258
               then
                 ((let t_262 = t_251.(t_258) in
                   t_251.(t_258) <- t_251.(Pervasives.fst i_261);
                   t_251.(Pervasives.fst i_261) <- t_262);
                  t_255 := (- (! t_255)));
               Some (Pervasives.snd i_261))
          | None  -> None) in
       (match t_266 with
        | Some i_267 ->
            ((for j_268 = t_258 + 1 to t_253 - 1 do
                (let t_269 = (t_251.(j_268)).(t_259) in
                 if t_269 <> 0
                 then
                   (for j_270 = t_259 + 1 to t_252 - 1 do
                      (t_251.(j_268)).(j_270) <-
                      ((((t_251.(j_268)).(j_270)) * i_267) -
                         (((t_251.(t_258)).(j_270)) * t_269))
                        / (! t_254)
                    done;
                    (t_251.(j_268)).(t_259) <- 0))
              done;
              t_254 := i_267);
             t_248 := ((! t_248) + 1))
        | None  -> t_255 := 0);
       t_249 := ((! t_249) + 1))
      done;
    t_251>.
  
val resIA2 : (GAC_I.contr -> GenIA2.O.res) code = .<
  fun a_271  ->
    let t_272 = Pervasives.ref 0 in
    let t_273 = Pervasives.ref 0 in
    let t_275 = Array.map (fun x_274  -> Array.copy x_274) (Array.copy a_271) in
    let t_276 = Array.length (a_271.(0)) in
    let t_277 = Array.length a_271 in
    let t_278 = Pervasives.ref 1 in
    let t_279 = Pervasives.ref 1 in
    while ((! t_273) < t_276) && ((! t_272) < t_277) do
      (let t_282 = ! t_272 in
       let t_283 = ! t_273 in
       let t_284 = Pervasives.ref None in
       let t_290 =
         for j_287 = t_282 to t_277 - 1 do
           (let t_288 = (t_275.(j_287)).(t_283) in
            if t_288 <> 0
            then
              match ! t_284 with
              | Some i_289 ->
                  (if
                     (Pervasives.abs (Pervasives.snd i_289)) >
                       (Pervasives.abs t_288)
                   then t_284 := (Some (j_287, t_288)))
              | None  -> t_284 := (Some (j_287, t_288)))
         done;
         (match ! t_284 with
          | Some i_285 ->
              (if (Pervasives.fst i_285) <> t_282
               then
                 ((let t_286 = t_275.(t_282) in
                   t_275.(t_282) <- t_275.(Pervasives.fst i_285);
                   t_275.(Pervasives.fst i_285) <- t_286);
                  t_279 := (- (! t_279)));
               Some (Pervasives.snd i_285))
          | None  -> None) in
       (match t_290 with
        | Some i_291 ->
            ((for j_292 = t_282 + 1 to t_277 - 1 do
                (let t_293 = (t_275.(j_292)).(t_283) in
                 if t_293 <> 0
                 then
                   (for j_294 = t_283 + 1 to t_276 - 1 do
                      (t_275.(j_292)).(j_294) <-
                      ((((t_275.(j_292)).(j_294)) * i_291) -
                         (((t_275.(t_282)).(j_294)) * t_293))
                        / (! t_278)
                    done;
                    (t_275.(j_292)).(t_283) <- 0))
              done;
              t_278 := i_291);
             t_272 := ((! t_272) + 1))
        | None  -> t_279 := 0);
       t_273 := ((! t_273) + 1))
      done;
    (t_275,
      (if (! t_279) = 0
       then 0
       else if (! t_279) = 1 then ! t_278 else - (! t_278)))>.
  
val resIA3 : (GAC_I.contr -> GenIA3.O.res) code = .<
  fun a_295  ->
    let t_296 = Pervasives.ref 0 in
    let t_297 = Pervasives.ref 0 in
    let t_299 = Array.map (fun x_298  -> Array.copy x_298) (Array.copy a_295) in
    let t_300 = Array.length (a_295.(0)) in
    let t_301 = Array.length a_295 in
    let t_302 = Pervasives.ref 1 in
    let t_303 = Pervasives.ref 1 in
    while ((! t_297) < t_300) && ((! t_296) < t_301) do
      (let t_306 = ! t_296 in
       let t_307 = ! t_297 in
       let t_308 = Pervasives.ref None in
       let t_314 =
         for j_311 = t_306 to t_301 - 1 do
           (let t_312 = (t_299.(j_311)).(t_307) in
            if t_312 <> 0
            then
              match ! t_308 with
              | Some i_313 ->
                  (if
                     (Pervasives.abs (Pervasives.snd i_313)) >
                       (Pervasives.abs t_312)
                   then t_308 := (Some (j_311, t_312)))
              | None  -> t_308 := (Some (j_311, t_312)))
         done;
         (match ! t_308 with
          | Some i_309 ->
              (if (Pervasives.fst i_309) <> t_306
               then
                 ((let t_310 = t_299.(t_306) in
                   t_299.(t_306) <- t_299.(Pervasives.fst i_309);
                   t_299.(Pervasives.fst i_309) <- t_310);
                  t_303 := (- (! t_303)));
               Some (Pervasives.snd i_309))
          | None  -> None) in
       (match t_314 with
        | Some i_315 ->
            ((for j_316 = t_306 + 1 to t_301 - 1 do
                (let t_317 = (t_299.(j_316)).(t_307) in
                 if t_317 <> 0
                 then
                   (for j_318 = t_307 + 1 to t_300 - 1 do
                      (t_299.(j_316)).(j_318) <-
                      ((((t_299.(j_316)).(j_318)) * i_315) -
                         (((t_299.(t_306)).(j_318)) * t_317))
                        / (! t_302)
                    done;
                    (t_299.(j_316)).(t_307) <- 0))
              done;
              t_302 := i_315);
             t_296 := ((! t_296) + 1))
        | None  -> t_303 := 0);
       t_297 := ((! t_297) + 1))
      done;
    (t_299, (! t_296))>.
  
val resIA4 : (GAC_I.contr -> GenIA4.O.res) code = .<
  fun a_319  ->
    let t_320 = Pervasives.ref 0 in
    let t_321 = Pervasives.ref 0 in
    let t_323 = Array.map (fun x_322  -> Array.copy x_322) (Array.copy a_319) in
    let t_324 = Array.length (a_319.(0)) in
    let t_325 = Array.length a_319 in
    let t_326 = Pervasives.ref 1 in
    let t_327 = Pervasives.ref 1 in
    while ((! t_321) < t_324) && ((! t_320) < t_325) do
      (let t_330 = ! t_320 in
       let t_331 = ! t_321 in
       let t_332 = Pervasives.ref None in
       let t_338 =
         for j_335 = t_330 to t_325 - 1 do
           (let t_336 = (t_323.(j_335)).(t_331) in
            if t_336 <> 0
            then
              match ! t_332 with
              | Some i_337 ->
                  (if
                     (Pervasives.abs (Pervasives.snd i_337)) >
                       (Pervasives.abs t_336)
                   then t_332 := (Some (j_335, t_336)))
              | None  -> t_332 := (Some (j_335, t_336)))
         done;
         (match ! t_332 with
          | Some i_333 ->
              (if (Pervasives.fst i_333) <> t_330
               then
                 ((let t_334 = t_323.(t_330) in
                   t_323.(t_330) <- t_323.(Pervasives.fst i_333);
                   t_323.(Pervasives.fst i_333) <- t_334);
                  t_327 := (- (! t_327)));
               Some (Pervasives.snd i_333))
          | None  -> None) in
       (match t_338 with
        | Some i_339 ->
            ((for j_340 = t_330 + 1 to t_325 - 1 do
                (let t_341 = (t_323.(j_340)).(t_331) in
                 if t_341 <> 0
                 then
                   (for j_342 = t_331 + 1 to t_324 - 1 do
                      (t_323.(j_340)).(j_342) <-
                      ((((t_323.(j_340)).(j_342)) * i_339) -
                         (((t_323.(t_330)).(j_342)) * t_341))
                        / (! t_326)
                    done;
                    (t_323.(j_340)).(t_331) <- 0))
              done;
              t_326 := i_339);
             t_320 := ((! t_320) + 1))
        | None  -> t_327 := 0);
       t_321 := ((! t_321) + 1))
      done;
    (t_323,
      (if (! t_327) = 0
       then 0
       else if (! t_327) = 1 then ! t_326 else - (! t_326)), (! t_320))>.
  
val resIV1 : (GVC_I.contr -> GenIV1.O.res) code = .<
  fun a_343  ->
    let t_344 = Pervasives.ref 0 in
    let t_345 = Pervasives.ref 0 in
    let t_346 =
      { a_343 with Domains_common.arr = (Array.copy a_343.Domains_common.arr)
      } in
    let t_347 = a_343.Domains_common.m in
    let t_348 = a_343.Domains_common.n in
    let t_349 = Pervasives.ref 1 in
    let t_350 = Pervasives.ref 1 in
    while ((! t_345) < t_347) && ((! t_344) < t_348) do
      (let t_355 = ! t_344 in
       let t_356 = ! t_345 in
       let t_357 = Pervasives.ref None in
       let t_368 =
         for j_365 = t_355 to t_348 - 1 do
           (let t_366 =
              (t_346.Domains_common.arr).((j_365 * t_346.Domains_common.m) +
                                            t_356) in
            if t_366 <> 0
            then
              match ! t_357 with
              | Some i_367 ->
                  (if
                     (Pervasives.abs (Pervasives.snd i_367)) >
                       (Pervasives.abs t_366)
                   then t_357 := (Some (j_365, t_366)))
              | None  -> t_357 := (Some (j_365, t_366)))
         done;
         (match ! t_357 with
          | Some i_358 ->
              (if (Pervasives.fst i_358) <> t_355
               then
                 ((let a_359 = t_346.Domains_common.arr
                   and m_360 = t_346.Domains_common.m in
                   let i1_361 = t_355 * m_360
                   and i2_362 = (Pervasives.fst i_358) * m_360 in
                   for i_363 = t_356 to m_360 - 1 do
                     let t_364 = a_359.(i1_361 + i_363) in
                     a_359.(i1_361 + i_363) <- a_359.(i2_362 + i_363);
                     a_359.(i2_362 + i_363) <- t_364
                   done);
                  t_350 := (- (! t_350)));
               Some (Pervasives.snd i_358))
          | None  -> None) in
       (match t_368 with
        | Some i_369 ->
            ((for j_370 = t_355 + 1 to t_348 - 1 do
                (let t_371 =
                   (t_346.Domains_common.arr).((j_370 *
                                                  t_346.Domains_common.m)
                                                 + t_356) in
                 if t_371 <> 0
                 then
                   (for j_372 = t_356 + 1 to t_347 - 1 do
                      (t_346.Domains_common.arr).((j_370 *
                                                     t_346.Domains_common.m)
                                                    + j_372)
                      <-
                      ((((t_346.Domains_common.arr).((j_370 *
                                                        t_346.Domains_common.m)
                                                       + j_372))
                          * i_369)
                         -
                         (((t_346.Domains_common.arr).((t_355 *
                                                          t_346.Domains_common.m)
                                                         + j_372))
                            * t_371))
                        / (! t_349)
                    done;
                    (t_346.Domains_common.arr).((j_370 *
                                                   t_346.Domains_common.m)
                                                  + t_356)
                    <- 0))
              done;
              t_349 := i_369);
             t_344 := ((! t_344) + 1))
        | None  -> t_350 := 0);
       t_345 := ((! t_345) + 1))
      done;
    t_346>.
  
val resIV2 : (GVC_I.contr -> GenIV2.O.res) code = .<
  fun a_373  ->
    let t_374 = Pervasives.ref 0 in
    let t_375 = Pervasives.ref 0 in
    let t_376 =
      { a_373 with Domains_common.arr = (Array.copy a_373.Domains_common.arr)
      } in
    let t_377 = a_373.Domains_common.m in
    let t_378 = a_373.Domains_common.n in
    let t_379 = Pervasives.ref 1 in
    let t_380 = Pervasives.ref 1 in
    while ((! t_375) < t_377) && ((! t_374) < t_378) do
      (let t_385 = ! t_374 in
       let t_386 = ! t_375 in
       let t_387 = Pervasives.ref None in
       let t_398 =
         for j_395 = t_385 to t_378 - 1 do
           (let t_396 =
              (t_376.Domains_common.arr).((j_395 * t_376.Domains_common.m) +
                                            t_386) in
            if t_396 <> 0
            then
              match ! t_387 with
              | Some i_397 ->
                  (if
                     (Pervasives.abs (Pervasives.snd i_397)) >
                       (Pervasives.abs t_396)
                   then t_387 := (Some (j_395, t_396)))
              | None  -> t_387 := (Some (j_395, t_396)))
         done;
         (match ! t_387 with
          | Some i_388 ->
              (if (Pervasives.fst i_388) <> t_385
               then
                 ((let a_389 = t_376.Domains_common.arr
                   and m_390 = t_376.Domains_common.m in
                   let i1_391 = t_385 * m_390
                   and i2_392 = (Pervasives.fst i_388) * m_390 in
                   for i_393 = t_386 to m_390 - 1 do
                     let t_394 = a_389.(i1_391 + i_393) in
                     a_389.(i1_391 + i_393) <- a_389.(i2_392 + i_393);
                     a_389.(i2_392 + i_393) <- t_394
                   done);
                  t_380 := (- (! t_380)));
               Some (Pervasives.snd i_388))
          | None  -> None) in
       (match t_398 with
        | Some i_399 ->
            ((for j_400 = t_385 + 1 to t_378 - 1 do
                (let t_401 =
                   (t_376.Domains_common.arr).((j_400 *
                                                  t_376.Domains_common.m)
                                                 + t_386) in
                 if t_401 <> 0
                 then
                   (for j_402 = t_386 + 1 to t_377 - 1 do
                      (t_376.Domains_common.arr).((j_400 *
                                                     t_376.Domains_common.m)
                                                    + j_402)
                      <-
                      ((((t_376.Domains_common.arr).((j_400 *
                                                        t_376.Domains_common.m)
                                                       + j_402))
                          * i_399)
                         -
                         (((t_376.Domains_common.arr).((t_385 *
                                                          t_376.Domains_common.m)
                                                         + j_402))
                            * t_401))
                        / (! t_379)
                    done;
                    (t_376.Domains_common.arr).((j_400 *
                                                   t_376.Domains_common.m)
                                                  + t_386)
                    <- 0))
              done;
              t_379 := i_399);
             t_374 := ((! t_374) + 1))
        | None  -> t_380 := 0);
       t_375 := ((! t_375) + 1))
      done;
    (t_376,
      (if (! t_380) = 0
       then 0
       else if (! t_380) = 1 then ! t_379 else - (! t_379)))>.
  
val resIV3 : (GVC_I.contr -> GenIV3.O.res) code = .<
  fun a_403  ->
    let t_404 = Pervasives.ref 0 in
    let t_405 = Pervasives.ref 0 in
    let t_406 =
      { a_403 with Domains_common.arr = (Array.copy a_403.Domains_common.arr)
      } in
    let t_407 = a_403.Domains_common.m in
    let t_408 = a_403.Domains_common.n in
    let t_409 = Pervasives.ref 1 in
    let t_410 = Pervasives.ref 1 in
    while ((! t_405) < t_407) && ((! t_404) < t_408) do
      (let t_415 = ! t_404 in
       let t_416 = ! t_405 in
       let t_417 = Pervasives.ref None in
       let t_428 =
         for j_425 = t_415 to t_408 - 1 do
           (let t_426 =
              (t_406.Domains_common.arr).((j_425 * t_406.Domains_common.m) +
                                            t_416) in
            if t_426 <> 0
            then
              match ! t_417 with
              | Some i_427 ->
                  (if
                     (Pervasives.abs (Pervasives.snd i_427)) >
                       (Pervasives.abs t_426)
                   then t_417 := (Some (j_425, t_426)))
              | None  -> t_417 := (Some (j_425, t_426)))
         done;
         (match ! t_417 with
          | Some i_418 ->
              (if (Pervasives.fst i_418) <> t_415
               then
                 ((let a_419 = t_406.Domains_common.arr
                   and m_420 = t_406.Domains_common.m in
                   let i1_421 = t_415 * m_420
                   and i2_422 = (Pervasives.fst i_418) * m_420 in
                   for i_423 = t_416 to m_420 - 1 do
                     let t_424 = a_419.(i1_421 + i_423) in
                     a_419.(i1_421 + i_423) <- a_419.(i2_422 + i_423);
                     a_419.(i2_422 + i_423) <- t_424
                   done);
                  t_410 := (- (! t_410)));
               Some (Pervasives.snd i_418))
          | None  -> None) in
       (match t_428 with
        | Some i_429 ->
            ((for j_430 = t_415 + 1 to t_408 - 1 do
                (let t_431 =
                   (t_406.Domains_common.arr).((j_430 *
                                                  t_406.Domains_common.m)
                                                 + t_416) in
                 if t_431 <> 0
                 then
                   (for j_432 = t_416 + 1 to t_407 - 1 do
                      (t_406.Domains_common.arr).((j_430 *
                                                     t_406.Domains_common.m)
                                                    + j_432)
                      <-
                      ((((t_406.Domains_common.arr).((j_430 *
                                                        t_406.Domains_common.m)
                                                       + j_432))
                          * i_429)
                         -
                         (((t_406.Domains_common.arr).((t_415 *
                                                          t_406.Domains_common.m)
                                                         + j_432))
                            * t_431))
                        / (! t_409)
                    done;
                    (t_406.Domains_common.arr).((j_430 *
                                                   t_406.Domains_common.m)
                                                  + t_416)
                    <- 0))
              done;
              t_409 := i_429);
             t_404 := ((! t_404) + 1))
        | None  -> t_410 := 0);
       t_405 := ((! t_405) + 1))
      done;
    (t_406, (! t_404))>.
  
val resIV4 : (GVC_I.contr -> GenIV4.O.res) code = .<
  fun a_433  ->
    let t_434 = Pervasives.ref 0 in
    let t_435 = Pervasives.ref 0 in
    let t_436 =
      { a_433 with Domains_common.arr = (Array.copy a_433.Domains_common.arr)
      } in
    let t_437 = a_433.Domains_common.m in
    let t_438 = a_433.Domains_common.n in
    let t_439 = Pervasives.ref 1 in
    let t_440 = Pervasives.ref 1 in
    while ((! t_435) < t_437) && ((! t_434) < t_438) do
      (let t_445 = ! t_434 in
       let t_446 = ! t_435 in
       let t_447 = Pervasives.ref None in
       let t_458 =
         for j_455 = t_445 to t_438 - 1 do
           (let t_456 =
              (t_436.Domains_common.arr).((j_455 * t_436.Domains_common.m) +
                                            t_446) in
            if t_456 <> 0
            then
              match ! t_447 with
              | Some i_457 ->
                  (if
                     (Pervasives.abs (Pervasives.snd i_457)) >
                       (Pervasives.abs t_456)
                   then t_447 := (Some (j_455, t_456)))
              | None  -> t_447 := (Some (j_455, t_456)))
         done;
         (match ! t_447 with
          | Some i_448 ->
              (if (Pervasives.fst i_448) <> t_445
               then
                 ((let a_449 = t_436.Domains_common.arr
                   and m_450 = t_436.Domains_common.m in
                   let i1_451 = t_445 * m_450
                   and i2_452 = (Pervasives.fst i_448) * m_450 in
                   for i_453 = t_446 to m_450 - 1 do
                     let t_454 = a_449.(i1_451 + i_453) in
                     a_449.(i1_451 + i_453) <- a_449.(i2_452 + i_453);
                     a_449.(i2_452 + i_453) <- t_454
                   done);
                  t_440 := (- (! t_440)));
               Some (Pervasives.snd i_448))
          | None  -> None) in
       (match t_458 with
        | Some i_459 ->
            ((for j_460 = t_445 + 1 to t_438 - 1 do
                (let t_461 =
                   (t_436.Domains_common.arr).((j_460 *
                                                  t_436.Domains_common.m)
                                                 + t_446) in
                 if t_461 <> 0
                 then
                   (for j_462 = t_446 + 1 to t_437 - 1 do
                      (t_436.Domains_common.arr).((j_460 *
                                                     t_436.Domains_common.m)
                                                    + j_462)
                      <-
                      ((((t_436.Domains_common.arr).((j_460 *
                                                        t_436.Domains_common.m)
                                                       + j_462))
                          * i_459)
                         -
                         (((t_436.Domains_common.arr).((t_445 *
                                                          t_436.Domains_common.m)
                                                         + j_462))
                            * t_461))
                        / (! t_439)
                    done;
                    (t_436.Domains_common.arr).((j_460 *
                                                   t_436.Domains_common.m)
                                                  + t_446)
                    <- 0))
              done;
              t_439 := i_459);
             t_434 := ((! t_434) + 1))
        | None  -> t_440 := 0);
       t_435 := ((! t_435) + 1))
      done;
    (t_436,
      (if (! t_440) = 0
       then 0
       else if (! t_440) = 1 then ! t_439 else - (! t_439)), (! t_434))>.
  
val resIV5 : (GVC_I.contr -> GenIV5.O.res) code = .<
  fun a_463  ->
    let t_464 = Pervasives.ref 0 in
    let t_465 = Pervasives.ref 0 in
    let t_466 =
      { a_463 with Domains_common.arr = (Array.copy a_463.Domains_common.arr)
      } in
    let t_467 = a_463.Domains_common.m in
    let t_468 = a_463.Domains_common.n in
    let t_469 = Pervasives.ref 1 in
    let t_470 = Pervasives.ref 1 in
    while ((! t_465) < t_467) && ((! t_464) < t_468) do
      (let t_475 = ! t_464 in
       let t_476 = ! t_465 in
       let t_477 = Pervasives.ref None in
       let t_496 =
         for j_492 = t_475 to t_468 - 1 do
           for j_493 = t_476 to t_467 - 1 do
             (let t_494 =
                (t_466.Domains_common.arr).((j_492 * t_466.Domains_common.m)
                                              + j_493) in
              if t_494 <> 0
              then
                match ! t_477 with
                | Some i_495 ->
                    (if
                       (Pervasives.abs (Pervasives.snd i_495)) >
                         (Pervasives.abs t_494)
                     then t_477 := (Some ((j_492, j_493), t_494)))
                | None  -> t_477 := (Some ((j_492, j_493), t_494)))
           done
         done;
         (match ! t_477 with
          | Some i_478 ->
              (if (Pervasives.snd (Pervasives.fst i_478)) <> t_476
               then
                 ((let a_485 = t_466.Domains_common.arr
                   and nm_486 =
                     t_466.Domains_common.n * t_466.Domains_common.m
                   and m_487 = t_466.Domains_common.m in
                   let rec loop_488 i1_489 i2_490 =
                     if i2_490 < nm_486
                     then
                       let t_491 = a_485.(i1_489) in
                       (a_485.(i1_489) <- a_485.(i2_490);
                        a_485.(i2_490) <- t_491;
                        loop_488 (i1_489 + m_487) (i2_490 + m_487)) in
                   loop_488 t_476 (Pervasives.snd (Pervasives.fst i_478)));
                  t_470 := (- (! t_470)));
               if (Pervasives.fst (Pervasives.fst i_478)) <> t_475
               then
                 ((let a_479 = t_466.Domains_common.arr
                   and m_480 = t_466.Domains_common.m in
                   let i1_481 = t_475 * m_480
                   and i2_482 =
                     (Pervasives.snd (Pervasives.fst i_478)) * m_480 in
                   for i_483 = t_476 to m_480 - 1 do
                     let t_484 = a_479.(i1_481 + i_483) in
                     a_479.(i1_481 + i_483) <- a_479.(i2_482 + i_483);
                     a_479.(i2_482 + i_483) <- t_484
                   done);
                  t_470 := (- (! t_470)));
               Some (Pervasives.snd i_478))
          | None  -> None) in
       (match t_496 with
        | Some i_497 ->
            ((for j_498 = t_475 + 1 to t_468 - 1 do
                (let t_499 =
                   (t_466.Domains_common.arr).((j_498 *
                                                  t_466.Domains_common.m)
                                                 + t_476) in
                 if t_499 <> 0
                 then
                   (for j_500 = t_476 + 1 to t_467 - 1 do
                      (t_466.Domains_common.arr).((j_498 *
                                                     t_466.Domains_common.m)
                                                    + j_500)
                      <-
                      ((((t_466.Domains_common.arr).((j_498 *
                                                        t_466.Domains_common.m)
                                                       + j_500))
                          * i_497)
                         -
                         (((t_466.Domains_common.arr).((t_475 *
                                                          t_466.Domains_common.m)
                                                         + j_500))
                            * t_499))
                        / (! t_469)
                    done;
                    (t_466.Domains_common.arr).((j_498 *
                                                   t_466.Domains_common.m)
                                                  + t_476)
                    <- 0))
              done;
              t_469 := i_497);
             t_464 := ((! t_464) + 1))
        | None  -> t_470 := 0);
       t_465 := ((! t_465) + 1))
      done;
    (t_466,
      (if (! t_470) = 0
       then 0
       else if (! t_470) = 1 then ! t_469 else - (! t_469)), (! t_464))>.
  
val resIV6 : (GVC_I.contr -> GenIV6.O.res) code = .<
  fun a_501  ->
    let t_502 = Pervasives.ref 0 in
    let t_503 = Pervasives.ref 0 in
    let t_504 =
      { a_501 with Domains_common.arr = (Array.copy a_501.Domains_common.arr)
      } in
    let t_505 = a_501.Domains_common.m in
    let t_506 = a_501.Domains_common.n in
    let t_507 = Pervasives.ref 1 in
    let t_508 = Pervasives.ref 1 in
    let t_509 = Pervasives.ref [] in
    while ((! t_503) < t_505) && ((! t_502) < t_506) do
      (let t_514 = ! t_502 in
       let t_515 = ! t_503 in
       let t_516 = Pervasives.ref None in
       let t_535 =
         for j_531 = t_514 to t_506 - 1 do
           for j_532 = t_515 to t_505 - 1 do
             (let t_533 =
                (t_504.Domains_common.arr).((j_531 * t_504.Domains_common.m)
                                              + j_532) in
              if t_533 <> 0
              then
                match ! t_516 with
                | Some i_534 ->
                    (if
                       (Pervasives.abs (Pervasives.snd i_534)) >
                         (Pervasives.abs t_533)
                     then t_516 := (Some ((j_531, j_532), t_533)))
                | None  -> t_516 := (Some ((j_531, j_532), t_533)))
           done
         done;
         (match ! t_516 with
          | Some i_517 ->
              (if (Pervasives.snd (Pervasives.fst i_517)) <> t_515
               then
                 (((let a_524 = t_504.Domains_common.arr
                    and nm_525 =
                      t_504.Domains_common.n * t_504.Domains_common.m
                    and m_526 = t_504.Domains_common.m in
                    let rec loop_527 i1_528 i2_529 =
                      if i2_529 < nm_525
                      then
                        let t_530 = a_524.(i1_528) in
                        (a_524.(i1_528) <- a_524.(i2_529);
                         a_524.(i2_529) <- t_530;
                         loop_527 (i1_528 + m_526) (i2_529 + m_526)) in
                    loop_527 t_515 (Pervasives.snd (Pervasives.fst i_517)));
                   t_508 := (- (! t_508)));
                  t_509 :=
                    ((Domains_common.ColSwap
                        ((Pervasives.snd (Pervasives.fst i_517)), t_514))
                    :: (! t_509)));
               if (Pervasives.fst (Pervasives.fst i_517)) <> t_514
               then
                 (((let a_518 = t_504.Domains_common.arr
                    and m_519 = t_504.Domains_common.m in
                    let i1_520 = t_514 * m_519
                    and i2_521 =
                      (Pervasives.snd (Pervasives.fst i_517)) * m_519 in
                    for i_522 = t_515 to m_519 - 1 do
                      let t_523 = a_518.(i1_520 + i_522) in
                      a_518.(i1_520 + i_522) <- a_518.(i2_521 + i_522);
                      a_518.(i2_521 + i_522) <- t_523
                    done);
                   t_508 := (- (! t_508)));
                  t_509 :=
                    ((Domains_common.RowSwap
                        ((Pervasives.fst (Pervasives.fst i_517)), t_514))
                    :: (! t_509)));
               Some (Pervasives.snd i_517))
          | None  -> None) in
       (match t_535 with
        | Some i_536 ->
            ((for j_537 = t_514 + 1 to t_506 - 1 do
                (let t_538 =
                   (t_504.Domains_common.arr).((j_537 *
                                                  t_504.Domains_common.m)
                                                 + t_515) in
                 if t_538 <> 0
                 then
                   (for j_539 = t_515 + 1 to t_505 - 1 do
                      (t_504.Domains_common.arr).((j_537 *
                                                     t_504.Domains_common.m)
                                                    + j_539)
                      <-
                      ((((t_504.Domains_common.arr).((j_537 *
                                                        t_504.Domains_common.m)
                                                       + j_539))
                          * i_536)
                         -
                         (((t_504.Domains_common.arr).((t_514 *
                                                          t_504.Domains_common.m)
                                                         + j_539))
                            * t_538))
                        / (! t_507)
                    done;
                    (t_504.Domains_common.arr).((j_537 *
                                                   t_504.Domains_common.m)
                                                  + t_515)
                    <- 0))
              done;
              t_507 := i_536);
             t_502 := ((! t_502) + 1))
        | None  -> t_508 := 0);
       t_503 := ((! t_503) + 1))
      done;
    (t_504,
      (if (! t_508) = 0
       then 0
       else if (! t_508) = 1 then ! t_507 else - (! t_507)), (! t_502),
      (! t_509))>.
  
val resFA11 : (GAC_F.contr -> GenFA11.O.res) code = .<
  fun a_540  ->
    let t_541 = Pervasives.ref 0 in
    let t_542 = Pervasives.ref 0 in
    let t_544 = Array.map (fun x_543  -> Array.copy x_543) (Array.copy a_540) in
    let t_545 = Array.length (a_540.(0)) in
    let t_546 = Array.length a_540 in
    while ((! t_542) < t_545) && ((! t_541) < t_546) do
      (let t_549 = ! t_541 in
       let t_550 = ! t_542 in
       let t_551 = Pervasives.ref None in
       let t_560 =
         for j_556 = t_549 to t_546 - 1 do
           for j_557 = t_550 to t_545 - 1 do
             (let t_558 = (t_544.(j_556)).(j_557) in
              if t_558 <> 0.
              then
                match ! t_551 with
                | Some i_559 ->
                    (if
                       (Pervasives.abs_float (Pervasives.snd i_559)) <
                         (Pervasives.abs_float t_558)
                     then t_551 := (Some ((j_556, j_557), t_558)))
                | None  -> t_551 := (Some ((j_556, j_557), t_558)))
           done
         done;
         (match ! t_551 with
          | Some i_552 ->
              (if (Pervasives.snd (Pervasives.fst i_552)) <> t_550
               then
                 for r_554 = 0 to (Array.length t_544) - 1 do
                   (let t_555 = (t_544.(r_554)).(t_550) in
                    (t_544.(r_554)).(t_550) <-
                    (t_544.(r_554)).(Pervasives.snd (Pervasives.fst i_552));
                    (t_544.(r_554)).(Pervasives.snd (Pervasives.fst i_552))
                    <- t_555)
                 done;
               if (Pervasives.fst (Pervasives.fst i_552)) <> t_549
               then
                 (let t_553 = t_544.(t_549) in
                  t_544.(t_549) <-
                  t_544.(Pervasives.snd (Pervasives.fst i_552));
                  t_544.(Pervasives.snd (Pervasives.fst i_552)) <- t_553);
               Some (Pervasives.snd i_552))
          | None  -> None) in
       (match t_560 with
        | Some i_561 ->
            ((for j_562 = t_549 + 1 to t_546 - 1 do
                (let t_563 = (t_544.(j_562)).(t_550) in
                 if t_563 <> 0.
                 then
                   (for j_564 = t_550 + 1 to t_545 - 1 do
                      (t_544.(j_562)).(j_564) <-
                      ((t_544.(j_562)).(j_564)) -.
                        ((t_563 /. i_561) *. ((t_544.(t_549)).(j_564)))
                    done;
                    (t_544.(j_562)).(t_550) <- 0.))
              done;
              ());
             t_541 := ((! t_541) + 1))
        | None  -> ());
       t_542 := ((! t_542) + 1))
      done;
    t_544>.
  
val resFA12 : (GAC_F.contr -> GenFA12.O.res) code = .<
  fun a_565  ->
    let t_566 = Pervasives.ref 0 in
    let t_567 = Pervasives.ref 0 in
    let t_569 = Array.map (fun x_568  -> Array.copy x_568) (Array.copy a_565) in
    let t_570 = Array.length (a_565.(0)) in
    let t_571 = Array.length a_565 in
    let t_572 = Pervasives.ref 1. in
    let t_573 = Pervasives.ref 1 in
    while ((! t_567) < t_570) && ((! t_566) < t_571) do
      (let t_576 = ! t_566 in
       let t_577 = ! t_567 in
       let t_578 = Pervasives.ref None in
       let t_587 =
         for j_583 = t_576 to t_571 - 1 do
           for j_584 = t_577 to t_570 - 1 do
             (let t_585 = (t_569.(j_583)).(j_584) in
              if t_585 <> 0.
              then
                match ! t_578 with
                | Some i_586 ->
                    (if
                       (Pervasives.abs_float (Pervasives.snd i_586)) <
                         (Pervasives.abs_float t_585)
                     then t_578 := (Some ((j_583, j_584), t_585)))
                | None  -> t_578 := (Some ((j_583, j_584), t_585)))
           done
         done;
         (match ! t_578 with
          | Some i_579 ->
              (if (Pervasives.snd (Pervasives.fst i_579)) <> t_577
               then
                 (for r_581 = 0 to (Array.length t_569) - 1 do
                    (let t_582 = (t_569.(r_581)).(t_577) in
                     (t_569.(r_581)).(t_577) <-
                     (t_569.(r_581)).(Pervasives.snd (Pervasives.fst i_579));
                     (t_569.(r_581)).(Pervasives.snd (Pervasives.fst i_579))
                     <- t_582)
                  done;
                  t_573 := (- (! t_573)));
               if (Pervasives.fst (Pervasives.fst i_579)) <> t_576
               then
                 ((let t_580 = t_569.(t_576) in
                   t_569.(t_576) <-
                   t_569.(Pervasives.snd (Pervasives.fst i_579));
                   t_569.(Pervasives.snd (Pervasives.fst i_579)) <- t_580);
                  t_573 := (- (! t_573)));
               Some (Pervasives.snd i_579))
          | None  -> None) in
       (match t_587 with
        | Some i_588 ->
            ((for j_589 = t_576 + 1 to t_571 - 1 do
                (let t_590 = (t_569.(j_589)).(t_577) in
                 if t_590 <> 0.
                 then
                   (for j_591 = t_577 + 1 to t_570 - 1 do
                      (t_569.(j_589)).(j_591) <-
                      ((t_569.(j_589)).(j_591)) -.
                        ((t_590 /. i_588) *. ((t_569.(t_576)).(j_591)))
                    done;
                    (t_569.(j_589)).(t_577) <- 0.))
              done;
              t_572 := ((! t_572) *. i_588));
             t_566 := ((! t_566) + 1))
        | None  -> t_573 := 0);
       t_567 := ((! t_567) + 1))
      done;
    (t_569,
      (if (! t_573) = 0
       then 0.
       else if (! t_573) = 1 then ! t_572 else -. (! t_572)))>.
  
val resFA13 : (GAC_F.contr -> GenFA13.O.res) code = .<
  fun a_592  ->
    let t_593 = Pervasives.ref 0 in
    let t_594 = Pervasives.ref 0 in
    let t_596 = Array.map (fun x_595  -> Array.copy x_595) (Array.copy a_592) in
    let t_597 = Array.length (a_592.(0)) in
    let t_598 = Array.length a_592 in
    while ((! t_594) < t_597) && ((! t_593) < t_598) do
      (let t_601 = ! t_593 in
       let t_602 = ! t_594 in
       let t_603 = Pervasives.ref None in
       let t_612 =
         for j_608 = t_601 to t_598 - 1 do
           for j_609 = t_602 to t_597 - 1 do
             (let t_610 = (t_596.(j_608)).(j_609) in
              if t_610 <> 0.
              then
                match ! t_603 with
                | Some i_611 ->
                    (if
                       (Pervasives.abs_float (Pervasives.snd i_611)) <
                         (Pervasives.abs_float t_610)
                     then t_603 := (Some ((j_608, j_609), t_610)))
                | None  -> t_603 := (Some ((j_608, j_609), t_610)))
           done
         done;
         (match ! t_603 with
          | Some i_604 ->
              (if (Pervasives.snd (Pervasives.fst i_604)) <> t_602
               then
                 for r_606 = 0 to (Array.length t_596) - 1 do
                   (let t_607 = (t_596.(r_606)).(t_602) in
                    (t_596.(r_606)).(t_602) <-
                    (t_596.(r_606)).(Pervasives.snd (Pervasives.fst i_604));
                    (t_596.(r_606)).(Pervasives.snd (Pervasives.fst i_604))
                    <- t_607)
                 done;
               if (Pervasives.fst (Pervasives.fst i_604)) <> t_601
               then
                 (let t_605 = t_596.(t_601) in
                  t_596.(t_601) <-
                  t_596.(Pervasives.snd (Pervasives.fst i_604));
                  t_596.(Pervasives.snd (Pervasives.fst i_604)) <- t_605);
               Some (Pervasives.snd i_604))
          | None  -> None) in
       (match t_612 with
        | Some i_613 ->
            ((for j_614 = t_601 + 1 to t_598 - 1 do
                (let t_615 = (t_596.(j_614)).(t_602) in
                 if t_615 <> 0.
                 then
                   (for j_616 = t_602 + 1 to t_597 - 1 do
                      (t_596.(j_614)).(j_616) <-
                      ((t_596.(j_614)).(j_616)) -.
                        ((t_615 /. i_613) *. ((t_596.(t_601)).(j_616)))
                    done;
                    (t_596.(j_614)).(t_602) <- 0.))
              done;
              ());
             t_593 := ((! t_593) + 1))
        | None  -> ());
       t_594 := ((! t_594) + 1))
      done;
    (t_596, (! t_593))>.
  
val resFA14 : (GAC_F.contr -> GenFA14.O.res) code = .<
  fun a_617  ->
    let t_618 = Pervasives.ref 0 in
    let t_619 = Pervasives.ref 0 in
    let t_621 = Array.map (fun x_620  -> Array.copy x_620) (Array.copy a_617) in
    let t_622 = Array.length (a_617.(0)) in
    let t_623 = Array.length a_617 in
    let t_624 = Pervasives.ref 1. in
    let t_625 = Pervasives.ref 1 in
    while ((! t_619) < t_622) && ((! t_618) < t_623) do
      (let t_628 = ! t_618 in
       let t_629 = ! t_619 in
       let t_630 = Pervasives.ref None in
       let t_639 =
         for j_635 = t_628 to t_623 - 1 do
           for j_636 = t_629 to t_622 - 1 do
             (let t_637 = (t_621.(j_635)).(j_636) in
              if t_637 <> 0.
              then
                match ! t_630 with
                | Some i_638 ->
                    (if
                       (Pervasives.abs_float (Pervasives.snd i_638)) <
                         (Pervasives.abs_float t_637)
                     then t_630 := (Some ((j_635, j_636), t_637)))
                | None  -> t_630 := (Some ((j_635, j_636), t_637)))
           done
         done;
         (match ! t_630 with
          | Some i_631 ->
              (if (Pervasives.snd (Pervasives.fst i_631)) <> t_629
               then
                 (for r_633 = 0 to (Array.length t_621) - 1 do
                    (let t_634 = (t_621.(r_633)).(t_629) in
                     (t_621.(r_633)).(t_629) <-
                     (t_621.(r_633)).(Pervasives.snd (Pervasives.fst i_631));
                     (t_621.(r_633)).(Pervasives.snd (Pervasives.fst i_631))
                     <- t_634)
                  done;
                  t_625 := (- (! t_625)));
               if (Pervasives.fst (Pervasives.fst i_631)) <> t_628
               then
                 ((let t_632 = t_621.(t_628) in
                   t_621.(t_628) <-
                   t_621.(Pervasives.snd (Pervasives.fst i_631));
                   t_621.(Pervasives.snd (Pervasives.fst i_631)) <- t_632);
                  t_625 := (- (! t_625)));
               Some (Pervasives.snd i_631))
          | None  -> None) in
       (match t_639 with
        | Some i_640 ->
            ((for j_641 = t_628 + 1 to t_623 - 1 do
                (let t_642 = (t_621.(j_641)).(t_629) in
                 if t_642 <> 0.
                 then
                   (for j_643 = t_629 + 1 to t_622 - 1 do
                      (t_621.(j_641)).(j_643) <-
                      ((t_621.(j_641)).(j_643)) -.
                        ((t_642 /. i_640) *. ((t_621.(t_628)).(j_643)))
                    done;
                    (t_621.(j_641)).(t_629) <- 0.))
              done;
              t_624 := ((! t_624) *. i_640));
             t_618 := ((! t_618) + 1))
        | None  -> t_625 := 0);
       t_619 := ((! t_619) + 1))
      done;
    (t_621,
      (if (! t_625) = 0
       then 0.
       else if (! t_625) = 1 then ! t_624 else -. (! t_624)), (! t_618))>.
  
val resFA24 : (GAC_F.contr -> GenFA24.O.res) code = .<
  fun a_644  ->
    let t_645 = Pervasives.ref 0 in
    let t_646 = Pervasives.ref 0 in
    let t_648 = Array.map (fun x_647  -> Array.copy x_647) (Array.copy a_644) in
    let t_649 = Array.length (a_644.(0)) in
    let t_650 = Array.length a_644 in
    let t_651 = Pervasives.ref 1. in
    let t_652 = Pervasives.ref 1 in
    let t_653 = Pervasives.ref [] in
    while ((! t_646) < t_649) && ((! t_645) < t_650) do
      (let t_656 = ! t_645 in
       let t_657 = ! t_646 in
       let t_658 = Pervasives.ref None in
       let t_664 =
         for j_661 = t_656 to t_650 - 1 do
           (let t_662 = (t_648.(j_661)).(t_657) in
            if t_662 <> 0.
            then
              match ! t_658 with
              | Some i_663 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_663)) <
                       (Pervasives.abs_float t_662)
                   then t_658 := (Some (j_661, t_662)))
              | None  -> t_658 := (Some (j_661, t_662)))
         done;
         (match ! t_658 with
          | Some i_659 ->
              (if (Pervasives.fst i_659) <> t_656
               then
                 (((let t_660 = t_648.(t_656) in
                    t_648.(t_656) <- t_648.(Pervasives.fst i_659);
                    t_648.(Pervasives.fst i_659) <- t_660);
                   t_652 := (- (! t_652)));
                  t_653 :=
                    ((Domains_common.RowSwap ((Pervasives.fst i_659), t_656))
                    :: (! t_653)));
               Some (Pervasives.snd i_659))
          | None  -> None) in
       (match t_664 with
        | Some i_665 ->
            ((for j_666 = t_656 + 1 to t_650 - 1 do
                (let t_667 = (t_648.(j_666)).(t_657) in
                 if t_667 <> 0.
                 then
                   (for j_668 = t_657 + 1 to t_649 - 1 do
                      (t_648.(j_666)).(j_668) <-
                      ((t_648.(j_666)).(j_668)) -.
                        ((t_667 /. i_665) *. ((t_648.(t_656)).(j_668)))
                    done;
                    (t_648.(j_666)).(t_657) <- 0.))
              done;
              t_651 := ((! t_651) *. i_665));
             t_645 := ((! t_645) + 1))
        | None  -> t_652 := 0);
       t_646 := ((! t_646) + 1))
      done;
    (t_648,
      (if (! t_652) = 0
       then 0.
       else if (! t_652) = 1 then ! t_651 else -. (! t_651)), (! t_645),
      (! t_653))>.
  
val resFA25 : (GAC_F.contr -> GenFA25.O.res) code = .<
  fun a_669  ->
    let t_670 = Pervasives.ref 0 in
    let t_671 = Pervasives.ref 0 in
    let t_673 = Array.map (fun x_672  -> Array.copy x_672) (Array.copy a_669) in
    let t_674 = Array.length (a_669.(0)) in
    let t_675 = Array.length a_669 in
    let t_676 = Pervasives.ref 1. in
    let t_677 = Pervasives.ref 1 in
    let t_679 = Pervasives.ref (Array.init t_675 (fun i_678  -> i_678)) in
    while ((! t_671) < t_674) && ((! t_670) < t_675) do
      (let t_682 = ! t_670 in
       let t_683 = ! t_671 in
       let t_684 = Pervasives.ref None in
       let t_694 =
         for j_691 = t_682 to t_675 - 1 do
           (let t_692 = (t_673.(j_691)).(t_683) in
            if t_692 <> 0.
            then
              match ! t_684 with
              | Some i_693 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_693)) <
                       (Pervasives.abs_float t_692)
                   then t_684 := (Some (j_691, t_692)))
              | None  -> t_684 := (Some (j_691, t_692)))
         done;
         (match ! t_684 with
          | Some i_685 ->
              (if (Pervasives.fst i_685) <> t_682
               then
                 (((let t_686 = t_673.(t_682) in
                    t_673.(t_682) <- t_673.(Pervasives.fst i_685);
                    t_673.(Pervasives.fst i_685) <- t_686);
                   t_677 := (- (! t_677)));
                  t_679 :=
                    ((let (x_687,y_688) = ((Pervasives.fst i_685), t_682) in
                      let b_689 = ! t_679
                      and t_690 = (! t_679).(x_687) in
                      b_689.(x_687) <- b_689.(y_688);
                      b_689.(y_688) <- t_690;
                      b_689)));
               Some (Pervasives.snd i_685))
          | None  -> None) in
       (match t_694 with
        | Some i_695 ->
            ((for j_696 = t_682 + 1 to t_675 - 1 do
                (let t_697 = (t_673.(j_696)).(t_683) in
                 if t_697 <> 0.
                 then
                   (for j_698 = t_683 + 1 to t_674 - 1 do
                      (t_673.(j_696)).(j_698) <-
                      ((t_673.(j_696)).(j_698)) -.
                        ((t_697 /. i_695) *. ((t_673.(t_682)).(j_698)))
                    done;
                    (t_673.(j_696)).(t_683) <- 0.))
              done;
              t_676 := ((! t_676) *. i_695));
             t_670 := ((! t_670) + 1))
        | None  -> t_677 := 0);
       t_671 := ((! t_671) + 1))
      done;
    (t_673,
      (if (! t_677) = 0
       then 0.
       else if (! t_677) = 1 then ! t_676 else -. (! t_676)), (! t_670),
      (! t_679))>.
  
val resFA26 : (GAC_F.contr -> GenFA26.O.res) code = .<
  fun a_699  ->
    let t_700 = Pervasives.ref 0 in
    let t_701 = Pervasives.ref 0 in
    let t_703 = Array.map (fun x_702  -> Array.copy x_702) (Array.copy a_699) in
    let t_704 = Array.length (a_699.(0)) in
    let t_705 = Array.length a_699 in
    while ((! t_701) < t_704) && ((! t_700) < t_705) do
      (let t_708 = ! t_700 in
       let t_709 = ! t_701 in
       let t_710 = Pervasives.ref None in
       let t_716 =
         for j_713 = t_708 to t_705 - 1 do
           (let t_714 = (t_703.(j_713)).(t_709) in
            if t_714 <> 0.
            then
              match ! t_710 with
              | Some i_715 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_715)) <
                       (Pervasives.abs_float t_714)
                   then t_710 := (Some (j_713, t_714)))
              | None  -> t_710 := (Some (j_713, t_714)))
         done;
         (match ! t_710 with
          | Some i_711 ->
              (if (Pervasives.fst i_711) <> t_708
               then
                 (let t_712 = t_703.(t_708) in
                  t_703.(t_708) <- t_703.(Pervasives.fst i_711);
                  t_703.(Pervasives.fst i_711) <- t_712);
               Some (Pervasives.snd i_711))
          | None  -> None) in
       (match t_716 with
        | Some i_717 ->
            ((for j_718 = t_708 + 1 to t_705 - 1 do
                (let t_719 = (t_703.(j_718)).(t_709) in
                 if t_719 <> 0.
                 then
                   (for j_720 = t_709 + 1 to t_704 - 1 do
                      (t_703.(j_718)).(j_720) <-
                      ((t_703.(j_718)).(j_720)) -.
                        ((t_719 /. i_717) *. ((t_703.(t_708)).(j_720)))
                    done;
                    (t_703.(j_718)).(t_709) <- 0.))
              done;
              ());
             t_700 := ((! t_700) + 1))
        | None  -> ());
       t_701 := ((! t_701) + 1))
      done;
    t_703>.
  
val resRA1 : (GAC_R.contr -> GenRA1.O.res) code = .<
  fun a_721  ->
    let t_722 = Pervasives.ref 0 in
    let t_723 = Pervasives.ref 0 in
    let t_725 = Array.map (fun x_724  -> Array.copy x_724) (Array.copy a_721) in
    let t_726 = Array.length (a_721.(0)) in
    let t_727 = Array.length a_721 in
    while ((! t_723) < t_726) && ((! t_722) < t_727) do
      (let t_730 = ! t_722 in
       let t_731 = ! t_723 in
       let t_732 = Pervasives.ref None in
       let t_739 =
         (let t_735 = (t_725.(t_730)).(t_731) in
          if t_735 <> (* CSP zero *)
          then t_732 := (Some (t_730, t_735))
          else
            (let rec loop_736 j_737 =
               if j_737 < t_727
               then
                 let t_738 = (t_725.(j_737)).(t_731) in
                 (if t_738 = (* CSP zero *)
                  then loop_736 (j_737 + 1)
                  else t_732 := (Some (j_737, t_738))) in
             loop_736 (t_730 + 1)));
         (match ! t_732 with
          | Some i_733 ->
              (if (Pervasives.fst i_733) <> t_730
               then
                 (let t_734 = t_725.(t_730) in
                  t_725.(t_730) <- t_725.(Pervasives.fst i_733);
                  t_725.(Pervasives.fst i_733) <- t_734);
               Some (Pervasives.snd i_733))
          | None  -> None) in
       (match t_739 with
        | Some i_740 ->
            ((for j_741 = t_730 + 1 to t_727 - 1 do
                (let t_742 = (t_725.(j_741)).(t_731) in
                 if t_742 <> (* CSP zero *)
                 then
                   (for j_743 = t_731 + 1 to t_726 - 1 do
                      (t_725.(j_741)).(j_743) <-
                      Num.sub_num ((t_725.(j_741)).(j_743))
                        (Num.mult_num (Num.div_num t_742 i_740)
                           ((t_725.(t_730)).(j_743)))
                    done;
                    (t_725.(j_741)).(t_731) <- (* CSP zero *)))
              done;
              ());
             t_722 := ((! t_722) + 1))
        | None  -> ());
       t_723 := ((! t_723) + 1))
      done;
    t_725>.
  
val resRA2 : (GAC_R.contr -> GenRA2.O.res) code = .<
  fun a_744  ->
    let t_745 = Pervasives.ref 0 in
    let t_746 = Pervasives.ref 0 in
    let t_748 = Array.map (fun x_747  -> Array.copy x_747) (Array.copy a_744) in
    let t_749 = Array.length (a_744.(0)) in
    let t_750 = Array.length a_744 in
    let t_751 = Pervasives.ref (* CSP one *) in
    let t_752 = Pervasives.ref 1 in
    while ((! t_746) < t_749) && ((! t_745) < t_750) do
      (let t_755 = ! t_745 in
       let t_756 = ! t_746 in
       let t_757 = Pervasives.ref None in
       let t_764 =
         (let t_760 = (t_748.(t_755)).(t_756) in
          if t_760 <> (* CSP zero *)
          then t_757 := (Some (t_755, t_760))
          else
            (let rec loop_761 j_762 =
               if j_762 < t_750
               then
                 let t_763 = (t_748.(j_762)).(t_756) in
                 (if t_763 = (* CSP zero *)
                  then loop_761 (j_762 + 1)
                  else t_757 := (Some (j_762, t_763))) in
             loop_761 (t_755 + 1)));
         (match ! t_757 with
          | Some i_758 ->
              (if (Pervasives.fst i_758) <> t_755
               then
                 ((let t_759 = t_748.(t_755) in
                   t_748.(t_755) <- t_748.(Pervasives.fst i_758);
                   t_748.(Pervasives.fst i_758) <- t_759);
                  t_752 := (- (! t_752)));
               Some (Pervasives.snd i_758))
          | None  -> None) in
       (match t_764 with
        | Some i_765 ->
            ((for j_766 = t_755 + 1 to t_750 - 1 do
                (let t_767 = (t_748.(j_766)).(t_756) in
                 if t_767 <> (* CSP zero *)
                 then
                   (for j_768 = t_756 + 1 to t_749 - 1 do
                      (t_748.(j_766)).(j_768) <-
                      Num.sub_num ((t_748.(j_766)).(j_768))
                        (Num.mult_num (Num.div_num t_767 i_765)
                           ((t_748.(t_755)).(j_768)))
                    done;
                    (t_748.(j_766)).(t_756) <- (* CSP zero *)))
              done;
              t_751 := (Num.mult_num (! t_751) i_765));
             t_745 := ((! t_745) + 1))
        | None  -> t_752 := 0);
       t_746 := ((! t_746) + 1))
      done;
    (t_748,
      (if (! t_752) = 0
       then (* CSP zero *)
       else if (! t_752) = 1 then ! t_751 else Num.minus_num (! t_751)))>.
  
val resRA3 : (GAC_R.contr -> GenRA3.O.res) code = .<
  fun a_769  ->
    let t_770 = Pervasives.ref 0 in
    let t_771 = Pervasives.ref 0 in
    let t_773 = Array.map (fun x_772  -> Array.copy x_772) (Array.copy a_769) in
    let t_774 = Array.length (a_769.(0)) in
    let t_775 = Array.length a_769 in
    while ((! t_771) < t_774) && ((! t_770) < t_775) do
      (let t_778 = ! t_770 in
       let t_779 = ! t_771 in
       let t_780 = Pervasives.ref None in
       let t_787 =
         (let t_783 = (t_773.(t_778)).(t_779) in
          if t_783 <> (* CSP zero *)
          then t_780 := (Some (t_778, t_783))
          else
            (let rec loop_784 j_785 =
               if j_785 < t_775
               then
                 let t_786 = (t_773.(j_785)).(t_779) in
                 (if t_786 = (* CSP zero *)
                  then loop_784 (j_785 + 1)
                  else t_780 := (Some (j_785, t_786))) in
             loop_784 (t_778 + 1)));
         (match ! t_780 with
          | Some i_781 ->
              (if (Pervasives.fst i_781) <> t_778
               then
                 (let t_782 = t_773.(t_778) in
                  t_773.(t_778) <- t_773.(Pervasives.fst i_781);
                  t_773.(Pervasives.fst i_781) <- t_782);
               Some (Pervasives.snd i_781))
          | None  -> None) in
       (match t_787 with
        | Some i_788 ->
            ((for j_789 = t_778 + 1 to t_775 - 1 do
                (let t_790 = (t_773.(j_789)).(t_779) in
                 if t_790 <> (* CSP zero *)
                 then
                   (for j_791 = t_779 + 1 to t_774 - 1 do
                      (t_773.(j_789)).(j_791) <-
                      Num.sub_num ((t_773.(j_789)).(j_791))
                        (Num.mult_num (Num.div_num t_790 i_788)
                           ((t_773.(t_778)).(j_791)))
                    done;
                    (t_773.(j_789)).(t_779) <- (* CSP zero *)))
              done;
              ());
             t_770 := ((! t_770) + 1))
        | None  -> ());
       t_771 := ((! t_771) + 1))
      done;
    (t_773, (! t_770))>.
  
val resRA4 : (GAC_R.contr -> GenRA4.O.res) code = .<
  fun a_792  ->
    let t_793 = Pervasives.ref 0 in
    let t_794 = Pervasives.ref 0 in
    let t_796 = Array.map (fun x_795  -> Array.copy x_795) (Array.copy a_792) in
    let t_797 = Array.length (a_792.(0)) in
    let t_798 = Array.length a_792 in
    let t_799 = Pervasives.ref (* CSP one *) in
    let t_800 = Pervasives.ref 1 in
    while ((! t_794) < t_797) && ((! t_793) < t_798) do
      (let t_803 = ! t_793 in
       let t_804 = ! t_794 in
       let t_805 = Pervasives.ref None in
       let t_812 =
         (let t_808 = (t_796.(t_803)).(t_804) in
          if t_808 <> (* CSP zero *)
          then t_805 := (Some (t_803, t_808))
          else
            (let rec loop_809 j_810 =
               if j_810 < t_798
               then
                 let t_811 = (t_796.(j_810)).(t_804) in
                 (if t_811 = (* CSP zero *)
                  then loop_809 (j_810 + 1)
                  else t_805 := (Some (j_810, t_811))) in
             loop_809 (t_803 + 1)));
         (match ! t_805 with
          | Some i_806 ->
              (if (Pervasives.fst i_806) <> t_803
               then
                 ((let t_807 = t_796.(t_803) in
                   t_796.(t_803) <- t_796.(Pervasives.fst i_806);
                   t_796.(Pervasives.fst i_806) <- t_807);
                  t_800 := (- (! t_800)));
               Some (Pervasives.snd i_806))
          | None  -> None) in
       (match t_812 with
        | Some i_813 ->
            ((for j_814 = t_803 + 1 to t_798 - 1 do
                (let t_815 = (t_796.(j_814)).(t_804) in
                 if t_815 <> (* CSP zero *)
                 then
                   (for j_816 = t_804 + 1 to t_797 - 1 do
                      (t_796.(j_814)).(j_816) <-
                      Num.sub_num ((t_796.(j_814)).(j_816))
                        (Num.mult_num (Num.div_num t_815 i_813)
                           ((t_796.(t_803)).(j_816)))
                    done;
                    (t_796.(j_814)).(t_804) <- (* CSP zero *)))
              done;
              t_799 := (Num.mult_num (! t_799) i_813));
             t_793 := ((! t_793) + 1))
        | None  -> t_800 := 0);
       t_794 := ((! t_794) + 1))
      done;
    (t_796,
      (if (! t_800) = 0
       then (* CSP zero *)
       else if (! t_800) = 1 then ! t_799 else Num.minus_num (! t_799)),
      (! t_793))>.
  
val resFA5 : (GAC_F.contr * int -> GenFA5.O.res) code = .<
  fun a_817  ->
    let t_818 = Pervasives.ref 0 in
    let t_819 = Pervasives.ref 0 in
    let t_821 =
      Array.map (fun x_820  -> Array.copy x_820)
        (Array.copy (Pervasives.fst a_817)) in
    let t_822 = Array.length ((Pervasives.fst a_817).(0)) in
    let t_823 = Pervasives.snd a_817 in
    let t_824 = Array.length (Pervasives.fst a_817) in
    while ((! t_819) < t_822) && ((! t_818) < t_823) do
      (let t_827 = ! t_818 in
       let t_828 = ! t_819 in
       let t_829 = Pervasives.ref None in
       let t_835 =
         for j_832 = t_827 to t_824 - 1 do
           (let t_833 = (t_821.(j_832)).(t_828) in
            if t_833 <> 0.
            then
              match ! t_829 with
              | Some i_834 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_834)) <
                       (Pervasives.abs_float t_833)
                   then t_829 := (Some (j_832, t_833)))
              | None  -> t_829 := (Some (j_832, t_833)))
         done;
         (match ! t_829 with
          | Some i_830 ->
              (if (Pervasives.fst i_830) <> t_827
               then
                 (let t_831 = t_821.(t_827) in
                  t_821.(t_827) <- t_821.(Pervasives.fst i_830);
                  t_821.(Pervasives.fst i_830) <- t_831);
               Some (Pervasives.snd i_830))
          | None  -> None) in
       (match t_835 with
        | Some i_836 ->
            ((for j_837 = t_827 + 1 to t_824 - 1 do
                (let t_838 = (t_821.(j_837)).(t_828) in
                 if t_838 <> 0.
                 then
                   (for j_839 = t_828 + 1 to t_822 - 1 do
                      (t_821.(j_837)).(j_839) <-
                      ((t_821.(j_837)).(j_839)) -.
                        ((t_838 /. i_836) *. ((t_821.(t_827)).(j_839)))
                    done;
                    (t_821.(j_837)).(t_828) <- 0.))
              done;
              ());
             t_818 := ((! t_818) + 1))
        | None  -> ());
       t_819 := ((! t_819) + 1))
      done;
    t_821>.
  
val resFA6 : (GAC_F.contr * int -> GenFA6.O.res) code = .<
  fun a_840  ->
    let t_841 = Pervasives.ref 0 in
    let t_842 = Pervasives.ref 0 in
    let t_844 =
      Array.map (fun x_843  -> Array.copy x_843)
        (Array.copy (Pervasives.fst a_840)) in
    let t_845 = Array.length ((Pervasives.fst a_840).(0)) in
    let t_846 = Pervasives.snd a_840 in
    let t_847 = Array.length (Pervasives.fst a_840) in
    let t_848 = Pervasives.ref 1. in
    let t_849 = Pervasives.ref 1 in
    while ((! t_842) < t_845) && ((! t_841) < t_846) do
      (let t_852 = ! t_841 in
       let t_853 = ! t_842 in
       let t_854 = Pervasives.ref None in
       let t_860 =
         for j_857 = t_852 to t_847 - 1 do
           (let t_858 = (t_844.(j_857)).(t_853) in
            if t_858 <> 0.
            then
              match ! t_854 with
              | Some i_859 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_859)) <
                       (Pervasives.abs_float t_858)
                   then t_854 := (Some (j_857, t_858)))
              | None  -> t_854 := (Some (j_857, t_858)))
         done;
         (match ! t_854 with
          | Some i_855 ->
              (if (Pervasives.fst i_855) <> t_852
               then
                 ((let t_856 = t_844.(t_852) in
                   t_844.(t_852) <- t_844.(Pervasives.fst i_855);
                   t_844.(Pervasives.fst i_855) <- t_856);
                  t_849 := (- (! t_849)));
               Some (Pervasives.snd i_855))
          | None  -> None) in
       (match t_860 with
        | Some i_861 ->
            ((for j_862 = t_852 + 1 to t_847 - 1 do
                (let t_863 = (t_844.(j_862)).(t_853) in
                 if t_863 <> 0.
                 then
                   (for j_864 = t_853 + 1 to t_845 - 1 do
                      (t_844.(j_862)).(j_864) <-
                      ((t_844.(j_862)).(j_864)) -.
                        ((t_863 /. i_861) *. ((t_844.(t_852)).(j_864)))
                    done;
                    (t_844.(j_862)).(t_853) <- 0.))
              done;
              t_848 := ((! t_848) *. i_861));
             t_841 := ((! t_841) + 1))
        | None  -> t_849 := 0);
       t_842 := ((! t_842) + 1))
      done;
    (t_844,
      (if (! t_849) = 0
       then 0.
       else if (! t_849) = 1 then ! t_848 else -. (! t_848)))>.
  
val resFA7 : (GAC_F.contr * int -> GenFA7.O.res) code = .<
  fun a_865  ->
    let t_866 = Pervasives.ref 0 in
    let t_867 = Pervasives.ref 0 in
    let t_869 =
      Array.map (fun x_868  -> Array.copy x_868)
        (Array.copy (Pervasives.fst a_865)) in
    let t_870 = Array.length ((Pervasives.fst a_865).(0)) in
    let t_871 = Pervasives.snd a_865 in
    let t_872 = Array.length (Pervasives.fst a_865) in
    while ((! t_867) < t_870) && ((! t_866) < t_871) do
      (let t_875 = ! t_866 in
       let t_876 = ! t_867 in
       let t_877 = Pervasives.ref None in
       let t_883 =
         for j_880 = t_875 to t_872 - 1 do
           (let t_881 = (t_869.(j_880)).(t_876) in
            if t_881 <> 0.
            then
              match ! t_877 with
              | Some i_882 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_882)) <
                       (Pervasives.abs_float t_881)
                   then t_877 := (Some (j_880, t_881)))
              | None  -> t_877 := (Some (j_880, t_881)))
         done;
         (match ! t_877 with
          | Some i_878 ->
              (if (Pervasives.fst i_878) <> t_875
               then
                 (let t_879 = t_869.(t_875) in
                  t_869.(t_875) <- t_869.(Pervasives.fst i_878);
                  t_869.(Pervasives.fst i_878) <- t_879);
               Some (Pervasives.snd i_878))
          | None  -> None) in
       (match t_883 with
        | Some i_884 ->
            ((for j_885 = t_875 + 1 to t_872 - 1 do
                (let t_886 = (t_869.(j_885)).(t_876) in
                 if t_886 <> 0.
                 then
                   (for j_887 = t_876 + 1 to t_870 - 1 do
                      (t_869.(j_885)).(j_887) <-
                      ((t_869.(j_885)).(j_887)) -.
                        ((t_886 /. i_884) *. ((t_869.(t_875)).(j_887)))
                    done;
                    (t_869.(j_885)).(t_876) <- 0.))
              done;
              ());
             t_866 := ((! t_866) + 1))
        | None  -> ());
       t_867 := ((! t_867) + 1))
      done;
    (t_869, (! t_866))>.
  
val resFA8 : (GAC_F.contr * int -> GenFA8.O.res) code = .<
  fun a_888  ->
    let t_889 = Pervasives.ref 0 in
    let t_890 = Pervasives.ref 0 in
    let t_892 =
      Array.map (fun x_891  -> Array.copy x_891)
        (Array.copy (Pervasives.fst a_888)) in
    let t_893 = Array.length ((Pervasives.fst a_888).(0)) in
    let t_894 = Pervasives.snd a_888 in
    let t_895 = Array.length (Pervasives.fst a_888) in
    let t_896 = Pervasives.ref 1. in
    let t_897 = Pervasives.ref 1 in
    while ((! t_890) < t_893) && ((! t_889) < t_894) do
      (let t_900 = ! t_889 in
       let t_901 = ! t_890 in
       let t_902 = Pervasives.ref None in
       let t_908 =
         for j_905 = t_900 to t_895 - 1 do
           (let t_906 = (t_892.(j_905)).(t_901) in
            if t_906 <> 0.
            then
              match ! t_902 with
              | Some i_907 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_907)) <
                       (Pervasives.abs_float t_906)
                   then t_902 := (Some (j_905, t_906)))
              | None  -> t_902 := (Some (j_905, t_906)))
         done;
         (match ! t_902 with
          | Some i_903 ->
              (if (Pervasives.fst i_903) <> t_900
               then
                 ((let t_904 = t_892.(t_900) in
                   t_892.(t_900) <- t_892.(Pervasives.fst i_903);
                   t_892.(Pervasives.fst i_903) <- t_904);
                  t_897 := (- (! t_897)));
               Some (Pervasives.snd i_903))
          | None  -> None) in
       (match t_908 with
        | Some i_909 ->
            ((for j_910 = t_900 + 1 to t_895 - 1 do
                (let t_911 = (t_892.(j_910)).(t_901) in
                 if t_911 <> 0.
                 then
                   (for j_912 = t_901 + 1 to t_893 - 1 do
                      (t_892.(j_910)).(j_912) <-
                      ((t_892.(j_910)).(j_912)) -.
                        ((t_911 /. i_909) *. ((t_892.(t_900)).(j_912)))
                    done;
                    (t_892.(j_910)).(t_901) <- 0.))
              done;
              t_896 := ((! t_896) *. i_909));
             t_889 := ((! t_889) + 1))
        | None  -> t_897 := 0);
       t_890 := ((! t_890) + 1))
      done;
    (t_892,
      (if (! t_897) = 0
       then 0.
       else if (! t_897) = 1 then ! t_896 else -. (! t_896)), (! t_889))>.
  
val resFA9 : (GAC_F.contr -> GenFA9.O.res) code = .<
  fun a_913  ->
    let t_914 = Pervasives.ref 0 in
    let t_915 = Pervasives.ref 0 in
    let t_917 = Array.map (fun x_916  -> Array.copy x_916) (Array.copy a_913) in
    let t_918 = Array.length (a_913.(0)) in
    let t_919 = Array.length a_913 in
    let t_920 = Pervasives.ref [] in
    while ((! t_915) < t_918) && ((! t_914) < t_919) do
      (let t_921 = ! t_914 in
       let t_922 = ! t_915 in
       let t_923 = Pervasives.ref None in
       let t_929 =
         for j_926 = t_921 to t_919 - 1 do
           (let t_927 = (t_917.(j_926)).(t_922) in
            if t_927 <> 0.
            then
              match ! t_923 with
              | Some i_928 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_928)) <
                       (Pervasives.abs_float t_927)
                   then t_923 := (Some (j_926, t_927)))
              | None  -> t_923 := (Some (j_926, t_927)))
         done;
         (match ! t_923 with
          | Some i_924 ->
              (if (Pervasives.fst i_924) <> t_921
               then
                 ((let t_925 = t_917.(t_921) in
                   t_917.(t_921) <- t_917.(Pervasives.fst i_924);
                   t_917.(Pervasives.fst i_924) <- t_925);
                  t_920 :=
                    ((Domains_common.RowSwap ((Pervasives.fst i_924), t_921))
                    :: (! t_920)));
               Some (Pervasives.snd i_924))
          | None  -> None) in
       (match t_929 with
        | Some i_930 ->
            ((for j_931 = t_921 + 1 to t_919 - 1 do
                (let t_932 = (t_917.(j_931)).(t_922) in
                 if t_932 <> 0.
                 then
                   for j_933 = t_922 + 1 to t_918 - 1 do
                     (t_917.(j_931)).(j_933) <-
                     ((t_917.(j_931)).(j_933)) -.
                       ((t_932 /. i_930) *. ((t_917.(t_921)).(j_933)))
                   done)
              done;
              ());
             t_914 := ((! t_914) + 1))
        | None  -> ());
       t_915 := ((! t_915) + 1))
      done;
    (t_917, (! t_920))>.
  
val resFA31 : (GAC_F.contr -> GenFA31.O.res) code = .<
  fun a_934  ->
    let t_935 = Pervasives.ref 0 in
    let t_936 = Pervasives.ref 0 in
    let t_938 = Array.map (fun x_937  -> Array.copy x_937) (Array.copy a_934) in
    let t_939 = Array.length (a_934.(0)) in
    let t_940 = Array.length a_934 in
    let t_941 = Pervasives.ref [] in
    let t_944 =
      Array.init t_940
        (fun i_942  ->
           Array.init t_939 (fun j_943  -> if i_942 = j_943 then 1. else 0.)) in
    while ((! t_936) < t_939) && ((! t_935) < t_940) do
      (let t_945 = ! t_935 in
       let t_946 = ! t_936 in
       let t_947 = Pervasives.ref None in
       let t_953 =
         for j_950 = t_945 to t_940 - 1 do
           (let t_951 = (t_938.(j_950)).(t_946) in
            if t_951 <> 0.
            then
              match ! t_947 with
              | Some i_952 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_952)) <
                       (Pervasives.abs_float t_951)
                   then t_947 := (Some (j_950, t_951)))
              | None  -> t_947 := (Some (j_950, t_951)))
         done;
         (match ! t_947 with
          | Some i_948 ->
              (if (Pervasives.fst i_948) <> t_945
               then
                 ((let t_949 = t_938.(t_945) in
                   t_938.(t_945) <- t_938.(Pervasives.fst i_948);
                   t_938.(Pervasives.fst i_948) <- t_949);
                  t_941 :=
                    ((Domains_common.RowSwap ((Pervasives.fst i_948), t_945))
                    :: (! t_941)));
               Some (Pervasives.snd i_948))
          | None  -> None) in
       (match t_953 with
        | Some i_954 ->
            ((for j_955 = t_945 + 1 to t_940 - 1 do
                (let t_956 = (t_938.(j_955)).(t_946) in
                 if t_956 <> 0.
                 then
                   (for j_957 = t_946 + 1 to t_939 - 1 do
                      (t_938.(j_955)).(j_957) <-
                      ((t_938.(j_955)).(j_957)) -.
                        ((t_956 /. i_954) *. ((t_938.(t_945)).(j_957)))
                    done;
                    (t_944.(j_955)).(t_946) <- t_956 /. i_954;
                    (t_938.(j_955)).(t_946) <- 0.))
              done;
              ());
             t_935 := ((! t_935) + 1))
        | None  -> ());
       t_936 := ((! t_936) + 1))
      done;
    (t_938, t_944, (! t_941))>.
  
val resFA32 : (GAC_F.contr -> GenFA32.O.res) code = .<
  fun a_958  ->
    let t_959 = Pervasives.ref 0 in
    let t_960 = Pervasives.ref 0 in
    let t_962 = Array.map (fun x_961  -> Array.copy x_961) (Array.copy a_958) in
    let t_963 = Array.length (a_958.(0)) in
    let t_964 = Array.length a_958 in
    let t_965 = Pervasives.ref [] in
    while ((! t_960) < t_963) && ((! t_959) < t_964) do
      (let t_966 = ! t_959 in
       let t_967 = ! t_960 in
       let t_968 = Pervasives.ref None in
       let t_974 =
         for j_971 = t_966 to t_964 - 1 do
           (let t_972 = (t_962.(j_971)).(t_967) in
            if t_972 <> 0.
            then
              match ! t_968 with
              | Some i_973 ->
                  (if
                     (Pervasives.abs_float (Pervasives.snd i_973)) <
                       (Pervasives.abs_float t_972)
                   then t_968 := (Some (j_971, t_972)))
              | None  -> t_968 := (Some (j_971, t_972)))
         done;
         (match ! t_968 with
          | Some i_969 ->
              (if (Pervasives.fst i_969) <> t_966
               then
                 ((let t_970 = t_962.(t_966) in
                   t_962.(t_966) <- t_962.(Pervasives.fst i_969);
                   t_962.(Pervasives.fst i_969) <- t_970);
                  t_965 :=
                    ((Domains_common.RowSwap ((Pervasives.fst i_969), t_966))
                    :: (! t_965)));
               Some (Pervasives.snd i_969))
          | None  -> None) in
       (match t_974 with
        | Some i_975 ->
            ((for j_976 = t_966 + 1 to t_964 - 1 do
                (let t_977 = (t_962.(j_976)).(t_967) in
                 if t_977 <> 0.
                 then
                   for j_978 = t_967 + 1 to t_963 - 1 do
                     (t_962.(j_976)).(j_978) <-
                     ((t_962.(j_976)).(j_978)) -.
                       ((t_977 /. i_975) *. ((t_962.(t_966)).(j_978)))
                   done)
              done;
              ());
             t_959 := ((! t_959) + 1))
        | None  -> ());
       t_960 := ((! t_960) + 1))
      done;
    (t_962, (! t_965))>.
  
val resZp3 : (GVC_Z3.contr -> GenZp3.O.res) code = .<
  fun a_979  ->
    let t_980 = Pervasives.ref 0 in
    let t_981 = Pervasives.ref 0 in
    let t_982 =
      { a_979 with Domains_common.arr = (Array.copy a_979.Domains_common.arr)
      } in
    let t_983 = a_979.Domains_common.m in
    let t_984 = a_979.Domains_common.n in
    let t_985 = Pervasives.ref 1 in
    let t_986 = Pervasives.ref 1 in
    let t_987 = Pervasives.ref [] in
    while ((! t_981) < t_983) && ((! t_980) < t_984) do
      (let t_992 = ! t_980 in
       let t_993 = ! t_981 in
       let t_994 = Pervasives.ref None in
       let t_1006 =
         (let t_1002 =
            (t_982.Domains_common.arr).((t_993 * t_982.Domains_common.m) +
                                          t_992) in
          if t_1002 <> 0
          then t_994 := (Some (t_992, t_1002))
          else
            (let rec loop_1003 j_1004 =
               if j_1004 < t_984
               then
                 let t_1005 =
                   (t_982.Domains_common.arr).((j_1004 *
                                                  t_982.Domains_common.m)
                                                 + t_993) in
                 (if t_1005 = 0
                  then loop_1003 (j_1004 + 1)
                  else t_994 := (Some (j_1004, t_1005))) in
             loop_1003 (t_992 + 1)));
         (match ! t_994 with
          | Some i_995 ->
              (if (Pervasives.fst i_995) <> t_992
               then
                 (((let a_996 = t_982.Domains_common.arr
                    and m_997 = t_982.Domains_common.m in
                    let i1_998 = t_992 * m_997
                    and i2_999 = (Pervasives.fst i_995) * m_997 in
                    for i_1000 = t_993 to m_997 - 1 do
                      let t_1001 = a_996.(i1_998 + i_1000) in
                      a_996.(i1_998 + i_1000) <- a_996.(i2_999 + i_1000);
                      a_996.(i2_999 + i_1000) <- t_1001
                    done);
                   t_986 := (- (! t_986)));
                  t_987 :=
                    ((Domains_common.RowSwap ((Pervasives.fst i_995), t_992))
                    :: (! t_987)));
               Some (Pervasives.snd i_995))
          | None  -> None) in
       (match t_1006 with
        | Some i_1007 ->
            ((for j_1008 = t_992 + 1 to t_984 - 1 do
                (let t_1009 =
                   (t_982.Domains_common.arr).((j_1008 *
                                                  t_982.Domains_common.m)
                                                 + t_993) in
                 if t_1009 <> 0
                 then
                   (for j_1010 = t_993 + 1 to t_983 - 1 do
                      (t_982.Domains_common.arr).((j_1008 *
                                                     t_982.Domains_common.m)
                                                    + j_1010)
                      <-
                      (* CSP minus *)
                        ((t_982.Domains_common.arr).((j_1008 *
                                                        t_982.Domains_common.m)
                                                       + j_1010))
                        ((* CSP times *) ((* CSP div *) t_1009 i_1007)
                           ((t_982.Domains_common.arr).((t_992 *
                                                           t_982.Domains_common.m)
                                                          + j_1010)))
                    done;
                    (t_982.Domains_common.arr).((j_1008 *
                                                   t_982.Domains_common.m)
                                                  + t_993)
                    <- 0))
              done;
              t_985 := ((* CSP times *) (! t_985) i_1007));
             t_980 := ((! t_980) + 1))
        | None  -> t_986 := 0);
       t_981 := ((! t_981) + 1))
      done;
    (t_982,
      (if (! t_986) = 0
       then 0
       else if (! t_986) = 1 then ! t_985 else (* CSP uminus *) (! t_985)),
      (! t_980), (! t_987))>.
  
val resZp19 : (GVC_Z19.contr -> GenZp19.O.res) code = .<
  fun a_1011  ->
    let t_1012 = Pervasives.ref 0 in
    let t_1013 = Pervasives.ref 0 in
    let t_1014 =
      {
        a_1011 with
        Domains_common.arr = (Array.copy a_1011.Domains_common.arr)
      } in
    let t_1015 = a_1011.Domains_common.m in
    let t_1016 = a_1011.Domains_common.n in
    let t_1017 = Pervasives.ref 1 in
    let t_1018 = Pervasives.ref 1 in
    let t_1019 = Pervasives.ref [] in
    while ((! t_1013) < t_1015) && ((! t_1012) < t_1016) do
      (let t_1024 = ! t_1012 in
       let t_1025 = ! t_1013 in
       let t_1026 = Pervasives.ref None in
       let t_1038 =
         (let t_1034 =
            (t_1014.Domains_common.arr).((t_1025 * t_1014.Domains_common.m) +
                                           t_1024) in
          if t_1034 <> 0
          then t_1026 := (Some (t_1024, t_1034))
          else
            (let rec loop_1035 j_1036 =
               if j_1036 < t_1016
               then
                 let t_1037 =
                   (t_1014.Domains_common.arr).((j_1036 *
                                                   t_1014.Domains_common.m)
                                                  + t_1025) in
                 (if t_1037 = 0
                  then loop_1035 (j_1036 + 1)
                  else t_1026 := (Some (j_1036, t_1037))) in
             loop_1035 (t_1024 + 1)));
         (match ! t_1026 with
          | Some i_1027 ->
              (if (Pervasives.fst i_1027) <> t_1024
               then
                 (((let a_1028 = t_1014.Domains_common.arr
                    and m_1029 = t_1014.Domains_common.m in
                    let i1_1030 = t_1024 * m_1029
                    and i2_1031 = (Pervasives.fst i_1027) * m_1029 in
                    for i_1032 = t_1025 to m_1029 - 1 do
                      let t_1033 = a_1028.(i1_1030 + i_1032) in
                      a_1028.(i1_1030 + i_1032) <- a_1028.(i2_1031 + i_1032);
                      a_1028.(i2_1031 + i_1032) <- t_1033
                    done);
                   t_1018 := (- (! t_1018)));
                  t_1019 :=
                    ((Domains_common.RowSwap
                        ((Pervasives.fst i_1027), t_1024))
                    :: (! t_1019)));
               Some (Pervasives.snd i_1027))
          | None  -> None) in
       (match t_1038 with
        | Some i_1039 ->
            ((for j_1040 = t_1024 + 1 to t_1016 - 1 do
                (let t_1041 =
                   (t_1014.Domains_common.arr).((j_1040 *
                                                   t_1014.Domains_common.m)
                                                  + t_1025) in
                 if t_1041 <> 0
                 then
                   (for j_1042 = t_1025 + 1 to t_1015 - 1 do
                      (t_1014.Domains_common.arr).((j_1040 *
                                                      t_1014.Domains_common.m)
                                                     + j_1042)
                      <-
                      (* CSP div *)
                        ((* CSP minus *)
                           ((* CSP times *)
                              ((t_1014.Domains_common.arr).((j_1040 *
                                                               t_1014.Domains_common.m)
                                                              + j_1042))
                              i_1039)
                           ((* CSP times *)
                              ((t_1014.Domains_common.arr).((t_1024 *
                                                               t_1014.Domains_common.m)
                                                              + j_1042))
                              t_1041)) (! t_1017)
                    done;
                    (t_1014.Domains_common.arr).((j_1040 *
                                                    t_1014.Domains_common.m)
                                                   + t_1025)
                    <- 0))
              done;
              t_1017 := i_1039);
             t_1012 := ((! t_1012) + 1))
        | None  -> t_1018 := 0);
       t_1013 := ((! t_1013) + 1))
      done;
    (t_1014,
      (if (! t_1018) = 0
       then 0
       else if (! t_1018) = 1 then ! t_1017 else (* CSP uminus *) (! t_1017)),
      (! t_1012), (! t_1019))>.
  
val rFA1 : GAC_F.contr -> GenFA1.O.res = <fun>
val rFA2 : GAC_F.contr -> GenFA2.O.res = <fun>
val rFA3 : GAC_F.contr -> GenFA3.O.res = <fun>
val rFA4 : GAC_F.contr -> GenFA4.O.res = <fun>
File "domains_code.ml", line 142, characters 31-34:
Error: Unbound record field Domains_common.arr

Exception: Failure "Error type-checking generated code: scope extrusion?".
# 
